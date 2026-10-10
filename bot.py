"""
国旗リアクション翻訳 Discord BOT (PLaMo API 利用)

メッセージに国旗の絵文字リアクションが付けられると、
その国旗に対応する言語へメッセージを翻訳し、
チャンネルに返信（全員に見える形）で投稿します。
"""

import asyncio
import difflib
import json
import logging
import math
import os
import re
import time
from collections import OrderedDict

import aiohttp
import discord
from dotenv import load_dotenv

load_dotenv()

DISCORD_TOKEN = os.environ["DISCORD_TOKEN"]
PLAMO_API_KEY = os.environ["PLAMO_API_KEY"]

PLAMO_ENDPOINT = "https://api.platform.preferredai.jp/v1/chat/completions"
PLAMO_MODEL = "plamo-3.0-prime"

# 起動ログに表示。新しいコードが動いているかの確認用
BOT_VERSION = "4 (admin-only commands, per-server ban)"

# max_tokens 未指定だと 20480 が入り、入力+max_tokens がコンテキスト長を
# 超えるとエラーになるため、明示的に指定する
MAX_TOKENS = 8192
# 翻訳対象の最大文字数（長すぎるメッセージは拒否）
MAX_SOURCE_CHARS = 4000

DISCORD_MESSAGE_LIMIT = 2000
CACHE_SIZE = 500

# 国旗絵文字 -> (表示名, プロンプトで使う言語名)
FLAG_LANGUAGES: dict[str, tuple[str, str]] = {
    "🇯🇵": ("日本語", "Japanese"),
    "🇺🇸": ("English", "English"),
    "🇬🇧": ("English", "English"),
    "🇦🇺": ("English", "English"),
    "🇨🇦": ("English", "English"),
    "🇨🇳": ("简体中文", "Simplified Chinese"),
    "🇹🇼": ("繁體中文", "Traditional Chinese"),
    "🇭🇰": ("繁體中文(香港)", "Traditional Chinese (Hong Kong)"),
    "🇰🇷": ("한국어", "Korean"),
    "🇫🇷": ("Français", "French"),
    "🇩🇪": ("Deutsch", "German"),
    "🇪🇸": ("Español", "Spanish"),
    "🇲🇽": ("Español", "Spanish"),
    "🇮🇹": ("Italiano", "Italian"),
    "🇵🇹": ("Português", "Portuguese"),
    "🇧🇷": ("Português (Brasil)", "Brazilian Portuguese"),
    "🇷🇺": ("Русский", "Russian"),
    "🇺🇦": ("Українська", "Ukrainian"),
    "🇵🇱": ("Polski", "Polish"),
    "🇳🇱": ("Nederlands", "Dutch"),
    "🇸🇪": ("Svenska", "Swedish"),
    "🇳🇴": ("Norsk", "Norwegian"),
    "🇩🇰": ("Dansk", "Danish"),
    "🇫🇮": ("Suomi", "Finnish"),
    "🇬🇷": ("Ελληνικά", "Greek"),
    "🇹🇷": ("Türkçe", "Turkish"),
    "🇸🇦": ("العربية", "Arabic"),
    "🇦🇪": ("العربية", "Arabic"),
    "🇮🇱": ("עברית", "Hebrew"),
    "🇮🇳": ("हिन्दी", "Hindi"),
    "🇧🇩": ("বাংলা", "Bengali"),
    "🇹🇭": ("ภาษาไทย", "Thai"),
    "🇻🇳": ("Tiếng Việt", "Vietnamese"),
    "🇮🇩": ("Bahasa Indonesia", "Indonesian"),
    "🇲🇾": ("Bahasa Melayu", "Malay"),
    "🇵🇭": ("Filipino", "Filipino (Tagalog)"),
    "🇨🇿": ("Čeština", "Czech"),
    "🇭🇺": ("Magyar", "Hungarian"),
    "🇷🇴": ("Română", "Romanian"),
}

logging.basicConfig(level=logging.INFO)
log = logging.getLogger("translate-bot")

intents = discord.Intents.default()
intents.reactions = True
intents.guilds = True
intents.messages = True
# メッセージ本文を読むために必要（Developer Portal で Message Content Intent を ON にすること）
intents.message_content = True

client = discord.Client(intents=intents)

http_session: aiohttp.ClientSession | None = None

# 同じメッセージ x 同じ言語の重複翻訳を防ぐためのキャッシュ / 実行中セット
translation_cache: "OrderedDict[tuple[int, str], bool]" = OrderedDict()
in_flight: set[tuple[int, str]] = set()


# 翻訳機能の利用を禁止されたユーザー（サーバーごとに管理。再起動しても残るよう JSON に保存）
BANNED_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "banned_users.json")


def load_banned() -> dict[int, set[int]]:
    try:
        with open(BANNED_FILE, encoding="utf-8") as f:
            data = json.load(f)
        # {"サーバーID": [ユーザーID, ...]} の形式のみ読み込む
        if isinstance(data, dict):
            return {int(g): {int(u) for u in users} for g, users in data.items()}
        return {}
    except FileNotFoundError:
        return {}
    except Exception:
        log.exception("banned_users.json の読み込みに失敗しました")
        return {}


def save_banned() -> None:
    tmp = BANNED_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump({str(g): sorted(u) for g, u in banned_users.items() if u}, f)
    os.replace(tmp, BANNED_FILE)


banned_users: dict[int, set[int]] = load_banned()


class UntranslatedError(Exception):
    """翻訳できなかった（原文のまま / 別の言語 / 空）。"""


def _normalize(s: str) -> str:
    return "".join(s.split()).lower()


_HANGUL = re.compile(r"[\u1100-\u11ff\u3130-\u318f\uac00-\ud7af]")
_KANA = re.compile(r"[\u3040-\u30ff]")
_HAN = re.compile(r"[\u3400-\u4dbf\u4e00-\u9fff]")
_CYRILLIC = re.compile(r"[\u0400-\u04ff]")
_GREEK = re.compile(r"[\u0370-\u03ff]")
_ARABIC = re.compile(r"[\u0600-\u06ff\u0750-\u077f]")
_HEBREW = re.compile(r"[\u0590-\u05ff]")
_DEVANAGARI = re.compile(r"[\u0900-\u097f]")
_BENGALI = re.compile(r"[\u0980-\u09ff]")
_THAI = re.compile(r"[\u0e00-\u0e7f]")

# 非ラテン文字の言語は、出力にその文字種が十分含まれているかを確認する
SCRIPT_REQUIRED = {
    "Korean": _HANGUL,
    "Russian": _CYRILLIC,
    "Ukrainian": _CYRILLIC,
    "Greek": _GREEK,
    "Arabic": _ARABIC,
    "Hebrew": _HEBREW,
    "Hindi": _DEVANAGARI,
    "Bengali": _BENGALI,
    "Thai": _THAI,
}


def _script_ok(output: str, language: str) -> bool:
    """出力が目的の言語の文字種で書かれているかを確認する。"""
    letters = [c for c in output if c.isalpha()]
    if not letters:
        return True
    n = len(letters)

    def frac(pattern: re.Pattern) -> float:
        return sum(1 for c in letters if pattern.match(c)) / n

    if language == "Japanese":
        return True
    if "Chinese" in language:
        return frac(_HAN) >= 0.5 and frac(_KANA) <= 0.05
    required = SCRIPT_REQUIRED.get(language)
    if required is not None:
        return frac(required) >= 0.5
    # ラテン文字系の言語: 日本語・中国語・ハングルが多ければ失敗とみなす
    return frac(_KANA) + frac(_HAN) + frac(_HANGUL) <= 0.2


def _is_valid(source: str, output: str, language: str) -> bool:
    if not output:
        return False
    a, b = _normalize(source), _normalize(output)
    if a == b or difflib.SequenceMatcher(None, a, b).ratio() > 0.9:
        return False
    return _script_ok(output, language)


def _clean_output(output: str) -> str:
    """モデルが付けがちな <text> タグを取り除く。"""
    out = output.strip()
    out = re.sub(r"^\s*</?text>\s*|\s*</?text>\s*$", "", out).strip()
    return out


async def _call_plamo(
    messages: list[dict], temperature: float, reasoning: bool = False
) -> str:
    assert http_session is not None

    payload = {
        "model": PLAMO_MODEL,
        "messages": messages,
        "temperature": temperature,
        # reasoning のトークンも max_tokens に含まれるため、有効時は多めに確保する
        "max_tokens": 8192 if reasoning else MAX_TOKENS,
        "reasoning_effort": "medium" if reasoning else "none",
    }
    headers = {
        "Authorization": f"Bearer {PLAMO_API_KEY}",
        "Content-Type": "application/json",
    }

    async with http_session.post(
        PLAMO_ENDPOINT,
        json=payload,
        headers=headers,
        timeout=aiohttp.ClientTimeout(total=120),
    ) as resp:
        body = await resp.text()
        if resp.status != 200:
            raise RuntimeError(f"PLaMo API error {resp.status}: {body[:300]}")
        data = await resp.json(content_type=None)

    # content が最終的な回答。reasoning / reasoning_content は推論過程なので使わない
    content = (data["choices"][0]["message"].get("content") or "").strip()
    if not content:
        raise RuntimeError("PLaMo API returned an empty translation")
    return content


async def _translate_once(
    text: str,
    target_language: str,
    temperature: float = 0.2,
    strict: bool = False,
    reasoning: bool = False,
) -> str:
    system = (
        "あなたはプロの翻訳者です。"
        f"ユーザーが与える文章を、必ず{target_language}に翻訳してください。"
        f"入力文が{target_language}以外の言語で書かれている場合、原文をそのまま出力してはいけません。"
        "出力は翻訳文のみとし、説明・注釈・引用符・「翻訳:」などの前置きは付けないでください。"
        "改行、Markdown、絵文字、URL、Discordのメンションやカスタム絵文字"
        "（<@123>, <#123>, <:name:123> など）はそのまま保持してください。"
    )
    user = f"次の文章を{target_language}に翻訳してください。\n\n<text>\n{text}\n</text>"
    if strict:
        user += (
            "\n\n注意: 前回は翻訳されず原文のまま出力されました。"
            f"今回は必ず{target_language}の文字・単語で書いてください。"
        )

    output = await _call_plamo(
        [
            {"role": "system", "content": system},
            {"role": "user", "content": user},
        ],
        temperature=temperature,
        reasoning=reasoning,
    )
    return _clean_output(output)


async def translate(text: str, target_language: str) -> str:
    """text を target_language に翻訳する。

    target_language は「Korean (한국어)」のような表示用ラベルでもよい。
    1. 通常の翻訳
    2. 失敗（原文のまま / 目的の文字種でない）なら、プロンプトを強め reasoning を有効にして再試行
    3. それでもだめなら英語を経由（原文 -> 英語 -> 目的の言語）
    すべて失敗したら UntranslatedError。
    """
    # 文字種チェック用の言語名（"Korean (한국어)" -> "Korean"）
    base = target_language.split(" (")[0]

    # 1回目: 通常
    out = await _translate_once(text, target_language)
    if _is_valid(text, out, base):
        return out
    log.warning("[%s] 1回目: 無効な出力。出力=%r", base, out[:80])

    # 2回目: reasoning を有効にして再試行
    out = await _translate_once(
        text, target_language, temperature=0.6, strict=True, reasoning=True
    )
    if _is_valid(text, out, base):
        return out
    log.warning("[%s] 2回目(reasoning): 無効な出力。出力=%r", base, out[:80])

    # 3回目: 英語を経由
    if base != "English":
        english = await _translate_once(text, "English")
        if _is_valid(text, english, "English"):
            out = await _translate_once(
                english, target_language, temperature=0.3, strict=True, reasoning=True
            )
            if _is_valid(english, out, base) and _is_valid(text, out, base):
                log.info("[%s] 英語経由で翻訳に成功", base)
                return out
            log.warning("[%s] 英語経由の2段目が無効。出力=%r", base, out[:80])
        else:
            log.warning("[English] 英語への翻訳が無効。出力=%r", english[:80])

    raise UntranslatedError()


def build_source_text(message: discord.Message) -> str:
    """翻訳対象のテキストを取り出す（本文が空なら embed の説明文を使う）。"""
    text = message.content.strip()
    if not text and message.embeds:
        parts = []
        for e in message.embeds:
            if e.title:
                parts.append(e.title)
            if e.description:
                parts.append(e.description)
        text = "\n".join(parts).strip()
    return text


def split_for_discord(text: str, limit: int = DISCORD_MESSAGE_LIMIT) -> list[str]:
    """Discord の文字数制限に収まるよう分割する。"""
    chunks = []
    while len(text) > limit:
        cut = text.rfind("\n", 0, limit)
        if cut <= 0:
            cut = limit
        chunks.append(text[:cut])
        text = text[cut:].lstrip("\n")
    if text:
        chunks.append(text)
    return chunks


@client.event
async def on_ready():
    global http_session
    if http_session is None:
        http_session = aiohttp.ClientSession()
    log.info("Logged in as %s (id=%s)", client.user, client.user.id)
    log.info("bot version: %s", BOT_VERSION)


_ID_PATTERN = re.compile(r"\d{17,20}")


@client.event
async def on_message(message: discord.Message):
    """管理コマンド: !ping / !t-ban / !t-unban（サーバーの管理者権限を持つ人のみ）。"""
    if message.author.bot or message.guild is None:
        return

    cmd, _, arg = message.content.strip().partition(" ")
    cmd = cmd.lower()
    if cmd not in ("!ping", "!t-ban", "!t-unban"):
        return
    # 管理者権限を持たない人には何も反応しない
    perms = getattr(message.author, "guild_permissions", None)
    if perms is None or not perms.administrator:
        return

    if cmd == "!ping":
        # Gateway(WebSocket) のレイテンシ
        latency = client.latency
        gateway_ms = f"{latency * 1000:.0f} ms" if not math.isnan(latency) else "N/A"

        # メッセージ送信にかかった時間（REST API の往復）
        start = time.perf_counter()
        sent = await message.reply("🏓 計測中...", mention_author=False)
        api_ms = (time.perf_counter() - start) * 1000

        await sent.edit(
            content=f"🏓 Pong!\nGateway: **{gateway_ms}**\nAPI: **{api_ms:.0f} ms**"
        )
        return

    # --- !t-ban / !t-unban: メンションまたはユーザーIDを指定 ---
    no_mentions = discord.AllowedMentions.none()
    m = _ID_PATTERN.search(arg)
    if not m:
        await message.reply(
            f"使い方: `{cmd} @ユーザー` または `{cmd} ユーザーID`",
            mention_author=False,
            allowed_mentions=no_mentions,
        )
        return
    target_id = int(m.group())
    banned = banned_users.setdefault(message.guild.id, set())

    if cmd == "!t-ban":
        member = message.guild.get_member(target_id) or next(
            (u for u in message.mentions if u.id == target_id), None
        )
        is_admin = bool(
            member
            and getattr(member, "guild_permissions", None)
            and member.guild_permissions.administrator
        )
        if is_admin or (client.user and target_id == client.user.id):
            await message.reply(
                "このユーザーは禁止できません。",
                mention_author=False,
                allowed_mentions=no_mentions,
            )
            return
        if target_id in banned:
            text = f"<@{target_id}> はすでに翻訳機能を禁止されています。"
        else:
            banned.add(target_id)
            save_banned()
            text = f"🔨 <@{target_id}> を翻訳機能の利用禁止にしました。"
    else:  # !t-unban
        if target_id in banned:
            banned.discard(target_id)
            save_banned()
            text = f"✅ <@{target_id}> の翻訳機能の禁止を解除しました。"
        else:
            text = f"<@{target_id}> は禁止されていません。"

    await message.reply(text, mention_author=False, allowed_mentions=no_mentions)


@client.event
async def on_raw_reaction_add(payload: discord.RawReactionActionEvent):
    # BOT 自身のリアクションは無視
    if client.user and payload.user_id == client.user.id:
        return

    # 翻訳機能を禁止されたユーザーのリアクションは無反応
    if payload.guild_id and payload.user_id in banned_users.get(payload.guild_id, ()):
        return

    flag = str(payload.emoji)
    if flag not in FLAG_LANGUAGES:
        return

    display_name, language = FLAG_LANGUAGES[flag]
    key = (payload.message_id, language)

    # すでに翻訳済み / 翻訳中なら何もしない
    if key in translation_cache or key in in_flight:
        return
    in_flight.add(key)

    try:
        channel = client.get_channel(payload.channel_id) or await client.fetch_channel(
            payload.channel_id
        )
        message = await channel.fetch_message(payload.message_id)

        # BOT の翻訳結果自体は再翻訳しない
        if client.user and message.author.id == client.user.id:
            return

        source = build_source_text(message)
        if not source:
            return
        if len(source) > MAX_SOURCE_CHARS:
            await message.reply(
                f"{flag} メッセージが長すぎるため翻訳できません（{MAX_SOURCE_CHARS}文字まで）。",
                mention_author=False,
            )
            return

        async with channel.typing():
            lang_label = language if display_name == language else f"{language} ({display_name})"
            translated = await translate(source, lang_label)

        header = f"{flag} **{display_name}** に翻訳しました:\n"
        chunks = split_for_discord(header + translated)

        # 最初の1通は元メッセージへの返信、残りは続けて投稿（全員に表示される）
        first = await message.reply(
            chunks[0],
            mention_author=False,
            allowed_mentions=discord.AllowedMentions.none(),
        )
        for chunk in chunks[1:]:
            await channel.send(
                chunk, allowed_mentions=discord.AllowedMentions.none()
            )

        translation_cache[key] = True
        while len(translation_cache) > CACHE_SIZE:
            translation_cache.popitem(last=False)

    except UntranslatedError:
        try:
            await message.reply(
                f"{flag} {display_name} に翻訳できませんでした"
                "（すでにその言語の文章か、モデルが翻訳に失敗しました）。",
                mention_author=False,
                delete_after=20,
            )
        except Exception:
            pass
    except discord.Forbidden:
        log.warning("権限不足: channel=%s", payload.channel_id)
    except discord.NotFound:
        log.warning("メッセージまたはチャンネルが見つかりません")
    except Exception as e:
        log.exception("翻訳に失敗しました")
        try:
            channel = client.get_channel(payload.channel_id)
            if channel:
                await channel.send(
                    f"{flag} 翻訳に失敗しました。しばらくしてからもう一度お試しください。",
                    delete_after=15,
                )
        except Exception:
            pass
    finally:
        in_flight.discard(key)


async def main():
    async with client:
        await client.start(DISCORD_TOKEN)


if __name__ == "__main__":
    try:
        asyncio.run(main())
    finally:
        if http_session and not http_session.closed:
            asyncio.run(http_session.close())
