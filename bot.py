"""
Discord <-> Roblox profile board bot (discord.py 2.x)

A channel shows everyone who linked an account. Each message is one image with up to
3 people (3 columns x 1 row): Discord avatar + name on the left, Roblox full-body
skin + name on the right. Changes edit the messages in place; /repost (and an automatic
repost every hour) sends fresh messages so the "(edited)" mark disappears.

Commands:
    /link roblox_name [user]   link your Roblox account (admins can link someone else)
    /unlink [user]             remove a link (admins can remove someone else's)
    /search query              find someone by Discord name, Roblox name or ID
    /custom color [color] [border]   set your own card background / border colour (#RRGGBB)
    /custom banner image       use a picture as your whole card background
    /custom reset [user]       remove your customisation (only the bot owner can reset someone else's)
    /setup channel             (admin) choose the channel that shows the board
    /repost                    (bot owner) send the board again as fresh messages
    /export                    (admin) download every profile as a JSON file
    /import file               (admin) load a JSON file made by /export
                               (banner pictures live in the banners/ folder, copy it too)
"""
from __future__ import annotations

import asyncio
import hashlib
import io
import json
import math
import os
import re
import shutil
import traceback
from datetime import datetime, timezone
from functools import lru_cache
from pathlib import Path
from typing import Any, Optional

import aiohttp
import discord
from aiohttp import web
from discord import app_commands
from discord.ext import commands, tasks
from dotenv import load_dotenv
from PIL import Image, ImageDraw, ImageFont, ImageOps

load_dotenv()

# ────────────────────────────── CONFIG ──────────────────────────────
PROFILES_FILE = Path(os.getenv("PROFILES_FILE", "profiles.json"))
STATE_FILE = Path(os.getenv("STATE_FILE", "profile_board_state.json"))
FONT_PATH = os.getenv("FONT_PATH", "")
BANNER_DIR = Path(os.getenv("BANNER_DIR", "banners"))

SCHEMA_VERSION = 1          # version of the /export file format
RENDER_VERSION = 3         # bump when the card layout changes so every page is redrawn
PAGE_SIZE = 3               # people per image
COLS = 3                    # columns per image (3 people -> 3 x 1)
REFRESH_HOURS = 6           # how often names and avatars are re-fetched
REPOST_HOURS = 1            # how often the board is re-sent as fresh messages
SYNC_DELAY = 3              # seconds to wait so several changes become one board update
MAX_IMPORT_BYTES = 5_000_000
MAX_BANNER_BYTES = 8_000_000

CELL_W, CELL_H, GAP = 440, 340, 10
LEFT_W = 170                # width of the Discord half of a card
BODY = 250                  # Roblox full-body picture size
AV = 112                    # Discord avatar size
AV_BORDER = 2

BG_COLOR = (27, 27, 22)
CARD_COLOR = (42, 42, 37)
EMPTY_COLOR = (34, 34, 29)  # unused slot in a page
NAME_COLOR = (255, 255, 255)
LABEL_COLOR = (150, 150, 150)


# ────────────────────────────── STORAGE ──────────────────────────────
class JsonFile:
    """JSON file with atomic writes and a .bak copy of the previous version.
    A corrupt file raises instead of silently becoming empty, so it can't be overwritten."""

    def __init__(self, path: Path, default: Any) -> None:
        self.path = path
        self.default = default

    def load(self) -> Any:
        if not self.path.exists():
            return json.loads(json.dumps(self.default))
        try:
            return json.loads(self.path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            raise RuntimeError(
                f"{self.path} is corrupt ({exc}). Fix it or restore {self.path.with_suffix('.bak')}; "
                "refusing to continue so nothing gets overwritten."
            ) from exc

    def save(self, data: Any) -> None:
        tmp = self.path.with_suffix(".tmp")
        tmp.write_text(json.dumps(data, indent=2, ensure_ascii=False), encoding="utf-8")
        if self.path.exists():
            shutil.copy2(self.path, self.path.with_suffix(".bak"))
        os.replace(tmp, self.path)


store = JsonFile(PROFILES_FILE, [])        # [{discord_id, roblox_id, discord_name, roblox_name, linked_at}]
state_file = JsonFile(STATE_FILE, {})      # {guild, channel, pages: [{message, hash}]}
data_lock = asyncio.Lock()                 # profile changes
sync_lock = asyncio.Lock()                 # board updates


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


# ────────────────────────────── ROBLOX API ──────────────────────────────
class RobloxAPI:
    def __init__(self) -> None:
        self.session: Optional[aiohttp.ClientSession] = None

    async def start(self) -> None:
        self.session = aiohttp.ClientSession(
            timeout=aiohttp.ClientTimeout(total=15),
            headers={"User-Agent": "RobloxProfileBoardBot/1.0"},
        )

    async def close(self) -> None:
        if self.session:
            await self.session.close()

    async def _json(self, method: str, url: str, **kw: Any) -> Optional[dict]:
        try:
            assert self.session
            async with self.session.request(method, url, **kw) as r:
                if r.status != 200:
                    print(f"[roblox] {method} {url} -> {r.status} {(await r.text())[:200]}")
                    return None
                return await r.json()
        except (aiohttp.ClientError, asyncio.TimeoutError) as exc:
            print(f"[roblox] {method} {url} failed: {exc!r}")
            return None

    async def image(self, url: str) -> Optional[bytes]:
        try:
            assert self.session
            async with self.session.get(url) as r:
                return await r.read() if r.status == 200 else None
        except (aiohttp.ClientError, asyncio.TimeoutError) as exc:
            print(f"[roblox] image {url} failed: {exc!r}")
            return None

    async def lookup(self, username: str) -> Optional[tuple[int, str]]:
        """Return (user id, canonical username) or None"""
        data = await self._json(
            "POST",
            "https://users.roblox.com/v1/usernames/users",
            json={"usernames": [username], "excludeBannedUsers": False},
        )
        if data and data.get("data"):
            row = data["data"][0]
            return int(row["id"]), row["name"]
        return None

    async def names(self, ids: list[int]) -> dict[int, str]:
        out: dict[int, str] = {}
        for i in range(0, len(ids), 100):
            data = await self._json(
                "POST",
                "https://users.roblox.com/v1/users",
                json={"userIds": ids[i : i + 100], "excludeBannedUsers": False},
            )
            for row in (data or {}).get("data", []):
                out[int(row["id"])] = row["name"]
        return out

    async def body_urls(self, ids: list[int]) -> dict[int, str]:
        """Full-body picture URL per user id"""
        urls: dict[int, str] = {}
        pending = ids
        for _ in range(5):  # Roblox answers "Pending" while it renders
            if not pending:
                break
            retry: list[int] = []
            for i in range(0, len(pending), 100):
                data = await self._json(
                    "GET",
                    "https://thumbnails.roblox.com/v1/users/avatar",
                    params={
                        "userIds": ",".join(map(str, pending[i : i + 100])),
                        "size": "420x420",
                        "format": "Png",
                        "isCircular": "false",
                    },
                )
                for item in (data or {}).get("data", []):
                    if item.get("state") == "Completed" and item.get("imageUrl"):
                        urls[int(item["targetId"])] = item["imageUrl"]
                    elif item.get("state") == "Pending":
                        retry.append(int(item["targetId"]))
            pending = retry
            if pending:
                await asyncio.sleep(1)
        return urls


rbx = RobloxAPI()

# In-memory caches. Failed refreshes keep the old entry, so a bad API moment never blanks a card.
discord_cache: dict[int, dict] = {}   # id -> {name, key, avatar}
roblox_cache: dict[int, dict] = {}    # id -> {name, url, img}


async def refresh_info(force: bool = False) -> None:
    """Fetch names and pictures that are missing (or everything when force=True),
    then store the latest names in the profile file."""
    async with data_lock:
        profiles = store.load()

    # Discord
    sem = asyncio.Semaphore(8)

    async def load_discord(uid: int) -> None:
        async with sem:
            old = discord_cache.get(uid, {})
            try:
                user = await bot.fetch_user(uid)
            except discord.HTTPException:
                return
            asset = user.display_avatar.replace(size=256, format="png")
            entry = {"name": user.display_name, "key": user.display_avatar.key, "avatar": old.get("avatar")}
            if old.get("key") != entry["key"] or not entry["avatar"]:
                try:
                    entry["avatar"] = await asset.read()
                except discord.HTTPException:
                    pass
            discord_cache[uid] = entry

    await asyncio.gather(
        *(load_discord(p["discord_id"]) for p in profiles if force or p["discord_id"] not in discord_cache)
    )

    # Roblox
    ids = [p["roblox_id"] for p in profiles if force or p["roblox_id"] not in roblox_cache]
    if ids:
        names, urls = await asyncio.gather(rbx.names(ids), rbx.body_urls(ids))
        for rid in ids:
            entry = dict(roblox_cache.get(rid, {}))
            if rid in names:
                entry["name"] = names[rid]
            if rid in urls and urls[rid] != entry.get("url"):
                img = await rbx.image(urls[rid])
                if img:
                    entry["url"], entry["img"] = urls[rid], img
            if entry:
                roblox_cache[rid] = entry

    # keep the stored (and exported) names current
    async with data_lock:
        profiles = store.load()
        dirty = False
        for p in profiles:
            d = discord_cache.get(p["discord_id"], {})
            r = roblox_cache.get(p["roblox_id"], {})
            if d.get("name") and d["name"] != p.get("discord_name"):
                p["discord_name"], dirty = d["name"], True
            if r.get("name") and r["name"] != p.get("roblox_name"):
                p["roblox_name"], dirty = r["name"], True
        if dirty:
            store.save(profiles)


HEX_RE = re.compile(r"^#?([0-9a-fA-F]{6})$")
BANNER_NAME_RE = re.compile(r"^\d+\.png$")


def parse_hex(text: Optional[str]) -> Optional[str]:
    """'ff0000' / '#FF0000' -> '#FF0000', anything else -> None"""
    m = HEX_RE.match((text or "").strip())
    return "#" + m.group(1).upper() if m else None


def hex_rgb(code: str) -> tuple[int, int, int]:
    return int(code[1:3], 16), int(code[3:5], 16), int(code[5:7], 16)


def lighten(rgb: tuple[int, int, int]) -> tuple[int, int, int]:
    return tuple(min(255, int(c + (255 - c) * 0.35)) for c in rgb)  # type: ignore[return-value]


def card_for(p: dict) -> dict:
    d = discord_cache.get(p["discord_id"], {})
    r = roblox_cache.get(p["roblox_id"], {})

    bg = hex_rgb(p["color"]) if p.get("color") else None
    border = hex_rgb(p["border"]) if p.get("border") else (lighten(bg) if bg else None)
    banner = BANNER_DIR / p["banner"] if p.get("banner") else None
    if banner and not banner.exists():
        banner = None
    if banner or not bg:
        text = NAME_COLOR
    else:  # dark text on light backgrounds so names stay readable
        text = (20, 20, 20) if (0.299 * bg[0] + 0.587 * bg[1] + 0.114 * bg[2]) > 170 else NAME_COLOR

    return {
        "discord_name": d.get("name") or p.get("discord_name") or str(p["discord_id"]),
        "discord_avatar": d.get("avatar"),
        "roblox_name": r.get("name") or p.get("roblox_name") or str(p["roblox_id"]),
        "roblox_img": r.get("img"),
        "bg": bg,
        "border": border,
        "banner": banner,
        "text": text,
    }


def ordered_profiles() -> list[dict]:
    """Profiles in the order they were linked, so a new person lands at the end of the board"""
    return store.load()


# ────────────────────────────── IMAGE ──────────────────────────────
@lru_cache(maxsize=None)
def get_font(size: int) -> ImageFont.FreeTypeFont:
    if FONT_PATH:
        try:
            return ImageFont.truetype(FONT_PATH, size)
        except OSError:
            print(f"[font] could not open {FONT_PATH}, using the default font")
    return ImageFont.load_default(size=size)


def fit_text(draw: ImageDraw.ImageDraw, text: str, font: ImageFont.FreeTypeFont, max_w: int) -> str:
    if draw.textlength(text, font=font) <= max_w:
        return text
    while len(text) > 1 and draw.textlength(text + "…", font=font) > max_w:
        text = text[:-1]
    return text + "…"


def draw_centered(draw: ImageDraw.ImageDraw, cx: int, y: int, text: str, size: int, fill: tuple, max_w: int) -> None:
    font = get_font(size)
    text = fit_text(draw, text, font, max_w)
    draw.text((cx - draw.textlength(text, font=font) / 2, y), text, font=font, fill=fill)


def circle_avatar(data: Optional[bytes]) -> Image.Image:
    size = AV * 4  # draw big, shrink for smooth edges
    im: Optional[Image.Image] = None
    if data:
        try:
            im = Image.open(io.BytesIO(data)).convert("RGBA").resize((size, size), Image.Resampling.LANCZOS)
        except Exception:
            im = None
    if im is None:
        im = Image.new("RGBA", (size, size), (90, 90, 90, 255))
    mask = Image.new("L", (size, size), 0)
    ImageDraw.Draw(mask).ellipse((0, 0, size - 1, size - 1), fill=255)
    out = Image.new("RGBA", (size, size), (0, 0, 0, 0))
    out.paste(im, (0, 0), mask)
    ImageDraw.Draw(out).ellipse((0, 0, size - 1, size - 1), outline=(255, 255, 255, 255), width=AV_BORDER * 4)
    return out.resize((AV, AV), Image.Resampling.LANCZOS)


def roblox_body(data: Optional[bytes]) -> Image.Image:
    if data:
        try:
            return Image.open(io.BytesIO(data)).convert("RGBA").resize((BODY, BODY), Image.Resampling.LANCZOS)
        except Exception:
            pass
    out = Image.new("RGBA", (BODY, BODY), (0, 0, 0, 0))
    ImageDraw.Draw(out).rounded_rectangle((BODY // 2 - 55, 20, BODY // 2 + 55, BODY - 20), radius=24, fill=(90, 90, 90, 255))
    return out


@lru_cache(maxsize=1)
def card_mask() -> Image.Image:
    mask = Image.new("L", (CELL_W, CELL_H), 0)
    ImageDraw.Draw(mask).rounded_rectangle((0, 0, CELL_W - 1, CELL_H - 1), radius=18, fill=255)
    return mask


def banner_image(path: Path) -> Optional[Image.Image]:
    """Banner as a full-card background, darkened so names and skins stay readable"""
    try:
        im = ImageOps.fit(Image.open(path).convert("RGB"), (CELL_W, CELL_H), Image.Resampling.LANCZOS)
    except Exception:
        return None
    black = Image.new("RGB", im.size, (0, 0, 0))
    im = Image.blend(im, black, 0.3)
    band = Image.new("L", im.size, 0)
    ImageDraw.Draw(band).rectangle((0, 14 + BODY, CELL_W, CELL_H), fill=150)  # extra shade behind the names
    im.paste(black, (0, 0), band)
    return im


def render_page(cards: list[dict]) -> bytes:
    n = len(cards)
    cols, rows = COLS, max(1, math.ceil(n / COLS))  # always a full frame, even with 1 or 2 people
    img = Image.new("RGB", (cols * CELL_W + (cols + 1) * GAP, rows * CELL_H + (rows + 1) * GAP), BG_COLOR)
    draw = ImageDraw.Draw(img)
    right_cx = LEFT_W + (CELL_W - LEFT_W) // 2

    for i in range(n, cols * rows):  # empty slots keep the frame
        r, col = divmod(i, COLS)
        x, y = GAP + col * (CELL_W + GAP), GAP + r * (CELL_H + GAP)
        draw.rounded_rectangle((x, y, x + CELL_W - 1, y + CELL_H - 1), radius=18, fill=EMPTY_COLOR)

    for i, c in enumerate(cards):
        r, col = divmod(i, COLS)
        x, y = GAP + col * (CELL_W + GAP), GAP + r * (CELL_H + GAP)
        banner = banner_image(c["banner"]) if c["banner"] else None
        if banner:
            img.paste(banner, (x, y), card_mask())
        else:
            draw.rounded_rectangle((x, y, x + CELL_W - 1, y + CELL_H - 1), radius=18, fill=c["bg"] or CARD_COLOR)
        if c["border"]:
            draw.rounded_rectangle((x, y, x + CELL_W - 1, y + CELL_H - 1), radius=18, outline=c["border"], width=4)

        av = circle_avatar(c["discord_avatar"])
        img.paste(av, (x + LEFT_W // 2 - AV // 2, y + 14 + BODY // 2 - AV // 2), av)
        body = roblox_body(c["roblox_img"])
        img.paste(body, (x + right_cx - BODY // 2, y + 14), body)

        for cx, name, label in ((LEFT_W // 2, c["discord_name"], "DISCORD"), (right_cx, c["roblox_name"], "ROBLOX")):
            zone_w = LEFT_W if label == "DISCORD" else CELL_W - LEFT_W
            draw_centered(draw, x + cx, y + 274, name, 24, c["text"], zone_w - 20)
            draw_centered(draw, x + cx, y + 308, label, 15, LABEL_COLOR, zone_w - 20)

    buf = io.BytesIO()
    img.save(buf, format="PNG")
    return buf.getvalue()


def fingerprint(cards: list[dict]) -> str:
    """Changes whenever anything visible on the page changes"""
    h = hashlib.sha1(f"v{RENDER_VERSION}".encode())
    for c in cards:
        h.update(c["discord_name"].encode() + b"\0" + c["roblox_name"].encode() + b"\0")
        for key in ("discord_avatar", "roblox_img"):
            h.update(hashlib.sha1(c[key] or b"").digest())
        h.update(repr((c["bg"], c["border"], c["text"])).encode())
        if c["banner"]:
            try:
                h.update(str(c["banner"].stat().st_mtime_ns).encode())
            except OSError:
                pass
    return h.hexdigest()


# ────────────────────────────── BOARD ──────────────────────────────
async def get_channel(channel_id: int) -> Optional[discord.abc.Messageable]:
    try:
        return bot.get_channel(channel_id) or await bot.fetch_channel(channel_id)  # type: ignore[return-value]
    except discord.HTTPException:
        return None


async def delete_message(channel_id: int, message_id: int) -> None:
    channel = await get_channel(channel_id)
    try:
        await channel.get_partial_message(message_id).delete()  # type: ignore[union-attr]
    except (discord.HTTPException, AttributeError):
        pass


def png_file(png: bytes) -> discord.File:
    return discord.File(io.BytesIO(png), filename="profiles.png")


async def sync_board() -> None:
    """Make the channel match the profile list. Only pages that changed are touched."""
    state = state_file.load()
    if not state.get("channel"):
        return
    channel = await get_channel(state["channel"])
    if channel is None:
        print("[board] channel not found, run /setup again")
        return

    await refresh_info()
    profiles = ordered_profiles()
    groups = [profiles[i : i + PAGE_SIZE] for i in range(0, len(profiles), PAGE_SIZE)]
    pages: list[dict] = state.setdefault("pages", [])

    for i, group in enumerate(groups):
        cards = [card_for(p) for p in group]
        digest = fingerprint(cards)
        cur = pages[i] if i < len(pages) else None
        if cur and cur["hash"] == digest:
            continue

        png = await asyncio.to_thread(render_page, cards)
        msg_id: Optional[int] = None
        if cur:
            try:
                await channel.get_partial_message(cur["message"]).edit(attachments=[png_file(png)])  # type: ignore[union-attr]
                msg_id = cur["message"]
            except discord.NotFound:
                # someone deleted this page: repost it and everything after it to keep the order
                for later in pages[i + 1 :]:
                    await delete_message(state["channel"], later["message"])
                del pages[i + 1 :]
        if msg_id is None:
            msg = await channel.send(file=png_file(png))
            msg_id = msg.id

        entry = {"message": msg_id, "hash": digest}
        if i < len(pages):
            pages[i] = entry
        else:
            pages.append(entry)
        state_file.save(state)  # save as we go, so a crash never orphans messages

    for extra in pages[len(groups) :]:
        await delete_message(state["channel"], extra["message"])
    del pages[len(groups) :]
    state_file.save(state)


async def repost_board() -> bool:
    """Send every page again as a fresh message (no "(edited)" mark), then delete the old ones.
    The caller must hold sync_lock."""
    state = state_file.load()
    if not state.get("channel"):
        return False
    old = state.get("pages", [])
    state["pages"] = []
    state_file.save(state)
    try:
        await sync_board()  # no pages are known, so everything is sent as new messages
    finally:
        for page in old:
            await delete_message(state["channel"], page["message"])
    return True


_pending: Optional[asyncio.Task] = None


def schedule_sync() -> None:
    """Several changes within a few seconds become a single board update"""
    global _pending
    if _pending and not _pending.done():
        return
    _pending = asyncio.create_task(_delayed_sync())


async def _delayed_sync() -> None:
    global _pending
    await asyncio.sleep(SYNC_DELAY)
    _pending = None  # a change from now on schedules a new run
    async with sync_lock:
        try:
            await sync_board()
        except Exception:
            traceback.print_exc()


# ────────────────────────────── KEEP ALIVE ──────────────────────────────
async def start_keep_alive() -> None:
    """Tiny web server so UptimeRobot has an address to ping (Replit)"""
    app = web.Application()
    app.router.add_get("/", lambda request: web.Response(text="Bot is alive"))
    runner = web.AppRunner(app)
    await runner.setup()
    await web.TCPSite(runner, "0.0.0.0", int(os.getenv("PORT", "8080"))).start()


# ────────────────────────────── BOT ──────────────────────────────
class ProfileBot(commands.Bot):
    def __init__(self) -> None:
        super().__init__(command_prefix="!", intents=discord.Intents.default())

    async def setup_hook(self) -> None:
        await start_keep_alive()
        store.load()
        state_file.load()  # fail fast if a file is corrupt
        await rbx.start()
        await self.tree.sync()
        refresh_loop.start()
        repost_loop.start()

    async def close(self) -> None:
        await rbx.close()
        await super().close()


bot = ProfileBot()


@tasks.loop(hours=REFRESH_HOURS)
async def refresh_loop() -> None:
    async with sync_lock:
        try:
            await refresh_info(force=True)
            await sync_board()
        except Exception:
            traceback.print_exc()


@refresh_loop.before_loop
async def _before_refresh() -> None:
    await bot.wait_until_ready()


@tasks.loop(hours=REPOST_HOURS)
async def repost_loop() -> None:
    if repost_loop.current_loop == 0:
        return  # the first run happens at startup; only repost once a full interval has passed
    async with sync_lock:
        try:
            await repost_board()
        except Exception:
            traceback.print_exc()


@repost_loop.before_loop
async def _before_repost() -> None:
    await bot.wait_until_ready()


def is_admin(interaction: discord.Interaction) -> bool:
    return interaction.permissions.manage_guild


# ────────────────────────────── /link /unlink ──────────────────────────────
@bot.tree.command(name="link", description="Link a Roblox account to a Discord account")
@app_commands.guild_only()
@app_commands.describe(roblox_name="Roblox username", user="(admins only) link someone else")
async def link_cmd(interaction: discord.Interaction, roblox_name: str, user: Optional[discord.User] = None) -> None:
    target = user or interaction.user
    if target.id != interaction.user.id and not is_admin(interaction):
        return await interaction.response.send_message("❌ Only admins can link someone else", ephemeral=True)
    if target.bot:
        return await interaction.response.send_message("❌ Bots can't be linked", ephemeral=True)

    await interaction.response.defer(ephemeral=True)
    found = await rbx.lookup(roblox_name.strip())
    if not found:
        return await interaction.followup.send("❌ No Roblox player found with that username")
    rid, rname = found

    async with data_lock:
        profiles = store.load()
        clash = next((p for p in profiles if p["roblox_id"] == rid and p["discord_id"] != target.id), None)
        if clash:
            return await interaction.followup.send(
                f"❌ **{rname}** is already linked to <@{clash['discord_id']}>. Unlink them first."
            )
        mine = next((p for p in profiles if p["discord_id"] == target.id), None)
        if mine:
            mine["roblox_id"], mine["roblox_name"] = rid, rname
            verb = "Updated"
        else:
            profiles.append(
                {
                    "discord_id": target.id,
                    "roblox_id": rid,
                    "discord_name": target.display_name,
                    "roblox_name": rname,
                    "linked_at": now_iso(),
                }
            )
            verb = "Linked"
        store.save(profiles)

    schedule_sync()
    await interaction.followup.send(f"✅ {verb}: <@{target.id}> ↔ **{rname}**")


@bot.tree.command(name="unlink", description="Remove a link from the board")
@app_commands.guild_only()
@app_commands.describe(user="(admins only) unlink someone else")
async def unlink_cmd(interaction: discord.Interaction, user: Optional[discord.User] = None) -> None:
    target = user or interaction.user
    if target.id != interaction.user.id and not is_admin(interaction):
        return await interaction.response.send_message("❌ Only admins can unlink someone else", ephemeral=True)

    async with data_lock:
        profiles = store.load()
        mine = next((p for p in profiles if p["discord_id"] == target.id), None)
        if not mine:
            return await interaction.response.send_message("❌ That person isn't on the board", ephemeral=True)
        profiles.remove(mine)
        store.save(profiles)
    (BANNER_DIR / f"{target.id}.png").unlink(missing_ok=True)

    schedule_sync()
    await interaction.response.send_message(f"✅ Removed <@{target.id}> from the board", ephemeral=True)


# ────────────────────────────── /search ──────────────────────────────
def find_matches(query: str) -> list[dict]:
    q = query.strip().lower()
    if not q:
        return []
    out = []
    for p in ordered_profiles():
        c = card_for(p)
        if q in (str(p["discord_id"]), str(p["roblox_id"])) or q in c["discord_name"].lower() or q in c["roblox_name"].lower():
            out.append(p)
    return out


async def search_autocomplete(interaction: discord.Interaction, current: str) -> list[app_commands.Choice[str]]:
    q = current.strip().lower()
    out: list[app_commands.Choice[str]] = []
    for p in ordered_profiles():
        c = card_for(p)
        label = f"{c['discord_name']} · {c['roblox_name']}"
        if not q or q in label.lower() or q in (str(p["discord_id"]), str(p["roblox_id"])):
            out.append(app_commands.Choice(name=label[:100], value=str(p["discord_id"])))
            if len(out) == 25:
                break
    return out


@bot.tree.command(name="search", description="Find someone by Discord name, Roblox name or ID")
@app_commands.guild_only()
@app_commands.describe(query="Discord name, Roblox name, or either ID")
@app_commands.autocomplete(query=search_autocomplete)
async def search_cmd(interaction: discord.Interaction, query: str) -> None:
    await interaction.response.defer(ephemeral=True)
    matches = find_matches(query)
    if not matches:
        return await interaction.followup.send("❌ Nobody matches that")

    state = state_file.load()
    pages = state.get("pages", [])
    position = {p["discord_id"]: i for i, p in enumerate(ordered_profiles())}

    lines = []
    for p in matches[:10]:
        c = card_for(p)
        line = f"• <@{p['discord_id']}> · Roblox **{c['roblox_name']}**"
        page = position[p["discord_id"]] // PAGE_SIZE
        if state.get("channel") and page < len(pages):
            line += f" · [jump to board](https://discord.com/channels/{interaction.guild_id}/{state['channel']}/{pages[page]['message']})"
        lines.append(line)
    if len(matches) > 10:
        lines.append(f"…and {len(matches) - 10} more, try a longer search")

    png = await asyncio.to_thread(render_page, [card_for(p) for p in matches[:PAGE_SIZE]])
    await interaction.followup.send("\n".join(lines), file=png_file(png))


# ────────────────────────────── /setup ──────────────────────────────
@bot.tree.command(name="setup", description="Choose the channel that shows the profile board")
@app_commands.guild_only()
@app_commands.default_permissions(manage_guild=True)
@app_commands.describe(channel="Channel for the board (best set to read-only for members)")
async def setup_cmd(interaction: discord.Interaction, channel: discord.TextChannel) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admins only", ephemeral=True)

    perms = channel.permissions_for(interaction.guild.me)  # type: ignore[union-attr]
    missing = [
        name
        for name, ok in (("View Channel", perms.view_channel), ("Send Messages", perms.send_messages), ("Attach Files", perms.attach_files))
        if not ok
    ]
    if missing:
        return await interaction.response.send_message(f"❌ I'm missing in {channel.mention}: {', '.join(missing)}", ephemeral=True)

    await interaction.response.defer(ephemeral=True)
    async with sync_lock:
        state = state_file.load()
        if state.get("channel") != channel.id:
            for page in state.get("pages", []):  # moving the board: clean up the old one
                await delete_message(state["channel"], page["message"])
            state = {"guild": interaction.guild_id, "channel": channel.id, "pages": []}
            state_file.save(state)
        await sync_board()
    await interaction.followup.send(f"✅ The board is now in {channel.mention}")


# ────────────────────────────── /repost ──────────────────────────────
@bot.tree.command(name="repost", description="Send the board again as fresh messages (removes the \"edited\" mark)")
@app_commands.guild_only()
async def repost_cmd(interaction: discord.Interaction) -> None:
    if not await bot.is_owner(interaction.user):
        return await interaction.response.send_message("❌ Only the bot owner can do this", ephemeral=True)
    await interaction.response.defer(ephemeral=True)
    async with sync_lock:
        done = await repost_board()
    await interaction.followup.send("✅ Board reposted" if done else "❌ No board yet, run /setup first")


# ────────────────────────────── /custom ──────────────────────────────
custom = app_commands.Group(name="custom", description="Customise your own card", guild_only=True)
bot.tree.add_command(custom)


def save_banner(raw: bytes, path: Path) -> None:
    im = ImageOps.fit(Image.open(io.BytesIO(raw)).convert("RGB"), (CELL_W, CELL_H), Image.Resampling.LANCZOS)
    BANNER_DIR.mkdir(parents=True, exist_ok=True)
    im.save(path, format="PNG")


async def update_profile(discord_id: int, **fields: Any) -> bool:
    async with data_lock:
        profiles = store.load()
        mine = next((p for p in profiles if p["discord_id"] == discord_id), None)
        if not mine:
            return False
        mine.update(fields)
        store.save(profiles)
    return True


NOT_LINKED = "❌ You're not on the board yet, use `/link` first"


@custom.command(name="color", description="Set your card background and/or border colour")
@app_commands.describe(color="Background colour, e.g. #FF0000", border="Border colour, e.g. #FFFFFF (default: a lighter shade of the background)")
async def custom_color(interaction: discord.Interaction, color: Optional[str] = None, border: Optional[str] = None) -> None:
    if color is None and border is None:
        return await interaction.response.send_message("❌ Give a `color`, a `border`, or both (format #RRGGBB)", ephemeral=True)
    fields: dict[str, str] = {}
    for key, value in (("color", color), ("border", border)):
        if value is None:
            continue
        code = parse_hex(value)
        if not code:
            return await interaction.response.send_message(f"❌ `{value}` isn't a valid colour, use #RRGGBB", ephemeral=True)
        fields[key] = code
    if not await update_profile(interaction.user.id, **fields):
        return await interaction.response.send_message(NOT_LINKED, ephemeral=True)
    schedule_sync()
    await interaction.response.send_message("✅ Colours saved, the board will update in a moment", ephemeral=True)


@custom.command(name="banner", description="Use a picture as your whole card background")
@app_commands.describe(image="PNG, JPG, WEBP or GIF (first frame)")
async def custom_banner(interaction: discord.Interaction, image: discord.Attachment) -> None:
    if not (image.content_type or "").startswith("image/"):
        return await interaction.response.send_message("❌ That isn't an image", ephemeral=True)
    if image.size > MAX_BANNER_BYTES:
        return await interaction.response.send_message("❌ Image is too big (max 8 MB)", ephemeral=True)
    await interaction.response.defer(ephemeral=True)

    async with data_lock:
        if not any(p["discord_id"] == interaction.user.id for p in store.load()):
            return await interaction.followup.send(NOT_LINKED)

    name = f"{interaction.user.id}.png"
    try:
        await asyncio.to_thread(save_banner, await image.read(), BANNER_DIR / name)
    except Exception:
        return await interaction.followup.send("❌ I couldn't read that image")

    await update_profile(interaction.user.id, banner=name)
    schedule_sync()
    await interaction.followup.send("✅ Banner saved, the board will update in a moment")


@custom.command(name="reset", description="Remove your colours and banner")
@app_commands.describe(user="(bot owner only) reset someone else's card")
async def custom_reset(interaction: discord.Interaction, user: Optional[discord.User] = None) -> None:
    target = user or interaction.user
    if target.id != interaction.user.id and not await bot.is_owner(interaction.user):
        return await interaction.response.send_message("❌ Only the bot owner can reset someone else's card", ephemeral=True)

    async with data_lock:
        profiles = store.load()
        mine = next((p for p in profiles if p["discord_id"] == target.id), None)
        if not mine:
            return await interaction.response.send_message("❌ That person isn't on the board", ephemeral=True)
        for key in ("color", "border", "banner"):
            mine.pop(key, None)
        store.save(profiles)
    (BANNER_DIR / f"{target.id}.png").unlink(missing_ok=True)

    schedule_sync()
    await interaction.response.send_message(f"✅ Reset the card of <@{target.id}>", ephemeral=True)


# ────────────────────────────── /export /import ──────────────────────────────
@bot.tree.command(name="export", description="Download every profile as a JSON file")
@app_commands.guild_only()
@app_commands.default_permissions(manage_guild=True)
async def export_cmd(interaction: discord.Interaction) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admins only", ephemeral=True)
    await interaction.response.defer(ephemeral=True)
    async with data_lock:
        profiles = store.load()
    payload = {"schema_version": SCHEMA_VERSION, "exported_at": now_iso(), "profiles": profiles}
    raw = json.dumps(payload, indent=2, ensure_ascii=False).encode("utf-8")
    name = f"profiles-{datetime.now(timezone.utc):%Y%m%d}.json"
    await interaction.followup.send(
        f"📦 {len(profiles)} profile(s). Use `/import` with this file on a new bot "
        f"and copy the `{BANNER_DIR}/` folder next to it so banners come along.",
        file=discord.File(io.BytesIO(raw), filename=name),
    )


def parse_import(raw: bytes, existing: list[dict]) -> tuple[Optional[str], list[dict], int, int]:
    """Return (error, new profiles, duplicate count, invalid count)"""
    try:
        data = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError):
        return "❌ That isn't a valid JSON file", [], 0, 0
    if not isinstance(data, dict) or data.get("schema_version") != SCHEMA_VERSION:
        got = data.get("schema_version") if isinstance(data, dict) else None
        return f"❌ Unsupported file (schema_version {got!r}, expected {SCHEMA_VERSION})", [], 0, 0
    if not isinstance(data.get("profiles"), list):
        return "❌ The file has no `profiles` list", [], 0, 0

    have_d = {p["discord_id"] for p in existing}
    have_r = {p["roblox_id"] for p in existing}
    new: list[dict] = []
    dup = bad = 0
    for item in data["profiles"]:
        try:
            did, rid = int(item["discord_id"]), int(item["roblox_id"])
            if did <= 0 or rid <= 0:
                raise ValueError
        except (KeyError, TypeError, ValueError):
            bad += 1
            continue
        if did in have_d or rid in have_r:
            dup += 1
            continue
        have_d.add(did)
        have_r.add(rid)
        profile = {
            "discord_id": did,
            "roblox_id": rid,
            "discord_name": str(item.get("discord_name") or "")[:100],
            "roblox_name": str(item.get("roblox_name") or "")[:100],
            "linked_at": str(item.get("linked_at") or now_iso()),
        }
        for key in ("color", "border"):
            code = parse_hex(item.get(key) if isinstance(item.get(key), str) else None)
            if code:
                profile[key] = code
        if item.get("banner") == f"{did}.png" and (BANNER_DIR / f"{did}.png").exists():
            profile["banner"] = f"{did}.png"  # the picture itself must already be in banners/
        new.append(profile)
    return None, new, dup, bad


class ImportView(discord.ui.View):
    def __init__(self, owner_id: int, new: list[dict]) -> None:
        super().__init__(timeout=120)
        self.owner_id = owner_id
        self.new = new

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        return interaction.user.id == self.owner_id

    @discord.ui.button(label="Import", style=discord.ButtonStyle.success)
    async def confirm(self, interaction: discord.Interaction, button: discord.ui.Button) -> None:
        async with data_lock:
            profiles = store.load()
            have_d = {p["discord_id"] for p in profiles}
            have_r = {p["roblox_id"] for p in profiles}
            added = 0
            for p in self.new:  # re-check: the list may have changed while the preview was open
                if p["discord_id"] in have_d or p["roblox_id"] in have_r:
                    continue
                profiles.append(p)
                have_d.add(p["discord_id"])
                have_r.add(p["roblox_id"])
                added += 1
            store.save(profiles)
        self.stop()
        schedule_sync()
        await interaction.response.edit_message(content=f"✅ Imported {added} profile(s)", view=None)

    @discord.ui.button(label="Cancel", style=discord.ButtonStyle.secondary)
    async def cancel(self, interaction: discord.Interaction, button: discord.ui.Button) -> None:
        self.stop()
        await interaction.response.edit_message(content="Import cancelled", view=None)


@bot.tree.command(name="import", description="Load profiles from a file made by /export")
@app_commands.guild_only()
@app_commands.default_permissions(manage_guild=True)
@app_commands.describe(file="The JSON file from /export")
async def import_cmd(interaction: discord.Interaction, file: discord.Attachment) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admins only", ephemeral=True)
    if file.size > MAX_IMPORT_BYTES:
        return await interaction.response.send_message("❌ File is too big", ephemeral=True)

    await interaction.response.defer(ephemeral=True)
    async with data_lock:
        existing = store.load()
    err, new, dup, bad = parse_import(await file.read(), existing)
    if err:
        return await interaction.followup.send(err)
    if not new:
        return await interaction.followup.send(f"Nothing to import ({dup} already present, {bad} invalid)")
    await interaction.followup.send(
        f"**{len(new)}** new · {dup} already present (skipped) · {bad} invalid (skipped)\nImport the new ones?",
        view=ImportView(interaction.user.id, new),
    )


if __name__ == "__main__":
    token = os.environ.get("DISCORD_TOKEN")
    if not token:
        raise SystemExit("Missing DISCORD_TOKEN environment variable")
    bot.run(token)