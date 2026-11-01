"""Display live heart-rate notifications from a Xiaomi Mi Band 6."""

from __future__ import annotations

import asyncio
import csv
import ctypes
import json
import math
import os
import queue
import re
import shutil
import statistics
import struct
import tempfile
import threading
import time
import tkinter as tk
import winsound
from tkinter import colorchooser, filedialog, font as tkfont, messagebox, ttk
from datetime import datetime
from pathlib import Path
from typing import Final

from bleak import BleakScanner
from bleak.backends.device import BLEDevice
from bleak.backends.scanner import AdvertisementData
import sv_ttk
from PIL import Image, ImageDraw, ImageFont, ImageTk


DEFAULT_SAMPLE_FREQUENCY: Final = 1.0
MIN_SAMPLE_FREQUENCY: Final = 0.1
MAX_SAMPLE_FREQUENCY: Final = 100.0
XIAOMI_COMPANY_ID: Final = 0x0157
MAC_ADDRESS_PATTERN: Final = re.compile(r"^[0-9A-Fa-f]{2}(:[0-9A-Fa-f]{2}){5}$")
DEFAULT_NUMBER_FORMAT: Final = "{bpm} BPM"
DEFAULT_HEART_COLOR: Final = "#e53935"
DEFAULT_NUMBER_COLOR: Final = "#ffffff"
DEFAULT_FLOATING_BACKGROUND: Final = "#202124"
FLOATING_TRANSPARENT_COLOR: Final = "#ff00ff"
DEFAULT_ICON_SIZE: Final = 42
DEFAULT_NUMBER_SIZE: Final = 18
DEFAULT_FONT_FAMILY: Final = "Segoe UI"
DEFAULT_LOW_BPM: Final = 50
DEFAULT_HIGH_BPM: Final = 120
RESTING_BPM_MAX: Final = 60
ELEVATED_BPM_MIN: Final = 100

_GWL_EXSTYLE = -20
_WS_EX_LAYERED = 0x00080000
_ULW_ALPHA = 0x00000002
_AC_SRC_ALPHA = 1
_SWP_NOSIZE = 0x0001
_SWP_NOMOVE = 0x0002
_SWP_NOZORDER = 0x0004
_SWP_FRAMECHANGED = 0x0020
_SWP_NOACTIVATE = 0x0010
_HWND_TOPMOST = ctypes.c_void_p(-1)


class _Point(ctypes.Structure):
    _fields_ = [("x", ctypes.c_long), ("y", ctypes.c_long)]


class _Size(ctypes.Structure):
    _fields_ = [("cx", ctypes.c_long), ("cy", ctypes.c_long)]


class _BlendFunction(ctypes.Structure):
    _fields_ = [
        ("BlendOp", ctypes.c_ubyte),
        ("BlendFlags", ctypes.c_ubyte),
        ("SourceConstantAlpha", ctypes.c_ubyte),
        ("AlphaFormat", ctypes.c_ubyte),
    ]


class _BitmapInfoHeader(ctypes.Structure):
    _fields_ = [
        ("biSize", ctypes.c_uint32),
        ("biWidth", ctypes.c_int32),
        ("biHeight", ctypes.c_int32),
        ("biPlanes", ctypes.c_uint16),
        ("biBitCount", ctypes.c_uint16),
        ("biCompression", ctypes.c_uint32),
        ("biSizeImage", ctypes.c_uint32),
        ("biXPelsPerMeter", ctypes.c_int32),
        ("biYPelsPerMeter", ctypes.c_int32),
        ("biClrUsed", ctypes.c_uint32),
        ("biClrImportant", ctypes.c_uint32),
    ]


class _BitmapInfo(ctypes.Structure):
    _fields_ = [
        ("bmiHeader", _BitmapInfoHeader),
        ("bmiColors", ctypes.c_uint32 * 1),
    ]


_WIN32_SIGNATURES_READY = False


def _configure_win32_signatures() -> None:
    """Declare Win32 prototypes once, before the first native call.

    Every coordinate these functions accept is a physical pixel;
    FloatingHeartWindow sizes/positions its HWND exclusively through Tk's
    ``wm geometry`` and only uploads content via UpdateLayeredWindow.
    """
    global _WIN32_SIGNATURES_READY
    if _WIN32_SIGNATURES_READY:
        return
    user32 = ctypes.windll.user32
    gdi32 = ctypes.windll.gdi32
    user32.GetWindowLongW.restype = ctypes.c_long
    user32.GetWindowLongW.argtypes = [ctypes.c_void_p, ctypes.c_int]
    user32.SetWindowLongW.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_long]
    if hasattr(user32, "GetDpiForWindow"):
        user32.GetDpiForWindow.restype = ctypes.c_uint
        user32.GetDpiForWindow.argtypes = [ctypes.c_void_p]
    user32.SetWindowPos.argtypes = [
        ctypes.c_void_p,
        ctypes.c_void_p,
        ctypes.c_int,
        ctypes.c_int,
        ctypes.c_int,
        ctypes.c_int,
        ctypes.c_uint,
    ]
    user32.SetWindowPos.restype = ctypes.c_int
    user32.UpdateLayeredWindow.argtypes = [
        ctypes.c_void_p,
        ctypes.c_void_p,
        ctypes.POINTER(_Point),
        ctypes.POINTER(_Size),
        ctypes.c_void_p,
        ctypes.POINTER(_Point),
        ctypes.c_uint32,
        ctypes.POINTER(_BlendFunction),
        ctypes.c_uint32,
    ]
    user32.UpdateLayeredWindow.restype = ctypes.c_int
    user32.GetDC.argtypes = [ctypes.c_void_p]
    user32.GetDC.restype = ctypes.c_void_p
    user32.ReleaseDC.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
    gdi32.CreateCompatibleDC.argtypes = [ctypes.c_void_p]
    gdi32.CreateCompatibleDC.restype = ctypes.c_void_p
    gdi32.CreateDIBSection.argtypes = [
        ctypes.c_void_p,
        ctypes.POINTER(_BitmapInfo),
        ctypes.c_uint32,
        ctypes.POINTER(ctypes.c_void_p),
        ctypes.c_void_p,
        ctypes.c_uint32,
    ]
    gdi32.CreateDIBSection.restype = ctypes.c_void_p
    gdi32.SelectObject.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
    gdi32.SelectObject.restype = ctypes.c_void_p
    gdi32.DeleteObject.argtypes = [ctypes.c_void_p]
    gdi32.DeleteDC.argtypes = [ctypes.c_void_p]
    gdi32.GdiFlush.argtypes = []
    gdi32.GdiFlush.restype = ctypes.c_int
    _WIN32_SIGNATURES_READY = True


_FONT_REGISTRY: dict[str, list[tuple[str, int, bool, bool]]] | None = None
_FONT_REGISTRY_STATE: Final = Path(
    os.environ.get("APPDATA", str(Path.home()))
) / "MiBandHeartRateMonitor" / "font-cache.json"
_FONT_REGISTRY_BUILDING = threading.Event()
_FONT_REGISTRY_LOCK = threading.Lock()


def _fonts_dir_fingerprint() -> str:
    """Mtime fingerprint of the font directory, to invalidate the cache."""
    fonts_dir = Path(os.environ.get("WINDIR", "C:\\Windows")) / "Fonts"
    try:
        stamp = fonts_dir.stat().st_mtime_ns
    except OSError:
        stamp = 0
    count = 0
    try:
        for pattern in ("*.ttf", "*.otf", "*.ttc", "*.otc"):
            count += sum(1 for _ in fonts_dir.glob(pattern))
    except OSError:
        pass
    return f"{stamp}:{count}"


def _font_registry_ready() -> bool:
    return _FONT_REGISTRY is not None


def _font_registry() -> dict[str, list[tuple[str, int, bool, bool]]]:
    """Return the name->font mapping, building it synchronously if needed.

    Startup paths should instead call ``_font_registry_ensure`` (async) and
    draw with the quick fallback while building: a cold build blocks for
    seconds (measured 3.7 s over 789 MB of installed fonts).
    """
    global _FONT_REGISTRY
    if _FONT_REGISTRY is not None:
        return _FONT_REGISTRY
    with _FONT_REGISTRY_LOCK:
        if _FONT_REGISTRY is not None:
            return _FONT_REGISTRY
        cached = _font_cache_load()
        if cached is not None:
            _FONT_REGISTRY = cached
        else:
            _FONT_REGISTRY = _font_registry_build()
            _font_cache_save(_FONT_REGISTRY)
        return _FONT_REGISTRY


def _font_registry_build() -> dict[str, list[tuple[str, int, bool, bool]]]:
    """Map every family-name variant to (file, face, bold, italic)."""
    registry: dict[str, list[tuple[str, int, bool, bool]]] = {}
    fonts_dir = Path(os.environ.get("WINDIR", "C:\\Windows")) / "Fonts"
    candidates = (
        list(fonts_dir.glob("*.ttf"))
        + list(fonts_dir.glob("*.otf"))
        + list(fonts_dir.glob("*.ttc"))
        + list(fonts_dir.glob("*.otc"))
    )
    for path in candidates:
        try:
            data = path.read_bytes()
        except OSError:
            continue
        for name, is_bold, is_italic in _sfnt_family_names(data):
            registry.setdefault(name, []).append((str(path), 0, is_bold, is_italic))
    return registry


def _font_cache_load() -> dict[str, list[tuple[str, int, bool, bool]]] | None:
    try:
        payload = json.loads(_FONT_REGISTRY_STATE.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError, ValueError):
        return None
    if not isinstance(payload, dict) or payload.get("version") != 2:
        return None
    if payload.get("fingerprint") != _fonts_dir_fingerprint():
        return None
    entries = payload.get("registry")
    if not isinstance(entries, dict):
        return None
    registry: dict[str, list[tuple[str, int, bool, bool]]] = {}
    try:
        for name, rows in entries.items():
            registry[str(name)] = [
                (str(row[0]), int(row[1]), bool(row[2]), bool(row[3]))
                for row in rows
            ]
    except (TypeError, ValueError, IndexError):
        return None
    return registry


def _font_cache_save(registry: dict[str, list[tuple[str, int, bool, bool]]]) -> None:
    try:
        _FONT_REGISTRY_STATE.parent.mkdir(parents=True, exist_ok=True)
        payload = {
            "version": 2,
            "fingerprint": _fonts_dir_fingerprint(),
            "registry": registry,
        }
        _FONT_REGISTRY_STATE.write_text(
            json.dumps(payload, ensure_ascii=False), encoding="utf-8"
        )
    except (OSError, TypeError, ValueError):
        pass  # cache is best-effort; the slow path still works


def _font_registry_ensure() -> bool:
    """Kick off async registry building; return True when already ready.

    The build thread touches no Tk state, so it is safe beside the
    mainloop. Callers redraw once ``_font_registry_ready()`` turns True.
    """
    if _FONT_REGISTRY is not None:
        return True
    if _FONT_REGISTRY_BUILDING.is_set():
        return False
    _FONT_REGISTRY_BUILDING.set()
    threading.Thread(
        target=lambda: _font_registry(), daemon=True
    ).start()
    return False


def _decode_utf16be(data: bytes) -> str:
    return data.decode("utf-16-be", "replace")


def _sfnt_family_names(data: bytes) -> list[tuple[str, bool, bool]]:
    """Extract (family, is_bold, is_italic) from an sfnt/ttc name table.

    Parses the header directly so localized Chinese family names (微软雅黑)
    become matchable alongside the English ones (Microsoft YaHei).
    """
    families: list[tuple[str, bool, bool]] = []
    try:
        if data[:4] == b"ttcf":
            count = struct.unpack_from(">I", data, 8)[0]
            offsets = [
                struct.unpack_from(">I", data, 12 + 4 * position)[0]
                for position in range(min(count, 16))
            ]
        else:
            offsets = [0]
        for offset in offsets:
            if data[offset:offset + 4] not in (b"\x00\x01\x00\x00", b"OTTO", b"true"):
                continue
            num_tables = struct.unpack_from(">H", data, offset + 4)[0]
            name_offset = 0
            for table in range(num_tables):
                record = offset + 12 + 16 * table
                if data[record:record + 4] == b"name":
                    name_offset = struct.unpack_from(">I", data, record + 8)[0]
                    break
            if not name_offset or name_offset + 6 > len(data):
                continue
            count = struct.unpack_from(">H", data, name_offset + 2)[0]
            string_offset = name_offset + struct.unpack_from(">H", data, name_offset + 4)[0]
            families_local: dict[tuple[int, int], str] = {}
            subfamily_bold = False
            subfamily_italic = False
            for record in range(count):
                entry = name_offset + 6 + 12 * record
                if entry + 12 > len(data):
                    break
                (
                    platform, _, language, name_id, length, value_offset
                ) = struct.unpack_from(">6H", data, entry)
                if name_id not in (1, 2):
                    continue
                raw = data[
                    string_offset + value_offset:string_offset + value_offset + length
                ]
                if not raw:
                    continue
                if platform in (0, 3):
                    text = _decode_utf16be(raw)
                elif platform == 1:
                    text = raw.decode("latin-1", "replace")
                else:
                    continue
                lowered = text.casefold()
                if name_id == 1:
                    # Keep every (platform, language) variant so the English
                    # name survives next to the localized zh-CN one.
                    families_local[(platform, language)] = text
                elif name_id == 2:
                    subfamily_bold = subfamily_bold or (
                        "bold" in lowered or "black" in lowered
                    )
                    subfamily_italic = subfamily_italic or (
                        "italic" in lowered or "oblique" in lowered
                    )
            seen: set[str] = set()
            for text in families_local.values():
                normalized = text.casefold().replace(" ", "")
                if normalized and normalized not in seen:
                    seen.add(normalized)
                    families.append((normalized, subfamily_bold, subfamily_italic))
    except (struct.error, OSError, ValueError):
        return families
    return families


def _font_registry() -> dict[str, list[tuple[str, int, bool, bool]]]:
    """Map every family-name variant to (file, face, bold, italic), built once."""
    global _FONT_REGISTRY
    if _FONT_REGISTRY is not None:
        return _FONT_REGISTRY
    registry: dict[str, list[tuple[str, int, bool, bool]]] = {}
    fonts_dir = Path(os.environ.get("WINDIR", "C:\\Windows")) / "Fonts"
    candidates = (
        list(fonts_dir.glob("*.ttf"))
        + list(fonts_dir.glob("*.otf"))
        + list(fonts_dir.glob("*.ttc"))
        + list(fonts_dir.glob("*.otc"))
    )
    for path in candidates:
        try:
            data = path.read_bytes()
        except OSError:
            continue
        for name, is_bold, is_italic in _sfnt_family_names(data):
            registry.setdefault(name, []).append((str(path), 0, is_bold, is_italic))
    _FONT_REGISTRY = registry
    return registry


class FloatingHeartWindow(tk.Toplevel):
    """A draggable desktop overlay for the latest heart-rate value."""

    _HEART_PATTERN: tuple[str, ...] = (
        " XX  XX ",
        "XXXXXXXX",
        "XXXXXXXX",
        "XXXXXXXX",
        " XXXXXX ",
        "  XXXX  ",
        "   XX   ",
        "   XX   ",
        "        ",
    )

    def __init__(self, owner: tk.Tk) -> None:
        super().__init__(owner)
        self.withdraw()
        self.title("心率悬浮窗")
        _configure_win32_signatures()
        self._window_x = 80
        self._window_y = 80
        self.geometry(f"160x80+{self._window_x}+{self._window_y}")
        self.resizable(True, True)
        # A layered window must not expose Tk's native client-area painting.
        self.overrideredirect(True)
        self.attributes("-topmost", True)
        self._number_format = DEFAULT_NUMBER_FORMAT
        self._heart_color = DEFAULT_HEART_COLOR
        self._number_color = DEFAULT_NUMBER_COLOR
        self._background = DEFAULT_FLOATING_BACKGROUND
        self._icon_style = "像素心脏"
        self._icon_size = DEFAULT_ICON_SIZE
        self._number_size = DEFAULT_NUMBER_SIZE
        self._font_family = DEFAULT_FONT_FAMILY
        self._custom_icon_path = ""
        self._custom_icon_image: Image.Image | None = None
        self._custom_icon_cache_key: tuple[str, int] | None = None
        self._font_path_cache: dict[tuple[str, bool], str | None] = {}
        self._redraw_job: str | None = None
        self._icon_x = 140
        self._icon_y = 48
        self._number_x = 140
        self._number_y = 162
        self._bpm = "--"
        self._drag_origin: tuple[int, int] | None = None
        self._chrome_hidden = True
        self._background_opacity = 0.75
        self._content_opacity = 1.0
        self._last_uploaded: tuple[int, int, bytes] | None = None
        self._layout_size: tuple[int, int] = (160, 80)
        self._history: list[int] = []
        self._HISTORY_LIMIT: Final = 120
        self._min_value: int | None = None
        self._max_value: int | None = None
        self._show_chart = False
        self._show_extremes = False
        self._beat_enabled = False
        self._beat_job: str | None = None
        self._beat_bpm = 60.0
        self._beat_anchor = time.monotonic()
        self._last_signal = 0.0
        self._beat_scale = 1.0
        self._font_watch_job: str | None = None
        self.configure(background="#000000")
        self.update_idletasks()
        self._enable_layered_window()
        self.bind("<ButtonPress-1>", self._start_drag)
        self.bind("<B1-Motion>", self._drag)
        self.protocol("WM_DELETE_WINDOW", self._hide)

    def state(self) -> str:
        return str(super().state())


    def update_value(self, bpm: object) -> None:
        self._bpm = str(bpm)
        try:
            value = int(bpm)
        except (TypeError, ValueError):
            value = None
        if value is not None:
            self._history.append(value)
            if len(self._history) > self._HISTORY_LIMIT:
                del self._history[: len(self._history) - self._HISTORY_LIMIT]
            if self._min_value is None or value < self._min_value:
                self._min_value = value
            if self._max_value is None or value > self._max_value:
                self._max_value = value
            if self._beat_enabled and value >= 30:
                # Re-anchor the cardiac cycle to the fresh sample so the
                # animation follows the real rhythm, not wall-clock drift.
                self._beat_bpm = value
                self._beat_anchor = time.monotonic()
                self._last_signal = self._beat_anchor
        self._schedule_redraw()

    def update_style(
        self,
        number_format: str,
        icon_style: str,
        icon_x: float,
        icon_y: float,
        number_x: float,
        number_y: float,
        icon_size: int,
        number_size: int,
        font_family: str,
        custom_icon_path: str,
        heart_color: str,
        number_color: str,
        background: str,
        background_opacity: float,
        content_opacity: float,
        hide_chrome: bool,
        show_chart: bool = False,
        show_extremes: bool = False,
        beat_enabled: bool = False,
    ) -> None:
        self._number_format = number_format
        self._icon_style = icon_style
        self._icon_x = icon_x
        self._icon_y = icon_y
        self._number_x = number_x
        self._number_y = number_y
        self._icon_size = max(8, int(icon_size))
        self._number_size = max(8, int(number_size))
        self._font_family = font_family or DEFAULT_FONT_FAMILY
        self._custom_icon_path = custom_icon_path
        self._heart_color = heart_color
        self._number_color = number_color
        self._background = background
        # Layered rendering is always borderless. Keep the setting for API
        # compatibility, but never switch the native window style mid-frame.
        self._chrome_hidden = True
        self._background_opacity = background_opacity
        self._content_opacity = content_opacity
        self._show_chart = bool(show_chart)
        self._show_extremes = bool(show_extremes)
        if self._show_chart != show_chart or self._show_extremes != show_extremes:
            self._show_chart = show_chart
            self._show_extremes = show_extremes
            self._last_uploaded = None  # force a full repaint
        self._set_beat_enabled(bool(beat_enabled))
        self.attributes("-topmost", True)
        self._schedule_redraw()

    def _set_beat_enabled(self, enabled: bool) -> None:
        if enabled == self._beat_enabled:
            return
        self._beat_enabled = enabled
        self._last_uploaded = None
        if enabled:
            if self._history:
                self._beat_bpm = float(self._history[-1])
            self._beat_anchor = time.monotonic()
            self._last_signal = self._beat_anchor
            self._start_beat_loop()
        elif self._beat_job is not None:
            self.after_cancel(self._beat_job)
            self._beat_job = None
            self._beat_scale = 1.0

    def _start_beat_loop(self) -> None:
        if self._beat_job is not None or not self._beat_enabled:
            return
        self._beat_job = self.after(33, self._beat_tick)

    def _beat_tick(self) -> None:
        self._beat_job = None
        if not self._beat_enabled:
            return
        now = time.monotonic()
        if now - self._last_signal > 5.0:
            # No fresh samples: fall back to a calm breathing shimmer.
            breath = 0.5 - 0.5 * math.cos(2 * math.pi * (now % 4) / 4)
            self._beat_scale = 1.0 + 0.03 * breath
        else:
            bpm = max(30.0, min(220.0, self._beat_bpm))
            period = 60.0 / bpm
            phase = ((now - self._beat_anchor) % period) / period
            self._beat_scale = _beat_scale(phase)
        self._schedule_redraw()
        self._beat_job = self.after(33, self._beat_tick)

    def _schedule_redraw(self) -> None:
        if self._redraw_job is not None:
            self.after_cancel(self._redraw_job)
        self._redraw_job = self.after(16, self._run_redraw)
        self._schedule_font_watch()

    def _schedule_font_watch(self) -> None:
        """While the async font registry builds, redraw once it is ready."""
        if self._font_watch_job is not None or _font_registry_ready():
            return
        self._font_watch_job = self.after(120, self._font_watch_tick)

    def _font_watch_tick(self) -> None:
        self._font_watch_job = None
        if _font_registry_ready():
            self._font_path_cache.clear()
            self._last_uploaded = None
            self._schedule_redraw()
            return
        self._font_watch_job = self.after(120, self._font_watch_tick)

    def _run_redraw(self) -> None:
        self._redraw_job = None
        self._redraw()

    def _redraw(self) -> None:
        try:
            number = self._number_format.format(bpm=self._bpm)
        except (KeyError, ValueError, IndexError):
            number = self._bpm
        self._resize_to_content(number)
        self._render_overlay(number)

    def _render_overlay(self, number: str) -> None:
        # The HWND is sized and positioned solely through Tk's wm geometry,
        # which probes showed to be the only reliable absolute mapping here.
        width, height = self._layout_size
        if width <= 1 or height <= 1:
            return
        image = self._compose_overlay(number, width, height)
        self._set_layered_image(image)

    def _compose_overlay(self, number: str, width: int, height: int) -> Image.Image:
        """Compose background and content before the single native alpha upload.

        All layout coordinates are Tk logical pixels, which match the native
        window pixels 1:1 in this process (measured), so no DPI scaling.
        """
        image = Image.new("RGBA", (width, height), (0, 0, 0, 0))
        if self._background_opacity > 0:
            draw = ImageDraw.Draw(image)
            draw.rectangle(
                (0, 0, width, height),
                fill=self._rgba(self._background, self._background_opacity),
            )
        content = Image.new("RGBA", (width, height), (0, 0, 0, 0))
        content_draw = ImageDraw.Draw(content)
        icon_x, icon_y = int(round(self._icon_x)), int(round(self._icon_y))
        beat = getattr(self, "_beat_scale", 1.0) if self._beat_enabled else 1.0
        if self._icon_style == "像素心脏":
            icon_size = self._icon_size * beat
            cell = icon_size / 8
            start_x = icon_x - icon_size / 2
            start_y = icon_y - icon_size * 9 / 16
            color = self._rgba(self._heart_color, self._content_opacity)
            for row, pattern in enumerate(self._HEART_PATTERN):
                for column, pixel in enumerate(pattern):
                    if pixel == "X":
                        content_draw.rectangle(
                            (
                                start_x + column * cell,
                                start_y + row * cell,
                                start_x + (column + 1) * cell,
                                start_y + (row + 1) * cell,
                            ),
                            fill=color,
                        )
        elif self._icon_style == "文字心脏":
            content_draw.text(
                (icon_x, icon_y),
                "♥",
                font=self._load_font(round(self._icon_size * beat)),
                fill=self._rgba(self._heart_color, self._content_opacity),
                anchor="mm",
            )
        elif self._icon_style == "MC心脏":
            mc_heart = self._get_mc_heart_image(beat)
            if mc_heart is not None:
                alpha = mc_heart.getchannel("A").point(
                    lambda value: round(value * self._content_opacity)
                )
                tinted = mc_heart.copy()
                tinted.putalpha(alpha)
                content.alpha_composite(
                    tinted,
                    (icon_x - tinted.width // 2, icon_y - tinted.height // 2),
                )
        elif self._icon_style == "自定义图标":
            custom_icon = self._get_custom_icon_image(
                round(self._icon_size * beat)
            )
            if custom_icon is not None:
                alpha = custom_icon.getchannel("A").point(
                    lambda value: round(value * self._content_opacity)
                )
                custom_icon = custom_icon.copy()
                custom_icon.putalpha(alpha)
                content.alpha_composite(
                    custom_icon,
                    (icon_x - custom_icon.width // 2, icon_y - custom_icon.height // 2),
                )
        content_draw.text(
            (int(round(self._number_x)), int(round(self._number_y))),
            number,
            font=self._load_font(self._number_size, bold=True),
            fill=self._rgba(self._number_color, self._content_opacity),
            anchor="mm",
        )
        if self._show_chart and len(self._history) >= 2:
            self._draw_mini_chart(content, content_draw, width, height)
        if self._show_extremes and self._min_value is not None:
            content_draw.text(
                (width - 8, 8),
                f"低 {self._min_value}  高 {self._max_value}",
                fill=self._rgba(self._number_color, min(1.0, self._content_opacity * 0.8)),
                font=self._load_font(max(10, self._number_size // 2), bold=True),
                anchor="ra",
            )
        image.alpha_composite(content)
        return image

    def _draw_mini_chart(
        self, content: Image.Image, draw: ImageDraw.Draw, width: int, height: int
    ) -> None:
        """Sparkline of the recent BPM history at the bottom of the overlay."""
        history = self._history
        panel_height = min(56, max(28, height // 4))
        left, right = 6, width - 6
        bottom = height - 4
        top = bottom - panel_height
        values = history
        v_low, v_high = min(values), max(values)
        if v_low == v_high:
            v_low, v_high = v_low - 1, v_high + 1
        span = max(1, len(values) - 1)
        points = [
            (
                left + index / span * (right - left),
                bottom - (v - v_low) / (v_high - v_low) * (bottom - top),
            )
            for index, v in enumerate(values)
        ]
        draw.line(
            (left, top, right, top),
            fill=self._rgba(self._background, 0.9),
            width=1,
        )
        for value in (v_low, v_high):
            y = bottom - (value - v_low) / (v_high - v_low) * (bottom - top)
            draw.line((left, y, right, y), fill=self._rgba(self._background, 0.85), width=1)
            draw.text(
                (right - 2, y - 6 if value == v_high else y + 2),
                str(value),
                fill=self._rgba(self._number_color, self._content_opacity * 0.9),
                font=self._load_font(10),
                anchor="ra",
            )
        draw.line(points, fill=self._rgba(self._heart_color, self._content_opacity), width=2)
        last_x, last_y = points[-1]
        draw.ellipse(
            (last_x - 3, last_y - 3, last_x + 3, last_y + 3),
            fill=self._rgba(self._number_color, self._content_opacity),
        )

    def _enable_layered_window(self) -> None:
        _configure_win32_signatures()
        hwnd = self.winfo_id()
        user32 = ctypes.windll.user32
        style = user32.GetWindowLongW(hwnd, _GWL_EXSTYLE)
        if style == -1:
            raise ctypes.WinError()
        user32.SetWindowLongW(hwnd, _GWL_EXSTYLE, style | _WS_EX_LAYERED)
        if not (user32.GetWindowLongW(hwnd, _GWL_EXSTYLE) & _WS_EX_LAYERED):
            raise ctypes.WinError()

    def _set_layered_image(self, image: Image.Image) -> None:
        image = image.convert("RGBA")
        if image.width <= 0 or image.height <= 0:
            raise ValueError("layered image must have a positive size")
        # UpdateLayeredWindow requires premultiplied BGRA, not straight-alpha RGBA.
        data = bytearray(image.tobytes("raw", "BGRA"))
        for offset in range(0, len(data), 4):
            alpha = data[offset + 3]
            if alpha == 255:
                continue
            if alpha == 0:
                data[offset] = 0
                data[offset + 1] = 0
                data[offset + 2] = 0
            else:
                data[offset] = data[offset] * alpha // 255
                data[offset + 1] = data[offset + 1] * alpha // 255
                data[offset + 2] = data[offset + 2] * alpha // 255
        fingerprint = (image.width, image.height, bytes(data))
        if fingerprint == self._last_uploaded:
            return
        self._last_uploaded = fingerprint
        buffer = (ctypes.c_ubyte * len(data)).from_buffer(data)
        hwnd = self.winfo_id()
        user32 = ctypes.windll.user32
        gdi32 = ctypes.windll.gdi32
        screen_dc = user32.GetDC(0)
        if not screen_dc:
            raise ctypes.WinError()
        memory_dc = gdi32.CreateCompatibleDC(screen_dc)
        if not memory_dc:
            user32.ReleaseDC(0, screen_dc)
            raise ctypes.WinError()
        bitmap = None
        previous = None
        info = _BitmapInfo(
            _BitmapInfoHeader(
                ctypes.sizeof(_BitmapInfoHeader),
                image.width,
                -image.height,
                1,
                32,
                0,
                len(data),
                0,
                0,
                0,
                0,
            ),
            (0,),
        )
        bits = ctypes.c_void_p()
        bitmap = gdi32.CreateDIBSection(
            screen_dc,
            ctypes.byref(info),
            0,
            ctypes.byref(bits),
            None,
            0,
        )
        if not bitmap or not bits.value:
            gdi32.DeleteDC(memory_dc)
            user32.ReleaseDC(0, screen_dc)
            raise ctypes.WinError()
        try:
            previous = gdi32.SelectObject(memory_dc, bitmap)
            if not previous:
                raise ctypes.WinError()
            ctypes.memmove(bits.value, buffer, len(data))
            if not gdi32.GdiFlush():
                raise ctypes.WinError()
            blend = _BlendFunction(0, 0, 255, _AC_SRC_ALPHA)
            size = _Size(image.width, image.height)
            source = _Point(0, 0)
            # pptDst=NULL, ppsize=size: pure content update. The window keeps
            # exactly the position Tk's wm geometry gave it; passing screen
            # coordinates here would offset ONTO the existing location
            # (probe: window at (300,150) + pptDst(100,100) -> (400,250)).
            if not user32.UpdateLayeredWindow(
                hwnd, None, None, ctypes.byref(size),
                memory_dc, ctypes.byref(source), 0, ctypes.byref(blend), _ULW_ALPHA
            ):
                raise ctypes.WinError()
            if not gdi32.GdiFlush():
                raise ctypes.WinError()
        finally:
            if previous:
                gdi32.SelectObject(memory_dc, previous)
            if bitmap:
                gdi32.DeleteObject(bitmap)
            gdi32.DeleteDC(memory_dc)
            user32.ReleaseDC(0, screen_dc)

    @staticmethod
    def _rgba(color: str, opacity: float) -> tuple[int, int, int, int]:
        red, green, blue = FloatingHeartWindow._rgb(color)
        return red, green, blue, round(max(0.0, min(1.0, opacity)) * 255)

    @staticmethod
    def _rgb(color: str) -> tuple[int, int, int]:
        value = color.lstrip("#")
        return int(value[0:2], 16), int(value[2:4], 16), int(value[4:6], 16)

    def _load_font(self, size: int, bold: bool = False) -> ImageFont.FreeTypeFont | ImageFont.ImageFont:
        cache_key = (self._font_family, bold)
        path_string = self._font_path_cache.get(cache_key)
        if path_string is None and cache_key not in self._font_path_cache:
            # Tk hands us the localized family name (e.g. 微软雅黑), while
            # FreeType's getname() only exposes the English one. Match
            # against every language variant stored in the font files.
            if not _font_registry_ready():
                # First frames after launch: never block the UI thread on
                # the multi-second registry build (async in progress).
                # Draw with the default font; a redraw follows once ready.
                _font_registry_ensure()
                self._font_path_cache.pop(cache_key, None)
                try:
                    return ImageFont.load_default(size)
                except TypeError:
                    return ImageFont.load_default()
            registry = _font_registry()
            key = self._font_family.casefold().replace(" ", "")
            entries = registry.get(key, ())
            chosen: tuple[str, int, bool, bool] | None = None
            regular: tuple[str, int, bool, bool] | None = None
            for entry in entries:
                if entry[3]:
                    continue  # skip italic faces for the regular pick
                if not entry[2]:
                    regular = regular or entry
                if not bold or entry[2]:
                    chosen = chosen or entry
            chosen = chosen or regular
            if chosen is not None:
                path_string = f"{chosen[0]}|{chosen[1]}"
            self._font_path_cache[cache_key] = path_string
        if path_string is not None:
            try:
                path, index_text = path_string.rsplit("|", 1)
                return ImageFont.truetype(path, size, index=int(index_text))
            except OSError:
                pass
        try:
            return ImageFont.load_default(size)
        except TypeError:
            return ImageFont.load_default()


    def _resize_to_content(self, number: str) -> None:
        """Resize to the current coordinates without changing the user's position."""
        self.update_idletasks()
        text_width = max(40, len(number) * self._number_size * 0.62)
        icon_width, icon_height = self._icon_dimensions()
        heart_width = icon_width
        icon_half_width = heart_width / 2
        icon_half_height = icon_height / 2
        width = max(
            140,
            int(self._icon_x + icon_half_width + 20),
            int(self._number_x + text_width / 2 + 20),
            int(icon_half_width + 20),
        )
        height = max(
            70,
            int(self._icon_y + icon_half_height + 20)
            if self._icon_style != "无图标"
            else 0,
            int(self._number_y + 20),
            int(20 - min(self._icon_y - icon_half_height, self._number_y - 20)),
        )
        if self._show_chart:
            # Reserve room for the sparkline panel at the bottom.
            height = max(height, self._number_y + 20, height + min(56, max(28, height // 4)) // 2 + 16)
        if self._show_extremes and self._min_value is not None:
            width = max(width, 150)
        x, y = self._window_x, self._window_y
        self._layout_size = (width, height)
        if self.winfo_width() != width or self.winfo_height() != height:
            # The single source of truth for window placement: Tk's own
            # geometry engine (measured absolute, 1:1 with native pixels).
            self.geometry(f"{width}x{height}+{x}+{y}")
            self.update_idletasks()

    def _icon_dimensions(self) -> tuple[float, float]:
        beat = self._beat_scale if self._beat_enabled else 1.0
        if self._icon_style == "像素心脏":
            return self._icon_size * beat, self._icon_size * 9 / 8 * beat
        if self._icon_style == "文字心脏":
            return self._icon_size * beat, self._icon_size * beat
        if self._icon_style == "MC心脏":
            mc_heart = self._get_mc_heart_image(beat)
            if mc_heart is not None:
                return float(mc_heart.width), float(mc_heart.height)
        if self._icon_style == "自定义图标":
            image = self._get_custom_icon_image(round(self._icon_size * beat))
            if image is not None:
                return float(image.width), float(image.height)
        return 0.0, 0.0

    def _get_mc_heart_image(self, scale: float = 1.0) -> Image.Image | None:
        """The Minecraft heart sprite (Faithful 32x redraw), NEAREST-scaled.

        ``scale`` lets the beat animation enlarge the sprite. The target is
        rounded to continuous pixels (not integer multiples of the base) so
        the 1.0-1.18 beat scaling stays visible at every size; NEAREST keeps
        the pixels crisp, with the usual mild texel unevenness.
        """
        source = getattr(self, "_mc_heart_source", None)
        if source is None:
            sprite_path = Path(__file__).with_name("mc_heart.png")
            try:
                with Image.open(sprite_path) as image:
                    source = image.convert("RGBA")
            except (OSError, ValueError):
                return None
            self._mc_heart_source = source
        base = min(source.width, source.height)
        target = max(8, int(round(self._icon_size * max(0.5, scale))))
        if source.size != (target, target):
            source = self._mc_heart_source.resize(
                (target, target), Image.Resampling.NEAREST
            )
        return source

    def _get_custom_icon_image(self, pixel_size: int) -> Image.Image | None:
        if not self._custom_icon_path:
            return None
        cache_key = (self._custom_icon_path, int(pixel_size))
        if cache_key == self._custom_icon_cache_key:
            return self._custom_icon_image.copy() if self._custom_icon_image else None
        try:
            with Image.open(self._custom_icon_path) as source:
                source = source.convert("RGBA")
                source.thumbnail((pixel_size, pixel_size), Image.Resampling.LANCZOS)
                image = source.copy()
        except (OSError, ValueError):
            self._custom_icon_image = None
            self._custom_icon_cache_key = None
            return None
        self._custom_icon_image = image
        self._custom_icon_cache_key = cache_key
        return image.copy()

    def _start_drag(self, event: tk.Event[tk.Canvas]) -> None:
        self._drag_origin = (event.x_root, event.y_root)

    def _drag(self, event: tk.Event[tk.Canvas]) -> None:
        if self._drag_origin is None:
            return
        old_x, old_y = self._drag_origin
        x = self._window_x + event.x_root - old_x
        y = self._window_y + event.y_root - old_y
        self._window_x, self._window_y = x, y
        # Tk geometry is the only placement mechanism; layered content follows.
        self.geometry(f"+{x}+{y}")
        self._drag_origin = (event.x_root, event.y_root)

    def show(self) -> None:
        # Upload a complete frame while hidden; otherwise Tk briefly paints
        # its default white client area before UpdateLayeredWindow runs.
        width, height = self._layout_size
        self.geometry(f"{width}x{height}+{self._window_x}+{self._window_y}")
        self._last_uploaded = None
        self._redraw()
        self.deiconify()

    def _hide(self) -> None:
        self.withdraw()

    def destroy(self) -> None:
        if self._redraw_job is not None:
            self.after_cancel(self._redraw_job)
            self._redraw_job = None
        if self._beat_job is not None:
            self.after_cancel(self._beat_job)
            self._beat_job = None
        if self._font_watch_job is not None:
            self.after_cancel(self._font_watch_job)
            self._font_watch_job = None
        super().destroy()


class HtmlFloatingHeartWindow:
    """HTML/CSS overlay using WebView's native alpha composition."""

    def __init__(self, owner: tk.Tk) -> None:
        self._owner = owner
        self._window: object | None = None
        self._thread: threading.Thread | None = None
        self._visible = False
        self._bpm = "--"
        self._style: tuple[object, ...] = (
            DEFAULT_NUMBER_FORMAT,
            "像素心脏",
            140,
            48,
            140,
            162,
            DEFAULT_ICON_SIZE,
            DEFAULT_NUMBER_SIZE,
            DEFAULT_FONT_FAMILY,
            "",
            DEFAULT_HEART_COLOR,
            DEFAULT_NUMBER_COLOR,
            DEFAULT_FLOATING_BACKGROUND,
            0.75,
            1.0,
            False,
        )

    def update_value(self, bpm: object) -> None:
        self._bpm = str(bpm)
        self._evaluate("setBpm", self._bpm)

    def update_style(self, *style: object) -> None:
        if len(style) >= 10 and isinstance(style[9], str) and style[9]:
            style = (*style[:9], Path(style[9]).resolve().as_uri(), *style[10:])
        self._style = style
        self._evaluate("setStyle", *style, self._bpm)
        self._resize_webview(style)

    def _redraw(self) -> None:
        self._evaluate("setStyle", *self._style, self._bpm)

    def state(self) -> str:
        return "normal" if self._visible else "withdrawn"

    def show(self) -> None:
        if self._thread is None:
            self._thread = threading.Thread(target=self._start, daemon=True)
            self._thread.start()
        self._visible = True
        self._evaluate("showOverlay")

    def _hide(self) -> None:
        self._visible = False
        self._evaluate("hideOverlay")

    def destroy(self) -> None:
        self._evaluate("closeOverlay")

    def _start(self) -> None:
        import webview

        html = """
<!doctype html><html><head><meta charset="utf-8"><style>
html,body{margin:0;width:100%;height:100%;overflow:hidden;background:transparent}
#background{position:absolute;inset:0;border-radius:8px;pointer-events:none}
#content{position:absolute;inset:0;pointer-events:none}
#heart,#number{position:absolute;transform:translate(-50%,-50%);white-space:nowrap}
#heart.pixel{font-family:monospace;font-weight:bold;line-height:1}
#heart.text{line-height:1}
#heart img{display:block;width:100%;height:100%;object-fit:contain}
</style></head><body>
<div id="background"></div><div id="content">
<div id="heart"></div><div id="number"></div></div>
<script>
const q=id=>document.getElementById(id);
let bpm='--';
function setBpm(v){bpm=String(v); renderNumber();}
function renderNumber(){q('number').textContent=(window.numberFormat||'{bpm} BPM').replaceAll('{bpm}',bpm);}
function hex(v){return v.startsWith('#')?v:'#202124'}
function setStyle(numberFormat,iconStyle,iconX,iconY,numberX,numberY,iconSize,numberSize,fontFamily,iconPath,heartColor,numberColor,background,bgOpacity,contentOpacity){
 window.numberFormat=String(numberFormat); renderNumber();
 document.body.style.width=Math.max(140,Math.ceil(Math.max(iconX+iconSize/2+20,numberX+numberSize*8+20)))+'px';
 document.body.style.height=Math.max(70,Math.ceil(Math.max(iconY+iconSize/2+20,numberY+numberSize+20)))+'px';
 q('background').style.background=hex(background); q('background').style.opacity=Number(bgOpacity);
 q('content').style.opacity=Number(contentOpacity);
 q('number').style.left=iconX*0+numberX+'px'; q('number').style.top=numberY+'px';
 q('number').style.color=hex(numberColor); q('number').style.fontFamily=String(fontFamily);
 q('number').style.fontSize=numberSize+'px'; q('number').style.fontWeight='bold';
 const h=q('heart'); h.style.left=iconX+'px'; h.style.top=iconY+'px'; h.style.width=iconSize+'px'; h.style.height=iconSize+'px'; h.style.color=hex(heartColor);
 h.className='';
 if(iconStyle==='无图标'){h.textContent='';}
 else if(iconStyle==='文字心脏'){h.className='text';h.textContent='♥';h.style.fontSize=iconSize+'px';}
 else if(iconStyle==='自定义图标' && iconPath){h.innerHTML='<img src="'+iconPath.replaceAll('\\\\','/')+'">';}
 else {h.className='pixel';h.textContent='♥';h.style.fontSize=iconSize+'px';}
}
function showOverlay(){document.body.style.display='block'}
function hideOverlay(){document.body.style.display='none'}
function closeOverlay(){window.close()}
hideOverlay();
</script></body></html>
"""
        self._window = webview.create_window(
            "心率悬浮窗",
            html=html,
            frameless=True,
            transparent=True,
            on_top=True,
            easy_drag=True,
            width=280,
            height=190,
        )
        self._window.events.loaded += self._on_loaded  # type: ignore[attr-defined]
        webview.start()

    def _on_loaded(self) -> None:
        self._evaluate("setStyle", *self._style, self._bpm)
        self._resize_webview(self._style)
        if self._visible:
            self._evaluate("showOverlay")

    def _resize_webview(self, style: tuple[object, ...]) -> None:
        if self._window is None or len(style) < 8:
            return
        try:
            icon_x, icon_y = float(style[2]), float(style[3])
            number_x, number_y = float(style[4]), float(style[5])
            icon_size, number_size = float(style[6]), float(style[7])
            width = max(140, int(max(icon_x + icon_size / 2 + 20, number_x + number_size * 8 + 20)))
            height = max(70, int(max(icon_y + icon_size / 2 + 20, number_y + number_size + 20)))
            self._window.resize(width, height)  # type: ignore[attr-defined]
        except (AttributeError, RuntimeError, TypeError, ValueError):
            return

    def _evaluate(self, function: str, *args: object) -> None:
        window = self._window
        if window is None:
            return
        payload = json.dumps(args, ensure_ascii=False)
        script = f"{function}.apply(null,{payload})"
        try:
            window.evaluate_js(script)  # type: ignore[attr-defined]
        except (RuntimeError, AttributeError):
            pass


class HeartRateSession:
    """One monitoring run's samples with elapsed-time stamps, in seconds."""

    def __init__(self, device_name: str, address: str, sample_frequency: float) -> None:
        self.started_at = datetime.now()
        self.device_name = device_name
        self.address = address
        self.sample_frequency = sample_frequency
        self.samples: list[tuple[float, int]] = []

    def add(self, elapsed: float, bpm: int) -> None:
        self.samples.append((elapsed, bpm))

    @property
    def values(self) -> list[int]:
        return [bpm for _, bpm in self.samples]

    def summary(self) -> dict[str, object]:
        """Descriptive statistics over the collected BPM values."""
        values = self.values
        result: dict[str, object] = {
            "开始时间": self.started_at.strftime("%Y-%m-%d %H:%M:%S"),
            "设备": f"{self.device_name} ({self.address})",
            "样本数": len(values),
            "时长（秒）": round(self.samples[-1][0] - self.samples[0][0], 1)
            if len(values) >= 2
            else 0.0,
        }
        if not values:
            return result
        result.update(
            {
                "均值": round(statistics.mean(values), 2),
                "中位数": statistics.median(values),
                "最小值": min(values),
                "最大值": max(values),
                "极差": max(values) - min(values),
                "样本标准差": round(statistics.stdev(values), 2)
                if len(values) >= 2
                else 0.0,
                "总体标准差": round(statistics.pstdev(values), 2)
                if len(values) >= 2
                else 0.0,
                "方差": round(statistics.variance(values), 2)
                if len(values) >= 2
                else 0.0,
                "众数": _mode_text(values),
                "第一四分位数 Q1": statistics.quantiles(values, n=4, method="inclusive")[0]
                if len(values) >= 2
                else min(values),
                "第三四分位数 Q3": statistics.quantiles(values, n=4, method="inclusive")[2]
                if len(values) >= 2
                else max(values),
                "静息区间样本（≤60）": sum(1 for v in values if v <= RESTING_BPM_MAX),
                "正常区间样本（61-99）": sum(
                    1 for v in values if RESTING_BPM_MAX < v < ELEVATED_BPM_MIN
                ),
                "偏高区间样本（≥100）": sum(1 for v in values if v >= ELEVATED_BPM_MIN),
            }
        )
        return result


def _mode_text(values: list[int]) -> str:
    counts: dict[int, int] = {}
    for value in values:
        counts[value] = counts.get(value, 0) + 1
    top = max(counts.values())
    modes = sorted(value for value, count in counts.items() if count == top)
    if len(modes) == len(counts):
        return "无（各值出现次数相同）"
    shown = ", ".join(str(value) for value in modes[:6])
    if len(modes) > 6:
        shown += " 等"
    return f"{shown}（{top} 次）"


_CHART_MARGIN = 46


def _render_line_chart(
    samples: list[tuple[float, int]], width: int = 760, height: int = 340
) -> Image.Image:
    """BPM over elapsed time as a line plot with grid and axis labels."""
    image = Image.new("RGBA", (width, height), "#ffffff")
    draw = ImageDraw.Draw(image)
    font = _chart_font(13)
    if len(samples) < 2:
        draw.text(
            (width // 2, height // 2),
            "样本不足，无法绘制折线图",
            fill="#666666",
            font=font,
            anchor="mm",
        )
        return image
    left, top, right, bottom = _CHART_MARGIN, 18, width - 14, height - 40
    times = [t for t, _ in samples]
    values = [v for _, v in samples]
    t_min, t_max = times[0], max(times[-1], times[0] + 0.001)
    v_min, v_max = min(values), max(values)
    if v_min == v_max:
        v_min, v_max = v_min - 1, v_max + 1
    pad = (v_max - v_min) * 0.08
    v_min, v_max = v_min - pad, v_max + pad

    def px(t: float) -> float:
        return left + (t - t_min) / (t_max - t_min) * (right - left)

    def py(v: float) -> float:
        return bottom - (v - v_min) / (v_max - v_min) * (bottom - top)

    for grid_value in range(int(v_min) - 1, int(v_max) + 2):
        if v_min <= grid_value <= v_max:
            y = py(grid_value)
            draw.line((left, y, right, y), fill="#dddddd", width=1)
            draw.text((left - 6, y), str(grid_value), fill="#555555", font=font, anchor="rm")
    draw.line((left, top, left, bottom), fill="#333333", width=1)
    draw.line((left, bottom, right, bottom), fill="#333333", width=1)
    points = [(px(t), py(v)) for t, v in samples]
    if len(points) > width:
        step = len(points) / (width // 2)
        thinned = [points[int(i)] for i in range(0, len(points), step)]
    else:
        thinned = points
    draw.line(thinned, fill="#e53935", width=2, joint="curve")
    for x, y in thinned[:: max(1, len(thinned) // 60)]:
        draw.ellipse((x - 2, y - 2, x + 2, y + 2), fill="#e53935")
    draw.text(
        ((left + right) / 2, height - 14),
        f"时间（秒，{t_min:.0f} – {t_max:.0f}）",
        fill="#555555",
        font=font,
        anchor="mm",
    )
    draw.text(
        (12, (top + bottom) / 2),
        "BPM",
        fill="#555555",
        font=font,
        anchor="mm",
    )
    return image


def _render_scatter_chart(
    samples: list[tuple[float, int]], width: int = 760, height: int = 340
) -> Image.Image:
    """Pure scatter plot: no connecting line, color drifts blue->red in time.

    The color gradient carries information the line chart cannot: where in
    the session each BPM value occurred.
    """
    image = Image.new("RGBA", (width, height), "#ffffff")
    draw = ImageDraw.Draw(image)
    if len(samples) < 2:
        draw.text(
            (width // 2, height // 2),
            "样本不足，无法绘制散点图",
            fill="#666666",
            font=_chart_font(13),
            anchor="mm",
        )
        return image
    left, top, right, bottom = _CHART_MARGIN, 18, width - 14, height - 40
    times = [t for t, _ in samples]
    values = [v for _, v in samples]
    v_low, v_high = min(values), max(values)
    if v_low == v_high:
        v_low, v_high = v_low - 1, v_high + 1
    pad = (v_high - v_low) * 0.08
    v_min, v_max = v_low - pad, v_high + pad
    t_min, t_max = times[0], max(times[-1], times[0] + 0.001)
    median = statistics.median(values)

    def px(t: float) -> float:
        return left + (t - t_min) / (t_max - t_min) * (right - left)

    def py(v: float) -> float:
        return bottom - (v - v_min) / (v_max - v_min) * (bottom - top)

    for grid_value in range(int(v_min) - 1, int(v_max) + 2):
        if v_min <= grid_value <= v_max:
            y = py(grid_value)
            draw.line((left, y, right, y), fill="#dddddd", width=1)
            draw.text(
                (left - 6, y),
                str(grid_value),
                fill="#555555",
                font=_chart_font(13),
                anchor="rm",
            )
    draw.line((left, top, left, bottom), fill="#333333", width=1)
    draw.line((left, bottom, right, bottom), fill="#333333", width=1)

    # Median as a horizontal dashed reference line.
    median_y = py(median)
    x = left
    while x < right:
        draw.line((x, median_y, min(x + 8, right), median_y), fill="#43a047", width=2)
        x += 14
    draw.text(
        (right - 4, median_y - 10),
        f"中位数 {median:g}",
        fill="#43a047",
        font=_chart_font(12),
        anchor="rm",
    )

    # Points colored along a blue -> red time gradient.
    span = max(1e-6, t_max - t_min)
    for t, v in samples:
        ratio = (t - t_min) / span
        red = int(30 + ratio * (211 - 30))
        green = int(136 + ratio * (57 - 136))
        blue = int(229 + ratio * (53 - 229))
        x, y = px(t), py(v)
        draw.ellipse((x - 3, y - 3, x + 3, y + 3), fill=(red, green, blue, 255))

    # Ring the first min and max samples and label them.
    highlights = (
        (min(values), "#1e88e5", "最小"),
        (max(values), "#fb8c00", "最大"),
    )
    legend_x = right - 150
    for order, (value, color, label) in enumerate(highlights):
        first = next((t for t, v in samples if v == value), None)
        if first is None:
            continue
        x, y = px(first), py(value)
        draw.ellipse((x - 6, y - 6, x + 6, y + 6), outline=color, width=2)
        draw.text(
            (legend_x, top + 4 + 16 * order),
            f"{label} {value}",
            fill=color,
            font=_chart_font(12),
        )

    draw.text(
        ((left + right) / 2, height - 14),
        f"时间（秒，{t_min:.0f} – {t_max:.0f}）· 点色随时间由蓝渐变到红",
        fill="#555555",
        font=_chart_font(13),
        anchor="mm",
    )
    draw.text((12, (top + bottom) / 2), "BPM", fill="#555555", font=_chart_font(13), anchor="mm")
    return image


def _render_histogram(
    values: list[int], width: int = 760, height: int = 340
) -> Image.Image:
    """BPM distribution: one bar per observed value."""
    image = Image.new("RGBA", (width, height), "#ffffff")
    draw = ImageDraw.Draw(image)
    font = _chart_font(13)
    if not values:
        draw.text(
            (width // 2, height // 2),
            "无样本",
            fill="#666666",
            font=font,
            anchor="mm",
        )
        return image
    counts: dict[int, int] = {}
    for value in values:
        counts[value] = counts.get(value, 0) + 1
    left, top, right, bottom = _CHART_MARGIN, 18, width - 14, height - 40
    keys = sorted(counts)
    peak = max(counts.values())
    slot = (right - left) / len(keys)
    bar_width = max(6, min(48, slot * 0.72))
    draw.line((left, top, left, bottom), fill="#333333", width=1)
    draw.line((left, bottom, right, bottom), fill="#333333", width=1)
    label_step = max(1, len(keys) // 14)
    for index, key in enumerate(keys):
        x_center = left + slot * (index + 0.5)
        bar_height = (bottom - top) * counts[key] / peak
        draw.rectangle(
            (x_center - bar_width / 2, bottom - bar_height,
             x_center + bar_width / 2, bottom),
            fill="#e53935",
        )
        if index % label_step == 0 or index == len(keys) - 1:
            draw.text(
                (x_center, bottom + 6),
                str(key),
                fill="#555555",
                font=font,
                anchor="mm",
            )
    for grid in range(1, 5):
        y = bottom - (bottom - top) * grid / 5
        draw.line((left, y, right, y), fill="#dddddd", width=1)
        draw.text(
            (left - 6, y),
            str(round(peak * grid / 5)),
            fill="#555555",
            font=font,
            anchor="rm",
        )
    draw.text(
        ((left + right) / 2, height - 14),
        "BPM（柱高 = 出现次数，峰值 %d）" % peak,
        fill="#555555",
        font=font,
        anchor="mm",
    )
    return image


_CHART_FONT_CACHE: dict[int, ImageFont.FreeTypeFont | ImageFont.ImageFont] = {}


def _beat_scale(phase: float) -> float:
    """Heart-beat scale factor for one cardiac cycle, phase in [0, 1).

    Classic "lub-dub" double pulse: a quick small contraction, a short
    pause, a stronger second contraction, then a slow relaxed fall and a
    quiet rest. Piecewise smooth (cosine-eased) so no linear kinks show at
    30 fps. Returns roughly 1.00-1.18.
    """

    def ease_out(progress: float) -> float:
        return 1.0 - (1.0 - progress) ** 2

    def ease_in_out(progress: float) -> float:
        return 0.5 - 0.5 * math.cos(math.pi * progress)

    rest = 1.0
    first_peak = 1.12
    second_peak = 1.18
    if phase < 0.12:
        return rest + (first_peak - rest) * ease_out(phase / 0.12)
    if phase < 0.22:
        return first_peak + (rest - first_peak) * ease_in_out(
            (phase - 0.12) / 0.10
        )
    if phase < 0.32:
        return rest + (second_peak - rest) * ease_out((phase - 0.22) / 0.10)
    if phase < 0.55:
        return second_peak + (rest - second_peak) * ease_in_out(
            (phase - 0.32) / 0.23
        )
    return rest


def _bucket_ohlc(
    samples: list[tuple[float, int]], bucket_seconds: float
) -> list[dict[str, float]]:
    """Aggregate samples into time buckets of open/high/low/close values."""
    buckets: list[dict[str, float]] = []
    for t, v in samples:
        slot = int(t // bucket_seconds)
        if buckets and buckets[-1]["slot"] == slot:
            current = buckets[-1]
            current["high"] = max(current["high"], v)
            current["low"] = min(current["low"], v)
            current["close"] = v
            current["count"] += 1
        else:
            buckets.append(
                {
                    "slot": slot,
                    "open": v,
                    "high": v,
                    "low": v,
                    "close": v,
                    "count": 1,
                }
            )
    return buckets


def _render_candlestick_chart(
    samples: list[tuple[float, int]], width: int = 760, height: int = 340
) -> Image.Image:
    """Stock-style candlestick chart: one OHLC candle per time bucket.

    Buckets adapt to session length so a short run still shows a handful of
    candles (aim for 10-40). Red = close >= open ( rising ), green = falling.
    """
    image = Image.new("RGBA", (width, height), "#ffffff")
    draw = ImageDraw.Draw(image)
    font = _chart_font(13)
    if len(samples) < 2:
        draw.text(
            (width // 2, height // 2),
            "样本不足，无法绘制 K 线图",
            fill="#666666",
            font=font,
            anchor="mm",
        )
        return image
    duration = samples[-1][0] - samples[0][0]
    bucket_seconds = max(5.0, duration / 24)
    buckets = _bucket_ohlc(samples, bucket_seconds)
    left, top, right, bottom = _CHART_MARGIN, 18, width - 14, height - 40
    v_low = min(b["low"] for b in buckets)
    v_high = max(b["high"] for b in buckets)
    if v_low == v_high:
        v_low, v_high = v_low - 1, v_high + 1
    pad = (v_high - v_low) * 0.08
    v_min, v_max = v_low - pad, v_high + pad
    slot_first = buckets[0]["slot"]
    slot_last = buckets[-1]["slot"]
    slot_span = max(1, slot_last - slot_first)

    def px(slot: int) -> float:
        return left + (slot - slot_first) / slot_span * (right - left)

    def py(v: float) -> float:
        return bottom - (v - v_min) / (v_max - v_min) * (bottom - top)

    for grid_value in range(int(v_min) - 1, int(v_max) + 2):
        if v_min <= grid_value <= v_max:
            y = py(grid_value)
            draw.line((left, y, right, y), fill="#dddddd", width=1)
            draw.text(
                (left - 6, y), str(grid_value), fill="#555555", font=font, anchor="rm"
            )
    draw.line((left, top, left, bottom), fill="#333333", width=1)
    draw.line((left, bottom, right, bottom), fill="#333333", width=1)

    candle_width = max(4, min(28, (right - left) / max(1, len(buckets)) * 0.6))
    for bucket in buckets:
        x = px(bucket["slot"])
        rising = bucket["close"] >= bucket["open"]
        color = "#e53935" if rising else "#2e7d32"
        top_y = py(bucket["high"])
        bottom_y = py(bucket["low"])
        draw.line((x, top_y, x, bottom_y), fill=color, width=1)  # wick
        body_top = py(max(bucket["open"], bucket["close"]))
        body_bottom = py(min(bucket["open"], bucket["close"]))
        if body_bottom - body_top < 2:
            body_bottom = body_top + 2
        if rising:
            draw.rectangle(
                (x - candle_width / 2, body_top, x + candle_width / 2, body_bottom),
                fill=color,
            )
        else:
            draw.rectangle(
                (x - candle_width / 2, body_top, x + candle_width / 2, body_bottom),
                fill="#ffffff",
                outline=color,
                width=2,
            )
    label_step = max(1, len(buckets) // 8)
    for index, bucket in enumerate(buckets):
        if index % label_step == 0 or index == len(buckets) - 1:
            draw.text(
                (px(bucket["slot"]), bottom + 6),
                f"{int(bucket['slot'] * bucket_seconds)}s",
                fill="#555555",
                font=font,
                anchor="mm",
            )
    draw.text(
        ((left + right) / 2, height - 14),
        f"K 线（每桶 {bucket_seconds:.0f} 秒，红 = 收 ≥ 开，绿 = 收 < 开）",
        fill="#555555",
        font=font,
        anchor="mm",
    )
    draw.text((12, (top + bottom) / 2), "BPM", fill="#555555", font=font, anchor="mm")
    return image


def _chart_font(size: int) -> ImageFont.FreeTypeFont | ImageFont.ImageFont:
    font = _CHART_FONT_CACHE.get(size)
    if font is None:
        try:
            font = ImageFont.truetype("C:\\Windows\\Fonts\\msyh.ttc", size)
        except OSError:
            try:
                font = ImageFont.load_default(size)
            except TypeError:
                font = ImageFont.load_default()
        _CHART_FONT_CACHE[size] = font
    return font


class StatisticsWindow(tk.Toplevel):
    """Statistics view of one monitoring session: numbers and charts."""

    def __init__(self, owner: tk.Tk, session: HeartRateSession) -> None:
        super().__init__(owner)
        self.title("心率统计")
        self.geometry("820x620")
        self.transient(owner)
        self._session = session
        self._photo_images: list[ImageTk.PhotoImage] = []

        summary = session.summary()
        header = ttk.Frame(self, padding=(14, 12))
        header.pack(fill=tk.X)
        ttk.Label(
            header,
            text=f"{summary['设备']}    开始于 {summary['开始时间']}    "
            f"共 {summary['样本数']} 个样本",
        ).pack(side=tk.LEFT)

        buttons = ttk.Frame(self, padding=(14, 0))
        buttons.pack(fill=tk.X)
        ttk.Button(buttons, text="导出 Excel（xlsx）", command=self._export).pack(
            side=tk.LEFT, padx=(0, 8)
        )
        ttk.Button(buttons, text="导出 CSV", command=self._export_csv).pack(
            side=tk.LEFT, padx=(0, 8)
        )
        ttk.Label(
            buttons,
            text="导出内容：原始时间序列 + 统计量 + 全部图表",
        ).pack(side=tk.LEFT)

        notebook = ttk.Notebook(self)
        notebook.pack(fill=tk.BOTH, expand=True, padx=14, pady=12)

        numbers_frame = ttk.Frame(notebook, padding=8)
        notebook.add(numbers_frame, text="统计量")
        columns = ("stat", "value")
        tree = ttk.Treeview(numbers_frame, columns=columns, show="headings", height=16)
        tree.heading("stat", text="统计量")
        tree.heading("value", text="数值")
        tree.column("stat", width=220, anchor=tk.W)
        tree.column("value", width=280, anchor=tk.W)
        tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar = ttk.Scrollbar(numbers_frame, orient=tk.VERTICAL, command=tree.yview)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        tree.configure(yscrollcommand=scrollbar.set)
        for name, value in summary.items():
            tree.insert("", tk.END, values=(name, value))

        self._chart_images: dict[str, Image.Image] = {
            "折线图": _render_line_chart(session.samples),
            "散点图": _render_scatter_chart(session.samples),
            "柱状图": _render_histogram(session.values),
            "K线图": _render_candlestick_chart(session.samples),
        }
        for title, image in self._chart_images.items():
            frame = ttk.Frame(notebook, padding=8)
            notebook.add(frame, text=title)
            photo = ImageTk.PhotoImage(image)
            self._photo_images.append(photo)
            ttk.Label(frame, image=photo).pack(anchor=tk.CENTER)

    def _export_csv(self) -> None:
        default_name = f"心率数据_{self._session.started_at:%Y%m%d_%H%M%S}.csv"
        path = filedialog.asksaveasfilename(
            parent=self,
            title="导出原始数据（CSV）",
            defaultextension=".csv",
            initialfile=default_name,
            filetypes=(("CSV 文件", "*.csv"),),
        )
        if not path:
            return
        try:
            export_session_csv(self._session, path)
        except OSError as error:
            messagebox.showerror("导出失败", f"无法写入 CSV 文件：{error}", parent=self)
            return
        messagebox.showinfo("导出成功", f"已保存到：\n{path}", parent=self)

    def _export(self) -> None:
        default_name = (
            f"心率统计_{self._session.started_at:%Y%m%d_%H%M%S}.xlsx"
        )
        path = filedialog.asksaveasfilename(
            parent=self,
            title="导出心率统计",
            defaultextension=".xlsx",
            initialfile=default_name,
            filetypes=(("Excel 工作簿", "*.xlsx"),),
        )
        if not path:
            return
        try:
            export_session_xlsx(self._session, path, self._chart_images)
        except (OSError, ValueError) as error:
            messagebox.showerror("导出失败", f"无法写入 Excel 文件：{error}", parent=self)
            return
        messagebox.showinfo("导出成功", f"已保存到：\n{path}", parent=self)


def export_session_csv(session: HeartRateSession, path: str) -> None:
    """Write the raw time series as CSV (Excel-compatible, UTF-8 BOM)."""
    with open(path, "w", encoding="utf-8-sig", newline="") as stream:
        writer = csv.writer(stream)
        writer.writerow(["时间（秒）", "心率（BPM）"])
        for elapsed, bpm in session.samples:
            writer.writerow([round(elapsed, 3), bpm])


def export_session_xlsx(
    session: HeartRateSession, path: str, charts: dict[str, Image.Image]
) -> None:
    """Write raw series, statistics and embedded chart images to a workbook."""
    try:
        from openpyxl import Workbook
        from openpyxl.drawing.image import Image as XlsxImage
        from openpyxl.styles import Font, PatternFill
        from openpyxl.utils import get_column_letter
    except ImportError as error:  # pragma: no cover - runtime guidance
        raise ValueError(
            "缺少 openpyxl，请先执行：py -m pip install openpyxl"
        ) from error

    workbook = Workbook()

    raw_sheet = workbook.active
    assert raw_sheet is not None
    raw_sheet.title = "原始时间序列"
    raw_sheet.append(["时间（秒）", "心率（BPM）"])
    for elapsed, bpm in session.samples:
        raw_sheet.append([round(elapsed, 3), bpm])
    raw_sheet.column_dimensions["A"].width = 14
    raw_sheet.column_dimensions["B"].width = 14
    raw_sheet.freeze_panes = "A2"

    stats_sheet = workbook.create_sheet("统计量")
    stats_sheet.append(["统计量", "数值"])
    for name, value in session.summary().items():
        stats_sheet.append([name, value])
    stats_sheet.column_dimensions["A"].width = 22
    stats_sheet.column_dimensions["B"].width = 32
    for cell in stats_sheet[1]:
        cell.font = Font(bold=True)
        cell.fill = PatternFill("solid", start_color="FFEEEEEE")

    chart_sheet = workbook.create_sheet("图表")
    chart_sheet["A1"] = "心率统计图表"
    chart_sheet["A1"].font = Font(bold=True, size=14)
    anchor_row = 3
    temp_paths: list[str] = []
    try:
        for index, (title, image) in enumerate(charts.items()):
            chart_sheet.cell(row=anchor_row, column=1, value=title).font = Font(
                bold=True, size=12
            )
            temp_path = Path(tempfile.gettempdir()) / (
                f"hrm_chart_{session.started_at:%Y%m%d%H%M%S}_{index}.png"
            )
            image.convert("RGB").save(temp_path, format="PNG")
            temp_paths.append(str(temp_path))
            xlsx_image = XlsxImage(temp_path)
            xlsx_image.width, xlsx_image.height = image.width * 0.75, image.height * 0.75
            chart_sheet.add_image(xlsx_image, f"A{anchor_row + 1}")
            anchor_row += 22
    finally:
        for temp_path in temp_paths:
            shutil.rmtree(temp_path, ignore_errors=True)
    chart_sheet.column_dimensions["A"].width = 30

    workbook.save(path)


def export_sessions_xlsx(
    sessions: list[HeartRateSession], path: str
) -> None:
    """Workbook for a multi-device run: one series sheet per device."""
    try:
        from openpyxl import Workbook
        from openpyxl.drawing.image import Image as XlsxImage
        from openpyxl.styles import Font
    except ImportError as error:  # pragma: no cover - runtime guidance
        raise ValueError(
            "缺少 openpyxl，请先执行：py -m pip install openpyxl"
        ) from error

    workbook = Workbook()
    overview = workbook.active
    assert overview is not None
    overview.title = "汇总"
    overview.append(["设备", "MAC 地址", "样本数", "均值", "最小值", "最大值", "标准差"])
    for session in sessions:
        values = session.values
        overview.append(
            [
                session.device_name,
                session.address,
                len(values),
                round(statistics.mean(values), 2) if values else "",
                min(values) if values else "",
                max(values) if values else "",
                round(statistics.stdev(values), 2) if len(values) >= 2 else "",
            ]
        )
    for column, width in zip("ABCDEFG", (18, 20, 10, 10, 10, 10, 10)):
        overview.column_dimensions[column].width = width
    for cell in overview[1]:
        cell.font = Font(bold=True)

    chart_sheet = workbook.create_sheet("图表")
    chart_sheet["A1"] = "多设备心率折线图"
    chart_sheet["A1"].font = Font(bold=True, size=14)
    anchor_row = 3
    temp_paths: list[str] = []
    try:
        for index, session in enumerate(sessions):
            chart_sheet.cell(
                row=anchor_row,
                column=1,
                value=f"{session.device_name} ({session.address})",
            ).font = Font(bold=True, size=12)
            image = _render_line_chart(session.samples)
            temp_path = Path(tempfile.gettempdir()) / (
                f"hrm_multi_chart_{index}_{int(time.time())}.png"
            )
            image.convert("RGB").save(temp_path, format="PNG")
            temp_paths.append(str(temp_path))
            xlsx_image = XlsxImage(temp_path)
            xlsx_image.width, xlsx_image.height = image.width * 0.75, image.height * 0.75
            chart_sheet.add_image(xlsx_image, f"A{anchor_row + 1}")
            anchor_row += 22
    finally:
        for temp_path in temp_paths:
            shutil.rmtree(temp_path, ignore_errors=True)
    for position, session in enumerate(sessions):
        sheet = workbook.create_sheet(
            f"设备{position + 1}"[:31]
        )
        sheet.append(["时间（秒）", "心率（BPM）"])
        for elapsed, bpm in session.samples:
            sheet.append([round(elapsed, 3), bpm])
        sheet.column_dimensions["A"].width = 14
        sheet.column_dimensions["B"].width = 14
        sheet.freeze_panes = "A2"
    workbook.save(path)


class MultiStatisticsWindow(tk.Toplevel):
    """Statistics over a multi-device monitoring run."""

    def __init__(self, owner: tk.Tk, sessions: list[HeartRateSession]) -> None:
        super().__init__(owner)
        self.title("心率统计（多设备）")
        self.geometry("860x640")
        self.transient(owner)
        self._sessions = sessions
        self._photo_images: list[ImageTk.PhotoImage] = []

        total = sum(len(s.values) for s in sessions)
        header = ttk.Frame(self, padding=(14, 12))
        header.pack(fill=tk.X)
        ttk.Label(
            header,
            text=f"{len(sessions)} 台设备，共 {total} 个样本",
        ).pack(side=tk.LEFT)

        buttons = ttk.Frame(self, padding=(14, 0))
        buttons.pack(fill=tk.X)
        ttk.Button(
            buttons, text="导出 Excel（xlsx，含每设备数据）",
            command=self._export,
        ).pack(side=tk.LEFT, padx=(0, 8))
        for session in sessions[:4]:
            ttk.Button(
                buttons,
                text=f"CSV：{session.device_name[:12]}",
                command=lambda s=session: self._export_csv(s),
            ).pack(side=tk.LEFT, padx=(0, 6))

        notebook = ttk.Notebook(self)
        notebook.pack(fill=tk.BOTH, expand=True, padx=14, pady=12)

        overview = ttk.Frame(notebook, padding=8)
        notebook.add(overview, text="设备对比")
        columns = ("name", "samples", "mean", "min", "max", "stdev")
        tree = ttk.Treeview(overview, columns=columns, show="headings", height=14)
        for column, text, width in (
            ("name", "设备", 200),
            ("samples", "样本数", 80),
            ("mean", "均值", 90),
            ("min", "最小", 80),
            ("max", "最大", 80),
            ("stdev", "标准差", 90),
        ):
            tree.heading(column, text=text)
            tree.column(column, width=width, anchor=tk.CENTER)
        tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        for session in sessions:
            values = session.values
            tree.insert(
                "",
                tk.END,
                values=(
                    session.device_name,
                    len(values),
                    round(statistics.mean(values), 2),
                    min(values),
                    max(values),
                    round(statistics.stdev(values), 2) if len(values) >= 2 else "-",
                ),
            )

        for session in sessions[:8]:
            frame = ttk.Frame(notebook, padding=8)
            notebook.add(frame, text=f"{session.device_name[:10]}")
            image = _render_line_chart(session.samples)
            photo = ImageTk.PhotoImage(image)
            self._photo_images.append(photo)
            ttk.Label(frame, image=photo).pack(anchor=tk.CENTER)

    def _export_csv(self, session: HeartRateSession) -> None:
        safe = re.sub(r'[\\/:*?"<>|]', "_", session.device_name)
        path = filedialog.asksaveasfilename(
            parent=self,
            title="导出原始数据（CSV）",
            defaultextension=".csv",
            initialfile=f"心率数据_{safe}.csv",
            filetypes=(("CSV 文件", "*.csv"),),
        )
        if not path:
            return
        try:
            export_session_csv(session, path)
        except OSError as error:
            messagebox.showerror("导出失败", f"无法写入 CSV 文件：{error}", parent=self)
            return
        messagebox.showinfo("导出成功", f"已保存到：\n{path}", parent=self)

    def _export(self) -> None:
        path = filedialog.asksaveasfilename(
            parent=self,
            title="导出多设备统计（xlsx）",
            defaultextension=".xlsx",
            initialfile=f"心率统计_多设备_{datetime.now():%Y%m%d_%H%M%S}.xlsx",
            filetypes=(("Excel 工作簿", "*.xlsx"),),
        )
        if not path:
            return
        try:
            export_sessions_xlsx(self._sessions, path)
        except (OSError, ValueError) as error:
            messagebox.showerror("导出失败", f"无法写入 Excel 文件：{error}", parent=self)
            return
        messagebox.showinfo("导出成功", f"已保存到：\n{path}", parent=self)


class HeartRateMonitor:
    """Run BLE discovery/notifications on a worker thread.

    With ``device_address`` empty, every Mi-band advertisement is accepted
    and reported as ``heart_rate_multi`` so several devices record at once;
    rate limiting is applied per device.
    """

    def __init__(
        self,
        events: queue.Queue[tuple[str, object]],
        device_address: str,
        sample_frequency: float,
        low_bpm: int = DEFAULT_LOW_BPM,
        high_bpm: int = DEFAULT_HIGH_BPM,
    ) -> None:
        self._events = events
        self._device_address = device_address.strip().lower()
        self._frequency_lock = threading.Lock()
        self._sample_interval = 1.0 / sample_frequency
        self._low_bpm = low_bpm
        self._high_bpm = high_bpm
        self._last_sample_time = 0.0
        self._last_device_info_time = 0.0
        self._last_status_time = 0.0
        self._last_sample_times: dict[str, float] = {}
        self._last_alert_time = 0.0
        self._stop_requested = threading.Event()
        self._pause_requested = threading.Event()
        self._thread: threading.Thread | None = None

    def start(self) -> None:
        if self._thread is not None and self._thread.is_alive():
            return
        self._stop_requested.clear()
        self._pause_requested.clear()
        self._thread = threading.Thread(target=self._run, daemon=True)
        self._thread.start()

    def stop(self) -> None:
        self._stop_requested.set()

    def pause(self) -> None:
        self._pause_requested.set()

    def resume(self) -> None:
        self._pause_requested.clear()

    def set_sample_frequency(self, sample_frequency: float) -> None:
        """Update the output rate without restarting the BLE scanner."""
        if not MIN_SAMPLE_FREQUENCY <= sample_frequency <= MAX_SAMPLE_FREQUENCY:
            raise ValueError(
                f"采样频率必须是 {MIN_SAMPLE_FREQUENCY:g} 到 "
                f"{MAX_SAMPLE_FREQUENCY:g} Hz 之间的数字。"
            )
        with self._frequency_lock:
            self._sample_interval = 1.0 / sample_frequency

    def _run(self) -> None:
        try:
            asyncio.run(self._monitor())
        except Exception as error:
            self._events.put(("error", str(error)))
        finally:
            self._events.put(("stopped", None))

    async def _monitor(self) -> None:
        self._events.put(("status", "正在监听心率广播（无需连接或写入权限）..."))

        def on_advertisement(device: BLEDevice, advertisement: AdvertisementData) -> None:
            self._on_advertisement(device, advertisement)

        scanner = BleakScanner(detection_callback=on_advertisement)
        await scanner.start()
        self._events.put(("status", "扫描器已启动，等待目标手环广播..."))
        try:
            while not self._stop_requested.is_set():
                await asyncio.sleep(0.25)
        finally:
            await scanner.stop()

    def _on_advertisement(
        self,
        device: BLEDevice,
        advertisement: AdvertisementData,
    ) -> None:
        if self._device_address and device.address.lower() != self._device_address:
            return

        data = advertisement.manufacturer_data.get(XIAOMI_COMPANY_ID)
        if data is None:
            return

        if len(data) <= 3:
            self._events.put(("error", "收到不完整的小米心率广播数据。"))
            return

        if self._pause_requested.is_set():
            return

        now = time.monotonic()
        address_key = device.address.lower()
        with self._frequency_lock:
            sample_interval = self._sample_interval
        last = self._last_sample_times.get(address_key, 0.0)
        if now - last < sample_interval:
            return
        self._last_sample_times[address_key] = now

        if not self._device_address and now - self._last_device_info_time >= 0.5:
            self._last_device_info_time = now
            self._events.put(
                (
                    "device_info",
                    {
                        "name": device.name or "未知设备",
                        "address": device.address,
                        "rssi": advertisement.rssi,
                    },
                )
            )
        self._last_sample_time = now
        if now - self._last_status_time >= 1.0:
            self._last_status_time = now
            self._events.put(
                ("status", f"已收到 {device.name or self._device_address} 的广播")
            )
        heart_rate = data[3]
        if self._device_address:
            self._check_alert(heart_rate, now)
            self._events.put(("heart_rate", heart_rate))
        else:
            self._events.put(
                (
                    "heart_rate_multi",
                    (device.address, device.name or device.address, heart_rate),
                )
            )

    def _check_alert(self, heart_rate: int, now: float) -> None:
        """Fire at most one alert per 30 s when BPM leaves the safe band."""
        if self._low_bpm <= heart_rate <= self._high_bpm:
            return
        if now - self._last_alert_time < 30.0:
            return
        self._last_alert_time = now
        kind = "过低" if heart_rate < self._low_bpm else "过高"
        self._events.put(("alert", f"心率{kind}：{heart_rate} BPM"))


class HeartRateWindow(tk.Tk):
    _CONFIG_PATH = (
        Path(os.environ.get("APPDATA", Path.home()))
        / "MiBandHeartRateMonitor"
        / "devices.json"
    )
    _LEGACY_CONFIG_PATHS = (
        _CONFIG_PATH,
    )

    def __init__(self) -> None:
        super().__init__()
        sv_ttk.set_theme("dark")
        self.title("小米手环 6 心率监控")
        self.minsize(0, 0)
        self.resizable(True, True)

        self._events: queue.Queue[tuple[str, object]] = queue.Queue()
        self._monitor: HeartRateMonitor | None = None
        self._closing = False
        self._session: HeartRateSession | None = None
        self._session_started: float = 0.0
        self._multi_sessions: dict[str, HeartRateSession] | None = None
        self._multi_session_started: float = 0.0
        self._statistics_window: StatisticsWindow | None = None
        self._frequency_update_job: str | None = None
        self._saved_addresses = self._load_saved_addresses()
        # pywebview's Windows GUI loop must own the process main thread and
        # cannot safely be started beside Tk's mainloop.
        self._floating_window = FloatingHeartWindow(self)
        self._scan_thread: threading.Thread | None = None
        self._app_config = self._load_app_config()
        self._hide_chrome_var = tk.BooleanVar(value=False)
        self._number_format_var = tk.StringVar(value=DEFAULT_NUMBER_FORMAT)
        self._icon_style_var = tk.StringVar(value="像素心脏")
        self._icon_size_var = tk.IntVar(value=DEFAULT_ICON_SIZE)
        self._number_size_var = tk.IntVar(value=DEFAULT_NUMBER_SIZE)
        self._font_family_var = tk.StringVar(value=DEFAULT_FONT_FAMILY)
        self._custom_icon_path = ""
        self._icon_x_var = tk.DoubleVar(value=140)
        self._icon_y_var = tk.DoubleVar(value=48)
        self._number_x_var = tk.DoubleVar(value=140)
        self._number_y_var = tk.DoubleVar(value=162)
        self._heart_color = DEFAULT_HEART_COLOR
        self._number_color = DEFAULT_NUMBER_COLOR
        self._floating_background = DEFAULT_FLOATING_BACKGROUND
        self._background_opacity_var = tk.DoubleVar(value=0.75)
        self._content_opacity_var = tk.DoubleVar(value=1.0)
        self._low_bpm_var = tk.IntVar(value=DEFAULT_LOW_BPM)
        self._high_bpm_var = tk.IntVar(value=DEFAULT_HIGH_BPM)
        self._show_chart_var = tk.BooleanVar(value=False)
        self._show_extremes_var = tk.BooleanVar(value=False)
        self._beat_enabled_var = tk.BooleanVar(value=False)
        self._floating_settings_visible = False
        self._apply_persisted_config()

        frame = ttk.Frame(self, padding=20)
        self._main_frame = frame
        frame.pack(fill=tk.BOTH, expand=True)
        frame.columnconfigure(1, weight=1)
        frame.columnconfigure(2, weight=0)
        ttk.Label(frame, text="手环 MAC 地址").grid(row=0, column=0, sticky=tk.W, pady=4)
        self._address_var = tk.StringVar(
            value=self._saved_addresses[0]
            if self._saved_addresses
            else ""
        )
        self._address_combo = ttk.Combobox(
            frame,
            textvariable=self._address_var,
            values=self._saved_addresses,
            width=22,
        )
        self._address_combo.grid(row=0, column=1, sticky=tk.EW, padx=(12, 0), pady=4)
        ttk.Button(
            frame,
            text="扫描设备",
            command=self._scan_devices,
        ).grid(row=0, column=2, padx=(8, 0), pady=4)
        ttk.Label(frame, text="采样频率（Hz）").grid(row=1, column=0, sticky=tk.W, pady=4)
        self._frequency_entry = ttk.Entry(frame, width=22)
        self._frequency_entry.insert(0, str(DEFAULT_SAMPLE_FREQUENCY))
        self._frequency_entry.grid(row=1, column=1, sticky=tk.EW, padx=(12, 0), pady=4)
        self._frequency_entry.bind("<KeyRelease>", self._schedule_frequency_update)
        self._multi_device_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(
            frame,
            text="多设备模式（记录所有小米心率广播）",
            variable=self._multi_device_var,
        ).grid(row=1, column=2, padx=(8, 0), pady=4, sticky=tk.W)
        ttk.Label(frame, text="当前心率", font=("Segoe UI", 13)).grid(
            row=2, column=0, columnspan=3, pady=(18, 0)
        )
        self._heart_rate_label = ttk.Label(
            frame,
            text="-- BPM",
            font=("Segoe UI", 34, "bold"),
        )
        self._heart_rate_label.grid(row=3, column=0, columnspan=3, pady=(8, 12))
        self._device_info_label = ttk.Label(
            frame,
            text="设备：--\n信号：-- dBm",
            justify=tk.CENTER,
        )
        self._device_info_label.grid(row=4, column=0, columnspan=3, pady=(0, 4))
        self._status_label = ttk.Label(frame, text="未连接", wraplength=400)
        self._status_label.grid(row=5, column=0, columnspan=3)
        thresholds_frame = ttk.Frame(frame)
        thresholds_frame.grid(row=6, column=0, columnspan=3, sticky=tk.W, pady=(6, 0))
        ttk.Label(thresholds_frame, text="提醒阈值：低于").pack(side=tk.LEFT)
        self._low_bpm_entry = ttk.Entry(thresholds_frame, width=5)
        self._low_bpm_entry.insert(0, str(self._low_bpm_var.get()))
        self._low_bpm_entry.pack(side=tk.LEFT, padx=(4, 8))
        ttk.Label(thresholds_frame, text="，高于").pack(side=tk.LEFT)
        self._high_bpm_entry = ttk.Entry(thresholds_frame, width=5)
        self._high_bpm_entry.insert(0, str(self._high_bpm_var.get()))
        self._high_bpm_entry.pack(side=tk.LEFT, padx=4)
        ttk.Label(
            thresholds_frame,
            text=" BPM，触发时提示音 + 状态栏警告（30 秒最多一次）",
        ).pack(side=tk.LEFT, padx=(0, 0))
        button_frame = ttk.Frame(frame)
        button_frame.grid(row=7, column=0, columnspan=3, pady=(16, 0))
        self._connect_button = ttk.Button(
            button_frame,
            text="开始读取",
            command=self._start_monitoring,
        )
        self._connect_button.pack(side=tk.LEFT, padx=4)
        self._pause_button = ttk.Button(
            button_frame,
            text="暂停采样",
            command=self._toggle_pause,
            state=tk.DISABLED,
        )
        self._pause_button.pack(side=tk.LEFT, padx=4)
        self._stop_button = ttk.Button(
            button_frame,
            text="停止",
            command=self._stop_monitoring,
            state=tk.DISABLED,
        )
        self._stop_button.pack(side=tk.LEFT, padx=4)
        self._theme_button = ttk.Button(
            button_frame,
            text="切换主题",
            command=self._toggle_theme,
        )
        self._theme_button.pack(side=tk.LEFT, padx=4)
        self._floating_button = ttk.Button(
            button_frame,
            text="显示悬浮窗",
            command=self._toggle_floating_window,
        )
        self._floating_button.pack(side=tk.LEFT, padx=4)
        self._floating_settings_button = ttk.Button(
            frame,
            text="展开悬浮窗设置",
            command=self._toggle_floating_settings,
        )
        self._floating_settings_button.grid(
            row=8,
            column=0,
            columnspan=3,
            sticky=tk.W,
            pady=(12, 0),
        )

        style_frame = ttk.LabelFrame(frame, text="悬浮窗样式", padding=8)
        style_frame.grid(row=9, column=0, columnspan=3, sticky=tk.EW, pady=(8, 0))
        style_frame.columnconfigure(1, weight=1)
        style_frame.columnconfigure(3, weight=1)
        ttk.Label(style_frame, text="数字格式").grid(row=0, column=0, sticky=tk.W, pady=3)
        format_entry = ttk.Entry(style_frame, textvariable=self._number_format_var)
        format_entry.grid(row=0, column=1, sticky=tk.EW, padx=(8, 0), pady=3)
        format_entry.bind("<KeyRelease>", self._apply_floating_style)
        ttk.Label(style_frame, text="图标").grid(row=1, column=0, sticky=tk.W, pady=3)
        icon_combo = ttk.Combobox(
            style_frame,
            textvariable=self._icon_style_var,
            values=("MC心脏", "像素心脏", "文字心脏", "自定义图标", "无图标"),
            state="readonly",
        )
        icon_combo.grid(row=1, column=1, sticky=tk.EW, padx=(8, 0), pady=3)
        icon_combo.bind("<<ComboboxSelected>>", self._apply_floating_style)
        ttk.Label(style_frame, text="图标大小").grid(row=2, column=2, sticky=tk.W, padx=(12, 0), pady=3)
        ttk.Scale(
            style_frame,
            from_=8,
            to=128,
            variable=self._icon_size_var,
            command=self._apply_floating_style,
        ).grid(row=2, column=3, sticky=tk.EW, pady=3)
        ttk.Button(
            style_frame,
            text="导入自定义图标",
            command=self._choose_custom_icon,
        ).grid(row=1, column=2, columnspan=2, sticky=tk.W, padx=(12, 0), pady=3)
        ttk.Label(style_frame, text="心脏 X / Y").grid(row=2, column=0, sticky=tk.W, pady=3)
        icon_xy = ttk.Frame(style_frame)
        icon_xy.grid(row=2, column=1, sticky=tk.EW, padx=(8, 0), pady=3)
        ttk.Scale(icon_xy, from_=0, to=500, variable=self._icon_x_var,
                  command=self._apply_floating_style).pack(side=tk.LEFT, fill=tk.X, expand=True)
        ttk.Scale(icon_xy, from_=0, to=300, variable=self._icon_y_var,
                  command=self._apply_floating_style).pack(side=tk.LEFT, fill=tk.X, expand=True)
        ttk.Label(style_frame, text="数字 X / Y").grid(row=3, column=0, sticky=tk.W, pady=3)
        number_xy = ttk.Frame(style_frame)
        number_xy.grid(row=3, column=1, sticky=tk.EW, padx=(8, 0), pady=3)
        ttk.Scale(number_xy, from_=0, to=600, variable=self._number_x_var,
                  command=self._apply_floating_style).pack(side=tk.LEFT, fill=tk.X, expand=True)
        ttk.Scale(number_xy, from_=0, to=300, variable=self._number_y_var,
                  command=self._apply_floating_style).pack(side=tk.LEFT, fill=tk.X, expand=True)
        ttk.Label(style_frame, text="数字大小").grid(row=3, column=2, sticky=tk.W, padx=(12, 0), pady=3)
        ttk.Scale(
            style_frame,
            from_=8,
            to=72,
            variable=self._number_size_var,
            command=self._apply_floating_style,
        ).grid(row=3, column=3, sticky=tk.EW, pady=3)
        ttk.Label(style_frame, text="字体").grid(row=4, column=0, sticky=tk.W, pady=3)
        font_combo = ttk.Combobox(
            style_frame,
            textvariable=self._font_family_var,
            values=sorted(tkfont.families(self)),
            state="readonly",
        )
        font_combo.grid(row=4, column=1, sticky=tk.EW, padx=(8, 0), pady=3)
        font_combo.bind("<<ComboboxSelected>>", self._apply_floating_style)
        ttk.Button(
            style_frame,
            text="数字颜色",
            command=lambda: self._choose_color("number"),
        ).grid(row=5, column=0, sticky=tk.W, pady=3)
        ttk.Button(
            style_frame,
            text="心脏颜色",
            command=lambda: self._choose_color("heart"),
        ).grid(row=5, column=1, sticky=tk.W, padx=(8, 0), pady=3)
        ttk.Button(
            style_frame,
            text="背景颜色",
            command=lambda: self._choose_color("background"),
        ).grid(row=6, column=0, sticky=tk.W, pady=3)
        ttk.Label(style_frame, text="透明度").grid(row=6, column=1, sticky=tk.W, padx=(8, 0))
        ttk.Label(style_frame, text="背景透明度").grid(
            row=7, column=0, sticky=tk.W, pady=3
        )
        ttk.Scale(
            style_frame,
            from_=0.0,
            to=1.0,
            variable=self._background_opacity_var,
            command=self._apply_floating_style,
        ).grid(row=7, column=1, sticky=tk.EW, pady=3)
        ttk.Label(style_frame, text="内容透明度").grid(
            row=8, column=0, sticky=tk.W, pady=3
        )
        ttk.Scale(
            style_frame,
            from_=0.0,
            to=1.0,
            variable=self._content_opacity_var,
            command=self._apply_floating_style,
        ).grid(row=8, column=1, sticky=tk.EW, pady=3)
        ttk.Label(
            style_frame,
            text="悬浮窗固定使用无边框分层模式",
        ).grid(row=9, column=0, columnspan=2, sticky=tk.W, pady=3)
        ttk.Checkbutton(
            style_frame,
            text="实时心率折线",
            variable=self._show_chart_var,
            command=self._apply_floating_style,
        ).grid(row=10, column=0, sticky=tk.W, pady=3)
        ttk.Checkbutton(
            style_frame,
            text="动态最高/最低值",
            variable=self._show_extremes_var,
            command=self._apply_floating_style,
        ).grid(row=10, column=1, sticky=tk.W, padx=(8, 0), pady=3)
        ttk.Checkbutton(
            style_frame,
            text="心脏跳动动画（随心率）",
            variable=self._beat_enabled_var,
            command=self._apply_floating_style,
        ).grid(row=11, column=0, columnspan=2, sticky=tk.W, pady=3)
        self._floating_style_frame = style_frame
        style_frame.grid_remove()

        self.protocol("WM_DELETE_WINDOW", self._close)
        self.after(30, self._process_events)
        # Defer the first overlay composition until the main window is on
        # screen; it also kicks off the async font-registry build.
        self.after_idle(self._apply_floating_style)
        # Apply the theme again after every ttk widget exists.  This avoids
        # the initial native ttk theme being painted until the first toggle.
        sv_ttk.set_theme("dark", root=self)
        self.after_idle(self._resize_main_window)

    def _apply_persisted_config(self) -> None:
        """Restore floating style, addresses and alert thresholds from disk."""
        style = self._app_config.get("style")
        if isinstance(style, dict):
            get = style.get
            self._number_format_var.set(str(get("number_format", DEFAULT_NUMBER_FORMAT)))
            self._icon_style_var.set(str(get("icon_style", "像素心脏")))
            try:
                self._icon_size_var.set(max(8, int(get("icon_size", DEFAULT_ICON_SIZE))))
                self._number_size_var.set(
                    max(8, int(get("number_size", DEFAULT_NUMBER_SIZE)))
                )
                self._icon_x_var.set(float(get("icon_x", 140)))
                self._icon_y_var.set(float(get("icon_y", 48)))
                self._number_x_var.set(float(get("number_x", 140)))
                self._number_y_var.set(float(get("number_y", 162)))
                self._background_opacity_var.set(float(get("background_opacity", 0.75)))
                self._content_opacity_var.set(float(get("content_opacity", 1.0)))
            except (TypeError, ValueError):
                pass
            self._font_family_var.set(str(get("font_family", DEFAULT_FONT_FAMILY)))
            self._custom_icon_path = str(get("custom_icon_path", ""))
            self._heart_color = str(get("heart_color", DEFAULT_HEART_COLOR))
            self._number_color = str(get("number_color", DEFAULT_NUMBER_COLOR))
            self._floating_background = str(
                get("background", DEFAULT_FLOATING_BACKGROUND)
            )
            self._show_chart_var.set(bool(get("show_chart", False)))
            self._show_extremes_var.set(bool(get("show_extremes", False)))
            self._beat_enabled_var.set(bool(get("beat_enabled", False)))
        thresholds = self._app_config.get("thresholds")
        if isinstance(thresholds, dict):
            try:
                low = int(thresholds.get("low_bpm", DEFAULT_LOW_BPM))
                high = int(thresholds.get("high_bpm", DEFAULT_HIGH_BPM))
            except (TypeError, ValueError):
                return
            if 20 <= low <= 200 and low <= high <= 250:
                self._low_bpm_var.set(low)
                self._high_bpm_var.set(high)

    def _toggle_theme(self) -> None:
        sv_ttk.toggle_theme(root=self)

    def _toggle_floating_settings(self) -> None:
        self._floating_settings_visible = not self._floating_settings_visible
        if self._floating_settings_visible:
            self._floating_style_frame.grid()
            self._floating_settings_button.configure(text="收起悬浮窗设置")
        else:
            self._floating_style_frame.grid_remove()
            self._floating_settings_button.configure(text="展开悬浮窗设置")
        self.after_idle(self._resize_main_window)

    def _resize_main_window(self) -> None:
        """Fit the main window to visible controls while preserving its position."""
        self.update_idletasks()
        width = max(560, self._main_frame.winfo_reqwidth())
        height = self._main_frame.winfo_reqheight()
        x, y = self.winfo_x(), self.winfo_y()
        self.geometry(f"{width}x{height}+{x}+{y}")

    def _toggle_floating_window(self) -> None:
        if self._floating_window.state() == "withdrawn":
            self._floating_window.show()
            self._floating_button.configure(text="隐藏悬浮窗")
            self._floating_window._redraw()
        else:
            self._floating_window._hide()
            self._floating_button.configure(text="显示悬浮窗")

    def _choose_color(self, target: str) -> None:
        current = {
            "number": self._number_color,
            "heart": self._heart_color,
            "background": self._floating_background,
        }[target]
        selected = colorchooser.askcolor(color=current, parent=self)[1]
        if selected is None:
            return
        if target == "number":
            self._number_color = selected
        elif target == "heart":
            self._heart_color = selected
        else:
            self._floating_background = selected
        self._apply_floating_style()

    def _choose_custom_icon(self) -> None:
        path = filedialog.askopenfilename(
            parent=self,
            title="选择悬浮窗图标",
            filetypes=(
                ("图片文件", "*.png *.gif *.ppm *.pgm"),
                ("所有文件", "*.*"),
            ),
        )
        if not path:
            return
        try:
            with Image.open(path) as image:
                image.verify()
        except (OSError, ValueError) as error:
            messagebox.showerror("图标导入失败", f"无法读取图片：{error}", parent=self)
            return
        self._custom_icon_path = path
        self._icon_style_var.set("自定义图标")
        self._apply_floating_style()

    def _apply_floating_style(self, *_: object) -> None:
        self._floating_window.update_style(
            self._number_format_var.get(),
            self._icon_style_var.get(),
            self._icon_x_var.get(),
            self._icon_y_var.get(),
            self._number_x_var.get(),
            self._number_y_var.get(),
            self._icon_size_var.get(),
            self._number_size_var.get(),
            self._font_family_var.get(),
            self._custom_icon_path,
            self._heart_color,
            self._number_color,
            self._floating_background,
            self._background_opacity_var.get(),
            self._content_opacity_var.get(),
            self._hide_chrome_var.get(),
            self._show_chart_var.get(),
            self._show_extremes_var.get(),
            self._beat_enabled_var.get(),
        )

    def _scan_devices(self) -> None:
        if self._scan_thread is not None and self._scan_thread.is_alive():
            return
        self._status_label.configure(text="正在扫描周边蓝牙设备（约 5 秒）...")
        self._scan_thread = threading.Thread(target=self._scan_devices_worker, daemon=True)
        self._scan_thread.start()

    def _scan_devices_worker(self) -> None:
        async def scan() -> list[dict[str, object]]:
            devices = await BleakScanner.discover(return_adv=True, timeout=5.0)
            results: list[dict[str, object]] = []
            for device, advertisement in devices.values():
                results.append(
                    {
                        "name": device.name or advertisement.local_name or "未知设备",
                        "address": device.address,
                        "rssi": advertisement.rssi,
                    }
                )
            return sorted(results, key=lambda item: int(item["rssi"]), reverse=True)

        try:
            results = asyncio.run(scan())
            self._events.put(("scan_results", results))
        except Exception as error:
            self._events.put(("error", f"扫描设备失败：{error}"))

    def _show_scan_results(self, results: object) -> None:
        if not isinstance(results, list):
            return
        dialog = tk.Toplevel(self)
        dialog.title("选择目标设备")
        dialog.geometry("520x320")
        dialog.transient(self)
        tree = ttk.Treeview(dialog, columns=("name", "address", "rssi"), show="headings")
        tree.heading("name", text="设备名称")
        tree.heading("address", text="MAC 地址")
        tree.heading("rssi", text="信号强度")
        tree.column("name", width=190)
        tree.column("address", width=190)
        tree.column("rssi", width=90, anchor=tk.CENTER)
        tree.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        for item in results:
            tree.insert(
                "",
                tk.END,
                values=(item["name"], item["address"], f"{item['rssi']} dBm"),
            )

        def choose(_: tk.Event[tk.Treeview] | None = None) -> None:
            selection = tree.selection()
            if not selection:
                return
            values = tree.item(selection[0], "values")
            self._address_var.set(str(values[1]).upper())
            dialog.destroy()
            self._status_label.configure(text=f"已选择设备：{values[0]}")

        tree.bind("<Double-1>", choose)
        ttk.Button(dialog, text="选择", command=choose).pack(pady=(0, 10))

    def _start_monitoring(self) -> None:
        multi_device = bool(self._multi_device_var.get())
        address = self._address_var.get().strip().upper()
        if not multi_device and not MAC_ADDRESS_PATTERN.fullmatch(address):
            messagebox.showerror(
                "配置错误",
                "请先点击“扫描设备”并选择目标设备，或输入有效的 "
                "MAC 地址（AA:BB:CC:DD:EE:FF）；也可以勾选多设备模式。",
                parent=self,
            )
            return

        try:
            sample_frequency = float(self._frequency_entry.get().strip())
        except ValueError:
            sample_frequency = 0
        if not MIN_SAMPLE_FREQUENCY <= sample_frequency <= MAX_SAMPLE_FREQUENCY:
            messagebox.showerror(
                "配置错误",
                f"采样频率必须是 {MIN_SAMPLE_FREQUENCY:g} 到 "
                f"{MAX_SAMPLE_FREQUENCY:g} Hz 之间的数字。",
                parent=self,
            )
            return
        try:
            low_bpm = int(self._low_bpm_entry.get().strip())
            high_bpm = int(self._high_bpm_entry.get().strip())
        except ValueError:
            low_bpm, high_bpm = self._low_bpm_var.get(), self._high_bpm_var.get()
        if not (20 <= low_bpm <= 250 and 20 <= high_bpm <= 250) or low_bpm > high_bpm:
            messagebox.showerror(
                "配置错误",
                "提醒阈值必须是 20-250 之间的数字，且低阈值不高于高阈值。",
                parent=self,
            )
            return
        self._low_bpm_var.set(low_bpm)
        self._high_bpm_var.set(high_bpm)

        if multi_device:
            self._monitor = HeartRateMonitor(
                self._events, "", sample_frequency, low_bpm, high_bpm
            )
            self._multi_sessions = {}
            self._multi_session_started = time.monotonic()
            self._session = None
            self._status_label.configure(text="多设备模式：监听所有小米心率广播...")
        else:
            self._address_var.set(address)
            self._save_address(address)
            self._monitor = HeartRateMonitor(
                self._events, address, sample_frequency, low_bpm, high_bpm
            )
            self._multi_sessions = None
            device_name = self._device_info_label.cget("text").split("\n")[0]
            self._session = HeartRateSession(address, address, sample_frequency)
            if device_name.startswith("设备：") and "(" not in device_name:
                self._session.device_name = device_name[3:].strip()
            self._session_started = time.monotonic()
            self._status_label.configure(text="准备监听广播...")
        self._save_config()
        self._connect_button.configure(state=tk.DISABLED)
        self._pause_button.configure(state=tk.NORMAL, text="暂停采样")
        self._stop_button.configure(state=tk.NORMAL)
        self._status_label.configure(text="准备监听广播...")
        self._monitor.start()

    def _toggle_pause(self) -> None:
        if self._monitor is None:
            return
        if self._pause_button.cget("text") == "暂停采样":
            self._monitor.pause()
            self._pause_button.configure(text="继续采样")
            self._status_label.configure(text="已暂停采样（蓝牙扫描仍在运行）")
        else:
            self._monitor.resume()
            self._pause_button.configure(text="暂停采样")
            self._status_label.configure(text="已恢复采样")

    def _stop_monitoring(self) -> None:
        if self._monitor is None:
            return
        self._monitor.stop()
        self._pause_button.configure(state=tk.DISABLED)
        self._stop_button.configure(state=tk.DISABLED)
        self._status_label.configure(text="正在停止...")

    def _show_statistics(self) -> None:
        """Pop the statistics window after each monitoring run ends."""
        finished = self._collect_finished_sessions()
        if not finished:
            return
        if self._statistics_window is not None and self._statistics_window.winfo_exists():
            self._statistics_window.destroy()
        if len(finished) == 1:
            self._statistics_window = StatisticsWindow(self, finished[0])
        else:
            self._statistics_window = MultiStatisticsWindow(self, finished)

    def _collect_finished_sessions(self) -> list[HeartRateSession]:
        sessions: list[HeartRateSession] = []
        if self._multi_sessions is not None:
            sessions = [
                session for session in self._multi_sessions.values() if session.values
            ]
            self._multi_sessions = None
        elif self._session is not None:
            if self._session.values:
                sessions = [self._session]
            self._session = None
        return sessions

    def _schedule_frequency_update(self, _: tk.Event[tk.Entry]) -> None:
        if self._frequency_update_job is not None:
            self.after_cancel(self._frequency_update_job)
        self._frequency_update_job = self.after(300, self._apply_frequency_update)

    def _apply_frequency_update(self) -> None:
        self._frequency_update_job = None
        try:
            sample_frequency = float(self._frequency_entry.get().strip())
        except ValueError:
            return
        if not MIN_SAMPLE_FREQUENCY <= sample_frequency <= MAX_SAMPLE_FREQUENCY:
            return
        if self._monitor is not None:
            self._monitor.set_sample_frequency(sample_frequency)
            self._status_label.configure(text=f"采样频率已更新为 {sample_frequency:g} Hz")

    def _process_events(self) -> None:
        try:
            while True:
                event, value = self._events.get_nowait()
                if event == "heart_rate":
                    self._heart_rate_label.configure(text=f"{value} BPM")
                    self._floating_window.update_value(value)
                    if self._session is not None and isinstance(value, int):
                        self._session.add(
                            time.monotonic() - self._session_started, value
                        )
                elif event == "heart_rate_multi":
                    address, name, bpm = value
                    self._record_multi_sample(address, name, bpm)
                elif event == "alert":
                    self._status_label.configure(text=f"⚠ {value}")
                    if not self._closing:
                        try:
                            winsound.Beep(1200, 300)
                        except RuntimeError:
                            pass
                elif event == "device_info":
                    info = value
                    self._device_info_label.configure(
                        text=(
                            f"设备：{info['name']}  ({info['address']})\n"
                            f"信号：{info['rssi']} dBm"
                        )
                    )
                elif event == "status":
                    self._status_label.configure(text=str(value))
                elif event == "scan_results":
                    self._show_scan_results(value)
                elif event == "error":
                    self._status_label.configure(text=f"错误：{value}")
                    if not self._closing:
                        messagebox.showerror("连接失败", str(value), parent=self)
                elif event == "stopped" and not self._closing:
                    self._connect_button.configure(state=tk.NORMAL)
                    self._pause_button.configure(state=tk.DISABLED, text="暂停采样")
                    self._stop_button.configure(state=tk.DISABLED)
                    self._status_label.configure(text="已停止")
                    self._show_statistics()
        except queue.Empty:
            pass
        if not self._closing:
            self.after(30, self._process_events)

    def _record_multi_sample(self, address: str, name: str, bpm: int) -> None:
        if self._multi_sessions is None:
            return
        session = self._multi_sessions.get(address)
        if session is None:
            session = HeartRateSession(name, address, self._current_frequency())
            self._multi_sessions[address] = session
        session.add(time.monotonic() - self._multi_session_started, bpm)
        listed = sum(len(s.values) for s in self._multi_sessions.values())
        self._multi_status_label.configure(
            text=f"正在记录 {len(self._multi_sessions)} 台设备，共 {listed} 个样本"
        )

    def _current_frequency(self) -> float:
        try:
            return float(self._frequency_entry.get().strip())
        except ValueError:
            return DEFAULT_SAMPLE_FREQUENCY

    def _close(self) -> None:
        self._closing = True
        if self._monitor is not None:
            self._monitor.stop()
        self._floating_window.destroy()
        if self._statistics_window is not None and self._statistics_window.winfo_exists():
            self._statistics_window.destroy()
        try:
            self._save_config()
        except tk.TclError:
            pass
        self.destroy()

    @classmethod
    def _load_saved_addresses(cls) -> list[str]:
        try:
            payload = json.loads(cls._CONFIG_PATH.read_text(encoding="utf-8"))
        except (FileNotFoundError, json.JSONDecodeError, OSError):
            return []
        if isinstance(payload, dict):
            addresses = payload.get("addresses", [])
        elif isinstance(payload, list):
            addresses = payload  # legacy format: a plain list of MACs
        else:
            return []
        if not isinstance(addresses, list):
            return []
        return [
            address.upper()
            for address in addresses
            if isinstance(address, str) and MAC_ADDRESS_PATTERN.fullmatch(address)
        ]

    def _load_app_config(self) -> dict[str, object]:
        """Full persisted config: addresses, floating style and thresholds."""
        try:
            payload = json.loads(self._CONFIG_PATH.read_text(encoding="utf-8"))
        except (FileNotFoundError, json.JSONDecodeError, OSError):
            return {}
        return payload if isinstance(payload, dict) else {}

    def _save_config(self) -> None:
        payload = {
            "addresses": self._saved_addresses,
            "style": {
                "number_format": self._number_format_var.get(),
                "icon_style": self._icon_style_var.get(),
                "icon_size": self._icon_size_var.get(),
                "number_size": self._number_size_var.get(),
                "font_family": self._font_family_var.get(),
                "custom_icon_path": self._custom_icon_path,
                "icon_x": self._icon_x_var.get(),
                "icon_y": self._icon_y_var.get(),
                "number_x": self._number_x_var.get(),
                "number_y": self._number_y_var.get(),
                "heart_color": self._heart_color,
                "number_color": self._number_color,
                "background": self._floating_background,
                "background_opacity": self._background_opacity_var.get(),
                "content_opacity": self._content_opacity_var.get(),
                "show_chart": self._show_chart_var.get(),
                "show_extremes": self._show_extremes_var.get(),
                "beat_enabled": self._beat_enabled_var.get(),
            },
            "thresholds": {
                "low_bpm": self._low_bpm_var.get(),
                "high_bpm": self._high_bpm_var.get(),
            },
        }
        try:
            self._CONFIG_PATH.parent.mkdir(parents=True, exist_ok=True)
            self._CONFIG_PATH.write_text(
                json.dumps(payload, ensure_ascii=False, indent=2),
                encoding="utf-8",
            )
        except OSError as error:
            self._status_label.configure(text=f"无法保存配置：{error}")

    def _save_address(self, address: str) -> None:
        self._saved_addresses = [
            address,
            *[saved for saved in self._saved_addresses if saved != address],
        ][:20]
        self._address_combo.configure(values=self._saved_addresses)
        self._save_config()


if __name__ == "__main__":
    HeartRateWindow().mainloop()
