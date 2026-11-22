"""YTikDL Pro - YouTube / TikTok Downloader (yt-dlp) with a dark, rounded Tkinter UI.

- Paste a link (or use the built-in Browse YouTube / Browse TikTok window) to add
  videos to a download list. You can select several videos at once.
- Each video has its own quality (or MP3) and its own audio language (original or
  YouTube auto-dubbed tracks); selectors let you apply the same quality / language
  to every video at once.
- Videos are delivered as H.264 (MP4); other codecs are converted with FFmpeg.

Requirements:
    pip install -U yt-dlp pillow pywebview
    FFmpeg (with ffprobe) installed and available in the PATH
    (For a .exe with auto-py-to-exe, add "webview" in Hidden Imports.)
"""

import io
import os
import queue
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import tkinter as tk
import tkinter.font as tkfont
import urllib.request
from functools import lru_cache
from pathlib import Path
from tkinter import filedialog, messagebox, ttk
from urllib.parse import parse_qs, urlparse

try:
    import yt_dlp
except ImportError:
    yt_dlp = None

try:
    from PIL import Image, ImageChops, ImageDraw, ImageTk
except ImportError:
    Image = ImageChops = ImageDraw = ImageTk = None


class Cancelled(Exception):
    """Raised when the user cancels an operation."""


NO_WINDOW = getattr(subprocess, "CREATE_NO_WINDOW", 0)

UNSUPPORTED_MSG = "Only YouTube (videos, Shorts, lives) and TikTok videos are supported."
IDLE_MSG = "Paste a link or use Browse YouTube / Browse TikTok to add videos."

THEME = {
    "bg": "#0A0B0F",
    "surface": "#13151C",
    "surface_alt": "#1B1E28",
    "surface_hover": "#262A38",
    "border": "#2A2F3D",
    "text": "#F5F7FA",
    "muted": "#8F97A8",
    "yt_red": "#FF0033",
    "yt_red_hover": "#E0002D",
    "tt_cyan": "#25F4EE",
    "tt_pink": "#FE2C55",
    "ok": "#2EE59D",
    "warn": "#FFB020",
    "err": "#FF4D6D",
    "disabled_bg": "#222531",
    "disabled_fg": "#5E6678",
}
TONES = {"muted": THEME["muted"], "info": THEME["tt_cyan"], "ok": THEME["ok"],
         "warn": THEME["warn"], "err": THEME["err"]}

FONT = "Segoe UI"

LOGO_FILE = "logo.png"
LOGO_HEIGHT = 40

RADIUS_BTN = 12
RADIUS_FIELD = 12
RADIUS_CARD = 18

H264 = "[vcodec~='^(avc|h264)']"

# Option = (label, yt-dlp format, audio_only, height)   height: 0 = best, None = audio
BEST_VIDEO = (
    "Best available (H.264, MP4)",
    f"bestvideo{H264}+bestaudio[acodec^=mp4a]/bestvideo{H264}+bestaudio/"
    f"best{H264}/bestvideo+bestaudio/best",
    False,
    0,
)
AUDIO_MP3 = ("MP3 - 192 kbps (audio only)", "bestaudio/best", True, None)
DEFAULT_OPTIONS = [BEST_VIDEO, AUDIO_MP3]

# Quality choices for the "apply to all" selector
APPLY_ALL = [
    ("Best available (MP4)", "best"),
    ("1080p (or closest)", 1080),
    ("720p (or closest)", 720),
    ("480p (or closest)", 480),
    ("360p (or closest)", 360),
    ("MP3 audio only", "audio"),
]

# Audio language: (label, language code or None for the default/original track)
DEFAULT_LANG = ("Original audio", None)

LANG_NAMES = {
    "en": "English", "fr": "Français", "es": "Español", "de": "Deutsch",
    "it": "Italiano", "pt": "Português", "ru": "Русский", "ja": "日本語",
    "ko": "한국어", "zh": "中文", "ar": "العربية", "hi": "हिन्दी",
    "tr": "Türkçe", "nl": "Nederlands", "pl": "Polski", "id": "Indonesia",
    "vi": "Tiếng Việt", "th": "ไทย", "uk": "Українська", "sv": "Svenska",
    "cs": "Čeština", "ro": "Română", "el": "Ελληνικά", "he": "עברית",
    "fa": "فارسی", "bn": "বাংলা", "ms": "Melayu", "fil": "Filipino",
}


# ---------- Helpers ----------
def lang_name(code: str) -> str:
    base = code.split("-")[0].lower()
    return LANG_NAMES.get(base, code)


def apply_language(fmt: str, lang) -> str:
    """Prefer the audio track of the chosen language, fall back to the default format."""
    if not lang:
        return fmt
    return fmt.replace("bestaudio", f"bestaudio[language={lang}]") + "/" + fmt


def is_tiktok(url: str) -> bool:
    host = (urlparse(url).hostname or "").lower()
    return host == "tiktok.com" or host.endswith(".tiktok.com")


def is_youtube(url: str) -> bool:
    host = (urlparse(url).hostname or "").lower()
    return host == "youtu.be" or host == "youtube.com" or host.endswith(".youtube.com")


def is_supported(url: str) -> bool:
    """True only for YouTube video/Shorts/live links and TikTok video links."""
    try:
        u = urlparse(url)
    except ValueError:
        return False
    if u.scheme not in ("http", "https"):
        return False
    host = (u.hostname or "").lower()
    path = u.path or ""

    if host == "youtu.be":
        return len(path.strip("/")) > 0
    if host == "youtube.com" or host.endswith(".youtube.com"):
        if path == "/watch":
            return bool(parse_qs(u.query).get("v"))
        for prefix in ("/shorts/", "/live/", "/embed/", "/v/"):
            if path.startswith(prefix) and len(path) > len(prefix):
                return True
        if path.endswith("/live") and path.startswith(("/@", "/channel/", "/c/", "/user/")):
            return True
        return False

    if host == "tiktok.com" or host.endswith(".tiktok.com"):
        if host in ("vm.tiktok.com", "vt.tiktok.com"):
            return len(path.strip("/")) > 0
        if path.startswith("/t/") and len(path) > 3:
            return True
        return "/video/" in path
    return False


def clean_video_url(url: str) -> str:
    """Keep only what identifies the video (v= for YouTube watch links)."""
    u = urlparse(url)
    host = (u.hostname or "").lower()
    if (host == "youtube.com" or host.endswith(".youtube.com")) and u.path == "/watch":
        v = (parse_qs(u.query).get("v") or [""])[0]
        return f"https://www.youtube.com/watch?v={v}" if v else url
    return f"{u.scheme}://{u.netloc}{u.path}"


def is_h264(vcodec: str) -> bool:
    return vcodec.lower().startswith(("avc", "h264"))


def build_format(height: int, fps: int, h264_only: bool) -> str:
    fps_filter = f"[fps>={fps - 1}][fps<={fps + 1}]" if fps else ""
    base = f"[height={height}]{fps_filter}"
    if h264_only:
        return (
            f"bestvideo{base}{H264}+bestaudio[acodec^=mp4a]/"
            f"bestvideo{base}{H264}+bestaudio/"
            f"best{base}{H264}/bestvideo{base}+bestaudio/best{base}"
        )
    return f"bestvideo{base}+bestaudio/best{base}"


def pick_option(options, target):
    """Index of the option matching target: 'best', 'audio' or a max height."""
    audio = next((i for i, o in enumerate(options) if o[2]), 0)
    if target == "audio":
        return audio
    if target == "best":
        return 0
    vids = [(i, o[3]) for i, o in enumerate(options) if not o[2] and o[3]]
    if not vids:
        return 0
    below = [v for v in vids if v[1] <= target]
    if below:
        return max(below, key=lambda v: v[1])[0]
    return min(vids, key=lambda v: v[1])[0]


def hint_for(error: str, default: str) -> str:
    low = error.lower()
    if "will begin" in low or "premieres in" in low or "upcoming" in low:
        return "This live stream or premiere has not started yet."
    if any(k in low for k in ("sign in", "log in", "login", "private", "members-only", "age")):
        return "This video may be private, age-restricted or reserved for members."
    return default


def human_size(n: float) -> str:
    mb = n / (1024 * 1024)
    return f"{mb / 1024:.2f} GB" if mb >= 1024 else f"{mb:.1f} MB"


def human_duration(seconds) -> str:
    if not seconds:
        return ""
    seconds = int(seconds)
    h, rem = divmod(seconds, 3600)
    m, s = divmod(rem, 60)
    return f"{h}:{m:02d}:{s:02d}" if h else f"{m}:{s:02d}"


def shorten(text: str, n: int = 80) -> str:
    return text if len(text) <= n else text[: n - 3].rstrip() + "..."


def app_dirs():
    dirs = []
    if getattr(sys, "frozen", False):
        dirs.append(Path(sys.executable).resolve().parent)
    if getattr(sys, "_MEIPASS", None):
        dirs.append(Path(sys._MEIPASS))
    dirs += [Path(__file__).resolve().parent, Path.cwd()]
    return dirs


def find_tool(name: str):
    exe = name + (".exe" if sys.platform.startswith("win") else "")
    for d in app_dirs():
        candidate = d / exe
        if candidate.is_file():
            return str(candidate)
    return shutil.which(name)


def open_folder(path: str):
    try:
        if sys.platform.startswith("win"):
            os.startfile(path)  # type: ignore[attr-defined]
        elif sys.platform == "darwin":
            subprocess.Popen(["open", path])
        else:
            subprocess.Popen(["xdg-open", path])
    except Exception as e:
        messagebox.showerror("Open folder", str(e))


# ---------- Mini browser (YouTube / TikTok only, multi-select) ----------
BROWSER_HOMES = {"yt": "https://www.youtube.com/", "tt": "https://www.tiktok.com/"}

BROWSER_JS = r"""
(function () {
  if (window.__ytikdl) return;
  window.__ytikdl = true;
  var HOME = "__HOME__";
  var sel = {};
  var lastNav = "";

  function hostOk(h) {
    h = (h || '').toLowerCase();
    return h === 'youtu.be' || /(^|\.)(youtube\.com|tiktok\.com)$/.test(h);
  }
  function toVideo(href) {
    try {
      var u = new URL(href, location.href), h = u.hostname.toLowerCase(), p = u.pathname;
      if (h === 'youtu.be') return p.length > 1 ? u.href : null;
      if (/(^|\.)youtube\.com$/.test(h)) {
        if (p === '/watch' && u.searchParams.get('v')) return u.href;
        if (/^\/(shorts|live)\/[^\/]+/.test(p)) return u.href;
        return null;
      }
      if (/(^|\.)tiktok\.com$/.test(h)) {
        if (p.indexOf('/video/') > -1) return u.href;
        if (/^\/t\/./.test(p)) return u.href;
        if ((h === 'vm.tiktok.com' || h === 'vt.tiktok.com') && p.length > 1) return u.href;
      }
    } catch (e) {}
    return null;
  }
  function keyOf(href) {
    try {
      var u = new URL(href, location.href), h = u.hostname.toLowerCase();
      if (/(^|\.)youtube\.com$/.test(h) && u.pathname === '/watch')
        return 'https://www.youtube.com/watch?v=' + u.searchParams.get('v');
      return u.protocol + '//' + u.host + u.pathname;
    } catch (e) { return ''; }
  }
  function call(fn, args, cb) {
    var a = window.pywebview && window.pywebview.api;
    if (a && a[fn]) a[fn].apply(a, args).then(cb);
    else setTimeout(function () { call(fn, args, cb); }, 150);
  }

  // ----- bottom bar -----
  var bar = document.createElement('div');
  bar.style.cssText = 'position:fixed;left:50%;bottom:18px;transform:translateX(-50%);' +
    'z-index:2147483647;display:flex;gap:14px;align-items:center;padding:10px 14px;' +
    'background:#13151C;border:1px solid #2A2F3D;border-radius:14px;color:#F5F7FA;' +
    'font:600 13px Segoe UI,Arial,sans-serif;box-shadow:0 6px 24px rgba(0,0,0,.55)';
  var info = document.createElement('span');
  var btn = document.createElement('button');
  btn.style.cssText = 'border:0;border-radius:10px;padding:9px 18px;cursor:pointer;' +
    'background:#2EE59D;color:#04191A;font:700 13px Segoe UI,Arial,sans-serif';
  btn.onclick = function () { call('finish', [], function () {}); };
  bar.appendChild(info); bar.appendChild(btn);
  (function mount() {
    if (document.body) document.body.appendChild(bar); else setTimeout(mount, 100);
  })();

  function render(urls) {
    sel = {};
    for (var i = 0; i < urls.length; i++) sel[urls[i]] = true;
    var n = urls.length;
    info.textContent = n ? (n + ' selected') : 'Click videos to select them';
    btn.textContent = 'Ready to download (' + n + ')';
    btn.disabled = !n;
    btn.style.opacity = n ? '1' : '.45';
    btn.style.cursor = n ? 'pointer' : 'default';
    mark();
  }
  function mark() {
    var links = document.querySelectorAll('a[href]');
    for (var i = 0; i < links.length; i++) {
      var a = links[i];
      if (!toVideo(a.href)) continue;
      if (sel[keyOf(a.href)]) {
        a.style.outline = '3px solid #25F4EE'; a.style.outlineOffset = '-3px';
        a.setAttribute('data-ytikdl', '1');
      } else if (a.getAttribute('data-ytikdl')) {
        a.style.outline = ''; a.removeAttribute('data-ytikdl');
      }
    }
  }
  function toggle(url, force) {
    call('toggle', [url, !!force], function (r) { render(r.urls); });
  }

  function onClick(e) {
    if (bar.contains(e.target)) return;
    var a = e.target && e.target.closest ? e.target.closest('a[href]') : null;
    if (!a) return;
    var v = toVideo(a.href);
    var block = false;
    if (v) { block = true; toggle(v, false); }
    else {
      try { if (!hostOk(new URL(a.href, location.href).hostname)) block = true; } catch (err) {}
    }
    if (block) { e.preventDefault(); e.stopPropagation(); e.stopImmediatePropagation(); }
  }
  document.addEventListener('click', onClick, true);
  document.addEventListener('auxclick', onClick, true);

  call('get', [], render);

  // Safety net: SPA navigation to a video page or to another domain
  setInterval(function () {
    if (!hostOk(location.hostname)) { location.replace(HOME); return; }
    var v = toVideo(location.href);
    if (v && lastNav !== v) {
      lastNav = v;
      var vids = document.querySelectorAll('video');
      for (var i = 0; i < vids.length; i++) { try { vids[i].pause(); } catch (e) {} }
      toggle(v, true);
      history.back();
    }
    mark();
  }, 500);
})();
"""


class BrowserApi:
    """API exposed to the page JavaScript (pywebview)."""

    def __init__(self, out_path):
        self._out = out_path
        self._window = None
        self._urls = []

    def toggle(self, url, force_on=False):
        clean = clean_video_url(str(url))
        if not is_supported(clean):
            return {"urls": list(self._urls), "key": "", "on": False}
        if clean in self._urls:
            if not force_on:
                self._urls.remove(clean)
        else:
            self._urls.append(clean)
        return {"urls": list(self._urls), "key": clean, "on": clean in self._urls}

    def get(self):
        return list(self._urls)

    def finish(self):
        if self._urls:
            Path(self._out).write_text("\n".join(self._urls), encoding="utf-8")
        if self._window is not None:
            self._window.destroy()
        return True


def run_browser(platform: str, out_path: str):
    """Runs in a separate process: opens the mini browser."""
    try:
        import webview
    except ImportError:
        sys.exit(2)
    home = BROWSER_HOMES.get(platform, BROWSER_HOMES["yt"])
    title = "Browse TikTok" if platform == "tt" else "Browse YouTube"
    api = BrowserApi(out_path)
    window = webview.create_window(title, home, js_api=api, width=1100, height=760,
                                   background_color="#0A0B0F")
    api._window = window
    js = BROWSER_JS.replace("__HOME__", home)
    window.events.loaded += lambda: window.evaluate_js(js)
    webview.start()


class YtdlpLogger:
    """yt-dlp logger that forwards messages to the UI."""

    def __init__(self, send):
        self.send = send

    def debug(self, msg):
        if msg.startswith("[debug]") or (msg.startswith("[download]") and "%" in msg):
            return
        self.send(msg)

    def info(self, msg):
        self.send(msg)

    def warning(self, msg):
        self.send(f"[!] {msg}")

    def error(self, msg):
        self.send(f"[X] {msg}")


# ---------- Rounded drawing ----------
@lru_cache(maxsize=512)
def _rr_photo(w, h, r, fill, outline, bw):
    s = 4
    img = Image.new("RGBA", (w * s, h * s), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)
    if outline:
        d.rounded_rectangle((0, 0, w * s - 1, h * s - 1), radius=r * s, fill=outline)
        d.rounded_rectangle(
            (bw * s, bw * s, w * s - 1 - bw * s, h * s - 1 - bw * s),
            radius=max(r - bw, 0) * s,
            fill=fill,
        )
    else:
        d.rounded_rectangle((0, 0, w * s - 1, h * s - 1), radius=r * s, fill=fill)
    img = img.resize((w, h), Image.LANCZOS)
    return ImageTk.PhotoImage(img)


def draw_round(canvas, w, h, r, fill, outline=None, bw=1, tag="bg", lower=True):
    canvas.delete(tag)
    if w < 2 or h < 2:
        return
    r = max(0, min(r, w // 2, h // 2))
    if Image is not None:
        photo = _rr_photo(w, h, r, fill, outline, bw)
        if not hasattr(canvas, "_photos"):
            canvas._photos = {}
        canvas._photos[tag] = photo
        canvas.create_image(0, 0, anchor="nw", image=photo, tag=tag)
    else:
        pts = [r, 0, w - r, 0, w, 0, w, r, w, h - r, w, h, w - r, h,
               r, h, 0, h, 0, h - r, 0, r, 0, 0]
        canvas.create_polygon(pts, smooth=True, fill=fill, outline=outline or fill,
                              width=bw if outline else 0, tag=tag)
    if lower:
        canvas.tag_lower(tag)


def _merge(cnf, kw):
    d = dict(cnf) if isinstance(cnf, dict) else {}
    d.update(kw)
    return d


# ---------- Rounded widgets ----------
def _bstyle(bg, fg, **kw):
    d = dict(bg=bg, fg=fg, hover=None, hover_fg=None, border=None, hover_border=None,
             font=(FONT, 9, "bold"), padx=14, pady=8, pill=False)
    d.update(kw)
    return d


T = THEME
BTN_STYLES = {
    "primary": _bstyle(T["yt_red"], "#FFFFFF", hover=T["yt_red_hover"],
                       font=(FONT, 11, "bold"), padx=26, pady=11),
    "secondary": _bstyle(T["surface_alt"], T["text"], hover=T["surface_hover"],
                         border=T["border"]),
    "small": _bstyle(T["surface_alt"], T["text"], hover=T["surface_hover"],
                     border=T["border"], padx=10, pady=5),
    "cancel": _bstyle(T["surface_alt"], T["tt_pink"], hover=T["tt_pink"],
                      hover_fg="#FFFFFF", border=T["tt_pink"], padx=16),
    "link": _bstyle(T["bg"], T["tt_cyan"], hover_fg="#FFFFFF", padx=4, pady=4),
    "chipoff": _bstyle(T["surface_alt"], T["disabled_fg"], font=(FONT, 8, "bold"),
                       padx=14, pady=5, pill=True),
    "chipyt": _bstyle(T["yt_red"], "#FFFFFF", font=(FONT, 8, "bold"),
                      padx=14, pady=5, pill=True),
    "chiptt": _bstyle(T["tt_cyan"], "#04191A", font=(FONT, 8, "bold"),
                      padx=14, pady=5, pill=True),
    "browse_yt": _bstyle(T["yt_red"], "#FFFFFF", hover=T["yt_red_hover"], padx=16),
    "browse_tt": _bstyle(T["tt_cyan"], "#04191A", hover="#1CD9D3", padx=16),
}


class RoundedButton(tk.Canvas):
    """Rounded button. Supports config(state=, text=, style=, command=)."""

    def __init__(self, master, text="", command=None, style="secondary",
                 state="normal", parent_bg=None):
        super().__init__(master, width=10, height=10, bg=parent_bg or THEME["surface"],
                         highlightthickness=0, bd=0)
        self._b_text = text
        self._b_cmd = command
        self._b_style = style
        self._b_state = state
        self._b_hover = False
        self._b_fit()
        self.bind("<Configure>", self._b_draw)
        self.bind("<Enter>", lambda e: self._b_set_hover(True))
        self.bind("<Leave>", lambda e: self._b_set_hover(False))
        self.bind("<ButtonRelease-1>", self._b_release)

    def _b_fit(self):
        st = BTN_STYLES[self._b_style]
        font = tkfont.Font(font=st["font"])
        w = font.measure(self._b_text) + 2 * st["padx"]
        h = font.metrics("linespace") + 2 * st["pady"]
        tk.Canvas.configure(self, width=w, height=h)

    def _b_set_hover(self, value):
        self._b_hover = value
        self._b_draw()

    def _b_release(self, e):
        if (self._b_state != "disabled" and self._b_cmd
                and 0 <= e.x <= self.winfo_width() and 0 <= e.y <= self.winfo_height()):
            self._b_cmd()

    def _b_draw(self, _e=None):
        w, h = self.winfo_width(), self.winfo_height()
        if w < 4 or h < 4:
            return
        st = BTN_STYLES[self._b_style]
        active = self._b_state != "disabled"
        hovered = self._b_hover and active and self._b_cmd is not None
        if not active:
            fill, fg = THEME["disabled_bg"], THEME["disabled_fg"]
            border = THEME["border"] if st["border"] else None
        elif hovered:
            fill = st["hover"] or st["bg"]
            fg = st["hover_fg"] or st["fg"]
            border = st["hover_border"] or st["border"]
            if st["hover"] and st["border"] == st["bg"]:
                border = fill
        else:
            fill, fg, border = st["bg"], st["fg"], st["border"]
        self.delete("all")
        radius = h // 2 if st["pill"] else RADIUS_BTN
        draw_round(self, w, h, radius, fill, border)
        self.create_text(w // 2, h // 2, text=self._b_text, fill=fg, font=st["font"])
        tk.Canvas.configure(self, cursor="hand2" if (active and self._b_cmd) else "arrow")

    def configure(self, cnf=None, **kw):
        kw = _merge(cnf, kw)
        refit = redraw = False
        if "state" in kw:
            self._b_state = kw.pop("state")
            redraw = True
        if "text" in kw:
            self._b_text = kw.pop("text")
            refit = redraw = True
        if "style" in kw:
            self._b_style = kw.pop("style")
            refit = redraw = True
        if "command" in kw:
            self._b_cmd = kw.pop("command")
            redraw = True
        if kw:
            tk.Canvas.configure(self, **kw)
        if refit:
            self._b_fit()
        if redraw:
            self._b_draw()

    config = configure


class RoundedEntry(tk.Canvas):
    """Rounded text field (wraps a tk.Entry)."""

    HEIGHT = 42

    def __init__(self, master, textvariable=None, parent_bg=None):
        super().__init__(master, width=100, height=self.HEIGHT,
                         bg=parent_bg or THEME["surface"], highlightthickness=0, bd=0)
        self._e_state = "normal"
        self._e_focus = False
        self.entry = tk.Entry(
            self, textvariable=textvariable, bg=THEME["surface_alt"], fg=THEME["text"],
            insertbackground=THEME["tt_cyan"], relief="flat", bd=0, highlightthickness=0,
            font=(FONT, 10), disabledbackground=THEME["disabled_bg"],
            disabledforeground=THEME["disabled_fg"],
            selectbackground=THEME["yt_red"], selectforeground="#FFFFFF",
        )
        self._e_win = self.create_window(14, self.HEIGHT // 2, window=self.entry, anchor="w")
        self.bind("<Configure>", self._e_draw)
        self.bind("<ButtonPress-1>", lambda e: self.entry.focus_set())
        self.entry.bind("<FocusIn>", lambda e: self._e_set_focus(True), add="+")
        self.entry.bind("<FocusOut>", lambda e: self._e_set_focus(False), add="+")

    def _e_set_focus(self, value):
        self._e_focus = value
        self._e_draw()

    def _e_draw(self, _e=None):
        w, h = self.winfo_width(), self.winfo_height()
        if w < 4 or h < 4:
            return
        disabled = self._e_state == "disabled"
        fill = THEME["disabled_bg"] if disabled else THEME["surface_alt"]
        border = THEME["tt_cyan"] if (self._e_focus and not disabled) else THEME["border"]
        draw_round(self, w, h, RADIUS_FIELD, fill, border)
        self.entry.configure(bg=fill)
        self.coords(self._e_win, 14, h // 2)
        self.itemconfigure(self._e_win, width=max(w - 28, 10))

    def focus_set(self):
        self.entry.focus_set()

    def configure(self, cnf=None, **kw):
        kw = _merge(cnf, kw)
        if "state" in kw:
            self._e_state = kw.pop("state")
            self.entry.configure(state=self._e_state)
            self._e_draw()
        if kw:
            tk.Canvas.configure(self, **kw)

    config = configure


class RoundedSelect(tk.Canvas):
    """Rounded drop-down list (replacement for ttk.Combobox)."""

    HEIGHT = 42

    def __init__(self, master, textvariable=None, parent_bg=None, height=None):
        super().__init__(master, width=100, height=height or self.HEIGHT,
                         bg=parent_bg or THEME["surface"], highlightthickness=0, bd=0)
        self._s_var = textvariable
        self._s_values = []
        self._s_index = -1
        self._s_state = "readonly"
        self._s_popup = None
        self._s_closed_at = 0.0
        self.bind("<Configure>", self._s_draw)
        self.bind("<ButtonPress-1>", self._s_click)

    def current(self, index=None):
        if index is None:
            return self._s_index
        if 0 <= index < len(self._s_values):
            self._s_index = index
            if self._s_var is not None:
                self._s_var.set(self._s_values[index])
        self._s_draw()

    def get(self):
        return self._s_values[self._s_index] if 0 <= self._s_index < len(self._s_values) else ""

    def __setitem__(self, key, value):
        if key == "values":
            self._s_values = list(value)
            self._s_index = -1
            self._s_draw()
        else:
            self.configure({key: value})

    def __getitem__(self, key):
        if key == "values":
            return tuple(self._s_values)
        return self.cget(key)

    def configure(self, cnf=None, **kw):
        kw = _merge(cnf, kw)
        if "state" in kw:
            self._s_state = kw.pop("state")
            self._s_draw()
        if "values" in kw:
            self["values"] = kw.pop("values")
        if kw:
            tk.Canvas.configure(self, **kw)

    config = configure

    def _s_draw(self, _e=None):
        w, h = self.winfo_width(), self.winfo_height()
        if w < 4 or h < 4:
            return
        disabled = self._s_state == "disabled"
        fill = THEME["disabled_bg"] if disabled else THEME["surface_alt"]
        border = THEME["tt_cyan"] if self._s_popup else THEME["border"]
        self.delete("all")
        draw_round(self, w, h, RADIUS_FIELD, fill, border)

        # FIX: the old loop re-added "..." on every pass, so the text grew back
        # and the loop never ended (UI freeze). Cut first, add "..." only once.
        text = self.get()
        font = tkfont.Font(font=(FONT, 10))
        limit = w - 56
        if font.measure(text) > limit:
            while len(text) > 1 and font.measure(text + "...") > limit:
                text = text[:-1]
            text = text.rstrip() + "..."
        fg = THEME["disabled_fg"] if disabled else THEME["text"]
        self.create_text(14, h // 2, text=text, anchor="w", fill=fg, font=(FONT, 10))

        cx, cy = w - 22, h // 2
        col = THEME["disabled_fg"] if disabled else THEME["tt_cyan"]
        self.create_line(cx - 5, cy - 2, cx, cy + 3, cx + 5, cy - 2, fill=col, width=2,
                         capstyle="round", joinstyle="round")
        tk.Canvas.configure(self, cursor="arrow" if disabled else "hand2")

    def _s_click(self, _e):
        if self._s_popup is not None:
            self._s_close()
            return
        if self._s_state == "disabled" or not self._s_values:
            return
        if time.time() - self._s_closed_at < 0.2:
            return
        self._s_open()

    def _s_open(self):
        top = tk.Toplevel(self)
        top.overrideredirect(True)
        top.configure(bg=THEME["tt_cyan"])
        lb = tk.Listbox(
            top, bg=THEME["surface_alt"], fg=THEME["text"],
            selectbackground=THEME["yt_red"], selectforeground="#FFFFFF",
            relief="flat", bd=0, highlightthickness=0, activestyle="none",
            font=(FONT, 10), height=min(len(self._s_values), 8), exportselection=False,
        )
        for v in self._s_values:
            lb.insert("end", "  " + v)
        lb.pack(padx=1, pady=1, fill="both", expand=True)
        if self._s_index >= 0:
            lb.selection_set(self._s_index)
            lb.see(self._s_index)

        x, y = self.winfo_rootx(), self.winfo_rooty() + self.winfo_height() + 4
        top.update_idletasks()
        top.geometry(f"{self.winfo_width()}x{top.winfo_reqheight()}+{x}+{y}")
        self._s_popup = top

        def pick_mouse(e):
            self._s_pick(lb.nearest(e.y))

        def pick_key(_e):
            sel = lb.curselection()
            if sel:
                self._s_pick(sel[0])

        def hover(e):
            lb.selection_clear(0, "end")
            lb.selection_set(lb.nearest(e.y))

        lb.bind("<ButtonRelease-1>", pick_mouse)
        lb.bind("<Return>", pick_key)
        lb.bind("<Motion>", hover)

        def wheel(e):
            delta = getattr(e, "delta", 0)
            if getattr(e, "num", None) == 4:
                delta = 120
            elif getattr(e, "num", None) == 5:
                delta = -120
            if delta:
                step = int(-delta / 120) if abs(delta) >= 120 else (-1 if delta > 0 else 1)
                lb.yview_scroll(step, "units")
                hover_idx = lb.nearest(e.y) if hasattr(e, "y") else None
                if hover_idx is not None:
                    lb.selection_clear(0, "end")
                    lb.selection_set(hover_idx)
            return "break"  # stop the event: the page must not scroll

        lb.bind("<MouseWheel>", wheel)
        lb.bind("<Button-4>", wheel)
        lb.bind("<Button-5>", wheel)
        lb.bind("<Escape>", lambda e: self._s_close())
        lb.bind("<FocusOut>", lambda e: self._s_close())
        lb.focus_force()
        self._s_draw()

    def _s_close(self):
        if self._s_popup is not None:
            popup, self._s_popup = self._s_popup, None
            popup.destroy()
            self._s_closed_at = time.time()
            self._s_draw()

    def _s_pick(self, index):
        self.current(index)
        self._s_close()
        self.event_generate("<<ComboboxSelected>>")


class RoundedProgress(tk.Canvas):
    """Rounded (pill) progress bar. Use .set(0-100)."""

    def __init__(self, master, parent_bg=None, height=10):
        super().__init__(master, width=100, height=height,
                         bg=parent_bg or THEME["surface"], highlightthickness=0, bd=0)
        self._p_val = 0.0
        self.bind("<Configure>", self._p_draw)

    def set(self, value):
        self._p_val = max(0.0, min(100.0, float(value)))
        self._p_draw()

    def _p_draw(self, _e=None):
        w, h = self.winfo_width(), self.winfo_height()
        if w < 4 or h < 4:
            return
        self.delete("all")
        draw_round(self, w, h, h // 2, THEME["surface_alt"], None, tag="bg")
        fw = int(w * self._p_val / 100)
        if fw > 0:
            draw_round(self, max(fw, h), h, h // 2, THEME["tt_cyan"], None,
                       tag="fg", lower=False)


class ThumbBox(tk.Canvas):
    """Rounded container for a video thumbnail."""

    def __init__(self, master, width, height, parent_bg=None):
        super().__init__(master, width=width, height=height,
                         bg=parent_bg or THEME["surface"], highlightthickness=0, bd=0)
        self._t_text = "Loading..."
        self._t_photo = None
        self.bind("<Configure>", self._t_draw)

    def show_text(self, text):
        self._t_photo = None
        self._t_text = text
        self._t_draw()

    def show_image(self, photo):
        self._t_photo = photo
        self._t_draw()

    def _t_draw(self, _e=None):
        w, h = self.winfo_width(), self.winfo_height()
        if w < 4 or h < 4:
            return
        self.delete("all")
        draw_round(self, w, h, 10, THEME["surface_alt"], THEME["border"])
        if self._t_photo is not None:
            self.create_image(w // 2, h // 2, image=self._t_photo)
        else:
            self.create_text(w // 2, h // 2, text=self._t_text, fill=THEME["disabled_fg"],
                             font=(FONT, 8))


class RoundCard(tk.Canvas):
    """Rounded card; put child widgets inside `.body`."""

    def __init__(self, master, parent_bg=None, pad=16):
        super().__init__(master, height=10, bg=parent_bg or THEME["bg"],
                         highlightthickness=0, bd=0)
        self._c_pad = pad
        self._c_height = 10
        self.body = tk.Frame(self, bg=THEME["surface"])
        self._c_win = self.create_window(pad, pad, window=self.body, anchor="nw")
        self.bind("<Configure>", self._c_on_canvas)
        self.body.bind("<Configure>", self._c_sync)
        self.after_idle(self._c_sync)

    def _c_on_canvas(self, e):
        self.itemconfigure(self._c_win, width=max(e.width - 2 * self._c_pad, 1))
        draw_round(self, e.width, e.height, RADIUS_CARD, THEME["surface"], THEME["border"])
        self._c_sync()

    def _c_sync(self, _e=None):
        need = self.body.winfo_reqheight() + 2 * self._c_pad
        if need > 2 * self._c_pad and need != self._c_height:
            self._c_height = need
            tk.Canvas.configure(self, height=need)


# ---------- Application ----------
class App(tk.Tk):
    W = 860
    H_COLLAPSED = 900
    ROW_THUMB_W = 112
    ROW_THUMB_H = 63

    def __init__(self):
        super().__init__()
        self.title("YTikDL Pro - YouTube & TikTok Downloader")
        self.geometry(f"{self.W}x{self.H_COLLAPSED}")
        self.minsize(760, 520)
        self.configure(bg=THEME["bg"])

        # Always full screen: starts full screen and goes back to it if anything leaves it.
        # (No Escape shortcut. To close: the Quit button, or Alt+F4.)
        self.after_idle(self._go_fullscreen)
        self.bind("<Map>", lambda e: self.after(50, self._go_fullscreen) if e.widget is self else None)
        self.bind("<Configure>", lambda e: self.after(50, self._go_fullscreen) if e.widget is self else None, add="+")

        self.msgs: queue.Queue = queue.Queue()
        self.cancel_event = threading.Event()
        self.fetch_sem = threading.Semaphore(3)
        self.busy = False
        self.auto_fetch_job = None
        self.log_visible = False
        self.browser_proc = None
        self.browser_out = None

        self.items = []  # one dict per video in the list
        self.next_id = 0
        self.global_target = None  # last "apply to all" quality choice
        self.global_lang = None  # last "apply to all" language choice
        self.all_lang_codes = [None, "orig"]

        self.var_url = tk.StringVar()
        self.var_folder = tk.StringVar(value=str(Path.home() / "Downloads"))
        self.var_status = tk.StringVar(value=IDLE_MSG)
        self.var_percent = tk.StringVar(value="0%")
        self.var_stats = tk.StringVar(value="")

        self._setup_styles()
        self._build()
        self._update_chips()
        self._refresh_buttons()
        self.var_url.trace_add("write", self._on_url_change)
        self.protocol("WM_DELETE_WINDOW", self._quit)
        self.after(100, self._process_messages)

    def _go_fullscreen(self):
        try:
            if not self.attributes("-fullscreen"):
                self.attributes("-fullscreen", True)
        except tk.TclError:
            pass

    # ---------- Styles ----------
    def _setup_styles(self):
        s = ttk.Style(self)
        s.theme_use("clam")
        t = THEME
        s.configure("App.TFrame", background=t["bg"])
        s.configure("Inner.TFrame", background=t["surface"])
        s.configure("Title.TLabel", background=t["bg"], foreground=t["text"],
                    font=(FONT, 20, "bold"))
        s.configure("Subtitle.TLabel", background=t["bg"], foreground=t["muted"],
                    font=(FONT, 9))
        s.configure("Section.TLabel", background=t["surface"], foreground=t["muted"],
                    font=(FONT, 8, "bold"))
        s.configure("RowTitle.TLabel", background=t["surface"], foreground=t["text"],
                    font=(FONT, 10, "bold"))
        s.configure("Meta.TLabel", background=t["surface"], foreground=t["muted"],
                    font=(FONT, 9))
        s.configure("State.TLabel", background=t["surface"], foreground=t["muted"],
                    font=(FONT, 9, "bold"))
        s.configure("Status.TLabel", background=t["surface"], foreground=t["muted"],
                    font=(FONT, 9))
        s.configure("Percent.TLabel", background=t["surface"], foreground=t["text"],
                    font=(FONT, 11, "bold"))
        s.configure("Stats.TLabel", background=t["surface"], foreground=t["muted"],
                    font=(FONT, 9))
        s.configure("Dark.Vertical.TScrollbar", background=t["surface_hover"],
                    troughcolor=t["surface_alt"], bordercolor=t["surface_alt"],
                    lightcolor=t["surface_hover"], darkcolor=t["surface_hover"],
                    arrowcolor=t["muted"], relief="flat")

    # ---------- UI ----------
    def _build(self):
        # Whole page is scrollable (scrollbar on the right + mouse wheel)
        page = tk.Canvas(self, bg=THEME["bg"], highlightthickness=0, bd=0)
        page_sb = ttk.Scrollbar(self, orient="vertical", command=page.yview,
                                style="Dark.Vertical.TScrollbar")
        page_sb.pack(side="right", fill="y")
        page.pack(side="left", fill="both", expand=True)
        page.configure(yscrollcommand=page_sb.set)
        root = ttk.Frame(page, style="App.TFrame", padding=(22, 18, 22, 18))
        self._page_win = page.create_window((0, 0), window=root, anchor="nw")
        root.bind("<Configure>", lambda e: page.configure(scrollregion=page.bbox("all")))
        page.bind("<Configure>", lambda e: page.itemconfigure(self._page_win, width=e.width))
        self.page_canvas = page
        self.bind_all("<MouseWheel>", self._on_page_wheel)
        root.columnconfigure(0, weight=1)

        # Header
        header = ttk.Frame(root, style="App.TFrame")
        header.grid(row=0, column=0, sticky="ew")
        header.columnconfigure(0, weight=1)

        titles = ttk.Frame(header, style="App.TFrame")
        titles.grid(row=0, column=0, sticky="w")
        title_row = ttk.Frame(titles, style="App.TFrame")
        title_row.pack(anchor="w")
        ttk.Label(title_row, text="YTikDL Pro", style="Title.TLabel").pack(side="left")
        self.logo_photo = self._load_logo()
        if self.logo_photo is not None:
            tk.Label(title_row, image=self.logo_photo, bg=THEME["bg"], bd=0).pack(
                side="left", padx=(12, 0))
        ttk.Label(titles, text="High-quality downloads  -  H.264 MP4 & MP3",
                  style="Subtitle.TLabel").pack(anchor="w")

        chips = ttk.Frame(header, style="App.TFrame")
        chips.grid(row=0, column=1, sticky="e")
        self.chip_yt = RoundedButton(chips, "YOUTUBE", style="chipoff", parent_bg=THEME["bg"])
        self.chip_yt.pack(side="left", padx=(0, 6))
        self.chip_tt = RoundedButton(chips, "TIKTOK", style="chipoff", parent_bg=THEME["bg"])
        self.chip_tt.pack(side="left")

        self.accent = tk.Canvas(root, height=3, bg=THEME["bg"], highlightthickness=0)
        self.accent.grid(row=1, column=0, sticky="ew", pady=(14, 16))
        self.accent.bind("<Configure>", self._draw_accent)

        # Card: link + browse buttons
        link_card = RoundCard(root)
        link_card.grid(row=2, column=0, sticky="ew")
        lb = link_card.body
        lb.columnconfigure(0, weight=1)
        ttk.Label(lb, text="ADD VIDEOS", style="Section.TLabel").grid(
            row=0, column=0, sticky="w", pady=(0, 8))
        self.entry_url = RoundedEntry(lb, textvariable=self.var_url)
        self.entry_url.grid(row=1, column=0, sticky="ew")
        self.entry_url.focus_set()
        self.btn_clear = RoundedButton(lb, "Clear", command=self._clear_url, style="secondary")
        self.btn_clear.grid(row=1, column=1, padx=(8, 0))
        self.btn_web_yt = RoundedButton(lb, "Browse YouTube", style="browse_yt",
                                        command=lambda: self._open_browser("yt"))
        self.btn_web_yt.grid(row=1, column=2, padx=(6, 0))
        self.btn_web_tt = RoundedButton(lb, "Browse TikTok", style="browse_tt",
                                        command=lambda: self._open_browser("tt"))
        self.btn_web_tt.grid(row=1, column=3, padx=(6, 0))

        # Card: video list
        queue_card = RoundCard(root)
        queue_card.grid(row=3, column=0, sticky="ew", pady=(14, 0))
        qb = queue_card.body
        qb.columnconfigure(0, weight=1)

        top = ttk.Frame(qb, style="Inner.TFrame")
        top.grid(row=0, column=0, sticky="ew", pady=(0, 10))
        top.columnconfigure(0, weight=1)
        ttk.Label(top, text="YOUR VIDEOS", style="Section.TLabel").grid(
            row=0, column=0, sticky="w")
        self.btn_clear_list = RoundedButton(top, "Clear list", command=self._clear_list,
                                            style="small")
        self.btn_clear_list.grid(row=0, column=1, sticky="e")

        bulk = ttk.Frame(top, style="Inner.TFrame")
        bulk.grid(row=1, column=0, columnspan=2, sticky="ew", pady=(10, 0))
        for c in range(2):
            bulk.columnconfigure(c, weight=1, uniform="bulk")

        def bulk_select(col, title, values, handler):
            ttk.Label(bulk, text=title, style="Meta.TLabel").grid(
                row=0, column=col, sticky="w", padx=(0 if col == 0 else 8, 0))
            sel = RoundedSelect(bulk, height=34)
            sel["values"] = values
            sel.current(0)
            sel.bind("<<ComboboxSelected>>", handler)
            sel.grid(row=1, column=col, sticky="ew", pady=(4, 0),
                     padx=(0 if col == 0 else 8, 0))
            return sel

        self.all_combo = bulk_select(0, "Same quality for all",
                                     ["Choose..."] + [a[0] for a in APPLY_ALL],
                                     self._on_all_selected)
        self.all_lang = bulk_select(1, "Same language for all",
                                    ["Choose...", "Original audio"],
                                    self._on_all_lang_selected)

        holder = ttk.Frame(qb, style="Inner.TFrame")
        holder.grid(row=1, column=0, sticky="ew")
        holder.columnconfigure(0, weight=1)
        self.list_canvas = tk.Canvas(holder, height=340, bg=THEME["surface"],
                                     highlightthickness=0, bd=0)
        self.list_canvas.grid(row=0, column=0, sticky="ew")
        sb = ttk.Scrollbar(holder, orient="vertical", command=self.list_canvas.yview,
                           style="Dark.Vertical.TScrollbar")
        sb.grid(row=0, column=1, sticky="ns")
        self.list_canvas.configure(yscrollcommand=sb.set)
        self.list_frame = tk.Frame(self.list_canvas, bg=THEME["surface"])
        self._list_win = self.list_canvas.create_window((0, 0), window=self.list_frame,
                                                        anchor="nw")
        self.list_frame.bind("<Configure>", lambda e: self.list_canvas.configure(
            scrollregion=self.list_canvas.bbox("all")))
        self.list_canvas.bind("<Configure>", lambda e: self.list_canvas.itemconfigure(
            self._list_win, width=e.width))
        self.list_canvas.bind("<Enter>", lambda e: self.bind_all("<MouseWheel>", self._on_wheel))
        self.list_canvas.bind("<Leave>", lambda e: self.bind_all("<MouseWheel>", self._on_page_wheel))
        self.lbl_empty = ttk.Label(
            self.list_frame, style="Meta.TLabel", justify="center",
            text="No videos yet.\nPaste a link above or use Browse YouTube / Browse TikTok.")
        self.lbl_empty.pack(pady=70, padx=40)

        # Card: folder + actions + progress
        work_card = RoundCard(root)
        work_card.grid(row=4, column=0, sticky="ew", pady=(14, 0))
        wb = work_card.body
        wb.columnconfigure(0, weight=1)

        ttk.Label(wb, text="SAVE TO", style="Section.TLabel").grid(
            row=0, column=0, sticky="w", pady=(0, 8))
        folder_row = ttk.Frame(wb, style="Inner.TFrame")
        folder_row.grid(row=1, column=0, sticky="ew")
        folder_row.columnconfigure(0, weight=1)
        self.entry_folder = RoundedEntry(folder_row, textvariable=self.var_folder)
        self.entry_folder.grid(row=0, column=0, sticky="ew")
        self.btn_browse = RoundedButton(folder_row, "Browse", command=self._browse,
                                        style="secondary")
        self.btn_browse.grid(row=0, column=1, padx=(8, 0))
        RoundedButton(folder_row, "Open", command=self._open_folder,
                      style="secondary").grid(row=0, column=2, padx=(6, 0))

        buttons = ttk.Frame(wb, style="Inner.TFrame")
        buttons.grid(row=2, column=0, sticky="ew", pady=(14, 0))
        buttons.columnconfigure(0, weight=1)
        self.btn_download = RoundedButton(buttons, "Download", command=self._start,
                                          style="primary")
        self.btn_download.grid(row=0, column=0, sticky="ew")
        self.btn_cancel = RoundedButton(buttons, "Cancel", command=self._cancel,
                                        state="disabled", style="cancel")
        self.btn_cancel.grid(row=0, column=1, padx=(8, 0))
        self.btn_quit = RoundedButton(buttons, "Quit", command=self._quit, style="secondary")
        self.btn_quit.grid(row=0, column=2, padx=(6, 0))

        prog = ttk.Frame(wb, style="Inner.TFrame")
        prog.grid(row=3, column=0, sticky="ew", pady=(14, 0))
        prog.columnconfigure(0, weight=1)
        self.progress = RoundedProgress(prog)
        self.progress.grid(row=0, column=0, sticky="ew")
        ttk.Label(prog, textvariable=self.var_percent, style="Percent.TLabel",
                  width=5, anchor="e").grid(row=0, column=1, padx=(10, 0))

        status_row = ttk.Frame(wb, style="Inner.TFrame")
        status_row.grid(row=4, column=0, sticky="ew", pady=(10, 0))
        status_row.columnconfigure(0, weight=1)
        self.lbl_status = ttk.Label(status_row, textvariable=self.var_status,
                                    style="Status.TLabel", wraplength=560, justify="left")
        self.lbl_status.grid(row=0, column=0, sticky="w")
        ttk.Label(status_row, textvariable=self.var_stats, style="Stats.TLabel").grid(
            row=0, column=1, sticky="e")

        # Details (collapsible log)
        self.btn_log = RoundedButton(root, "Show details  v", command=self._toggle_log,
                                     style="link", parent_bg=THEME["bg"])
        self.btn_log.grid(row=5, column=0, sticky="w", pady=(12, 0))

        self.log_card = RoundCard(root, pad=10)
        lgb = self.log_card.body
        lgb.columnconfigure(0, weight=1)
        self.log_box = tk.Text(
            lgb, height=8, state="disabled", wrap="word",
            bg=THEME["surface"], fg=THEME["text"], insertbackground=THEME["tt_cyan"],
            selectbackground=THEME["yt_red"], selectforeground="#FFFFFF",
            relief="flat", borderwidth=0, highlightthickness=0, padx=8, pady=6,
            font=("Consolas", 9),
        )
        self.log_box.grid(row=0, column=0, sticky="nsew")
        scroll = ttk.Scrollbar(lgb, command=self.log_box.yview,
                               style="Dark.Vertical.TScrollbar")
        scroll.grid(row=0, column=1, sticky="ns")
        self.log_box.configure(yscrollcommand=scroll.set)

        self.bind("<Configure>", self._on_resize, add="+")

    def _load_logo(self):
        folders = []
        if getattr(sys, "_MEIPASS", None):
            folders.append(Path(sys._MEIPASS))
        if getattr(sys, "frozen", False):
            folders.append(Path(sys.executable).resolve().parent)
        folders += [Path(__file__).resolve().parent, Path.cwd()]
        for folder in folders:
            path = folder / LOGO_FILE
            if not path.is_file():
                continue
            try:
                if Image is not None:
                    img = Image.open(path).convert("RGBA")
                    ratio = LOGO_HEIGHT / img.height
                    img = img.resize((max(1, round(img.width * ratio)), LOGO_HEIGHT),
                                     Image.LANCZOS)
                    photo = ImageTk.PhotoImage(img)
                    try:
                        self.iconphoto(True, photo)
                    except tk.TclError:
                        pass
                    return photo
                photo = tk.PhotoImage(file=str(path))
                factor = max(1, photo.height() // LOGO_HEIGHT)
                return photo.subsample(factor) if factor > 1 else photo
            except Exception:
                continue
        return None

    def _draw_accent(self, _event=None):
        c = self.accent
        c.delete("all")
        w = max(c.winfo_width(), 1)
        stops = [(0xFF, 0x00, 0x33), (0xFE, 0x2C, 0x55), (0x25, 0xF4, 0xEE)]
        for x in range(w):
            t = x / max(w - 1, 1) * (len(stops) - 1)
            i = min(int(t), len(stops) - 2)
            f = t - i
            a, b = stops[i], stops[i + 1]
            col = "#%02x%02x%02x" % tuple(int(a[k] + (b[k] - a[k]) * f) for k in range(3))
            c.create_line(x, 0, x, 3, fill=col)

    def _on_resize(self, event):
        if event.widget is self:
            self.lbl_status.configure(wraplength=max(event.width - 280, 240))

    def _on_wheel(self, e):
        self.list_canvas.yview_scroll(int(-e.delta / 120), "units")

    def _on_page_wheel(self, e):
        self.page_canvas.yview_scroll(int(-e.delta / 120) * 2, "units")

    def _toggle_log(self):
        self.log_visible = not self.log_visible
        if self.log_visible:
            self.log_card.grid(row=6, column=0, sticky="new", pady=(8, 0))
            self.btn_log.config(text="Hide details  ^")
            self.update_idletasks()
            self.page_canvas.yview_moveto(1.0)
        else:
            self.log_card.grid_remove()
            self.btn_log.config(text="Show details  v")

    # ---------- State helpers ----------
    def _set_status_tone(self, tone="muted"):
        self.lbl_status.configure(foreground=TONES.get(tone, THEME["muted"]))

    def _update_chips(self):
        yt = any(is_youtube(it["url"]) for it in self.items)
        tt = any(is_tiktok(it["url"]) for it in self.items)
        self.chip_yt.config(style="chipyt" if yt else "chipoff")
        self.chip_tt.config(style="chiptt" if tt else "chipoff")

    def _update_summary(self):
        if self.busy:
            return
        n = len(self.items)
        if not n:
            self._set_status_tone("muted")
            self.var_status.set(IDLE_MSG)
            return
        loading = sum(1 for it in self.items if it["status"] == "loading")
        ready = sum(1 for it in self.items if it["status"] == "ready")
        self._set_status_tone("info" if loading else "ok")
        if loading:
            self.var_status.set(f"{n} video(s) in the list - analyzing {loading}...")
        else:
            if any(it["status"] == "ready" and not self._all_chosen(it) for it in self.items):
                self.var_status.set(f"{n} video(s) in the list - choose quality and "
                                    "language to enable Download.")
            else:
                self.var_status.set(f"{n} video(s) in the list - {ready} ready to download.")

    def _all_chosen(self, it):
        """Quality and language chosen (a menu with no real choice counts).

        With a single video in the list, what is shown in its menus is enough.
        """
        if len(self.items) == 1:
            return True
        p = it["picked"]
        return p["q"] and (p["l"] or len(it["langs"]) <= 1)

    def _refresh_buttons(self):
        busy = self.busy
        ready = sum(1 for it in self.items if it["status"] == "ready")
        pending = any(it["status"] == "ready" and not self._all_chosen(it)
                      for it in self.items)
        self.btn_download.config(
            text=f"Download {ready} video(s)" if ready else "Download",
            state="disabled" if (busy or ready == 0 or pending) else "normal")
        self.btn_cancel.config(state="normal" if busy else "disabled")
        st = "disabled" if busy else "normal"
        self.entry_url.config(state=st)
        self.btn_clear.config(state=st)
        self.btn_web_yt.config(state="disabled" if (busy or self.browser_proc) else "normal")
        self.btn_web_tt.config(state="disabled" if (busy or self.browser_proc) else "normal")
        self.btn_browse.config(state=st)
        self.entry_folder.config(state=st)
        self.btn_clear_list.config(state="disabled" if (busy or not self.items) else "normal")
        self.all_combo.config(state="disabled" if (busy or ready == 0) else "readonly")
        self.all_lang.config(state="disabled" if (busy or ready == 0) else "readonly")
        for it in self.items:
            if "combo" in it:
                ok = (not busy) and it["status"] == "ready"
                it["combo"].config(state="readonly" if ok else "disabled")
            if "lang_combo" in it:
                ok = (not busy) and it["status"] == "ready" and len(it["langs"]) > 1
                it["lang_combo"].config(state="readonly" if ok else "disabled")
            if "btn_rm" in it:
                it["btn_rm"].config(state="disabled" if busy else "normal")

    def _log(self, text):
        self.log_box.config(state="normal")
        self.log_box.insert("end", text.rstrip() + "\n")
        self.log_box.see("end")
        self.log_box.config(state="disabled")

    def _set_progress(self, pct):
        self.progress.set(pct)
        self.var_percent.set(f"{int(pct)}%")

    def _browse(self):
        folder = filedialog.askdirectory(initialdir=self.var_folder.get() or ".")
        if folder:
            self.var_folder.set(folder)

    def _open_folder(self):
        folder = Path(self.var_folder.get().strip()).expanduser()
        if folder.exists():
            open_folder(str(folder))
        else:
            messagebox.showinfo("Open folder", "This folder does not exist yet.")

    def _clear_url(self):
        self.var_url.set("")
        self.entry_url.focus_set()

    # ---------- Mini browser ----------
    def _open_browser(self, platform):
        if self.busy or self.browser_proc is not None:
            return
        fd, out = tempfile.mkstemp(prefix="ytikdl_", suffix=".txt")
        os.close(fd)
        if getattr(sys, "frozen", False):
            cmd = [sys.executable]
        else:
            cmd = [sys.executable, str(Path(__file__).resolve())]
        cmd += ["--browse", platform, "--out", out]
        try:
            self.browser_proc = subprocess.Popen(cmd, creationflags=NO_WINDOW)
        except OSError as e:
            messagebox.showerror("Browser", str(e))
            return
        self.browser_out = out
        self._refresh_buttons()
        self.after(300, self._poll_browser)

    def _poll_browser(self):
        proc = self.browser_proc
        if proc is None:
            return
        if proc.poll() is None:
            self.after(300, self._poll_browser)
            return
        text = ""
        try:
            text = Path(self.browser_out).read_text(encoding="utf-8")
        except OSError:
            pass
        try:
            Path(self.browser_out).unlink(missing_ok=True)
        except OSError:
            pass
        code = proc.returncode
        self.browser_proc = None
        self.browser_out = None
        urls = [u.strip() for u in text.splitlines() if u.strip()]
        if urls:
            self._add_urls(urls)
            self.lift()
            self.focus_force()
        elif code == 2:
            messagebox.showerror("pywebview missing", "Install it with:\n\npip install pywebview")
        self._refresh_buttons()

    # ---------- URL entry ----------
    def _on_url_change(self, *_):
        if self.auto_fetch_job is not None:
            self.after_cancel(self.auto_fetch_job)
            self.auto_fetch_job = None
        if self.busy:
            return
        url = self.var_url.get().strip()
        looks_like_url = url.lower().startswith(("http://", "https://"))
        if looks_like_url and not is_supported(url):
            self._set_status_tone("err")
            self.var_status.set(UNSUPPORTED_MSG)
        elif looks_like_url:
            self._set_status_tone("info")
            self.var_status.set("Link detected...")
            self.auto_fetch_job = self.after(500, self._auto_add)
        else:
            self._update_summary()

    def _auto_add(self):
        self.auto_fetch_job = None
        url = self.var_url.get().strip()
        if self.busy or not is_supported(url):
            return
        self.var_url.set("")
        self._add_urls([url])

    # ---------- Video list ----------
    def _find(self, iid):
        for it in self.items:
            if it["id"] == iid:
                return it
        return None

    def _add_urls(self, urls):
        if yt_dlp is None:
            messagebox.showerror("yt-dlp missing", "Install it with:\n\npip install yt-dlp")
            return
        known = {it["url"] for it in self.items}
        added = 0
        for raw in urls:
            url = clean_video_url(raw)
            if not is_supported(url) or url in known:
                continue
            known.add(url)
            self.next_id += 1
            it = {"id": self.next_id, "url": url, "status": "loading", "title": url,
                  "options": list(DEFAULT_OPTIONS), "choice": 0,
                  "langs": [DEFAULT_LANG], "lang_choice": 0,
                  "picked": {"q": False, "l": False}}
            self.items.append(it)
            self._make_row(it)
            added += 1
            self._log(f"[+] Fetching: {url}")
            threading.Thread(target=self._fetch_worker, args=(url, it["id"]),
                             daemon=True).start()
        if added:
            self.lbl_empty.pack_forget()
            self.after(50, lambda: self.list_canvas.yview_moveto(1.0))
        self._update_chips()
        self._refresh_buttons()
        if added:
            self._update_summary()
        else:
            self._set_status_tone("warn")
            self.var_status.set("Those videos are already in the list.")

    def _make_row(self, it):
        card = RoundCard(self.list_frame, parent_bg=THEME["surface"], pad=8)
        card.pack(fill="x", pady=3, padx=(0, 6))
        b = card.body
        b.columnconfigure(1, weight=1)
        it["card"] = card

        it["thumb"] = ThumbBox(b, self.ROW_THUMB_W, self.ROW_THUMB_H)
        it["thumb"].grid(row=0, column=0, rowspan=3, sticky="nw")

        it["lbl_title"] = ttk.Label(b, text=shorten(it["url"], 60), style="RowTitle.TLabel",
                                    wraplength=380, justify="left")
        it["lbl_title"].grid(row=0, column=1, sticky="w", padx=(12, 0))
        it["lbl_meta"] = ttk.Label(b, text="Analyzing...", style="Meta.TLabel")
        it["lbl_meta"].grid(row=1, column=1, sticky="w", padx=(12, 0))

        sel = tk.Frame(b, bg=THEME["surface"])
        sel.grid(row=2, column=1, sticky="ew", padx=(12, 0), pady=(6, 0))
        sel.columnconfigure(0, weight=1)

        combo = RoundedSelect(sel, height=34)
        combo["values"] = [o[0] for o in it["options"]]
        combo.current(0)
        combo.config(state="disabled")
        combo.bind("<<ComboboxSelected>>", lambda e, it=it: self._on_row_quality(it))
        combo.grid(row=0, column=0, sticky="ew")
        it["combo"] = combo

        lang = RoundedSelect(sel, height=34)
        lang.configure(width=240)  # FIX: wider so "English (en) - original" fits
        lang["values"] = [l[0] for l in it["langs"]]
        lang.current(0)
        lang.config(state="disabled")
        lang.bind("<<ComboboxSelected>>", lambda e, it=it: self._on_row_lang(it))
        lang.grid(row=0, column=1, padx=(8, 0))
        it["lang_combo"] = lang

        it["lbl_state"] = ttk.Label(b, text="Loading...", style="State.TLabel")
        it["lbl_state"].grid(row=0, column=2, sticky="ne", padx=(8, 0))
        it["btn_rm"] = RoundedButton(b, "Remove", command=lambda it=it: self._remove(it),
                                     style="small")
        it["btn_rm"].grid(row=2, column=2, sticky="e", padx=(8, 0), pady=(6, 0))

    def _on_row_quality(self, it):
        it["choice"] = max(it["combo"].current(), 0)
        it["picked"]["q"] = True
        self._refresh_buttons()
        self._update_summary()

    def _on_all_selected(self, _e=None):
        i = self.all_combo.current()
        if i <= 0 or self.busy:
            return
        self.global_target = APPLY_ALL[i - 1][1]
        for it in self.items:
            if it["status"] == "ready":
                it["choice"] = pick_option(it["options"], self.global_target)
                it["combo"].current(it["choice"])
                it["picked"]["q"] = True
        self._log(f"[+] Quality for all: {APPLY_ALL[i - 1][0]}")
        self._refresh_buttons()
        self._update_summary()

    # ----- Language selection -----
    def _on_row_lang(self, it):
        it["lang_choice"] = max(it["lang_combo"].current(), 0)
        it["picked"]["l"] = True
        self._refresh_buttons()
        self._update_summary()

    def _apply_lang_target(self, it, target):
        idx = 0
        if target != "orig":
            for k, (_label, code) in enumerate(it["langs"]):
                if code and code.split("-")[0].lower() == target:
                    idx = k
                    break
        it["lang_choice"] = idx
        it["lang_combo"].current(idx)

    def _on_all_lang_selected(self, _e=None):
        i = self.all_lang.current()
        if i <= 0 or self.busy:
            return
        target = self.all_lang_codes[i]
        self.global_lang = target
        for it in self.items:
            if it["status"] == "ready":
                self._apply_lang_target(it, target)
                it["picked"]["l"] = True
        self._log(f"[+] Language for all: {self.all_lang['values'][i]}")
        self._refresh_buttons()
        self._update_summary()

    def _refresh_all_langs(self):
        names = {}
        for it in self.items:
            if it["status"] == "ready":
                for _label, code in it["langs"]:
                    if code:
                        names.setdefault(code.split("-")[0].lower(), lang_name(code))
        codes = sorted(names, key=lambda c: names[c])
        self.all_lang_codes = [None, "orig"] + codes
        self.all_lang["values"] = ["Choose...", "Original audio"] + [names[c] for c in codes]
        self.all_lang.current(0)

    def _remove(self, it):
        if self.busy:
            return
        it["status"] = "removed"
        it["card"].destroy()
        self.items.remove(it)
        if not self.items:
            self.lbl_empty.pack(pady=70, padx=40)
        self._update_chips()
        self._refresh_all_langs()
        self._refresh_buttons()
        self._update_summary()

    def _clear_list(self):
        if self.busy:
            return
        for it in self.items:
            it["status"] = "removed"
            it["card"].destroy()
        self.items = []
        self.lbl_empty.pack(pady=70, padx=40)
        self._set_progress(0)
        self._update_chips()
        self._refresh_all_langs()
        self._refresh_buttons()
        self._update_summary()

    def _set_item_state(self, it, text, tone="muted"):
        it["lbl_state"].configure(text=text, foreground=TONES.get(tone, THEME["muted"]))

    # ---------- Fetch ----------
    def _fetch_worker(self, url, iid):
        opts = {"noplaylist": True, "quiet": True, "no_warnings": True, "skip_download": True}
        try:
            with self.fetch_sem:
                with yt_dlp.YoutubeDL(opts) as ydl:
                    info = ydl.extract_info(url, download=False)
                entries = info.get("entries")
                if entries:
                    info = next(iter(entries))

                title = info.get("title") or "Unknown title"
                uploader = info.get("uploader") or info.get("channel") or ""
                duration = human_duration(info.get("duration"))
                is_live = bool(info.get("is_live"))
                h264_groups, other_groups = set(), set()
                tracks = {}  # audio language -> {"orig": bool, "dub": bool}
                is_vertical = "/shorts/" in url
                for f in info.get("formats") or []:
                    vcodec = f.get("vcodec") or "none"
                    height, width = f.get("height"), f.get("width")
                    if (vcodec == "none" and (f.get("acodec") or "none") != "none"
                            and f.get("language")):
                        note = (f.get("format_note") or "").lower()
                        t = tracks.setdefault(f["language"], {"orig": False, "dub": False})
                        t["orig"] |= "original" in note
                        t["dub"] |= "dubbed" in note
                    if vcodec == "none" or not height:
                        continue
                    if width and height > width:
                        is_vertical = True
                    key = (height, round(f.get("fps") or 0))
                    (h264_groups if is_h264(vcodec) else other_groups).add(key)

                convert_mode = not h264_groups
                groups = other_groups if convert_mode else h264_groups

                options = [BEST_VIDEO]
                for height, fps in sorted(groups, reverse=True):
                    label = f"{height}p" + (str(fps) if fps > 30 else "")
                    label += "  -  converted to H.264" if convert_mode else "  -  H.264"
                    options.append((label, build_format(height, fps, not convert_mode),
                                    False, height))
                options.append(AUDIO_MP3)

                # Original audio language
                orig_lang = next((c for c in tracks if tracks[c]["orig"]), None)
                if not orig_lang:
                    orig_lang = info.get("language") or None
                obase = orig_lang.split("-")[0].lower() if orig_lang else None
                if obase and not any(t["orig"] for t in tracks.values()):
                    for c in tracks:
                        if c.split("-")[0].lower() == obase:
                            tracks[c]["orig"] = True
                            orig_lang = c
                            break

                # Only the detected original language keeps the "original" flag
                if orig_lang in tracks:
                    for c in tracks:
                        tracks[c]["orig"] = (c == orig_lang)

                # Audio list: no separate "Original audio" entry when the original
                # language is known, it is simply labelled "(code) - original".
                langs = []
                for code in sorted(tracks, key=lambda c: (not tracks[c]["orig"], lang_name(c))):
                    label = f"{lang_name(code)} ({code})"
                    if tracks[code]["orig"]:
                        label += " - original"
                    elif tracks[code]["dub"]:
                        label += " - auto-dubbed"
                    langs.append((label, code))
                if not any(t["orig"] for t in tracks.values()):
                    langs = [l for l in langs
                             if not (obase and l[1].split("-")[0].lower() == obase)]
                    if orig_lang:
                        langs.insert(0, (f"{lang_name(orig_lang)} ({orig_lang}) - original",
                                         None))
                    else:
                        langs.insert(0, DEFAULT_LANG)

                image = self._load_thumbnail(info, is_vertical)
                meta = "  -  ".join(p for p in (uploader, duration) if p)
                if is_live:
                    meta = "LIVE  -  " + meta if meta else "LIVE"
            self.msgs.put(("item_info", (iid, title, meta, options, image, langs, orig_lang)))
        except Exception as e:
            self.msgs.put(("item_error", (iid, str(e))))

    @staticmethod
    def _crop_vertical(img):
        mask = ImageChops.difference(img, Image.new("RGB", img.size, (0, 0, 0)))
        bbox = mask.convert("L").point(lambda p: 255 if p > 20 else 0).getbbox()
        if bbox:
            w, h = bbox[2] - bbox[0], bbox[3] - bbox[1]
            if w * h > 0.3 * img.width * img.height:
                img = img.crop(bbox)
        target = 9 / 16
        if img.width / img.height > target + 0.02:
            new_w = int(img.height * target)
            left = (img.width - new_w) // 2
            img = img.crop((left, 0, left + new_w, img.height))
        return img

    @staticmethod
    def _round_corners(img, radius=8):
        s = 4
        w, h = img.size
        mask = Image.new("L", (w * s, h * s), 0)
        ImageDraw.Draw(mask).rounded_rectangle(
            (0, 0, w * s - 1, h * s - 1), radius=radius * s, fill=255)
        mask = mask.resize((w, h), Image.LANCZOS)
        out = img.convert("RGBA")
        out.putalpha(mask)
        return out

    def _load_thumbnail(self, info, is_vertical=False):
        if Image is None:
            return None
        urls = []
        if info.get("thumbnail"):
            urls.append(info["thumbnail"])
        for t in reversed(info.get("thumbnails") or []):
            u = t.get("url")
            if u and u not in urls:
                urls.append(u)
        for u in urls[:5]:
            try:
                req = urllib.request.Request(u, headers={"User-Agent": "Mozilla/5.0"})
                with urllib.request.urlopen(req, timeout=10) as r:
                    data = r.read()
                img = Image.open(io.BytesIO(data))
                img.load()
                img = img.convert("RGB")
                if is_vertical:
                    img = self._crop_vertical(img)
                img.thumbnail((self.ROW_THUMB_W - 8, self.ROW_THUMB_H - 8))
                return self._round_corners(img, 8)
            except Exception:
                continue
        return None

    # ---------- Download ----------
    def _start(self):
        if yt_dlp is None:
            messagebox.showerror("yt-dlp missing", "Install it with:\n\npip install yt-dlp")
            return
        if find_tool("ffmpeg") is None:
            messagebox.showerror(
                "FFmpeg missing",
                "FFmpeg is required (merging, MP3 conversion and H.264 conversion).\n\n"
                "Double-click 'install_ffmpeg.bat' (in the same folder as this program),\n"
                "wait until it finishes, then start the program again.",
            )
            return
        try:
            folder = Path(self.var_folder.get().strip()).expanduser()
            folder.mkdir(parents=True, exist_ok=True)
        except OSError as e:
            messagebox.showerror("Invalid folder", str(e))
            return

        jobs = []
        for it in self.items:
            if it["status"] != "ready":
                continue
            opt = it["options"][it["choice"]]
            lang = it["langs"][it["lang_choice"]][1]
            tag = lang or it.get("orig_lang")
            jobs.append((it["id"], it["url"], opt[1], opt[2], lang, tag))
            it["status"] = "queued"
            self._set_item_state(it, "Queued", "muted")
        if not jobs:
            return

        self.cancel_event.clear()
        self._set_progress(0)
        self.var_stats.set("")
        self._set_status_tone("info")
        self.var_status.set("Starting...")
        self.busy = True
        self._refresh_buttons()
        self._log(f"[+] Downloading {len(jobs)} video(s) to: {folder}")
        threading.Thread(target=self._download_worker, args=(jobs, folder),
                         daemon=True).start()

    def _cancel(self):
        self.cancel_event.set()
        self._set_status_tone("warn")
        self.var_status.set("Cancelling...")

    def _ensure_h264(self, path):
        ffmpeg = find_tool("ffmpeg")
        ffprobe = find_tool("ffprobe")
        if not ffmpeg or not ffprobe:
            self.msgs.put(("log", "[!] ffprobe not found: H.264 check skipped."))
            return
        probe = subprocess.run(
            [ffprobe, "-v", "error", "-select_streams", "v:0",
             "-show_entries", "stream=codec_name", "-of", "default=nw=1:nk=1", path],
            capture_output=True, text=True, creationflags=NO_WINDOW,
        )
        codec = probe.stdout.strip().lower()
        if not codec or codec == "h264":
            return

        self.msgs.put(("log", f"[+] Video codec is {codec}: converting to H.264..."))
        self.msgs.put(("status", f"Converting {codec} to H.264 (this may take a while)..."))
        src = Path(path)
        final = src.with_suffix(".mp4")
        tmp = final.with_name(final.stem + ".h264tmp.mp4")
        cmd = [
            ffmpeg, "-y", "-i", str(src), "-map", "0", "-c:s", "mov_text",
            "-c:v", "libx264", "-preset", "medium", "-crf", "18", "-pix_fmt", "yuv420p",
            "-c:a", "aac", "-b:a", "192k", "-movflags", "+faststart", str(tmp),
        ]
        proc = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                                creationflags=NO_WINDOW)
        while proc.poll() is None:
            if self.cancel_event.is_set():
                proc.terminate()
                proc.wait()
                tmp.unlink(missing_ok=True)
                raise Cancelled()
            time.sleep(0.3)
        if proc.returncode != 0:
            tmp.unlink(missing_ok=True)
            raise RuntimeError("FFmpeg failed to convert the video to H.264.")
        os.replace(tmp, final)
        if src != final:
            src.unlink(missing_ok=True)
        self.msgs.put(("log", f"[OK] Converted to H.264: {final.name}"))

    @staticmethod
    def _final_path(info):
        if info and info.get("entries"):
            entries = [e for e in info["entries"] if e]
            info = entries[0] if entries else None
        if not info:
            return None
        requested = info.get("requested_downloads") or []
        path = requested[0].get("filepath") if requested else info.get("filepath")
        return path if path and Path(path).exists() else None

    def _download_worker(self, jobs, folder):
        total = len(jobs)
        ok = failed = 0
        cancelled = False
        for n, (iid, url, fmt, audio_only, lang, tag) in enumerate(jobs):
            if self.cancel_event.is_set():
                cancelled = True
                break
            self.msgs.put(("item_state", (iid, "downloading", "Downloading...", "info")))
            self.msgs.put(("status", f"Downloading {n + 1}/{total}..."))
            try:
                self._download_one(url, fmt, audio_only, folder, iid, n, total, lang, tag)
                ok += 1
                self.msgs.put(("item_state", (iid, "done", "Done", "ok")))
            except Cancelled:
                cancelled = True
                break
            except yt_dlp.utils.DownloadError as e:
                if self.cancel_event.is_set():
                    cancelled = True
                    break
                failed += 1
                self.msgs.put(("log", f"[X] {e} {hint_for(str(e), '')}"))
                self.msgs.put(("item_state", (iid, "error", "Error", "err")))
            except Exception as e:
                failed += 1
                self.msgs.put(("log", f"[X] Unexpected error: {e}"))
                self.msgs.put(("item_state", (iid, "error", "Error", "err")))
            self.msgs.put(("progress", (n + 1) / total * 100))
        self.msgs.put(("done", (ok, failed, total, cancelled)))

    def _download_one(self, url, fmt, audio_only, folder, iid, n, total, lang=None, tag=None):
        name = "%(title).120s [%(id)s]" if is_tiktok(url) else "%(title).150s"
        if tag:
            name += f" ({tag})"  # language of the final audio, e.g. "Title (fr-FR)"
        template = name + (".%(ext)s" if audio_only else "_%(height)sp.%(ext)s")

        def hook(d):
            if self.cancel_event.is_set():
                raise Cancelled()
            if d.get("status") == "downloading":
                tot = d.get("total_bytes") or d.get("total_bytes_estimate")
                speed = (d.get("_speed_str") or "").strip()
                if tot:
                    frac = d.get("downloaded_bytes", 0) / tot
                    eta = (d.get("_eta_str") or "").strip()
                    self.msgs.put(("progress", (n + frac) / total * 100))
                    self.msgs.put(("item_state", (iid, None, f"{int(frac * 100)}%", "info")))
                    self.msgs.put(("status", f"Downloading {n + 1}/{total}..."))
                    self.msgs.put(("stats", f"{speed}  -  ETA {eta}"))
                else:
                    done = d.get("downloaded_bytes") or 0
                    self.msgs.put(("status", "Recording live stream... (Cancel to stop)"))
                    self.msgs.put(("stats", f"{human_size(done)}  -  {speed}"))
            elif d.get("status") == "finished":
                self.msgs.put(("status", f"Processing file {n + 1}/{total} (FFmpeg)..."))
                self.msgs.put(("stats", ""))

        opts = {
            "format": apply_language(fmt, lang),
            "outtmpl": str(folder / template),
            "noplaylist": True,
            "noprogress": True,
            "windowsfilenames": True,
            "logger": YtdlpLogger(lambda m: self.msgs.put(("log", m))),
            "progress_hooks": [hook],
        }
        ffmpeg_path = find_tool("ffmpeg")
        if ffmpeg_path:
            opts["ffmpeg_location"] = str(Path(ffmpeg_path).parent)
        if audio_only:
            opts["postprocessors"] = [
                {"key": "FFmpegExtractAudio", "preferredcodec": "mp3", "preferredquality": "192"}
            ]
        else:
            opts["merge_output_format"] = "mp4"

        with yt_dlp.YoutubeDL(opts) as ydl:
            info = ydl.extract_info(url, download=True)
        if not audio_only:
            path = self._final_path(info)
            if path:
                self._ensure_h264(path)

    # ---------- Thread -> UI ----------
    def _process_messages(self):
        try:
            while True:
                kind, data = self.msgs.get_nowait()
                if kind == "log":
                    self._log(data)
                elif kind == "progress":
                    self._set_progress(data)
                elif kind == "stats":
                    self.var_stats.set(data)
                elif kind == "status":
                    self._set_status_tone("info")
                    self.var_status.set(data)
                elif kind == "item_info":
                    self._on_item_info(data)
                elif kind == "item_error":
                    self._on_item_error(*data)
                elif kind == "item_state":
                    iid, status, text, tone = data
                    it = self._find(iid)
                    if it is not None:
                        self._set_item_state(it, text, tone)
                        if status:
                            it["status"] = status
                elif kind == "done":
                    self._on_done(*data)
        except queue.Empty:
            pass
        self.after(100, self._process_messages)

    def _on_item_info(self, data):
        iid, title, meta, options, image, langs, orig_lang = data
        it = self._find(iid)
        if it is None:
            return
        it["title"] = title
        it["options"] = options
        it["status"] = "ready"
        it["lbl_title"].configure(text=shorten(title, 90))
        it["lbl_meta"].configure(text=meta or " ")
        it["combo"]["values"] = [o[0] for o in options]
        it["choice"] = pick_option(options, self.global_target) if self.global_target else 0
        it["picked"]["q"] = bool(self.global_target)
        it["combo"].current(it["choice"])
        it["langs"] = langs
        it["orig_lang"] = orig_lang
        it["lang_combo"]["values"] = [l[0] for l in langs]
        it["lang_choice"] = 0
        it["lang_combo"].current(0)
        if self.global_lang:
            self._apply_lang_target(it, self.global_lang)
            it["picked"]["l"] = True
        if image is not None:
            it["photo"] = ImageTk.PhotoImage(image)
            it["thumb"].show_image(it["photo"])
        else:
            it["thumb"].show_text("No preview")
        self._set_item_state(it, "Ready", "ok")
        extra = f", {len(langs) - 1} audio language(s)" if len(langs) > 1 else ""
        self._log(f"[OK] {title}: {len(options) - 2} quality option(s) found{extra}.")
        self._refresh_all_langs()
        self._refresh_buttons()
        self._update_summary()

    def _on_item_error(self, iid, error):
        it = self._find(iid)
        if it is None:
            return
        it["status"] = "error"
        it["thumb"].show_text("No preview")
        it["lbl_meta"].configure(text=hint_for(error, "Could not fetch this video."))
        self._set_item_state(it, "Error", "err")
        self._log(f"[X] {error}")
        self._refresh_buttons()
        self._update_summary()

    def _on_done(self, ok, failed, total, cancelled):
        self.var_stats.set("")
        for it in self.items:
            if it["status"] in ("queued", "downloading"):
                it["status"] = "ready"
                self._set_item_state(it, "Ready", "ok")
        if cancelled:
            self._set_status_tone("warn")
            self.var_status.set(f"Download cancelled ({ok}/{total} completed).")
        elif failed:
            self._set_status_tone("err" if not ok else "warn")
            self.var_status.set(f"{ok} completed, {failed} failed (see details).")
        else:
            self._set_progress(100)
            self._set_status_tone("ok")
            self.var_status.set(f"All {ok} download(s) completed!")
        self._log(f"[OK] Finished: {ok} ok, {failed} failed, cancelled={cancelled}")
        self.busy = False
        self._refresh_buttons()

    # ---------- Quit ----------
    def _quit(self):
        if self.busy:
            if not messagebox.askyesno("Quit", "A download is in progress. Cancel it and quit?"):
                return
            self.cancel_event.set()
        if self.browser_proc is not None:
            self.browser_proc.terminate()
        self.destroy()


if __name__ == "__main__":
    if "--browse" in sys.argv:
        i = sys.argv.index("--browse")
        platform = sys.argv[i + 1]
        out = sys.argv[sys.argv.index("--out") + 1]
        run_browser(platform, out)
    else:
        App().mainloop()
