#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
SSD1309/SSD1306 OLED RSSリーダー (I2C/SPI両対応)
ファイル名    : SSD1309-RSS.py
概要          : SSD1309/SSD1306 OLED用 複数RSS対応リーダー
作成者        : Akihiko Fuji
更新日        : 2026/02/13
バージョン    : 1.8.1
------------------------------------------------
Raspberry Pi + luma.oled環境で動作する日本語対応RSSビューワー。
複数RSSソースを巡回し、記事を自動スクロール表示します。

 - I2C/SPI 接続を USE_SPI 変数で切り替え可能
 - GPIOボタンによる記事送り、ダブルクリックでフィード切替
 - 日本語表示のためフォント（例：JF-Dot）を同一フォルダに設置してください

必要ライブラリ:
    pip3 install luma.oled feedparser pillow RPi.GPIO asyncio
"""

import os
import sys
import time
import threading
import signal
import logging
import re
import textwrap
import asyncio
import contextlib
import csv
from pathlib import Path

from dataclasses import dataclass
from collections import deque
from typing import Dict, List, Any, Optional, Deque, Tuple, TypedDict

import aiohttp
import feedparser
from PIL import Image, ImageDraw, ImageFont

# luma.oled
from luma.oled.device import ssd1309  # ssd1306 を利用する場合は変更

# -----------------------------
# 設定値（上部に集約）
# -----------------------------

# 送りやフィードに利用するGPIOピン（BCM）
BUTTON_FEED = 18

RSS_FEED_FILE = "rss-read.me"

# RSS取得時のUser-Agent
USER_AGENT = "SSD1309-RSS/1.8 (+https://github.com/)"

# SPI接続時はTrue / I2C接続時はFalse
USE_SPI = False

# SPI/I2C パラメータ
SPI_PORT     = 0
SPI_DEVICE   = 0
SPI_GPIO_DC  = 24
SPI_GPIO_RST = 25
I2C_PORT     = 1
I2C_ADDRESS  = 0x3C

# OLED表示設定
OLED_CONTRAST = 0xFF

# 画面表示時間の設定 8:30 - 18:00 のみ利用するとしている
DISPLAY_TIME_START = ( 8, 30)
DISPLAY_TIME_END   = (18, 00)

# 表示メッセージ
LOADING_MESSAGE = "ニュースを読み込み中..."
NO_NEWS_MESSAGE = "ニュースがありません"
UNKNOWN_FEED_TITLE = "Unknown Feed"

# RSS取得/整形の設定
RSS_ENTRY_LIMIT = 10

# RSSフィード（rss-read.meが未配置/空のときに使われるデフォルト）
DEFAULT_RSS_FEEDS = [
    {"title": "NHKニュース"     , "url": "https://news.web.nhk/n-data/conf/na/rss/cat0.xml",       "color": 1, "type": "rss"},
    {"title": "NHKニュース 科学", "url": "https://news.web.nhk/n-data/conf/na/rss/cat3.xml",       "color": 1, "type": "rss"},
    {"title": "NHKニュース 政治", "url": "https://news.web.nhk/n-data/conf/na/rss/cat4.xml",       "color": 1, "type": "rss"},
    {"title": "NHKニュース 経済", "url": "https://news.web.nhk/n-data/conf/na/rss/cat5.xml",       "color": 1, "type": "rss"},
    {"title": "NHKニュース 国際", "url": "https://news.web.nhk/n-data/conf/na/rss/cat6.xml",       "color": 1, "type": "rss"},
]

@dataclass(frozen=True)
class NetworkSettings:
    max_retries: int = 3
    base_delay: float = 2.0
    timeout: float = 10.0

@dataclass(frozen=True)
class CacheSettings:
    max_items: int = 30

@dataclass(frozen=True)
class AnimationSettings:
    scroll_speed: float    = 4.0
    easing_duration: float = 0.8
    tail_margin_px: int    = 24

# 描画固定値は LayoutSettings（定数群として集約）
@dataclass(frozen=True)
class LayoutSettings:
    display_width: int             = 128
    display_height: int            = 64
    title_font_filename: str       = "JF-Dot-MPlusH10.ttf"
    main_font_filename: str        = "JF-Dot-MPlusH12.ttf"
    title_font_size: int           = 10
    main_font_size: int            = 12
    title_wrap_width: int          = 20
    title_line_height: int         = 12
    header_height: int             = 14
    header_content_padding_y: int  = 2
    desc_background_height: int    = 14
    title_desc_margin_y: int       = 2
    loading_effect_ticks: int      = 10
    loading_bar_count: int         = 20
    loading_segment_width: int     = 6
    feed_switch_notice_offset: int = 10
    transition_frame_step: float   = 1.5

class FeedItem(TypedDict):
    title: str
    description: str
    published: str
    link: str
    feed_title: str
    feed_color: int
    feed_index: int
    title_lines: List[str]
    desc_width: Optional[int]

# 周期/運用設定は AppConfig に集約
@dataclass(frozen=True)
class AppConfig:
    rss_update_interval: float   = 1800.0    # 秒｜RSSを再取得する間隔（30分ごとに最新化）
    feed_switch_interval: float  = 600.0     # 秒｜フィード自動切替の間隔（10分で次のフィードへ）
    article_display_time: float  = 25.0      # 秒｜短文（スクロール不要）の記事を次へ送るまでの待機時間
    pause_at_start: float        = 3.0       # 秒｜記事表示直後のスクロール一時停止（読み始めの“間”を作る）
    transition_frames: float     = 15.0      # フレーム数｜フィード/記事切替アニメの尺（多いほどゆっくり）
    gpio_poll_interval: float    = 0.02      # 秒｜GPIOポーリング周期（クリック検出のサンプリング間隔）
    main_update_interval: float  = 0.1       # 秒｜描画更新周期（CPU負荷と滑らかさのトレードオフ）
    double_click_interval: float = 0.6       # 秒｜ダブルクリック判定の間隔（この時間内の2押しでダブル扱い）
    debounce_sec: float          = 0.05      # 秒｜ボタンのチャタリング除去時間
    long_press_interval: float   = 1.5       # 秒｜長押し判定時間（消灯/点灯の切替）
    sleep_interval: int          = 30        # 秒｜表示時間外の待機間隔

# ログ設定
# ログ出力設定を初期化する
def setup_logging() -> logging.Logger:
    logger = logging.getLogger("rss_oled")
    logger.setLevel(logging.INFO)
    if not logger.handlers:
        handler = logging.StreamHandler(sys.stdout)
        fmt = logging.Formatter("[%(levelname)s] %(asctime)s %(message)s")
        handler.setFormatter(fmt)
        logger.addHandler(handler)
    return logger


# rss-read.meの色設定を解析する
def _parse_color_value(color_value: str, log: logging.Logger, line_no: int) -> int:
    try:
        return int(color_value)
    except ValueError:
        log.warning(
            "Invalid color value '%s' in rss-read.me line %d; using default 1",
            color_value,
            line_no,
        )
        return 1


# rss-read.meの1行を解析してフィード情報を作る
def _parse_feed_row(values: List[str], log: logging.Logger, line_no: int) -> Optional[Dict[str, Any]]:
    title = ""
    url = ""
    color = 1
    feed_type = "rss"
    if len(values) == 1:
        url = values[0]
        title = values[0]
    elif len(values) == 2:
        title, url = values
    elif len(values) == 3:
        title, url, third_value = values[:3]
        try:
            color = int(third_value)
        except ValueError:
            feed_type = third_value.lower()

    else:
        title, url, color_value, feed_type_value = values[:4]
        color = _parse_color_value(color_value, log, line_no)
        if feed_type_value:
            feed_type = feed_type_value.lower()
    if feed_type not in ("rss", "text"):
        log.warning(
            "Unknown feed type '%s' in rss-read.me line %d; using 'rss'",
            feed_type,
            line_no,
        )
        feed_type = "rss"
    if not url:
        log.warning("Missing URL in rss-read.me line %d; skipping", line_no)
        return None
    return {"title": title or url, "url": url, "color": color, "type": feed_type}


# RSS定義ファイルを読み込んでフィード一覧を返す
def _load_rss_feeds(feed_path: str, log: logging.Logger) -> Tuple[List[Dict[str, Any]], str]:
    if not os.path.exists(feed_path):
        log.warning("rss-read.me not found at %s; using built-in defaults", feed_path)
        return DEFAULT_RSS_FEEDS, "built-in defaults (rss-read.me not found)"

    feeds: List[Dict[str, Any]] = []
    try:
        with open(feed_path, newline="", encoding="utf-8") as handle:
            reader = csv.reader(handle)
            for line_no, row in enumerate(reader, start=1):
                if not row:
                    continue
                if row[0].strip().startswith("#"):
                    continue
                values = [item.strip() for item in row if item is not None]
                if not values:
                    continue
                feed = _parse_feed_row(values, log, line_no)
                if feed is not None:
                    feeds.append(feed)
    except (OSError, csv.Error) as exc:
        log.error("Failed to read rss-read.me (%s); using defaults", exc)
        return DEFAULT_RSS_FEEDS, "built-in defaults (rss-read.me unreadable)"

    if not feeds:
        log.warning("rss-read.me had no usable feeds; using built-in defaults")
        return DEFAULT_RSS_FEEDS, "built-in defaults (rss-read.me empty)"

    return feeds, f"rss-read.me ({len(feeds)} feeds)"


class RSSReaderApp:
    """RSSリーダーのメインアプリケーション。

    self.rss_feeds はフィード定義の配列で、self.news_items は feed index をキーに持つ取得済み記事リスト。
    フィードの順序（index）は起動中に不変であり、self.news_items のキーは self.rss_feeds の index と一致する。
    """
    # 主要変数と状態を初期化
    # アプリの初期状態と設定を構築する
    def __init__(self):
        # ロガー
        self.log = setup_logging()
        self.rss_feeds, self.rss_feed_source = _load_rss_feeds(
            os.path.join(os.path.dirname(os.path.abspath(__file__)), RSS_FEED_FILE),
            self.log,
        )
        self.log.info(f"RSS feeds loaded from {self.rss_feed_source}")

        # 表示・描画
        self.display = None

        # フォント
        self.TITLE_FONT = None
        self.FONT = None

        # 設定クラス
        self.network_settings = NetworkSettings()
        self.cache_settings = CacheSettings()
        self.animation_settings = AnimationSettings()
        self.layout_settings = LayoutSettings()
        self.config = AppConfig()

        # 状態（可変）
        # 時間計測は time.monotonic を使用し、表示用時刻は time.localtime/strftime を使う。
        self.news_items: Dict[int, List[FeedItem]] = {}  # 取得済みRSSをフィードindexごとに保持
        self.current_feed_index: int   = 0        # 現在表示中のフィードindex
        self.current_item_index: int   = 0        # 現在表示中の記事index（当該フィード内）
        self.scroll_position: float    = 0.0      # 説明文のスクロール位置（px）
        self.article_start_time: float = 0.0      # 現記事の表示開始モノトニック秒（PAUSE判定や経過時間計算に使用）
        self.auto_scroll_paused: bool  = True     # Trueの間は説明文スクロールを停止（pause_at_startで解除）
        self.feed_switch_time: float   = 0.0      # 直近のフィード切替モノトニック秒（中央通知の表示条件に利用）
        self.loading_effect: int       = 0        # ローディング演出の残カウンタ（0で非表示）
        self.transition_effect: float  = 0.0      # 切替アニメの残フレーム量（>0の間はスライド描画）
        self.transition_direction: int = 1        # 切替方向（1:右へ／-1:左へ）アニメのオフセット符号に使用
        self._prev_feed_index: int     = 0        # 直前に表示していたフィード
        self._prev_item_index: int     = 0        # 直前に表示していた記事

        self.feed_cache: Dict[int, Deque[FeedItem]] = {
            idx: deque(maxlen=self.cache_settings.max_items)
            for idx in range(len(self.rss_feeds))
        }
        self.failover_snapshot: Dict[int, List[FeedItem]] = {}

        # スケジューラ／タイマー代替：メインループ内の時刻管理
        self._last_main_update: float       = 0.0 # 直近の描画更新実行時刻（main_update_interval判定用）
        self._last_feed_switch_check: float = 0.0 # 直近のフィード切替チェック時刻（feed_switch_interval判定用）
        self._last_scroll_time: float       = 0.0
        self._scroll_ease_elapsed: float    = 0.0
        self._last_rss_refresh_attempt: float = 0.0
     
        # GPIO用
        self._gpio_available = False              # TrueならGPIO使用可能（環境により未接続/未導入の考慮）
        self._stop_event = threading.Event()      # 終了シグナル（スレッド/ループの安全停止に利用）
        self._background_tasks: List[asyncio.Task] = []
        self._gpio_module = None

        # クリック検出（ポーリング方式に統一）
        self._prev_button_state   = 1             # 直前のボタン状態（1:未押下, 0:押下）
        self._last_press_time     = 0.0           # 直近の押下時刻（単/ダブルクリックの時間間隔判定に使用）
        self._last_edge_time      = 0.0           # 直近のエッジ時刻（チャタリング抑止）
        self._click_count         = 0             # クリック回数カウント（1=シングル, 2=ダブル）
        self._press_start_time    = 0.0           # ボタン押下開始時刻
        self._long_press_handled  = False         # 長押し処理済みフラグ
        self._display_enabled     = True          # True=表示点灯、False=消灯
        self._display_blank_drawn = False         # 消灯時にブランクを描画済みか

        # ロック（必要最小限）
        self._state_lock = threading.Lock()
        self._desc_width_cache: Dict[Tuple[int, str, int], int] = {}

    # 記事切替時の表示状態を初期化する
    def _reset_article_state(
        self,
        transition_direction: int,
        *,
        keep_feed_idx: Optional[int] = None,
        keep_item_idx: Optional[int] = None,
        keep_link: Optional[str] = None,
    ) -> None:
        self.scroll_position = 0.0
        self.transition_effect = self.config.transition_frames
        self.transition_direction = transition_direction
        self.article_start_time = time.monotonic()
        self.auto_scroll_paused = True
        self._scroll_ease_elapsed = 0.0
        self._last_scroll_time = time.monotonic()
        if keep_feed_idx is not None and keep_item_idx is not None and keep_link is not None:
            keys_to_delete = [
                key
                for key in self._desc_width_cache
                if not (
                    key[0] == keep_feed_idx
                    and key[1] == keep_link
                    and key[2] == keep_item_idx
                )
            ]
            for key in keys_to_delete:
                self._desc_width_cache.pop(key, None)

# 1) 初期化処理
    # 初期化
    # 起動時の初期化処理をまとめて実行する
    def initialize(self) -> None:
        self._init_fonts()
        self._init_gpio()
        self._init_display()
        self._install_signal_handlers()
        monotonic_now = time.monotonic()
        self.article_start_time = monotonic_now
        self.feed_switch_time = monotonic_now - self.layout_settings.feed_switch_notice_offset  # 初回通知オフセット
        self._last_main_update = monotonic_now
        self._last_feed_switch_check = monotonic_now
        self._last_rss_refresh_attempt = monotonic_now
        self._last_scroll_time = monotonic_now
        self._scroll_ease_elapsed = 0.0
        self.scroll_position = 0.0

    # 日本語フォントの呼び出し
    # 表示用フォントを読み込む
    def _init_fonts(self) -> None:
        try:
            layout = self.layout_settings
            font_dir = os.path.dirname(os.path.abspath(__file__))
            title_font_file = os.path.join(font_dir, layout.title_font_filename)
            main_font_file = os.path.join(font_dir, layout.main_font_filename)
            self.TITLE_FONT = ImageFont.truetype(title_font_file, layout.title_font_size)
            self.FONT = ImageFont.truetype(main_font_file, layout.main_font_size)
            self.log.info("Fonts loaded")
        except OSError as e:
            self.log.error(f"Font loading error: {e} -> using default fonts")
            self.TITLE_FONT = ImageFont.load_default()
            self.FONT = ImageFont.load_default()
        except Exception as e:
            self.log.warning(f"Unexpected font loading issue: {e} -> using default fonts")
            self.TITLE_FONT = ImageFont.load_default()
            self.FONT = ImageFont.load_default()

    # GPIO初期化およびボタンスレッド起動
    # GPIOを初期化してボタン入力を準備する
    def _init_gpio(self) -> None:
        try:
            import RPi.GPIO as GPIO
            GPIO.setwarnings(False)
            GPIO.setmode(GPIO.BCM)
            GPIO.setup(BUTTON_FEED, GPIO.IN, pull_up_down=GPIO.PUD_UP)
            self._gpio_available = True
            self._gpio_module = GPIO
            self.log.info("GPIO initialized (polling ready)")
        except Exception as e:
            self._gpio_available = False
            self.log.info(f"GPIO not available, software-only mode: {e}")

    # OLED初期化 (I2C/SPI切替対応)
    # OLEDディスプレイを初期化する
    def _init_display(self) -> None:
        try:
            layout = self.layout_settings
            # SPIモード
            if USE_SPI:
                from luma.core.interface.serial import spi

                serial = spi(
                    device=SPI_DEVICE,
                    port=SPI_PORT,
                    gpio_DC=SPI_GPIO_DC,
                    gpio_RST=SPI_GPIO_RST,
                )
                self.display = ssd1309(
                    serial_interface=serial,
                    width=layout.display_width,
                    height=layout.display_height,
                ) # ssd1306 を利用する場合は変更
                self.log.info("OLED initialized (SPI mode)")

            # I2Cモード
            else:
                from luma.core.interface.serial import i2c

                serial = i2c(
                    port=I2C_PORT,
                    address=I2C_ADDRESS,
                ) # アドレスが異なる場合は sudo i2cdetect -y 1 で確認し変更してください
                self.display = ssd1309(
                    serial_interface=serial,
                    width=layout.display_width,
                    height=layout.display_height,
                ) # ssd1306 を利用する場合は変更
                self.log.info("OLED initialized (I2C mode)")

            self.display.contrast(OLED_CONTRAST)
            self.display.clear()
        except Exception as e:
            self.log.error(f"OLED initialization failed: {e}")
            raise

    # SIGINT/SIGTERMの終了ハンドラを登録
    # 終了シグナルのハンドラを登録する
    def _install_signal_handlers(self):
        signal.signal(signal.SIGINT, self._signal_handler)
        signal.signal(signal.SIGTERM, self._signal_handler)

# 2) RSS取得処理
    # RSS取得（非同期＆フェイルオーバー対応）
    # RSS取得のリトライとキャッシュ更新を行う
    async def fetch_rss_feed(self) -> bool:
        settings = self.network_settings
        total_attempts = settings.max_retries + 1
        self.log.info(
            f"Fetching RSS feeds... (timeout={settings.timeout}s, attempts={total_attempts})"
        )
        self.loading_effect = self.layout_settings.loading_effect_ticks

        # リトライしながらRSS取得を試みる
        for attempt in range(1, total_attempts + 1):
            self._last_rss_refresh_attempt = time.monotonic()
            try:
                successes, errors = await self._fetch_rss_feed_async()
            except asyncio.CancelledError:
                raise
            except Exception as exc:
                self.log.error(
                    f"RSS fetch error: {exc} (attempt {attempt}/{total_attempts})"
                )
                successes, errors = {}, {}

            if successes:
                self._update_cache(successes)
                if errors:
                    self._handle_partial_failures(errors)
                return True

            if errors:
                self._handle_partial_failures(errors)

            self.log.warning(
                f"No feed items retrieved (attempt {attempt}/{total_attempts})"
            )

            if attempt < total_attempts:
                delay = settings.base_delay * (2 ** (attempt - 1))
                self.log.debug(f"Retrying RSS fetch after {delay:.1f}s delay")
                await asyncio.sleep(delay)

        if self._restore_failover_snapshot():
            self.log.info("Using cached feed data due to fetch failure")
        return False

    # 全フィードを並列で取得する
    async def _fetch_rss_feed_async(self) -> Tuple[Dict[int, List[FeedItem]], Dict[int, Exception]]:
        timeout = aiohttp.ClientTimeout(total=self.network_settings.timeout)
        async with aiohttp.ClientSession(
            timeout=timeout,
            headers={"User-Agent": USER_AGENT},
        ) as session:
            # 全フィードの取得タスクを並列実行
            tasks = [
                self._fetch_single_feed(session, idx, feed_info)
                for idx, feed_info in enumerate(self.rss_feeds)
            ]
            results = await asyncio.gather(*tasks)

        successes: Dict[int, List[FeedItem]] = {}
        errors: Dict[int, Exception] = {}
        for idx, items, error in results:
            if error:
                errors[idx] = error
            else:
                successes[idx] = items
        return successes, errors

    # 単一フィードを種別に応じて取得する
    async def _fetch_single_feed(
        self,
        session: aiohttp.ClientSession,
        idx: int,
        feed_info: Dict[str, Any],
    ) -> Tuple[int, Optional[List[FeedItem]], Optional[Exception]]:
        try:
            if feed_info.get("type") == "text":
                return await self._fetch_text_feed(session, idx, feed_info)
            return await self._fetch_rss_feed(session, idx, feed_info)
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            self.log.error("Feed fetch failed for %s: %s", feed_info["title"], exc)
            return idx, None, exc

    # RSS形式のフィードを取得して整形する
    async def _fetch_rss_feed(
        self,
        session: aiohttp.ClientSession,
        idx: int,
        feed_info: Dict[str, Any],
    ) -> Tuple[int, Optional[List[FeedItem]], Optional[Exception]]:
        async with session.get(feed_info["url"]) as response:
            response.raise_for_status()
            payload = await response.read()

        feed = feedparser.parse(payload)
        entries = getattr(feed, "entries", [])[:RSS_ENTRY_LIMIT]
        feed_items = [
            self._build_feed_item(
                feed_info,
                idx,
                title=getattr(entry, "title", ""),
                description=self._sanitize_description(
                    getattr(entry, "summary", "")
                    or getattr(entry, "description", "")
                    or ""
                ),
                published=getattr(entry, "published", ""),
                link=getattr(entry, "link", ""),
            )
            for entry in entries
        ]
        self.log.info(f" -> {feed_info['title']}: {len(feed_items)} items")
        return idx, feed_items, None

    # テキスト形式のフィードを取得して整形する
    async def _fetch_text_feed(
        self,
        session: aiohttp.ClientSession,
        idx: int,
        feed_info: Dict[str, Any],
    ) -> Tuple[int, Optional[List[FeedItem]], Optional[Exception]]:
        source = feed_info["url"]
        if source.startswith(("http://", "https://")):
            async with session.get(source) as response:
                response.raise_for_status()
                text = await response.text()
        else:
            text = await asyncio.to_thread(self._read_text_file, source)

        description = text.strip()
        item = self._build_feed_item(
            feed_info,
            idx,
            title=feed_info["title"],
            description=description,
        )
        self.log.info(f" -> {feed_info['title']}: 1 item (text)")
        return idx, [item], None

    # ローカルテキストファイルを読み込む
    def _read_text_file(self, source: str) -> str:
        path = Path(source)
        if not path.is_file():
            raise FileNotFoundError(f"Text source not found: {source}")
        return path.read_text(encoding="utf-8")

    def _build_feed_item(
        self,
        feed_info: Dict[str, Any],
        idx: int,
        *,
        title: str,
        description: str,
        published: str = "",
        link: str = "",
    ) -> FeedItem:
        title_lines = textwrap.wrap(title, width=self.layout_settings.title_wrap_width)
        return {
            "title": title,
            "description": description,
            "published": published,
            "link": link,
            "feed_title": feed_info["title"],
            "feed_color": feed_info["color"],
            "feed_index": idx,
            "title_lines": title_lines,
            "desc_width": None,
        }

    @staticmethod
    def _sanitize_description(description: str) -> str:
        return re.sub(r"<[^>]+>", "", description)

 
    # 取得結果をキャッシュへ反映する
    def _update_cache(self, new_data: Dict[int, List[FeedItem]]) -> None:
        for idx, items in new_data.items():
            cache = self.feed_cache.setdefault(
                idx, deque(maxlen=self.cache_settings.max_items)
            )
            if items:
                cache.clear()
                cache.extend(items[: self.cache_settings.max_items])

        snapshot = self._apply_cache_to_news()
        if snapshot is not None:
            total_items = sum(len(items) for items in snapshot.values())
            self.log.info(f"Total items: {total_items}")

    # キャッシュ内容を表示用データへ適用する
    def _apply_cache_to_news(self) -> Optional[Dict[int, List[FeedItem]]]:
        if not self.feed_cache:
            return None

        snapshot: Dict[int, List[FeedItem]] = {
            idx: list(cache) for idx, cache in self.feed_cache.items()
        }
        with self._state_lock:
            self.news_items = snapshot
            self._desc_width_cache.clear()
            self._normalize_current_indices_locked()

        self.failover_snapshot = {
            idx: list(items) for idx, items in snapshot.items()
        }
        return snapshot

    # 失敗時にフェイルオーバーキャッシュを復元する
    def _restore_failover_snapshot(self) -> bool:
        if not self.failover_snapshot:
            return False

        with self._state_lock:
            self.news_items = {
                idx: list(items) for idx, items in self.failover_snapshot.items()
            }
            self._desc_width_cache.clear()
            self._normalize_current_indices_locked()
        self.log.warning("Restored news items from failover cache")
        return True


    # 現在のフィード/記事インデックスを有効範囲へ補正する（ロック下専用）
    def _normalize_current_indices_locked(self) -> None:
        if not self.rss_feeds:
            self.current_feed_index = 0
            self.current_item_index = 0
            return

        if self.current_feed_index < 0 or self.current_feed_index >= len(self.rss_feeds):
            self.current_feed_index = 0

        items = self.news_items.get(self.current_feed_index, [])
        if not items:
            self.current_item_index = 0
            return

        if self.current_item_index < 0 or self.current_item_index >= len(items):
            self.current_item_index = 0


    # 部分的な取得失敗をログに通知する
    def _handle_partial_failures(self, errors: Dict[int, Exception]) -> None:
        for idx, error in errors.items():
            feed_name = self.rss_feeds[idx]["title"]
            cache = self.feed_cache.get(idx)
            if cache and len(cache) > 0:
                self.log.warning(
                    f"Feed fallback used for {feed_name}: {error}"
                )
            else:
                self.log.error(f"Feed unavailable {feed_name}: {error}")

# 3) 描画・表示制御
    # 画面描画ユーティリティ
    # テキスト幅を計測する
    def get_text_width(self, text: str, font: ImageFont.FreeTypeFont) -> int:
        try:
            return int(font.getlength(text))
        except AttributeError:
            try:
                return font.getsize(text)[0]
            except AttributeError:
                dummy_image = Image.new("1", (1, 1))
                dummy_draw = ImageDraw.Draw(dummy_image)
                bbox = dummy_draw.textbbox((0, 0), text, font=font)
                return bbox[2] - bbox[0]

    # 記事本文とタイトルを描画する
    # 記事のタイトルと本文を描画する
    def draw_article_content(
        self,
        draw: ImageDraw.ImageDraw,
        item: FeedItem,
        base_x: int,
        base_y: int,
        highlight_title: bool = False,
    ) -> int:
        layout = self.layout_settings
        width = layout.display_width
        title_wrapped = item.get("title_lines") or textwrap.wrap(
            item["title"],
            width=layout.title_wrap_width,
        )
        y_pos = base_y
        for i, line in enumerate(title_wrapped[:2]):
            if highlight_title:
                title_width = self.get_text_width(line, self.FONT)
                draw.rectangle(
                    (
                        base_x - 2,
                        y_pos - 1,
                        base_x + title_width + 2,
                        y_pos + 11,
                    ),
                    fill=1,
                )
                draw.text((base_x, y_pos), line, font=self.FONT, fill=0)
            else:
                draw.text((base_x, y_pos), line, font=self.FONT, fill=1)
            y_pos += layout.title_line_height
        title_block_height = layout.title_line_height * (
            2 if len(title_wrapped) >= 2 else 1
        )
        y_pos = base_y + title_block_height
        draw.line([(base_x, y_pos + 1), (base_x + width - 4, y_pos + 1)], fill=1)
        y_pos += layout.title_desc_margin_y
        desc_background_height = layout.desc_background_height
        draw.rectangle(
            (base_x, y_pos, base_x + width - 4, y_pos + desc_background_height),
            fill=0,
        )
        desc = item["description"].replace("\n", " ").strip()
        scroll_offset = int(self.scroll_position)
        desc_x = base_x if self.auto_scroll_paused else (base_x - scroll_offset)
        draw.text((desc_x, y_pos), desc, font=self.FONT, fill=1)
        return y_pos + desc_background_height
                     
    # フィード切替時の通知（中央反転表示）
    # フィード切替通知を描画する
    def draw_feed_notification(self, draw: ImageDraw.ImageDraw, feed_name: str) -> None:
        layout = self.layout_settings
        width = layout.display_width
        height = layout.display_height
        draw.rectangle(
            (10, height // 2 - 12, width - 10, height // 2 + 12),
            fill=1,
        )
        text_width = self.get_text_width(feed_name, self.FONT)
        draw.text(
            ((width - text_width) // 2, height // 2 - 6),
            feed_name,
            font=self.FONT,
            fill=0,
        )
    # ヘッダ領域を描画する
    def _draw_header(self, draw: ImageDraw.ImageDraw, feed_idx: int) -> Tuple[str, int]:
        layout = self.layout_settings
        width = layout.display_width
        header_height = layout.header_height
        draw.rectangle((0, 0, width, header_height), fill=1)
        current_feed = UNKNOWN_FEED_TITLE
        if 0 <= feed_idx < len(self.rss_feeds):
            current_feed = self.rss_feeds[feed_idx]["title"]
        draw.text((2, 1), current_feed, font=self.TITLE_FONT, fill=0)
        current_time = time.strftime("%H:%M")
        time_width = self.get_text_width(current_time, self.TITLE_FONT)
        draw.text((width - time_width - 3, 1), current_time, font=self.TITLE_FONT, fill=0)
        draw.line([(0, header_height), (width, header_height)], fill=1)
        content_y = header_height + layout.header_content_padding_y
        return current_feed, content_y

    # ローディング状態を描画する
    def _draw_loading(self, draw: ImageDraw.ImageDraw) -> None:
        layout = self.layout_settings
        width = layout.display_width
        height = layout.display_height
        self.loading_effect -= 1
        message = LOADING_MESSAGE
        if self.loading_effect % 2 == 0:
            msg_width = self.get_text_width(message, self.FONT)
            draw.text(((width - msg_width) // 2, height // 2 - 6), message, font=self.FONT, fill=1)

        bar_count = layout.loading_bar_count
        segment_width = layout.loading_segment_width
        for i in range(bar_count):
            segment_x = ((self.loading_effect + i) % (width // segment_width)) * segment_width
            draw.rectangle((segment_x, height - 8, segment_x + segment_width - 2, height - 2), fill=1)

    # トランジション描画を行う
    def _draw_transition(
        self,
        draw: ImageDraw.ImageDraw,
        news_items: Dict[int, List[FeedItem]],
        content_y: int,
        feed_idx: int,
        item_idx: int,
        prev_feed_idx: int,
        prev_item_idx: int,
    ) -> None:
        width = self.layout_settings.display_width
        self.transition_effect -= self.layout_settings.transition_frame_step
        progress = self.transition_effect / self.config.transition_frames
        offset = int(width * progress * self.transition_direction)
        if (
            news_items
            and feed_idx in news_items
            and 0 <= item_idx < len(news_items[feed_idx])
        ):
            item = news_items[feed_idx][item_idx]
            self.draw_article_content(draw, item, 2 + offset, content_y)
            if (
                prev_feed_idx in news_items
                and news_items[prev_feed_idx]
                and 0 <= prev_item_idx < len(news_items[prev_feed_idx])
            ):
                prev_item = news_items[prev_feed_idx][prev_item_idx]
                next_x = 2 + width * (-self.transition_direction) + offset
                self.draw_article_content(draw, prev_item, next_x, content_y)

    # 記事描画を行う
    def _draw_article(
        self,
        draw: ImageDraw.ImageDraw,
        news_items: Dict[int, List[FeedItem]],
        content_y: int,
        feed_idx: int,
        item_idx: int,
    ) -> bool:
        if news_items and feed_idx in news_items and 0 <= item_idx < len(news_items[feed_idx]):
            item = news_items[feed_idx][item_idx]
            self.draw_article_content(draw, item, 2, content_y)
            return True
        return False

    # 空表示を描画する
    def _draw_empty_state(self, draw: ImageDraw.ImageDraw) -> None:
        message = NO_NEWS_MESSAGE
        msg_width = self.get_text_width(message, self.FONT)
        width = self.layout_settings.display_width
        height = self.layout_settings.display_height
        draw.text(((width - msg_width) // 2, height // 2 - 6), message, font=self.FONT, fill=1)

    # 現在のRSS記事内容を描画してImageを返す
    # 現在の表示内容を描画して画像を返す
    def draw_rss_screen(self) -> Image.Image:
        layout = self.layout_settings
        image = Image.new("1", (layout.display_width, layout.display_height))
        draw = ImageDraw.Draw(image)

        with self._state_lock:
            news_items = self.news_items
            feed_idx = self.current_feed_index
            item_idx = self.current_item_index
            prev_feed_idx = self._prev_feed_index
            prev_item_idx = self._prev_item_index

        # ヘッダ部分の描画
        current_feed, content_y = self._draw_header(draw, feed_idx)

        # 以下、ローディング／トランジション／通常描画
        if self.loading_effect > 0:
            self._draw_loading(draw)

        # トランジション中：記事を横スクロールで切替
        elif self.transition_effect > 0:
            self._draw_transition(
                draw,
                news_items,
                content_y,
                feed_idx,
                item_idx,
                prev_feed_idx,
                prev_item_idx,
            )

        # 通常記事表示
        elif self._draw_article(draw, news_items, content_y, feed_idx, item_idx):
            pass

        # ニュースが存在しない場合のメッセージ
        else:
            self._draw_empty_state(draw)

        # フィード切替通知
        if time.monotonic() - self.feed_switch_time < 2.0:
            self.draw_feed_notification(draw, current_feed)

        return image

# 4) GPIO処理・制御ロジック
    # 次のRSSフィードへ切替
    # 次のフィードへ切り替える
    def switch_feed(self):
        with self._state_lock:
            prev_feed = self.current_feed_index
            prev_item = self.current_item_index
            self.current_feed_index = (self.current_feed_index + 1) % len(self.rss_feeds)
            self.current_item_index = 0
            self._prev_feed_index = prev_feed
            self._prev_item_index = prev_item
            self.feed_switch_time = time.monotonic()
            keep_link = ""
            if (
                self.news_items
                and self.current_feed_index in self.news_items
                and self.news_items[self.current_feed_index]
            ):
                keep_link = self.news_items[self.current_feed_index][
                    self.current_item_index
                ].get("link", "")
            self._reset_article_state(
                transition_direction=-1,
                keep_feed_idx=self.current_feed_index,
                keep_item_idx=self.current_item_index,
                keep_link=keep_link,
            )
        self.log.info(f"Feed switched -> {self.rss_feeds[self.current_feed_index]['title']}")

    # 次の記事へ
    # 次の記事へ進める
    def move_to_next_article(self):
        with self._state_lock:
            if not self.news_items or self.current_feed_index not in self.news_items or not self.news_items[self.current_feed_index]:
                return
            prev_feed = self.current_feed_index
            prev_item = self.current_item_index
            if self.current_item_index < len(self.news_items[self.current_feed_index]) - 1:
                self.current_item_index += 1
            else:
                self.current_item_index = 0
            self._prev_feed_index = prev_feed
            self._prev_item_index = prev_item
            keep_link = self.news_items[self.current_feed_index][self.current_item_index].get(
                "link",
                "",
            )
            self._reset_article_state(
                transition_direction=-1,
                keep_feed_idx=self.current_feed_index,
                keep_item_idx=self.current_item_index,
                keep_link=keep_link,
            )

    # 前の記事へ（関数の呼び出しが掛かってないので、必要に応じてGPIOボタンなどに割り当てるなどをしてください）
    # 前の記事へ戻す
    def move_to_prev_article(self):
        with self._state_lock:
            if not self.news_items or self.current_feed_index not in self.news_items or not self.news_items[self.current_feed_index]:
                return
            prev_feed = self.current_feed_index
            prev_item = self.current_item_index
            if self.current_item_index > 0:
                self.current_item_index -= 1
            else:
                self.current_item_index = len(self.news_items[self.current_feed_index]) - 1
            self._prev_feed_index = prev_feed
            self._prev_item_index = prev_item
            keep_link = self.news_items[self.current_feed_index][self.current_item_index].get(
                "link",
                "",
            )
            self._reset_article_state(
                transition_direction=1,
                keep_feed_idx=self.current_feed_index,
                keep_item_idx=self.current_item_index,
                keep_link=keep_link,
            )


    # 説明文スクロール位置を更新する
    # 説明文のスクロール位置を更新する
    def update_scroll_position(self) -> None:
        """
        自動スクロールが有効な場合のみ self.scroll_position を増加させる。
        """
        if self.transition_effect > 0:
            return

        # 記事と経過時間の取得（ロック下）
        with self._state_lock:
            if (not self.news_items) or (self.current_feed_index not in self.news_items):
                return
            if not self.news_items[self.current_feed_index]:
                return
            feed_idx = self.current_feed_index
            item_idx = self.current_item_index
            if item_idx < 0 or item_idx >= len(self.news_items[feed_idx]):
                self.log.warning(
                    "Detected stale item index (feed=%d item=%d); resetting to 0",
                    feed_idx,
                    item_idx,
                )
                self.current_item_index = 0
                self._reset_article_state(transition_direction=-1)
                return
            item = self.news_items[feed_idx][item_idx]
            current_time = time.monotonic()
            elapsed_time = current_time - self.article_start_time

            # 表示開始直後は一時停止（pause_at_start 秒）
            if self.auto_scroll_paused:
                if elapsed_time >= self.config.pause_at_start:
                    self.auto_scroll_paused = False
                    self._scroll_ease_elapsed = 0.0
                    self._last_scroll_time = current_time
                return

            # 説明文の幅を計測
            desc = item["description"].replace("\n", " ").strip()
            cache_key = (feed_idx, item.get("link", ""), item_idx)
            desc_width = self._desc_width_cache.get(cache_key)
            if desc_width is None:
                desc_width = self.get_text_width(desc, self.FONT) if desc else 0
                self._desc_width_cache[cache_key] = desc_width

            # 短文（スクロール不要）は article_display_time 経過で次記事へ
            short_text = desc_width <= (self.layout_settings.display_width - 4)
            ready_to_advance = elapsed_time >= self.config.article_display_time if short_text else False

        if short_text:
            if ready_to_advance:
                self.move_to_next_article()
            return

        now = time.monotonic()
        delta_time = (
            now - self._last_scroll_time
            if self._last_scroll_time
            else self.config.main_update_interval
        )
        self._last_scroll_time = now
        self._scroll_ease_elapsed = min(
            self._scroll_ease_elapsed + delta_time,
            self.animation_settings.easing_duration,
        )
        progress = (
            self._scroll_ease_elapsed / self.animation_settings.easing_duration
            if self.animation_settings.easing_duration > 0
            else 1.0
        )
        ease = self._ease_out_cubic(progress)
        frame_factor = (
            delta_time / self.config.main_update_interval if self.config.main_update_interval else 1.0
        )
        increment = self.animation_settings.scroll_speed * ease * frame_factor

        with self._state_lock:
            self.scroll_position += increment
            tail_margin_px = self.animation_settings.tail_margin_px
            reached_tail = self.scroll_position > (
                desc_width + self.layout_settings.display_width + tail_margin_px
            )

        if reached_tail:
            self.move_to_next_article()

    @staticmethod
    # スクロール用イージングを計算する
    def _ease_out_cubic(t: float) -> float:
        t = max(0.0, min(1.0, t))
        return 1 - (1 - t) ** 3

    # GPIOポーリング（クリック/ダブルクリック処理）
    # GPIO入力をポーリングしてクリックを判定する
    async def _gpio_polling_loop(self) -> None:
        GPIO = self._gpio_module
        if GPIO is None:
            self.log.debug("GPIO module not available, polling loop not started")
            return

        self.log.info("GPIO polling task started")
        while not self._stop_event.is_set():
            try:
                state = GPIO.input(BUTTON_FEED)
                now = time.monotonic()
                if self._prev_button_state == 1 and state == 0:
                    if now - self._last_edge_time < self.config.debounce_sec:
                        self._prev_button_state = state
                        await asyncio.sleep(self.config.gpio_poll_interval)
                        continue
                    self._last_edge_time = now
                    self._press_start_time = now
                    self._long_press_handled = False

                if state == 0 and not self._long_press_handled:
                    if now - self._press_start_time >= self.config.long_press_interval:
                        self._set_display_enabled(not self._display_enabled)
                        self._long_press_handled = True
                        self._click_count = 0
                        self._last_press_time = 0.0

                if self._prev_button_state == 0 and state == 1:
                    if now - self._last_edge_time < self.config.debounce_sec:
                        self._prev_button_state = state
                        await asyncio.sleep(self.config.gpio_poll_interval)
                        continue
                    self._last_edge_time = now
                    if not self._long_press_handled:
                        if now - self._last_press_time <= self.config.double_click_interval:
                            self._click_count += 1
                        else:
                            self._click_count = 1
                        self._last_press_time = now
                    else:
                        self._click_count = 0

                if self._click_count > 0 and (now - self._last_press_time) > self.config.double_click_interval:
                    if self._click_count == 1:
                        self.move_to_next_article()
                        self.log.info("[GPIO] Single click -> next article")
                    else:
                        self.switch_feed()
                        self.log.info("[GPIO] Double click -> switch feed")
                    self._click_count = 0

                self._prev_button_state = state
                await asyncio.sleep(self.config.gpio_poll_interval)
            except asyncio.CancelledError:
                raise
            except Exception as e:
                self.log.error(f"GPIO polling error: {e}")
                await asyncio.sleep(0.1)

    # 時間帯表示制御
    # 表示時間帯かどうかを判定する
    def is_display_time(self) -> bool:
        now = time.localtime()
        now_hm = now.tm_hour * 60 + now.tm_min
        start_hm = DISPLAY_TIME_START[0] * 60 + DISPLAY_TIME_START[1]
        end_hm = DISPLAY_TIME_END[0] * 60 + DISPLAY_TIME_END[1]
        if start_hm <= end_hm:
            return start_hm <= now_hm < end_hm
        return now_hm >= start_hm or now_hm < end_hm

    # シグナル／終了処理
    # 終了シグナルを処理して安全に停止する
    def _signal_handler(self, sig, frame) -> None:
        self.log.info("Exiting...")
        self._stop_event.set()

    # 終了時のクリーンアップ処理
    def _cleanup(self) -> None:
        try:
            import RPi.GPIO as GPIO
            GPIO.cleanup()
        except Exception:
            pass
        if self.display:
            layout = self.layout_settings
            blank = Image.new("1", (layout.display_width, layout.display_height), 0)
            try:
                self.display.display(blank)
            except Exception:
                pass

    def _set_display_enabled(self, enabled: bool) -> None:
        if self._display_enabled == enabled:
            return
        self._display_enabled = enabled
        self._display_blank_drawn = False
        state = "on" if enabled else "off"
        self.log.info("Display toggled %s", state)

    def _draw_blank_display(self) -> None:
        if not self.display or self._display_blank_drawn:
            return
        layout = self.layout_settings
        blank = Image.new("1", (layout.display_width, layout.display_height), 0)
        try:
            self.display.display(blank)
            self._display_blank_drawn = True
        except Exception:
            pass

# 5) メインループ
    # メインループ
    # 非同期タスクを起動してメインループを実行する
    async def run(self) -> None:
        if self._gpio_available:
            self._background_tasks.append(asyncio.create_task(self._gpio_polling_loop()))

        if not await self.fetch_rss_feed():
            self.log.warning("First RSS fetch failed after retries")
            self._apply_cache_to_news()

        try:
            await self._main_loop()
        finally:
            for task in self._background_tasks:
                task.cancel()
                with contextlib.suppress(asyncio.CancelledError):
                    await task
            self._cleanup()

    # メインループで更新処理を繰り返す
    async def _main_loop(self) -> None:
        while not self._stop_event.is_set():
            now = time.monotonic()

            # 表示時間外は待機してループを続ける
            if await self._handle_display_window():
                continue

            # RSS更新・描画・自動切替の処理を実行
            await self._handle_rss_refresh(now)
            self._handle_display_update(now)
            self._handle_auto_feed_switch(now)

            await asyncio.sleep(0.01)

    # 表示更新のタイミングを管理する
    def _handle_display_update(self, now: float) -> None:
        if now - self._last_main_update < self.config.main_update_interval:
            return

        if not self._display_enabled:
            self._draw_blank_display()
            self._last_main_update = now
            return

        self.update_scroll_position()
        image = self.draw_rss_screen()
        try:
            self.display.display(image)
            self._display_blank_drawn = False
        except Exception as e:
            self.log.warning(f"OLED display error: {e}")
        self._last_main_update = now

    # 自動フィード切替を管理する
    def _handle_auto_feed_switch(self, now: float) -> None:
        if now - self._last_feed_switch_check < self.config.feed_switch_interval:
            return

        try:
            self.switch_feed()
        except Exception as e:
            self.log.warning(f"Auto feed switch error: {e}")
        finally:
            self._last_feed_switch_check = now

    # RSS再取得のタイミングを管理する
    async def _handle_rss_refresh(self, now: float) -> None:
        if now - self._last_rss_refresh_attempt < self.config.rss_update_interval:
            return

        if await self.fetch_rss_feed():
            self.log.info("Feeds refreshed")

    # 表示時間外の待機処理を行う
    async def _handle_display_window(self) -> bool:
        if not self._display_enabled:
            self._draw_blank_display()
            await asyncio.sleep(self.config.sleep_interval)
            current = time.monotonic()
            self._last_main_update = current
            self._last_scroll_time = current
            self._last_feed_switch_check = current
            return True

        if self.is_display_time():
            return False

        self._draw_blank_display()

        await asyncio.sleep(self.config.sleep_interval)
        current = time.monotonic()
        self._last_main_update = current
        self._last_scroll_time = current
        self._last_feed_switch_check = current
        return True

# 6) エントリーポイント
# アプリのエントリーポイント
async def main() -> None:
    app = RSSReaderApp()
    try:
        app.initialize()
        await app.run()
    except KeyboardInterrupt:
        app._signal_handler(None, None)
        app._cleanup()
    except Exception as e:
        # ここは最上位キャッチ。ログして安全終了
        logging.getLogger("rss_oled").error(f"Fatal error: {e}")
        app._signal_handler(None, None)
        app._cleanup()


if __name__ == "__main__":
    asyncio.run(main())
