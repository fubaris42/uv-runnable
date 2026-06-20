# /// script
# requires-python = ">=3.10"
# dependencies = [
#     "PySide6>=6.5.0",
#     "pymupdf>=1.24.0",
#     "winrt-Windows.Media.Ocr",
#     "winrt.windows.foundation",
#     "winrt-Windows.Storage.Streams",
#     "winrt-Windows.Graphics.Imaging",
#     "winrt-Windows.Security.Cryptography",
#     "pillow",
#     "pyahocorasick>=2.0.0",
#     "pillow-heif",
# ]
# ///

"""
PDF & Image Multi-Query Extractor (With Manual Review, Advanced Candidate Sorting, & Query Importer)
"""

from __future__ import annotations

import asyncio
import concurrent.futures
import csv
import hashlib
import io
import logging
import logging.handlers
import multiprocessing
import os
import re
import shutil
import sqlite3
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

import ahocorasick
import fitz  # PyMuPDF
import pillow_heif
from PIL import Image, ImageOps

from PySide6.QtCore import QEvent, QItemSelectionModel, QModelIndex, Qt, QThread, Signal
from PySide6.QtGui import (
    QBrush,
    QColor,
    QImage,
    QPixmap,
    QStandardItem,
    QStandardItemModel,
    QTransform,
)
from PySide6.QtWidgets import (
    QAbstractItemView,
    QApplication,
    QFileDialog,
    QGraphicsScene,
    QGraphicsView,
    QHBoxLayout,
    QLabel,
    QLineEdit,
    QMessageBox,
    QProgressBar,
    QPushButton,
    QSplitter,
    QTabWidget,
    QTableWidget,
    QTableWidgetItem,
    QTextEdit,
    QTreeView,
    QVBoxLayout,
    QWidget,
)

pillow_heif.register_heif_opener()

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------
OCR_DPI = 200
OCR_SAMPLE_PAGES = 5
OCR_SAMPLE_THRESH = 200
CONTENT_HASH_BYTES = 1_048_576
LOG_MAX_BYTES = 5_242_880
LOG_BACKUP_COUNT = 3

IMAGE_EXTENSIONS = {".jpg", ".jpeg", ".png", ".heif"}
SUPPORTED_EXTENSIONS = {".pdf"} | IMAGE_EXTENSIONS

log = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Logging
# ---------------------------------------------------------------------------


def _setup_logging(log_path: str | None = None) -> None:
    root = logging.getLogger()
    if root.handlers:
        return
    root.setLevel(logging.DEBUG)
    fmt = logging.Formatter(
        "%(asctime)s [%(levelname)s] %(name)s: %(message)s", datefmt="%H:%M:%S"
    )
    sh = logging.StreamHandler(sys.stderr)
    sh.setLevel(logging.INFO)
    sh.setFormatter(fmt)
    root.addHandler(sh)
    if log_path:
        fh = logging.handlers.RotatingFileHandler(
            log_path,
            maxBytes=LOG_MAX_BYTES,
            backupCount=LOG_BACKUP_COUNT,
            encoding="utf-8",
        )
        fh.setLevel(logging.DEBUG)
        fh.setFormatter(fmt)
        root.addHandler(fh)


# ---------------------------------------------------------------------------
# Path utilities
# ---------------------------------------------------------------------------


def _unc(path: str) -> str:
    """Return a \\\\?\\ -prefixed absolute path on Windows to bypass MAX_PATH."""
    if sys.platform != "win32":
        return path
    p = os.path.abspath(path)
    return p if p.startswith("\\\\?\\") else "\\\\?\\" + p


def safe_folder_name(name: str) -> str:
    return "".join(c for c in name if c.isalnum() or c in (" ", "_", "-")).strip()


# ---------------------------------------------------------------------------
# Content hashing
# ---------------------------------------------------------------------------


def content_hash(path: str) -> str:
    try:
        stat = os.stat(path)
        h = hashlib.blake2b(digest_size=16)
        h.update(f"{stat.st_size}:{stat.st_mtime_ns}".encode())
        with open(path, "rb") as fh:
            h.update(fh.read(CONTENT_HASH_BYTES))
        return h.hexdigest()
    except OSError:
        return hashlib.blake2b(path.encode(), digest_size=16).hexdigest()


# ---------------------------------------------------------------------------
# Aho-Corasick helpers
# ---------------------------------------------------------------------------


def build_automaton(
    queries: list[str],
) -> tuple[ahocorasick.Automaton, dict[str, set[int]]]:
    """Return a compiled automaton and a token→query-index map."""
    token_qset: dict[str, set[int]] = defaultdict(set)
    for qi, q in enumerate(queries):
        for part in (w.lower() for w in q.split() if len(w) > 1):
            token_qset[part].add(qi)

    A = ahocorasick.Automaton()
    for token, qset in token_qset.items():
        A.add_word(token, (token, qset))
    A.make_automaton()
    return A, token_qset


# ---------------------------------------------------------------------------
# OCR cache (SQLite, per-input-directory)
# ---------------------------------------------------------------------------

_ocr_cache_conn: sqlite3.Connection | None = None
_ocr_cache_path: str = ""

_CREATE_CACHE_TABLE = """
    CREATE TABLE IF NOT EXISTS ocr_cache (
        content_hash TEXT NOT NULL,
        page_num     INTEGER NOT NULL,
        text         TEXT NOT NULL,
        timestamp    REAL NOT NULL,
        PRIMARY KEY (content_hash, page_num)
    )
"""


def _get_cache_conn(db_path: str) -> sqlite3.Connection:
    global _ocr_cache_conn, _ocr_cache_path
    if _ocr_cache_conn is None or _ocr_cache_path != db_path:
        _ocr_cache_conn = sqlite3.connect(db_path, check_same_thread=False)
        _ocr_cache_conn.execute("PRAGMA journal_mode=WAL")
        _ocr_cache_conn.execute("PRAGMA synchronous=NORMAL")
        _ocr_cache_conn.execute(_CREATE_CACHE_TABLE)
        _ocr_cache_conn.commit()
        _ocr_cache_path = db_path
    return _ocr_cache_conn


def cache_load(db_path: str, file_hash: str, total_pages: int) -> dict[int, str] | None:
    try:
        con = _get_cache_conn(db_path)
        rows = con.execute(
            "SELECT page_num, text FROM ocr_cache WHERE content_hash=? ORDER BY page_num",
            (file_hash,),
        ).fetchall()
        if len(rows) == total_pages:
            con.execute(
                "UPDATE ocr_cache SET timestamp=? WHERE content_hash=?",
                (time.time(), file_hash),
            )
            con.commit()
            return {r[0]: r[1] for r in rows}
    except Exception:
        pass
    return None


def cache_save(db_path: str, file_hash: str, page_texts: dict[int, str]) -> None:
    try:
        con = _get_cache_conn(db_path)
        now = time.time()
        con.executemany(
            "INSERT OR REPLACE INTO ocr_cache (content_hash, page_num, text, timestamp) VALUES (?,?,?,?)",
            [(file_hash, pn, txt, now) for pn, txt in page_texts.items()],
        )
        con.commit()
    except Exception:
        pass


# ---------------------------------------------------------------------------
# Windows OCR pipeline  (worker-process scope – lazy globals reset per spawn)
# ---------------------------------------------------------------------------

_ocr_loop: asyncio.AbstractEventLoop | None = None
_ocr_engine: Any = None


def _ocr_engine_lazy() -> Any:
    global _ocr_engine
    if _ocr_engine is None:
        from winrt.windows.media.ocr import OcrEngine  # type: ignore[import]

        _ocr_engine = OcrEngine.try_create_from_user_profile_languages()
    return _ocr_engine


def _ocr_loop_lazy() -> asyncio.AbstractEventLoop:
    global _ocr_loop
    if _ocr_loop is None or _ocr_loop.is_closed():
        _ocr_loop = asyncio.new_event_loop()
        asyncio.set_event_loop(_ocr_loop)
    return _ocr_loop


async def _decode_bitmap(pil_img: Image.Image) -> Any:
    from winrt.windows.graphics.imaging import BitmapDecoder  # type: ignore[import]
    from winrt.windows.security.cryptography import CryptographicBuffer  # type: ignore[import]
    from winrt.windows.storage.streams import InMemoryRandomAccessStream  # type: ignore[import]

    buf = io.BytesIO()
    pil_img.save(buf, format="PNG")
    winrt_buf = CryptographicBuffer.create_from_byte_array(buf.getvalue())
    stream = InMemoryRandomAccessStream()
    await stream.write_async(winrt_buf)
    stream.seek(0)
    decoder = await BitmapDecoder.create_async(stream)
    return await decoder.get_software_bitmap_async()


async def _ocr_pipeline_async(images: list[Image.Image]) -> list[str]:
    engine = _ocr_engine_lazy()
    if not engine:
        return [""] * len(images)
    try:
        bitmaps = await asyncio.gather(*(_decode_bitmap(img) for img in images))
    except Exception:
        return [""] * len(images)
    results: list[str] = []
    for bitmap in bitmaps:
        try:
            result = await engine.recognize_async(bitmap)
            results.append(result.text if result else "")
        except Exception:
            results.append("")
    return results


def ocr_all_pages(images: list[Image.Image]) -> list[str]:
    if not images:
        return []
    return _ocr_loop_lazy().run_until_complete(_ocr_pipeline_async(images))


def render_page(page: fitz.Page, dpi: int = OCR_DPI) -> Image.Image:
    pix = page.get_pixmap(dpi=dpi)
    return Image.frombytes("RGB", [pix.width, pix.height], pix.samples)


# ---------------------------------------------------------------------------
# Core per-file processing  (runs in worker processes)
# ---------------------------------------------------------------------------


def process_file(
    file_path: str,
    queries: list[str],
    output_dir: str,
    cache_db: str,
    log_path: str,
) -> dict[str, Any]:
    _setup_logging(log_path)

    A, _token_qset = build_automaton(queries)

    p_obj = Path(file_path)
    file_ext = p_obj.suffix.lower()
    file_hash = content_hash(file_path)
    is_pdf = file_ext == ".pdf"

    page_texts: dict[int, str] = {}

    # ---- extract text (or OCR) ----------------------------------------
    if is_pdf:
        try:
            doc = fitz.open(_unc(file_path))
        except Exception as exc:
            log.error("Cannot open PDF %s: %s", file_path, exc)
            return {"counts": {}, "review_data": []}

        total_pages = len(doc)
        cached = cache_load(cache_db, file_hash, total_pages)
        if cached is not None:
            page_texts = cached
            doc.close()
        else:
            sample_n = min(OCR_SAMPLE_PAGES, total_pages)
            sample_chars = sum(len(doc[i].get_text() or "") for i in range(sample_n))
            if sample_chars >= OCR_SAMPLE_THRESH:
                for i in range(total_pages):
                    page_texts[i] = doc[i].get_text() or ""
                doc.close()
            else:
                images = [render_page(doc[i]) for i in range(total_pages)]
                doc.close()
                results = ocr_all_pages(images)
                page_texts = {i: t for i, t in enumerate(results)}
                cache_save(cache_db, file_hash, page_texts)
    else:
        total_pages = 1
        cached = cache_load(cache_db, file_hash, total_pages)
        if cached is not None:
            page_texts = cached
        else:
            try:
                with Image.open(file_path) as img:
                    img_corrected = ImageOps.exif_transpose(img)
                    results = ocr_all_pages([img_corrected.convert("RGB")])
                    page_texts = {0: results[0] if results else ""}
                    cache_save(cache_db, file_hash, page_texts)
            except Exception as exc:
                log.error("Cannot open image %s: %s", file_path, exc)
                return {"counts": {}, "review_data": []}

    # ---- match queries against extracted text --------------------------
    match_counts: dict[str, int] = {q: 0 for q in queries}
    review_items: list[dict] = []

    for page_idx, raw_text in page_texts.items():
        clean = raw_text.lower().replace(" ", "")

        for qi, query in enumerate(queries):
            tokens = [w.lower() for w in query.split() if len(w) > 1]
            found_tokens: set[str] = set()

            for _, (token, qset) in A.iter(clean):
                if qi in qset:
                    found_tokens.add(token)

            missing_tokens = [t for t in tokens if t not in found_tokens]
            is_approved = not missing_tokens

            # Include fully-approved hits AND partial candidates (≥1 token hit, multi-token query)
            if is_approved or (found_tokens and len(tokens) > 1):
                if is_approved:
                    match_counts[query] += 1

                review_items.append(
                    {
                        "id": f"{file_hash}_{page_idx}_{qi}",
                        "query": query,
                        "file_path": file_path,
                        "file_hash": file_hash,
                        "page_idx": page_idx,
                        "pre_approved": is_approved,
                        "missing_words": missing_tokens,
                        "text_content": raw_text,
                    }
                )

    # ---- write approved pages to output folder -------------------------
    approved_by_query: dict[str, list[int]] = defaultdict(list)
    for item in review_items:
        if item["pre_approved"]:
            approved_by_query[item["query"]].append(item["page_idx"])

    if is_pdf and approved_by_query:
        try:
            doc = fitz.open(_unc(file_path))
            for q, pages in approved_by_query.items():
                folder = Path(output_dir) / safe_folder_name(q)
                folder.mkdir(parents=True, exist_ok=True)
                out_doc = fitz.open()
                for pn in pages:
                    out_doc.insert_pdf(doc, from_page=pn, to_page=pn)
                out_doc.save(
                    _unc(str(folder / f"{p_obj.stem}_{file_hash}.pdf")),
                    garbage=4,
                    deflate=True,
                )
                out_doc.close()
            doc.close()
        except Exception as exc:
            log.error("Failed to write PDF output for %s: %s", file_path, exc)
    elif not is_pdf:
        for q, pages in approved_by_query.items():
            if pages:  # images are single-page; just copy once
                folder = Path(output_dir) / safe_folder_name(q)
                folder.mkdir(parents=True, exist_ok=True)
                shutil.copy2(file_path, folder / f"{p_obj.stem}_{file_hash}{file_ext}")

    return {"counts": match_counts, "review_data": review_items}


# ---------------------------------------------------------------------------
# Background processing thread
# ---------------------------------------------------------------------------


class ProcessingWorker(QThread):
    progress_signal = Signal(int, int, str)
    finished_signal = Signal(dict, list)
    error_signal = Signal(str)

    def __init__(
        self,
        input_dir: str,
        queries: list[str],
        output_dir: str,
        max_workers: int | None = None,
    ) -> None:
        super().__init__()
        self.input_dir = input_dir
        self.queries = queries
        self.output_dir = output_dir
        self.max_workers = max_workers or max(1, (os.cpu_count() or 4) - 1)
        self._cancel = False

    def cancel(self) -> None:
        self._cancel = True

    def run(self) -> None:
        all_files = [
            str(p)
            for p in Path(self.input_dir).rglob("*")
            if p.suffix.lower() in SUPPORTED_EXTENSIONS
        ]
        if not all_files:
            self.error_signal.emit("No supported assets found inside target folder.")
            return

        total = len(all_files)
        cache_db = _unc(os.path.join(self.input_dir, ".ocr_cache.db"))
        log_path = _unc(os.path.join(self.output_dir, "extractor.log"))
        _setup_logging(log_path)

        aggregate_counts: dict[str, int] = {q: 0 for q in self.queries}
        master_review_data: list[dict] = []

        ctx = multiprocessing.get_context("spawn")
        with concurrent.futures.ProcessPoolExecutor(
            max_workers=self.max_workers, mp_context=ctx
        ) as executor:
            future_map = {
                executor.submit(
                    process_file, f, self.queries, self.output_dir, cache_db, log_path
                ): f
                for f in all_files
            }

            done = 0
            for future in concurrent.futures.as_completed(future_map):
                if self._cancel:
                    executor.shutdown(wait=False, cancel_futures=True)
                    self.error_signal.emit("Run cancelled.")
                    return
                f_path = future_map[future]
                done += 1
                try:
                    res = future.result()
                    for q, c in res["counts"].items():
                        aggregate_counts[q] += c
                    master_review_data.extend(res["review_data"])
                    self.progress_signal.emit(
                        done, total, f"({done}/{total}) {Path(f_path).name}"
                    )
                except Exception as exc:
                    self.progress_signal.emit(
                        done, total, f"[FAIL] {Path(f_path).name}: {exc}"
                    )

        self._write_reports(aggregate_counts, master_review_data)
        self.finished_signal.emit(aggregate_counts, master_review_data)

    def _write_reports(self, counts: dict[str, int], review_data: list[dict]) -> None:
        try:
            out_path = Path(self.output_dir)
            out_path.mkdir(parents=True, exist_ok=True)

            with open(out_path / "report.csv", "w", newline="", encoding="utf-8") as f:
                writer = csv.writer(f)
                writer.writerow(["Query", "Total Approved Hits"])
                writer.writerows(counts.items())

            conn = sqlite3.connect(str(out_path / "extraction_history.db"))
            cursor = conn.cursor()
            cursor.execute(
                "CREATE TABLE IF NOT EXISTS summary_metrics (query TEXT PRIMARY KEY, hits INTEGER)"
            )
            cursor.execute("""
                CREATE TABLE IF NOT EXISTS candidates_log (
                    id TEXT PRIMARY KEY, query TEXT, file_path TEXT,
                    page_index INTEGER, pre_approved INTEGER
                )
            """)
            cursor.executemany(
                "INSERT OR REPLACE INTO summary_metrics VALUES (?,?)",
                list(counts.items()),
            )
            cursor.executemany(
                "INSERT OR REPLACE INTO candidates_log VALUES (?,?,?,?,?)",
                [
                    (
                        item["id"],
                        item["query"],
                        item["file_path"],
                        item["page_idx"],
                        1 if item["pre_approved"] else 0,
                    )
                    for item in review_data
                ],
            )
            conn.commit()
            conn.close()
        except Exception as exc:
            log.error("Failed to write output reports: %s", exc)


# ---------------------------------------------------------------------------
# Main application window
# ---------------------------------------------------------------------------


class ExtractorApp(QWidget):
    def __init__(self) -> None:
        super().__init__()
        self._worker: ProcessingWorker | None = None
        self.review_records: list[dict] = []
        self.current_review_item: dict | None = None
        self._live_counts: dict[str, int] = {}
        self.zoom_factor = 1.0
        self.current_rotation = 0
        self.view_text_mode = False
        self._init_ui()

    # ------------------------------------------------------------------
    # UI construction
    # ------------------------------------------------------------------

    def _init_ui(self) -> None:
        self.setWindowTitle("PDF & Image Multi-Query Extractor & Review HIL Pipeline")
        self.setMinimumSize(1150, 700)

        window_layout = QVBoxLayout(self)
        self.tabs = QTabWidget()
        window_layout.addWidget(self.tabs)

        self.tabs.addTab(self._build_dashboard_tab(), "Data Extraction Engine")
        self.tabs.addTab(self._build_review_tab(), "Manual Review Panel")

    def _build_dashboard_tab(self) -> QWidget:
        tab = QWidget()
        dash = QHBoxLayout(tab)
        dash.setSpacing(15)

        # -- left panel --------------------------------------------------
        left = QVBoxLayout()

        row_in = QHBoxLayout()
        self.input_edit = QLineEdit(placeholderText="Input folder...", readOnly=True)
        btn_in = QPushButton("Browse Input")
        btn_in.clicked.connect(self._browse_input)
        row_in.addWidget(self.input_edit)
        row_in.addWidget(btn_in)
        left.addLayout(row_in)

        row_out = QHBoxLayout()
        self.output_edit = QLineEdit(
            placeholderText="Output destination...", readOnly=True
        )
        btn_out = QPushButton("Browse Output")
        btn_out.clicked.connect(self._browse_output)
        row_out.addWidget(self.output_edit)
        row_out.addWidget(btn_out)
        left.addLayout(row_out)

        left.addWidget(QLabel("Queries:"))
        self.query_edit = QTextEdit(placeholderText="Queries (one per line)...")
        left.addWidget(self.query_edit, stretch=1)

        btn_import = QPushButton("Import Queries from .txt File")
        btn_import.clicked.connect(self._import_txt)
        left.addWidget(btn_import)

        self.status_label = QLabel("Status: Ready")
        self.progress_bar = QProgressBar()
        left.addWidget(self.status_label)
        left.addWidget(self.progress_bar)

        row_act = QHBoxLayout()
        self.btn_run = QPushButton("Start Processing")
        self.btn_run.clicked.connect(self._start)
        self.btn_cancel = QPushButton("Cancel")
        self.btn_cancel.setEnabled(False)
        self.btn_cancel.clicked.connect(self._cancel)
        row_act.addWidget(self.btn_run)
        row_act.addWidget(self.btn_cancel)
        left.addLayout(row_act)

        # -- right panel -------------------------------------------------
        right = QVBoxLayout()
        self.result_table = QTableWidget(0, 2)
        self.result_table.setHorizontalHeaderLabels(["Query", "Hits"])
        self.result_table.horizontalHeader().setStretchLastSection(True)
        right.addWidget(QLabel("Metrics Overview"))
        right.addWidget(self.result_table)

        dash.addLayout(left, stretch=4)
        dash.addLayout(right, stretch=5)
        return tab

    def _build_review_tab(self) -> QWidget:
        self.tab_review = QWidget()
        layout = QHBoxLayout(self.tab_review)
        splitter = QSplitter(Qt.Horizontal)
        layout.addWidget(splitter)

        # -- left: tree panel --------------------------------------------
        left_w = QWidget()
        left_l = QVBoxLayout(left_w)

        search_row = QHBoxLayout()
        search_row.addWidget(QLabel("Filter Query:"))
        self.search_bar = QLineEdit(
            placeholderText="Type query to filter tree panel..."
        )
        self.search_bar.textChanged.connect(self._rebuild_review_tree)
        search_row.addWidget(self.search_bar)
        left_l.addLayout(search_row)

        tree_btn_row = QHBoxLayout()
        btn_expand = QPushButton("Expand All")
        btn_expand.clicked.connect(
            self.review_tree.expandAll if hasattr(self, "review_tree") else lambda: None
        )
        btn_collapse = QPushButton("Collapse All")
        btn_collapse.clicked.connect(
            self.review_tree.collapseAll
            if hasattr(self, "review_tree")
            else lambda: None
        )
        tree_btn_row.addWidget(btn_expand)
        tree_btn_row.addWidget(btn_collapse)
        left_l.addLayout(tree_btn_row)

        self.review_tree = QTreeView()
        self.tree_model = QStandardItemModel()
        self.tree_model.setHorizontalHeaderLabels(
            ["Query Elements / Page Index Hierarchy"]
        )
        self.review_tree.setModel(self.tree_model)
        self.review_tree.setSelectionMode(QAbstractItemView.ExtendedSelection)
        self.review_tree.setStyleSheet("""
QTreeView                   { outline: 0; }
QTreeView::item             { border: 0px solid transparent; }
QTreeView::item:hover       { background: rgba(70,130,200,0.45); color: white; }
QTreeView::item:selected    { background: rgba(70,130,200,0.70); color: white; }
QTreeView::item:selected:!focus { background: rgba(70,130,200,0.50); color: white; }
QTreeView::item:focus       { background: rgba(70,130,200,0.70); color: white;
                               border: 0px solid transparent; }
        """)
        self.review_tree.installEventFilter(self)
        self.review_tree.clicked.connect(self._activate_index)
        self.review_tree.selectionModel().currentChanged.connect(
            lambda cur, _prev: self._activate_index(cur)
        )

        # Wire the expand/collapse buttons now that self.review_tree exists
        btn_expand.clicked.disconnect()
        btn_collapse.clicked.disconnect()
        btn_expand.clicked.connect(self.review_tree.expandAll)
        btn_collapse.clicked.connect(self.review_tree.collapseAll)

        left_l.addWidget(QLabel("Extracted Targets / Candidates Tree View"))
        left_l.addWidget(self.review_tree)
        splitter.addWidget(left_w)

        # -- right: preview + controls -----------------------------------
        right_w = QWidget()
        right_l = QVBoxLayout(right_w)

        ctrl_row = QHBoxLayout()
        for label, fn in [
            ("Zoom In", lambda: self._adjust_zoom(1.2)),
            ("Zoom Out", lambda: self._adjust_zoom(0.8)),
            ("Rotate CCW", lambda: self._rotate(-90)),
            ("Rotate CW", lambda: self._rotate(90)),
        ]:
            btn = QPushButton(label)
            btn.clicked.connect(fn)
            ctrl_row.addWidget(btn)

        self.btn_toggle_view = QPushButton("Switch to Text Layer View")
        self.btn_toggle_view.clicked.connect(self._toggle_view_mode)
        ctrl_row.addWidget(self.btn_toggle_view)
        right_l.addLayout(ctrl_row)

        self.gfx_scene = QGraphicsScene()
        self.gfx_view = QGraphicsView(self.gfx_scene)
        self.text_preview = QTextEdit()
        self.text_preview.setReadOnly(True)
        self.text_preview.hide()
        right_l.addWidget(self.gfx_view, stretch=1)
        right_l.addWidget(self.text_preview, stretch=1)

        dec_row = QHBoxLayout()
        self.btn_approve = QPushButton("Approve Candidate Page")
        self.btn_approve.setStyleSheet(
            "background-color:#27ae60;color:white;font-weight:bold;padding:6px;"
        )
        self.btn_reject = QPushButton("Reject / Extirpate Page")
        self.btn_reject.setStyleSheet(
            "background-color:#c0392b;color:white;font-weight:bold;padding:6px;"
        )
        self.btn_approve.clicked.connect(self._approve_current_item)
        self.btn_reject.clicked.connect(self._reject_current_item)
        dec_row.addWidget(self.btn_approve)
        dec_row.addWidget(self.btn_reject)
        right_l.addLayout(dec_row)

        splitter.addWidget(right_w)
        splitter.setSizes([400, 750])
        return self.tab_review

    # ------------------------------------------------------------------
    # Directory / query helpers
    # ------------------------------------------------------------------

    def _browse_input(self) -> None:
        d = QFileDialog.getExistingDirectory(self, "Input")
        if d:
            self.input_edit.setText(d)

    def _browse_output(self) -> None:
        d = QFileDialog.getExistingDirectory(self, "Output")
        if d:
            self.output_edit.setText(d)

    def _import_txt(self) -> None:
        fp, _ = QFileDialog.getOpenFileName(
            self, "Open Query File", "", "Text Files (*.txt)"
        )
        if not fp:
            return
        try:
            with open(fp, encoding="utf-8", errors="ignore") as fh:
                lines = [
                    ln.strip()
                    for ln in fh
                    if ln.strip() and not ln.strip().startswith("[")
                ]
            self.query_edit.setPlainText("\n".join(lines))
            QMessageBox.information(self, "Imported", f"Loaded {len(lines)} queries.")
        except Exception as exc:
            QMessageBox.critical(self, "Error", f"Failed to read file:\n{exc}")

    # ------------------------------------------------------------------
    # Processing control
    # ------------------------------------------------------------------

    def _start(self) -> None:
        input_dir = self.input_edit.text().strip()
        output_dir = self.output_edit.text().strip()
        queries = [
            q.strip() for q in self.query_edit.toPlainText().splitlines() if q.strip()
        ]

        if not input_dir or not output_dir or not queries:
            QMessageBox.warning(
                self,
                "Configuration Check",
                "Ensure directories and queries are defined completely.",
            )
            return

        self.btn_run.setEnabled(False)
        self.btn_cancel.setEnabled(True)
        self.progress_bar.setRange(0, 0)

        self._worker = ProcessingWorker(input_dir, queries, output_dir)
        self._worker.progress_signal.connect(self._on_progress)
        self._worker.finished_signal.connect(self._on_finished)
        self._worker.error_signal.connect(self._on_error)
        self._worker.start()

    def _cancel(self) -> None:
        if self._worker:
            self._worker.cancel()

    def _on_progress(self, current: int, total: int, msg: str) -> None:
        if self.progress_bar.maximum() == 0:
            self.progress_bar.setRange(0, total)
        self.progress_bar.setValue(current)
        self.status_label.setText(msg)

    def _on_finished(self, counts: dict[str, int], review_data: list[dict]) -> None:
        self.btn_run.setEnabled(True)
        self.btn_cancel.setEnabled(False)
        self.progress_bar.setRange(0, 100)
        self.progress_bar.setValue(100)
        self.status_label.setText(
            "Batch run finished. Reports generated in destination output path."
        )

        self.review_records = review_data
        self._live_counts = dict(counts)

        self._refresh_metrics_table()
        self._rebuild_review_tree()
        self.tabs.setCurrentWidget(self.tab_review)

    def _on_error(self, msg: str) -> None:
        self.btn_run.setEnabled(True)
        self.btn_cancel.setEnabled(False)
        self.progress_bar.setRange(0, 100)
        self.progress_bar.setValue(0)
        self.status_label.setText(f"Error: {msg}")
        QMessageBox.warning(self, "Processing Error", msg)

    # ------------------------------------------------------------------
    # Metrics table  (majority-value highlighting)
    # ------------------------------------------------------------------

    def _refresh_metrics_table(self) -> None:
        counts = self._live_counts
        self.result_table.setRowCount(len(counts))

        majority_value: int = 0
        if counts:
            frequency_map = Counter(counts.values())
            majority_value = frequency_map.most_common(1)[0][0]

        for idx, (q, c) in enumerate(sorted(counts.items())):
            self.result_table.setItem(idx, 0, QTableWidgetItem(q))

            count_item = QTableWidgetItem(str(c))
            if c != majority_value:
                if c < majority_value:
                    # Below majority → muted amber
                    count_item.setBackground(QBrush(QColor("#f1c40f")))
                else:
                    # Above majority → muted coral/orange
                    count_item.setBackground(QBrush(QColor("#e67e22")))
                count_item.setForeground(QBrush(QColor("#000000")))

            self.result_table.setItem(idx, 1, count_item)

    # ------------------------------------------------------------------
    # Persist metrics (CSV + SQLite) after every approve/reject action
    # ------------------------------------------------------------------

    def _persist_metrics(self) -> None:
        output_dir = self.output_edit.text().strip()
        if not output_dir:
            return
        out_path = Path(output_dir)
        try:
            out_path.mkdir(parents=True, exist_ok=True)

            with open(out_path / "report.csv", "w", newline="", encoding="utf-8") as f:
                writer = csv.writer(f)
                writer.writerow(["Query", "Total Approved Hits"])
                writer.writerows(self._live_counts.items())

            conn = sqlite3.connect(str(out_path / "extraction_history.db"))
            cursor = conn.cursor()
            cursor.execute(
                "CREATE TABLE IF NOT EXISTS summary_metrics (query TEXT PRIMARY KEY, hits INTEGER)"
            )
            cursor.execute("""
                CREATE TABLE IF NOT EXISTS candidates_log (
                    id TEXT PRIMARY KEY, query TEXT, file_path TEXT,
                    page_index INTEGER, pre_approved INTEGER
                )
            """)
            cursor.executemany(
                "INSERT OR REPLACE INTO summary_metrics VALUES (?,?)",
                list(self._live_counts.items()),
            )
            cursor.executemany(
                "INSERT OR REPLACE INTO candidates_log VALUES (?,?,?,?,?)",
                [
                    (
                        item["id"],
                        item["query"],
                        item["file_path"],
                        item["page_idx"],
                        1 if item["pre_approved"] else 0,
                    )
                    for item in self.review_records
                ],
            )
            conn.commit()
            conn.close()
        except Exception as exc:
            log.error("Failed to persist metrics after review action: %s", exc)

    # ------------------------------------------------------------------
    # Review tree
    # ------------------------------------------------------------------

    def _rebuild_review_tree(self) -> None:
        selected_id = (
            self.current_review_item["id"] if self.current_review_item else None
        )

        self.tree_model.clear()
        self.tree_model.setHorizontalHeaderLabels(["Query Target Layout Mapping Tree"])

        search_filter = self.search_bar.text().strip().lower()
        query_buckets: dict[str, list[dict]] = defaultdict(list)
        for item in self.review_records:
            if search_filter and search_filter not in item["query"].lower():
                continue
            query_buckets[item["query"]].append(item)

        target_node: QStandardItem | None = None

        for query, items in query_buckets.items():
            query_node = QStandardItem(query)
            query_node.setSelectable(False)
            self.tree_model.appendRow(query_node)

            for item in sorted(items, key=lambda x: len(x["missing_words"])):
                page_node = QStandardItem()
                p_name = Path(item["file_path"]).name

                if item["pre_approved"]:
                    page_node.setText(
                        f"Page {item['page_idx'] + 1} -> {p_name} [APPROVED]"
                    )
                    page_node.setForeground(QBrush(QColor("#27ae60")))
                else:
                    missing = ", ".join(item["missing_words"])
                    page_node.setText(
                        f"Page {item['page_idx'] + 1} -> {p_name} [CANDIDATE] (Missing: {missing})"
                    )
                    page_node.setToolTip(f"Missing terms: {missing}")
                    page_node.setForeground(QBrush(QColor("#d35400")))

                page_node.setData(item, Qt.UserRole)
                query_node.appendRow(page_node)

                if selected_id and item["id"] == selected_id:
                    target_node = page_node

        self.review_tree.expandAll()

        # tree_model.clear() replaces the underlying QItemSelectionModel;
        # reconnect so keyboard and mouse nav both stay live.
        self.review_tree.selectionModel().currentChanged.connect(
            lambda cur, _prev: self._activate_index(cur)
        )

        if target_node is not None:
            idx = self.tree_model.indexFromItem(target_node)
            self.review_tree.selectionModel().setCurrentIndex(
                idx, QItemSelectionModel.SelectionFlag.ClearAndSelect
            )

    def _activate_index(self, index: QModelIndex) -> None:
        node = self.tree_model.itemFromIndex(index)
        if not node:
            return
        item_data = node.data(Qt.UserRole)
        if not item_data:
            return
        self.current_review_item = item_data
        self._render_selected_element()

    def eventFilter(self, obj: object, event: QEvent) -> bool:
        if obj is self.review_tree and event.type() == QEvent.KeyPress:
            key = event.key()
            if key in (
                Qt.Key_Up,
                Qt.Key_Down,
                Qt.Key_Left,
                Qt.Key_Right,
                Qt.Key_PageUp,
                Qt.Key_PageDown,
                Qt.Key_Home,
                Qt.Key_End,
            ):
                result = super().eventFilter(obj, event)
                self._activate_index(self.review_tree.currentIndex())
                return result
        return super().eventFilter(obj, event)

    # ------------------------------------------------------------------
    # Page preview rendering
    # ------------------------------------------------------------------

    def _render_selected_element(self) -> None:
        if not self.current_review_item:
            return
        item = self.current_review_item

        if self.view_text_mode:
            self.gfx_view.hide()
            self.text_preview.show()
            self._render_text_view(item)
        else:
            self.text_preview.hide()
            self.gfx_view.show()
            self._render_graphics_view(item)

    def _render_text_view(self, item: dict) -> None:
        raw_text = item["text_content"]
        if not raw_text.strip():
            self.text_preview.setPlainText("[No text layer found]")
            return

        tokens = [w.strip() for w in item["query"].split() if len(w.strip()) > 1]
        html_text = (
            raw_text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
        )

        for token in tokens:
            pattern = re.compile(re.escape(token), re.IGNORECASE)
            html_text = pattern.sub(
                lambda m: (
                    f'<span style="background-color:#ffff00;color:#000000;font-weight:bold;">'
                    f"{m.group(0)}</span>"
                ),
                html_text,
            )

        html_text = html_text.replace("\n", "<br>")
        self.text_preview.setHtml(
            f"<div style='font-family:monospace;font-size:12px;'>{html_text}</div>"
        )

    def _render_graphics_view(self, item: dict) -> None:
        self.gfx_scene.clear()
        f_path = item["file_path"]
        is_pdf = Path(f_path).suffix.lower() == ".pdf"
        q_pixmap: QPixmap | None = None

        try:
            if is_pdf:
                doc = fitz.open(_unc(f_path))
                page = doc[item["page_idx"]]
                pix = page.get_pixmap(dpi=150)
                q_img = QImage(
                    pix.samples, pix.width, pix.height, pix.stride, QImage.Format_RGB888
                )
                q_pixmap = QPixmap.fromImage(q_img)
                doc.close()
            else:
                with Image.open(f_path) as img:
                    img_corr = ImageOps.exif_transpose(img).convert("RGB")
                    buf = io.BytesIO()
                    img_corr.save(buf, format="PNG")
                    q_pixmap = QPixmap()
                    q_pixmap.loadFromData(buf.getvalue(), "PNG")
        except Exception as exc:
            log.error("Failed to render page preview: %s", exc)
            return

        if q_pixmap and not q_pixmap.isNull():
            pix_item = self.gfx_scene.addPixmap(q_pixmap)
            self.gfx_scene.setSceneRect(pix_item.boundingRect())
            self._apply_transformations()
            self.gfx_view.fitInView(pix_item, Qt.KeepAspectRatio)

    def _apply_transformations(self) -> None:
        t = QTransform()
        t.scale(self.zoom_factor, self.zoom_factor)
        t.rotate(self.current_rotation)
        self.gfx_view.setTransform(t)

    def _adjust_zoom(self, factor: float) -> None:
        self.zoom_factor *= factor
        self._apply_transformations()

    def _rotate(self, degrees: int) -> None:
        self.current_rotation = (self.current_rotation + degrees) % 360
        self._apply_transformations()

    def _toggle_view_mode(self) -> None:
        self.view_text_mode = not self.view_text_mode
        self.btn_toggle_view.setText(
            "Switch to Graphics Image View"
            if self.view_text_mode
            else "Switch to Text Layer View"
        )
        self._render_selected_element()

    # ------------------------------------------------------------------
    # Approve / Reject actions
    # ------------------------------------------------------------------

    def _approve_current_item(self) -> None:
        if not self.current_review_item:
            return
        item = self.current_review_item
        if item["pre_approved"]:
            return

        try:
            folder = Path(self.output_edit.text().strip()) / safe_folder_name(
                item["query"]
            )
            folder.mkdir(parents=True, exist_ok=True)
            p_obj = Path(item["file_path"])

            if p_obj.suffix.lower() == ".pdf":
                doc = fitz.open(_unc(item["file_path"]))
                out_doc = fitz.open()
                out_doc.insert_pdf(
                    doc, from_page=item["page_idx"], to_page=item["page_idx"]
                )
                out_doc.save(
                    _unc(
                        str(folder / f"{p_obj.stem}_approved_{item['file_hash']}.pdf")
                    ),
                    garbage=4,
                    deflate=True,
                )
                out_doc.close()
                doc.close()
            else:
                shutil.copy2(
                    item["file_path"],
                    folder / f"{p_obj.stem}_approved_{item['file_hash']}{p_obj.suffix}",
                )

            item["pre_approved"] = True
            self._live_counts[item["query"]] = (
                self._live_counts.get(item["query"], 0) + 1
            )
            self._refresh_metrics_table()
            self._persist_metrics()
            self._update_tree_node_style(item)

        except Exception as exc:
            QMessageBox.critical(self, "I/O Error", f"Failed manual export: {exc}")

    def _reject_current_item(self) -> None:
        if not self.current_review_item:
            return
        item = self.current_review_item
        if not item["pre_approved"]:
            return

        try:
            folder = Path(self.output_edit.text().strip()) / safe_folder_name(
                item["query"]
            )
            p_obj = Path(item["file_path"])
            ext = ".pdf" if p_obj.suffix.lower() == ".pdf" else p_obj.suffix

            # Both batch-run (stem_hash) and manual-approve (stem_approved_hash) variants
            for candidate in [
                folder / f"{p_obj.stem}_{item['file_hash']}{ext}",
                folder / f"{p_obj.stem}_approved_{item['file_hash']}{ext}",
            ]:
                if candidate.exists():
                    candidate.unlink()

            item["pre_approved"] = False
            self._live_counts[item["query"]] = max(
                0, self._live_counts.get(item["query"], 1) - 1
            )
            self._refresh_metrics_table()
            self._persist_metrics()
            self._update_tree_node_style(item)

        except Exception as exc:
            QMessageBox.critical(self, "I/O Error", f"Failed cleanup: {exc}")

    def _update_tree_node_style(self, item: dict) -> None:
        """Refresh the label and colour of the currently-selected tree node in-place."""
        current_index = self.review_tree.selectionModel().currentIndex()
        if not current_index.isValid():
            return
        node = self.tree_model.itemFromIndex(current_index)
        if not node:
            return
        p_name = Path(item["file_path"]).name
        if item["pre_approved"]:
            node.setText(f"Page {item['page_idx'] + 1} -> {p_name} [APPROVED]")
            node.setForeground(QBrush(QColor("#27ae60")))
        else:
            missing = ", ".join(item["missing_words"])
            node.setText(
                f"Page {item['page_idx'] + 1} -> {p_name} [CANDIDATE] (Missing: {missing})"
            )
            node.setForeground(QBrush(QColor("#d35400")))
        node.setData(item, Qt.UserRole)


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------


def main() -> None:
    multiprocessing.freeze_support()
    _setup_logging()
    app = QApplication(sys.argv)
    window = ExtractorApp()
    window.showNormal()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
