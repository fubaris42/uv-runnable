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
#     "pillow-heif",  # Added for HEIF image support
# ]
# ///

"""
PDF & Image Multi-Query Extractor

Architecture
------------
GUI Thread
  |
  +-- QThread coordinator (ProcessingWorker)
          |
          +-- ProcessPoolExecutor  (one OS process per CPU core)
                  |
                  +-- per-File worker (process_file)
                          1. content-hash (BLAKE2b) -> check OCR cache (SQLite in Input Dir)
                          2. Text extraction (Native PDF text pass OR OCR pipeline for images/scans)
                          3. Aho-Corasick multi-pattern search (O(text) complexity)
                          4. Save matches -> output PDFs / Copied Images
                          5. return {query: hit_count} to coordinator
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
import sqlite3
import sys
import time
from collections import defaultdict
from pathlib import Path
from typing import Any

import ahocorasick
import fitz  # PyMuPDF
from PIL import Image
import pillow_heif  # Registers HEIF plugin with Pillow automatically

from PySide6.QtCore import Qt, QThread, Signal
from PySide6.QtWidgets import (
    QApplication, QFileDialog, QHBoxLayout, QLabel, QLineEdit,
    QMessageBox, QProgressBar, QPushButton, QTableWidget,
    QTableWidgetItem, QTextEdit, QVBoxLayout, QWidget, QFrame
)

# Register HEIF opener with Pillow
pillow_heif.register_heif_opener()

# ─────────────────────────────────────────────────────────────────────────────
# Constants
# ─────────────────────────────────────────────────────────────────────────────
OCR_DPI            = 200          
OCR_SAMPLE_PAGES   = 5            
OCR_SAMPLE_THRESH  = 200          
CONTENT_HASH_BYTES = 1_048_576    # 1 MB for fast content fingerprinting
LOG_MAX_BYTES      = 5_242_880    
LOG_BACKUP_COUNT   = 3

IMAGE_EXTENSIONS = {".jpg", ".jpeg", ".png", ".heif"}
SUPPORTED_EXTENSIONS = {".pdf"}.union(IMAGE_EXTENSIONS)

# ─────────────────────────────────────────────────────────────────────────────
# Logging Configuration
# ─────────────────────────────────────────────────────────────────────────────
def _setup_logging(log_path: str | None = None) -> None:
    root = logging.getLogger()
    if root.handlers:
        return
    root.setLevel(logging.DEBUG)
    fmt = logging.Formatter("%(asctime)s [%(levelname)s] %(name)s: %(message)s", datefmt="%H:%M:%S")
    sh = logging.StreamHandler(sys.stderr)
    sh.setLevel(logging.INFO)
    sh.setFormatter(fmt)
    root.addHandler(sh)
    if log_path:
        fh = logging.handlers.RotatingFileHandler(
            log_path, maxBytes=LOG_MAX_BYTES, backupCount=LOG_BACKUP_COUNT, encoding="utf-8"
        )
        fh.setLevel(logging.DEBUG)
        fh.setFormatter(fmt)
        root.addHandler(fh)

log = logging.getLogger(__name__)

def _unc(path: str) -> str:
    if sys.platform != "win32":
        return path
    p = os.path.abspath(path)
    return p if p.startswith("\\\\?\\") else "\\\\?\\" + p

def safe_folder_name(name: str) -> str:
    return "".join(c for c in name if c.isalnum() or c in (" ", "_", "-")).strip()

# ─────────────────────────────────────────────────────────────────────────────
# Fast Content Hashing (BLAKE2b)
# ─────────────────────────────────────────────────────────────────────────────
def content_hash(path: str) -> str:
    """
    Computes blake2b(size:mtime:first_1MB) for lightning-fast tracking.
    If a file is renamed or moved, its content hash remains identical.
    """
    try:
        stat = os.stat(path)
        h = hashlib.blake2b(digest_size=16)  # 16 bytes = 32 hex chars
        h.update(f"{stat.st_size}:{stat.st_mtime_ns}".encode())
        with open(path, "rb") as fh:
            h.update(fh.read(CONTENT_HASH_BYTES))
        return h.hexdigest()
    except OSError as exc:
        log.warning("Cannot hash %s: %s", path, exc)
        return hashlib.blake2b(path.encode(), digest_size=16).hexdigest()

# ─────────────────────────────────────────────────────────────────────────────
# Aho-Corasick Automaton Matching Engine
# ─────────────────────────────────────────────────────────────────────────────
def build_automaton(
    queries: list[str],
) -> tuple[ahocorasick.Automaton, dict[int, int]]:
    token_qset: dict[str, set[int]] = defaultdict(set)
    query_token_need: dict[int, int] = {}

    for qi, q in enumerate(queries):
        parts = [w.lower() for w in q.split() if len(w) > 1]
        query_token_need[qi] = len(parts)
        for part in parts:
            token_qset[part].add(qi)

    A = ahocorasick.Automaton()
    for token, qset in token_qset.items():
        A.add_word(token, (token, qset))
    A.make_automaton()

    return A, query_token_need

def search_page(
    clean_text: str,
    automaton: ahocorasick.Automaton,
    query_token_need: dict[int, int],
) -> set[int]:
    found_tokens: dict[int, set[str]] = defaultdict(set)
    for _, (token, qset) in automaton.iter(clean_text):
        for qi in qset:
            found_tokens[qi].add(token)

    return {
        qi
        for qi, needed in query_token_need.items()
        if len(found_tokens[qi]) >= needed
    }

# ─────────────────────────────────────────────────────────────────────────────
# SQLite OCR Cache Engine (Now with Garbage Collection support)
# ─────────────────────────────────────────────────────────────────────────────
_ocr_cache_conn: sqlite3.Connection | None = None
_ocr_cache_path: str = ""

def _get_cache_conn(db_path: str) -> sqlite3.Connection:
    global _ocr_cache_conn, _ocr_cache_path
    if _ocr_cache_conn is None or _ocr_cache_path != db_path:
        _ocr_cache_conn = sqlite3.connect(db_path, check_same_thread=False)
        _ocr_cache_conn.execute("PRAGMA journal_mode=WAL")
        _ocr_cache_conn.execute("PRAGMA synchronous=NORMAL")
        # Keyed on content_hash to automatically handle renames/moves seamlessly
        _ocr_cache_conn.execute("""
            CREATE TABLE IF NOT EXISTS ocr_cache (
                content_hash TEXT NOT NULL,
                page_num     INTEGER NOT NULL,
                text         TEXT NOT NULL,
                timestamp    REAL NOT NULL,
                PRIMARY KEY (content_hash, page_num)
            )
        """)
        _ocr_cache_conn.commit()
        _ocr_cache_path = db_path
    return _ocr_cache_conn

def cache_load(db_path: str, file_hash: str, total_pages: int) -> dict[int, str] | None:
    """Return {page_num: text} if ALL pages exist in cache."""
    try:
        con = _get_cache_conn(db_path)
        rows = con.execute(
            "SELECT page_num, text FROM ocr_cache WHERE content_hash=? ORDER BY page_num",
            (file_hash,),
        ).fetchall()
        if len(rows) == total_pages:
            # Update read timestamp for LRU cache tracking
            con.execute("UPDATE ocr_cache SET timestamp=? WHERE content_hash=?", (time.time(), file_hash))
            con.commit()
            return {r[0]: r[1] for r in rows}
    except Exception as exc:
        log.warning("OCR cache read error: %s", exc)
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
    except Exception as exc:
        log.warning("OCR cache write error: %s", exc)

def run_cache_garbage_collection(db_path: str, active_hashes: set[str]) -> None:
    """Removes records from the DB that do not match current files in the input directory."""
    try:
        con = sqlite3.connect(db_path)
        cursor = con.cursor()
        cursor.execute("SELECT DISTINCT content_hash FROM ocr_cache")
        cached_hashes = {r[0] for r in cursor.fetchall()}
        
        dead_hashes = cached_hashes - active_hashes
        if dead_hashes:
            log.info("Garbage collection: Purging %d obsolete file records from cache database.", len(dead_hashes))
            cursor.executemany(
                "DELETE FROM ocr_cache WHERE content_hash = ?",
                [(h,) for h in dead_hashes]
            )
            con.commit()
            con.execute("VACUUM")
            con.commit()
        con.close()
    except Exception as exc:
        log.warning("Cache database garbage collection failed: %s", exc)

# ─────────────────────────────────────────────────────────────────────────────
# Async WinRT OCR Engine Pipeline
# ─────────────────────────────────────────────────────────────────────────────
_ocr_loop:    asyncio.AbstractEventLoop | None = None
_ocr_engine:  Any = None

def _ocr_engine_lazy() -> Any:
    global _ocr_engine
    if _ocr_engine is None:
        from winrt.windows.media.ocr import OcrEngine  
        _ocr_engine = OcrEngine.try_create_from_user_profile_languages()
    return _ocr_engine

def _ocr_loop_lazy() -> asyncio.AbstractEventLoop:
    global _ocr_loop
    if _ocr_loop is None or _ocr_loop.is_closed():
        _ocr_loop = asyncio.new_event_loop()
        asyncio.set_event_loop(_ocr_loop)
    return _ocr_loop

async def _decode_bitmap(pil_img: Image.Image) -> Any:
    from winrt.windows.security.cryptography import CryptographicBuffer   
    from winrt.windows.storage.streams import InMemoryRandomAccessStream   
    from winrt.windows.graphics.imaging import BitmapDecoder               

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
    except Exception as exc:
        log.error("Failed concurrently decoding bitmaps: %s", exc)
        return [""] * len(images)

    results = []
    for idx, bitmap in enumerate(bitmaps):
        try:
            result = await engine.recognize_async(bitmap)
            results.append(result.text if result else "")
        except Exception as exc:
            log.warning("OCR engine error on page %d: %s", idx, exc)
            results.append("")
            
    return results

def ocr_all_pages(images: list[Image.Image]) -> list[str]:
    if not images:
        return []
    loop = _ocr_loop_lazy()
    return loop.run_until_complete(_ocr_pipeline_async(images))

def render_page(page: fitz.Page, dpi: int = OCR_DPI) -> Image.Image:
    pix = page.get_pixmap(dpi=dpi)
    return Image.frombytes("RGB", [pix.width, pix.height], pix.samples)

# ─────────────────────────────────────────────────────────────────────────────
# Consolidated Unified Processing Worker (PDFs + Images)
# ─────────────────────────────────────────────────────────────────────────────
def process_file(
    file_path: str,
    queries: list[str],
    automaton_payload: tuple[list[tuple[str, tuple[str, set[int]]]], dict[int, int]],
    output_dir: str,
    cache_db: str,
    log_path: str,
) -> dict[str, int]:
    """Process one PDF or Image. Returns {query_raw: items_matched}."""
    _setup_logging(log_path)
    match_counts: dict[str, int] = {q: 0 for q in queries}

    aho_words, query_token_need = automaton_payload
    A = ahocorasick.Automaton()
    for word, payload in aho_words:
        A.add_word(word, payload)
    A.make_automaton()

    p_obj = Path(file_path)
    file_name = p_obj.stem
    file_ext = p_obj.suffix.lower()
    file_hash = content_hash(file_path)

    page_texts: dict[int, str] = {}
    is_pdf = (file_ext == ".pdf")
    total_items = 0

    if is_pdf:
        try:
            doc = fitz.open(_unc(file_path))
            total_items = len(doc)
        except Exception as exc:
            log.error("Cannot open PDF %s: %s", file_path, exc)
            return match_counts
    else:
        total_items = 1 # Standalone Image is treated as a 1-page document

    # Check Consolidated Cache DB Engine
    cached = cache_load(cache_db, file_hash, total_items)
    if cached is not None:
        page_texts = cached
        log.debug("%s: loaded from OCR cache via BLAKE2b fingerprint match", file_name)
    else:
        if is_pdf:
            sample_n = min(OCR_SAMPLE_PAGES, total_items)
            sample_chars = sum(len(doc[i].get_text() or "") for i in range(sample_n))
            force_ocr = sample_chars < OCR_SAMPLE_THRESH

            if not force_ocr:
                for i in range(total_items):
                    page_texts[i] = doc[i].get_text() or ""
            else:
                log.info("%s: low text format -> Executing Pipeline OCR", file_name)
                images = [render_page(doc[i]) for i in range(total_items)]
                results = ocr_all_pages(images)
                page_texts = {i: t for i, t in enumerate(results)}
                cache_save(cache_db, file_hash, page_texts)
            doc.close()
        else:
                    # Standalone raw Image parsing pipeline (PNG, JPG, JPEG, HEIF)
                    log.info("%s: Processing standalone file image via OCR engine", file_name)
                    try:
                        from PIL import ImageOps  # Added for EXIF handling
                        
                        with Image.open(file_path) as img:
                            # Fix orientation issues before converting to RGB or sending to OCR
                            img_corrected = ImageOps.exif_transpose(img)
                            img_rgb = img_corrected.convert("RGB")
                            
                            results = ocr_all_pages([img_rgb])
                            page_texts = {0: results[0] if results else ""}
                            cache_save(cache_db, file_hash, page_texts)
                    except Exception as exc:
                        log.error("Failed to read image template file %s: %s", file_path, exc)
                        return match_counts

    # Step 2: Query Matching Engine pass
    query_hits: dict[int, list[int]] = defaultdict(list)
    for index, raw_text in page_texts.items():
        clean = raw_text.lower().replace(" ", "")
        for qi in search_page(clean, A, query_token_need):
            query_hits[qi].append(index)

    if not query_hits:
        return match_counts

    # Step 3: Extract & Save Match Subsets
    if is_pdf:
        try:
            doc = fitz.open(_unc(file_path))
            for qi, page_list in query_hits.items():
                raw_q = queries[qi]
                match_counts[raw_q] = len(page_list)

                folder = Path(output_dir) / safe_folder_name(raw_q)
                folder.mkdir(parents=True, exist_ok=True)
                out_path = _unc(str(folder / f"{file_name}_{file_hash}.pdf"))

                out_doc = fitz.open()
                for pn in page_list:
                    out_doc.insert_pdf(doc, from_page=pn, to_page=pn)
                out_doc.save(out_path, garbage=4, deflate=True)
                out_doc.close()
            doc.close()
        except Exception as exc:
            log.error("Failed partitioning match files for %s: %s", file_path, exc)
    else:
        # Save image profile match by safe replication
        for qi in query_hits.keys():
            raw_q = queries[qi]
            match_counts[raw_q] = 1

            folder = Path(output_dir) / safe_folder_name(raw_q)
            folder.mkdir(parents=True, exist_ok=True)
            out_path = folder / f"{file_name}_{file_hash}{file_ext}"
            try:
                import shutil
                shutil.copy2(file_path, out_path)
            except Exception as exc:
                log.error("Failed to copy matched image file %s: %s", file_path, exc)

    return match_counts

# ─────────────────────────────────────────────────────────────────────────────
# Serialization Payloads
# ─────────────────────────────────────────────────────────────────────────────
def build_automaton_payload(
    queries: list[str],
) -> tuple[list[tuple[str, tuple[str, set[int]]]], dict[int, int]]:
    token_qset:       dict[str, set[int]] = defaultdict(set)
    query_token_need: dict[int, int]      = {}

    for qi, q in enumerate(queries):
        parts = [w.lower() for w in q.split() if len(w) > 1]
        query_token_need[qi] = len(parts)
        for part in parts:
            token_qset[part].add(qi)

    aho_words = [(token, (token, qset)) for token, qset in token_qset.items()]
    return aho_words, query_token_need

def init_metrics_db(db_path: str, queries: list[str], csv_path: str) -> None:
    con = sqlite3.connect(db_path)
    con.execute("""
        CREATE TABLE IF NOT EXISTS metrics (
            query      TEXT PRIMARY KEY,
            page_count INTEGER DEFAULT 0
        )
    """)
    con.execute("DELETE FROM metrics") 
    con.executemany(
        "INSERT INTO metrics (query, page_count) VALUES (?, 0)",
        [(q,) for q in queries],
    )
    con.commit()
    con.close()

    try:
        if os.path.exists(_unc(csv_path)):
            os.remove(_unc(csv_path))
    except Exception as exc:
        log.warning("Could not clear previous CSV file: %s", exc)

def update_metrics_db(db_path: str, counts: dict[str, int]) -> None:
    con = sqlite3.connect(db_path)
    con.executemany(
        "UPDATE metrics SET page_count = page_count + ? WHERE query = ?",
        [(cnt, q) for q, cnt in counts.items() if cnt],
    )
    con.commit()
    con.close()

def export_metrics_csv(db_path: str, csv_path: str) -> None:
    con = sqlite3.connect(db_path)
    # Kept database query intact (ordered alphabetically by query)
    rows = con.execute("SELECT query, page_count FROM metrics ORDER BY query").fetchall()
    con.close()
    
    # Sort the retrieved data rows by match count (row[1]) lowest-to-highest in Python memory
    sorted_rows = sorted(rows, key=lambda row: row[1])
    
    with open(_unc(csv_path), "w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(["query", "match count"])
        w.writerows(sorted_rows)

# ─────────────────────────────────────────────────────────────────────────────
# QThread Process Orchestrator
# ─────────────────────────────────────────────────────────────────────────────
class ProcessingWorker(QThread):
    progress_signal = Signal(int, int, str)
    finished_signal = Signal(dict)
    error_signal    = Signal(str)

    def __init__(
        self,
        input_dir:   str,
        queries:     list[str],
        output_dir:  str,
        max_workers: int | None = None,
    ) -> None:
        super().__init__()
        self.input_dir   = input_dir
        self.queries     = queries
        self.output_dir  = output_dir
        self.max_workers = max_workers or max(1, (os.cpu_count() or 4) - 1)
        self._cancel     = False

    def cancel(self) -> None:
        self._cancel = True

    def run(self) -> None:
        try:
            self._run()
        except Exception as exc:
            log.exception("Fatal coordinator error")
            self.error_signal.emit(str(exc))

    def _run(self) -> None:
        # Scanning across all configured input variants
        all_files = [str(p) for p in Path(self.input_dir).rglob("*") if p.suffix.lower() in SUPPORTED_EXTENSIONS]
        if not all_files:
            self.error_signal.emit("No supported PDF or image records discovered inside the source target folder.")
            return

        total   = len(all_files)
        queries = self.queries
        out_dir = self.output_dir

        # FIXED: Cache database destination moved seamlessly into the target INPUT directory
        cache_db    = _unc(os.path.join(self.input_dir, ".ocr_cache.db"))
        metrics_db  = _unc(os.path.join(out_dir, "metrics.db"))
        csv_path    = os.path.join(out_dir, "query_match_counts.csv")
        log_path    = _unc(os.path.join(out_dir, "extractor.log"))

        _setup_logging(log_path)
        log.info("Starting run: %d files, %d queries, %d workers", total, len(queries), self.max_workers)

        aho_payload = build_automaton_payload(queries)
        init_metrics_db(metrics_db, queries, csv_path)

        aggregate: dict[str, int] = {q: 0 for q in queries}
        self.progress_signal.emit(0, total, f"Found {total} items. Orchestrating Multi-Process Core Layout...")

        ctx = multiprocessing.get_context("spawn")
        active_hashes: set[str] = set()

        with concurrent.futures.ProcessPoolExecutor(max_workers=self.max_workers, mp_context=ctx) as executor:
            future_map = {
                executor.submit(
                    process_file, f, queries, aho_payload, out_dir, cache_db, log_path
                ): f
                for f in all_files
            }

            done = 0
            for future in concurrent.futures.as_completed(future_map):
                if self._cancel:
                    executor.shutdown(wait=False, cancel_futures=True)
                    self.error_signal.emit("Processing cancelled by user.")
                    return

                f_path = future_map[future]
                short_name = Path(f_path).name
                done += 1

                try:
                    result = future.result()
                except Exception as exc:
                    log.error("Worker failed for %s: %s", short_name, exc)
                    self.progress_signal.emit(done, total, f"[ERROR] {short_name}: {exc}")
                    continue

                # Recalculate hash on coordinator thread to maintain deterministic tracking sets for GC pass
                active_hashes.add(content_hash(f_path))

                update_metrics_db(metrics_db, result)
                for q, cnt in result.items():
                    aggregate[q] += cnt

                self.progress_signal.emit(done, total, f"({done}/{total}) {short_name}")

        # Execute Cache Database Garbage Collection pass
        run_cache_garbage_collection(cache_db, active_hashes)

        export_metrics_csv(metrics_db, csv_path)
        log.info("Run completely synchronized. Aggregate items processed match: %d", sum(aggregate.values()))
        self.finished_signal.emit(aggregate)

# ─────────────────────────────────────────────────────────────────────────────
# UI Controller / Layout Interface (Dual-Panel Split View)
# ─────────────────────────────────────────────────────────────────────────────
class ExtractorApp(QWidget):
    def __init__(self) -> None:
        super().__init__()
        self._worker: ProcessingWorker | None = None
        self._t0 = 0.0
        self._init_ui()

    def _init_ui(self) -> None:
        self.setWindowTitle("PDF & Image Multi-Query Extractor")
        self.setMinimumSize(950, 500)

        main_layout = QHBoxLayout(self)
        main_layout.setSpacing(15)
        main_layout.setContentsMargins(15, 15, 15, 15)

        # LEFT PANEL
        left_container = QVBoxLayout()
        left_container.setSpacing(10)

        row_input = QHBoxLayout()
        self.input_edit = QLineEdit(placeholderText="Select input directory containing PDFs/Images...", readOnly=True)
        btn_input = QPushButton("Browse Input")
        btn_input.clicked.connect(self._browse_input)
        row_input.addWidget(self.input_edit)
        row_input.addWidget(btn_input)
        left_container.addLayout(row_input)

        row_output = QHBoxLayout()
        self.output_edit = QLineEdit(placeholderText="Select output destination folder...", readOnly=True)
        btn_output = QPushButton("Browse Output")
        btn_output.clicked.connect(self._browse_output)
        row_output.addWidget(self.output_edit)
        row_output.addWidget(btn_output)
        left_container.addLayout(row_output)

        row_workers = QHBoxLayout()
        row_workers.addWidget(QLabel("Parallel workers:"))
        self.workers_edit = QLineEdit(str(max(1, (os.cpu_count() or 4) - 1)))
        self.workers_edit.setMaximumWidth(60)
        row_workers.addWidget(self.workers_edit)
        row_workers.addStretch()
        left_container.addLayout(row_workers)

        left_container.addWidget(QLabel("Queries / Search terms (one per line):"))
        self.query_edit = QTextEdit(
            placeholderText="Type or paste queries here...\nExample:\nIQBAL MAULANA FAUZI\nPATRICK STAR"
        )
        left_container.addWidget(self.query_edit, stretch=1)

        btn_import = QPushButton("Import Queries from .txt File")
        btn_import.clicked.connect(self._import_txt)
        left_container.addWidget(btn_import)

        self.status_label = QLabel("Status: Ready")
        self.status_label.setWordWrap(True)
        left_container.addWidget(self.status_label)

        self.progress_bar = QProgressBar()
        self.progress_bar.setTextVisible(True)
        self.progress_bar.setFormat("%v / %m items")
        self.progress_bar.setValue(0)
        left_container.addWidget(self.progress_bar)

        row_actions = QHBoxLayout()
        self.btn_run = QPushButton("Start Processing")
        self.btn_run.setStyleSheet(
            "font-weight:bold;background-color:#2b78e4;color:white;padding:8px;border-radius:4px;"
        )
        self.btn_run.clicked.connect(self._start)
        row_actions.addWidget(self.btn_run)

        self.btn_cancel = QPushButton("Cancel")
        self.btn_cancel.setStyleSheet(
            "font-weight:bold;background-color:#c0392b;color:white;padding:8px;border-radius:4px;"
        )
        self.btn_cancel.setEnabled(False)
        self.btn_cancel.clicked.connect(self._cancel)
        row_actions.addWidget(self.btn_cancel)
        left_container.addLayout(row_actions)

        main_layout.addLayout(left_container, stretch=4)

        v_line = QFrame()
        v_line.setFrameShape(QFrame.VLine)
        v_line.setFrameShadow(QFrame.Sunken)
        main_layout.addWidget(v_line)

        # RIGHT PANEL
        right_container = QVBoxLayout()
        right_container.setSpacing(8)

        self.lbl_results = QLabel("Results View")
        self.lbl_results.setStyleSheet("font-weight: bold; font-size: 13px; color: #333333;")
        right_container.addWidget(self.lbl_results)

        self.result_table = QTableWidget(0, 2)
        self.result_table.setHorizontalHeaderLabels(["Query", "Items matched"])
        self.result_table.horizontalHeader().setStretchLastSection(True)
        self.result_table.setEditTriggers(QTableWidget.NoEditTriggers)
        right_container.addWidget(self.result_table)

        main_layout.addLayout(right_container, stretch=5)

    def _browse_input(self) -> None:
        d = QFileDialog.getExistingDirectory(self, "Select Input Directory")
        if d:
            self.input_edit.setText(d)

    def _browse_output(self) -> None:
        d = QFileDialog.getExistingDirectory(self, "Select Output Directory")
        if d:
            self.output_edit.setText(d)

    def _import_txt(self) -> None:
        fp, _ = QFileDialog.getOpenFileName(self, "Open Query File", "", "Text Files (*.txt)")
        if not fp:
            return
        try:
            with open(fp, encoding="utf-8", errors="ignore") as fh:
                lines = [ln.strip() for ln in fh if ln.strip() and not ln.strip().startswith("[")]
            self.query_edit.setPlainText("\n".join(lines))
            QMessageBox.information(self, "Imported", f"Loaded {len(lines)} queries.")
        except Exception as exc:
            QMessageBox.critical(self, "Error", f"Failed to read file:\n{exc}")

    def _start(self) -> None:
        input_dir  = self.input_edit.text().strip()
        output_dir = self.output_edit.text().strip()
        queries    = [q.strip() for q in self.query_edit.toPlainText().split("\n") if q.strip()]

        if not input_dir or not output_dir:
            QMessageBox.warning(self, "Validation", "Please select both Input and Output directories.")
            return
        if not queries:
            QMessageBox.warning(self, "Validation", "Please enter at least one query.")
            return

        try:
            workers = max(1, int(self.workers_edit.text()))
        except ValueError:
            workers = max(1, (os.cpu_count() or 4) - 1)

        self.result_table.setRowCount(0)
        self.progress_bar.setValue(0)
        self.progress_bar.setRange(0, 0)
        self.btn_run.setEnabled(False)
        self.btn_cancel.setEnabled(True)
        self._t0 = time.monotonic()

        self._worker = ProcessingWorker(input_dir, queries, output_dir, workers)
        self._worker.progress_signal.connect(self._on_progress)
        self._worker.finished_signal.connect(self._on_finished)
        self._worker.error_signal.connect(self._on_error)
        self._worker.start()

    def _cancel(self) -> None:
        if self._worker:
            self._worker.cancel()
        self.status_label.setText("Status: Cancelling...")
        self.btn_cancel.setEnabled(False)

    def _on_progress(self, current: int, total: int, msg: str) -> None:
        if self.progress_bar.maximum() == 0:
            self.progress_bar.setRange(0, total)
        self.progress_bar.setValue(current)
        elapsed = time.monotonic() - self._t0
        self.status_label.setText(f"[{elapsed:.1f}s]  {msg}")

    def _on_finished(self, counts: dict[str, int]) -> None:
            elapsed = time.monotonic() - self._t0
            self.progress_bar.setRange(0, 100)
            self.progress_bar.setValue(100)
            self.btn_run.setEnabled(True)
            self.btn_cancel.setEnabled(False)
            self.status_label.setText(f"Status: Complete in {elapsed:.1f}s -- metrics.db saved to destination folder")
            
            self.result_table.setRowCount(len(counts))
            
            # 1. Adjust UI Column Sizes to a 70:30 ratio layout
            total_width = self.result_table.viewport().width()
            if total_width <= 0:  # Fallback if window layout hasn't fully rendered its geometry yet
                total_width = self.result_table.width()
            self.result_table.setColumnWidth(0, int(total_width * 0.70))
            self.result_table.setColumnWidth(1, int(total_width * 0.30))
            
            # Calculate the majority (mode) baseline dynamically from the actual counts
            if counts:
                from collections import Counter
                majority_baseline = Counter(counts.values()).most_common(1)[0][0]
            else:
                majority_baseline = 0
                
            # Explicitly import everything needed for styling and UI item generation
            from PySide6.QtGui import QColor, QBrush
            from PySide6.QtWidgets import QTableWidgetItem
            
            # 0 [ dark magenta white bold text ]
            zero_bg = QBrush(QColor("#8B008B"))
            zero_fg = QBrush(QColor("#FFFFFF"))
            
            # under [ blood red background white bold text ]
            under_bg = QBrush(QColor("#8B0000"))
            under_fg = QBrush(QColor("#FFFFFF"))
            
            # over [ yellow-ish bg make sure text visible both light and dark mode ]
            over_bg = QBrush(QColor("#FFF2CC"))
            over_fg = QBrush(QColor("#202020"))  # Charcoal text for high contrast
            
            # 2. Sort items by match count from lowest to highest for UI display
            sorted_counts = sorted(counts.items(), key=lambda item: item[1])
            
            for row, (q, cnt) in enumerate(sorted_counts):
                # Column 0: Query Name
                query_item = QTableWidgetItem(q)
                self.result_table.setItem(row, 0, query_item)
                
                # Column 1: Match Count
                count_item = QTableWidgetItem(str(cnt))
                count_item.setTextAlignment(Qt.AlignCenter)
                
                # Apply styling rules based on the dynamic majority baseline
                if cnt == 0:
                    count_item.setBackground(zero_bg)
                    count_item.setForeground(zero_fg)
                    font = count_item.font()
                    font.setBold(True)
                    count_item.setFont(font)
                    
                elif cnt < majority_baseline:
                    count_item.setBackground(under_bg)
                    count_item.setForeground(under_fg)
                    font = count_item.font()
                    font.setBold(True)
                    count_item.setFont(font)
                    
                elif cnt > majority_baseline:
                    count_item.setBackground(over_bg)
                    count_item.setForeground(over_fg)
                    font = count_item.font()
                    font.setBold(True)
                    count_item.setFont(font)
                    
                self.result_table.setItem(row, 1, count_item)

    def _on_error(self, msg: str) -> None:
        self.progress_bar.setRange(0, 100)
        self.progress_bar.setValue(0)
        self.btn_run.setEnabled(True)
        self.btn_cancel.setEnabled(False)
        self.status_label.setText("Status: Error.")
        QMessageBox.critical(self, "Error", msg)

def main() -> None:
    multiprocessing.freeze_support()
    _setup_logging()
    app = QApplication(sys.argv)
    window = ExtractorApp()
    window.showNormal()
    sys.exit(app.exec())

if __name__ == "__main__":
    main()