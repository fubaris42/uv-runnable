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
import sqlite3
import sys
import time
from collections import defaultdict
from pathlib import Path
from typing import Any

import ahocorasick
import fitz  # PyMuPDF
from PIL import Image, ImageOps
import pillow_heif

from PySide6.QtCore import Qt, QThread, Signal
from PySide6.QtGui import QColor, QBrush, QPixmap, QImage, QTransform, QStandardItemModel, QStandardItem
from PySide6.QtWidgets import (
    QApplication, QFileDialog, QHBoxLayout, QLabel, QLineEdit,
    QMessageBox, QProgressBar, QPushButton, QTableWidget,
    QTableWidgetItem, QTextEdit, QVBoxLayout, QWidget, QFrame,
    QTabWidget, QTreeView, QGraphicsView, QGraphicsScene, QSplitter
)

pillow_heif.register_heif_opener()

OCR_DPI            = 200          
OCR_SAMPLE_PAGES   = 5            
OCR_SAMPLE_THRESH  = 200          
CONTENT_HASH_BYTES = 1_048_576    
LOG_MAX_BYTES      = 5_242_880    
LOG_BACKUP_COUNT   = 3

IMAGE_EXTENSIONS = {".jpg", ".jpeg", ".png", ".heif"}
SUPPORTED_EXTENSIONS = {".pdf"}.union(IMAGE_EXTENSIONS)

log = logging.getLogger(__name__)

def _setup_logging(log_path: str | None = None) -> None:
    root = logging.getLogger()
    if root.handlers: return
    root.setLevel(logging.DEBUG)
    fmt = logging.Formatter("%(asctime)s [%(levelname)s] %(name)s: %(message)s", datefmt="%H:%M:%S")
    sh = logging.StreamHandler(sys.stderr)
    sh.setLevel(logging.INFO)
    sh.setFormatter(fmt)
    root.addHandler(sh)
    if log_path:
        fh = logging.handlers.RotatingFileHandler(log_path, maxBytes=LOG_MAX_BYTES, backupCount=LOG_BACKUP_COUNT, encoding="utf-8")
        fh.setLevel(logging.DEBUG)
        fh.setFormatter(fmt)
        root.addHandler(fh)

def _unc(path: str) -> str:
    if sys.platform != "win32": return path
    p = os.path.abspath(path)
    return p if p.startswith("\\\\?\\") else "\\\\?\\" + p

def safe_folder_name(name: str) -> str:
    return "".join(c for c in name if c.isalnum() or c in (" ", "_", "-")).strip()

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

def build_automaton_payload(queries: list[str]) -> tuple[list[tuple[str, tuple[str, set[int]]]], dict[int, int]]:
    token_qset: dict[str, set[int]] = defaultdict(set)
    query_token_need: dict[int, int] = {}
    for qi, q in enumerate(queries):
        parts = [w.lower() for w in q.split() if len(w) > 1]
        query_token_need[qi] = len(parts)
        for part in parts:
            token_qset[part].add(qi)
    aho_words = [(token, (token, qset)) for token, qset in token_qset.items()]
    return aho_words, query_token_need

_ocr_cache_conn: sqlite3.Connection | None = None
_ocr_cache_path: str = ""

def _get_cache_conn(db_path: str) -> sqlite3.Connection:
    global _ocr_cache_conn, _ocr_cache_path
    if _ocr_cache_conn is None or _ocr_cache_path != db_path:
        _ocr_cache_conn = sqlite3.connect(db_path, check_same_thread=False)
        _ocr_cache_conn.execute("PRAGMA journal_mode=WAL")
        _ocr_cache_conn.execute("PRAGMA synchronous=NORMAL")
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
    try:
        con = _get_cache_conn(db_path)
        rows = con.execute("SELECT page_num, text FROM ocr_cache WHERE content_hash=? ORDER BY page_num", (file_hash,)).fetchall()
        if len(rows) == total_pages:
            con.execute("UPDATE ocr_cache SET timestamp=? WHERE content_hash=?", (time.time(), file_hash))
            con.commit()
            return {r[0]: r[1] for r in rows}
    except Exception:
        pass
    return None

def cache_save(db_path: str, file_hash: str, page_texts: dict[int, str]) -> None:
    try:
        con = _get_cache_conn(db_path)
        now = time.time()
        con.executemany("INSERT OR REPLACE INTO ocr_cache (content_hash, page_num, text, timestamp) VALUES (?,?,?,?)",
                        [(file_hash, pn, txt, now) for pn, txt in page_texts.items()])
        con.commit()
    except Exception:
        pass

_ocr_loop: asyncio.AbstractEventLoop | None = None
_ocr_engine: Any = None

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
    if not engine: return [""] * len(images)
    try:
        bitmaps = await asyncio.gather(*(_decode_bitmap(img) for img in images))
    except Exception:
        return [""] * len(images)
    results = []
    for bitmap in bitmaps:
        try:
            result = await engine.recognize_async(bitmap)
            results.append(result.text if result else "")
        except Exception:
            results.append("")
    return results

def ocr_all_pages(images: list[Image.Image]) -> list[str]:
    if not images: return []
    return _ocr_loop_lazy().run_until_complete(_ocr_pipeline_async(images))

def render_page(page: fitz.Page, dpi: int = OCR_DPI) -> Image.Image:
    pix = page.get_pixmap(dpi=dpi)
    return Image.frombytes("RGB", [pix.width, pix.height], pix.samples)

def process_file(
    file_path: str,
    queries: list[str],
    automaton_payload: tuple[list[tuple[str, tuple[str, set[int]]]], dict[int, int]],
    output_dir: str,
    cache_db: str,
    log_path: str,
) -> dict[str, Any]:
    _setup_logging(log_path)
    
    aho_words, query_token_need = automaton_payload
    A = ahocorasick.Automaton()
    for word, payload in aho_words:
        A.add_word(word, payload)
    A.make_automaton()

    p_obj = Path(file_path)
    file_name = p_obj.name
    file_ext = p_obj.suffix.lower()
    file_hash = content_hash(file_path)
    is_pdf = (file_ext == ".pdf")

    page_texts: dict[int, str] = {}
    total_items = 0

    if is_pdf:
        try:
            doc = fitz.open(_unc(file_path))
            total_items = len(doc)
        except Exception:
            return {"counts": {}, "review_data": []}
    else:
        total_items = 1

    cached = cache_load(cache_db, file_hash, total_items)
    if cached is not None:
        page_texts = cached
    else:
        if is_pdf:
            sample_n = min(OCR_SAMPLE_PAGES, total_items)
            sample_chars = sum(len(doc[i].get_text() or "") for i in range(sample_n))
            if sample_chars >= OCR_SAMPLE_THRESH:
                for i in range(total_items):
                    page_texts[i] = doc[i].get_text() or ""
            else:
                images = [render_page(doc[i]) for i in range(total_items)]
                results = ocr_all_pages(images)
                page_texts = {i: t for i, t in enumerate(results)}
                cache_save(cache_db, file_hash, page_texts)
            doc.close()
        else:
            try:
                with Image.open(file_path) as img:
                    img_corrected = ImageOps.exif_transpose(img)
                    results = ocr_all_pages([img_corrected.convert("RGB")])
                    page_texts = {0: results[0] if results else ""}
                    cache_save(cache_db, file_hash, page_texts)
            except Exception:
                return {"counts": {}, "review_data": []}

    match_counts = {q: 0 for q in queries}
    review_items = []

    for index, raw_text in page_texts.items():
        clean = raw_text.lower().replace(" ", "")
        
        for qi, query in enumerate(queries):
            tokens = [w.lower() for w in query.split() if len(w) > 1]
            found_tokens = set()
            
            for _, (token, qset) in A.iter(clean):
                if qi in qset:
                    found_tokens.add(token)

            missing_tokens = [t for t in tokens if t not in found_tokens]
            is_approved = len(missing_tokens) == 0

            if is_approved or (len(found_tokens) > 0 and len(tokens) > 1):
                if is_approved:
                    match_counts[query] += 1
                
                review_items.append({
                    "query": query,
                    "file_path": file_path,
                    "file_hash": file_hash,
                    "page_idx": index,
                    "pre_approved": is_approved,
                    "missing_words": missing_tokens,
                    "text_content": raw_text
                })

    if is_pdf:
        try:
            doc = fitz.open(_unc(file_path))
            pdf_hits = defaultdict(list)
            for item in review_items:
                if item["pre_approved"]:
                    pdf_hits[item["query"]].append(item["page_idx"])
                    
            for q, p_list in pdf_hits.items():
                folder = Path(output_dir) / safe_folder_name(q)
                folder.mkdir(parents=True, exist_ok=True)
                out_doc = fitz.open()
                for pn in p_list:
                    out_doc.insert_pdf(doc, from_page=pn, to_page=pn)
                out_doc.save(_unc(str(folder / f"{p_obj.stem}_{file_hash}.pdf")), garbage=4, deflate=True)
                out_doc.close()
            doc.close()
        except Exception:
            pass
    else:
        for item in review_items:
            if item["pre_approved"]:
                folder = Path(output_dir) / safe_folder_name(item["query"])
                folder.mkdir(parents=True, exist_ok=True)
                import shutil
                shutil.copy2(file_path, folder / f"{p_obj.stem}_{file_hash}{file_ext}")

    return {"counts": match_counts, "review_data": review_items}

class ProcessingWorker(QThread):
    progress_signal = Signal(int, int, str)
    finished_signal = Signal(dict, list)
    error_signal    = Signal(str)

    def __init__(self, input_dir: str, queries: list[str], output_dir: str, max_workers: int | None = None) -> None:
        super().__init__()
        self.input_dir = input_dir
        self.queries = queries
        self.output_dir = output_dir
        self.max_workers = max_workers or max(1, (os.cpu_count() or 4) - 1)
        self._cancel = False

    def cancel(self): self._cancel = True

    def run(self) -> None:
        all_files = [str(p) for p in Path(self.input_dir).rglob("*") if p.suffix.lower() in SUPPORTED_EXTENSIONS]
        if not all_files:
            self.error_signal.emit("No supported assets parsed inside target folder.")
            return

        total = len(all_files)
        cache_db = _unc(os.path.join(self.input_dir, ".ocr_cache.db"))
        log_path = _unc(os.path.join(self.output_dir, "extractor.log"))
        _setup_logging(log_path)

        aho_payload = build_automaton_payload(self.queries)
        aggregate_counts = {q: 0 for q in self.queries}
        master_review_data = []

        ctx = multiprocessing.get_context("spawn")
        with concurrent.futures.ProcessPoolExecutor(max_workers=self.max_workers, mp_context=ctx) as executor:
            future_map = {executor.submit(process_file, f, self.queries, aho_payload, self.output_dir, cache_db, log_path): f for f in all_files}
            
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
                    self.progress_signal.emit(done, total, f"({done}/{total}) {Path(f_path).name}")
                except Exception as exc:
                    self.progress_signal.emit(done, total, f"[FAIL] {Path(f_path).name}: {exc}")

        self.finished_signal.emit(aggregate_counts, master_review_data)

class ExtractorApp(QWidget):
    def __init__(self) -> None:
        super().__init__()
        self._worker: ProcessingWorker | None = None
        self.review_records: list[dict] = []
        self.current_review_item: dict | None = None
        self.zoom_factor = 1.0
        self.current_rotation = 0
        self.view_text_mode = False
        self._init_ui()

    def _init_ui(self) -> None:
        self.setWindowTitle("PDF & Image Multi-Query Extractor & Review HIL Pipeline")
        self.setMinimumSize(1150, 700)

        window_layout = QVBoxLayout(self)
        self.tabs = QTabWidget()
        window_layout.addWidget(self.tabs)

        # TAB 1: DASHBOARD EXTRACTOR
        tab_dash = QWidget()
        dash_layout = QHBoxLayout(tab_dash)
        dash_layout.setSpacing(15)
        
        left_panel = QVBoxLayout()
        row_in = QHBoxLayout(); self.input_edit = QLineEdit(placeholderText="Input folder...", readOnly=True)
        btn_in = QPushButton("Browse Input"); btn_in.clicked.connect(self._browse_input)
        row_in.addWidget(self.input_edit); row_in.addWidget(btn_in); left_panel.addLayout(row_in)

        row_out = QHBoxLayout(); self.output_edit = QLineEdit(placeholderText="Output destination...", readOnly=True)
        btn_out = QPushButton("Browse Output"); btn_out.clicked.connect(self._browse_output)
        row_out.addWidget(self.output_edit); row_out.addWidget(btn_out); left_panel.addLayout(row_out)

        self.query_edit = QTextEdit(placeholderText="Queries (one per line)...")
        left_panel.addWidget(QLabel("Queries:"))
        left_panel.addWidget(self.query_edit, stretch=1)

        # RESTORED: Import queries from .txt file button
        btn_import = QPushButton("Import Queries from .txt File")
        btn_import.clicked.connect(self._import_txt)
        left_panel.addWidget(btn_import)

        self.status_label = QLabel("Status: Ready")
        self.progress_bar = QProgressBar()
        left_panel.addWidget(self.status_label); left_panel.addWidget(self.progress_bar)

        row_act = QHBoxLayout()
        self.btn_run = QPushButton("Start Processing"); self.btn_run.clicked.connect(self._start)
        self.btn_cancel = QPushButton("Cancel"); self.btn_cancel.setEnabled(False); self.btn_cancel.clicked.connect(self._cancel)
        row_act.addWidget(self.btn_run); row_act.addWidget(self.btn_cancel); left_panel.addLayout(row_act)

        right_panel = QVBoxLayout()
        self.result_table = QTableWidget(0, 2); self.result_table.setHorizontalHeaderLabels(["Query", "Hits"])
        self.result_table.horizontalHeader().setStretchLastSection(True)
        right_panel.addWidget(QLabel("Metrics Overview"))
        right_panel.addWidget(self.result_table)

        dash_layout.addLayout(left_panel, stretch=4)
        dash_layout.addWidget(QFrame())
        dash_layout.addLayout(right_panel, stretch=5)
        self.tabs.addTab(tab_dash, "Data Extraction Engine")

        # TAB 2: MANUAL REVIEW SYSTEM
        self.tab_review = QWidget()
        review_layout = QHBoxLayout(self.tab_review)
        
        splitter = QSplitter(Qt.Horizontal)
        review_layout.addWidget(splitter)

        left_review_widget = QWidget()
        left_review_layout = QVBoxLayout(left_review_widget)
        
        # Tree Tree Utility Controls (Expand/Collapse All)
        tree_utility_row = QHBoxLayout()
        btn_expand_all = QPushButton("Expand All"); btn_expand_all.clicked.connect(self.review_tree_expand)
        btn_collapse_all = QPushButton("Collapse All"); btn_collapse_all.clicked.connect(self.review_tree_collapse)
        tree_utility_row.addWidget(btn_expand_all)
        tree_utility_row.addWidget(btn_collapse_all)
        left_review_layout.addLayout(tree_utility_row)

        self.review_tree = QTreeView()
        self.tree_model = QStandardItemModel()
        self.tree_model.setHorizontalHeaderLabels(["Query Elements / Page Index Hierarchy"])
        self.review_tree.setModel(self.tree_model)
        self.review_tree.clicked.connect(self._tree_item_selected)
        left_review_layout.addWidget(QLabel("Extracted Targets / Candidates Tree View"))
        left_review_layout.addWidget(self.review_tree)
        splitter.addWidget(left_review_widget)

        right_review_widget = QWidget()
        right_review_layout = QVBoxLayout(right_review_widget)
        
        row_ctrls = QHBoxLayout()
        btn_z_in = QPushButton("Zoom In"); btn_z_in.clicked.connect(lambda: self._adjust_zoom(1.2))
        btn_z_out = QPushButton("Zoom Out"); btn_z_out.clicked.connect(lambda: self._adjust_zoom(0.8))
        btn_ccw = QPushButton("Rotate CCW"); btn_ccw.clicked.connect(lambda: self._rotate(-90))
        btn_cw = QPushButton("Rotate CW"); btn_cw.clicked.connect(lambda: self._rotate(90))
        self.btn_toggle_view = QPushButton("Switch to Text Layer View"); self.btn_toggle_view.clicked.connect(self._toggle_view_mode)
        row_ctrls.addWidget(btn_z_in); row_ctrls.addWidget(btn_z_out); row_ctrls.addWidget(btn_ccw); row_ctrls.addWidget(btn_cw); row_ctrls.addWidget(self.btn_toggle_view)
        right_review_layout.addLayout(row_ctrls)

        self.gfx_view = QGraphicsView()
        self.gfx_scene = QGraphicsScene()
        self.gfx_view.setScene(self.gfx_scene)
        
        self.text_preview = QTextEdit()
        self.text_preview.setReadOnly(True)
        self.text_preview.hide()
        
        right_review_layout.addWidget(self.gfx_view, stretch=1)
        right_review_layout.addWidget(self.text_preview, stretch=1)

        row_decision = QHBoxLayout()
        self.btn_approve = QPushButton("Approve Candidate Page"); self.btn_approve.setStyleSheet("background-color:#27ae60;color:white;font-weight:bold;padding:6px;")
        self.btn_reject = QPushButton("Reject / Extirpate Page"); self.btn_reject.setStyleSheet("background-color:#c0392b;color:white;font-weight:bold;padding:6px;")
        self.btn_approve.clicked.connect(self._approve_current_item)
        self.btn_reject.clicked.connect(self._reject_current_item)
        row_decision.addWidget(self.btn_approve); row_decision.addWidget(self.btn_reject)
        right_review_layout.addLayout(row_decision)

        splitter.addWidget(right_review_widget)
        splitter.setSizes([400, 750])
        self.tabs.addTab(self.tab_review, "Manual Review Panel")

    def _browse_input(self):
        d = QFileDialog.getExistingDirectory(self, "Input")
        if d: self.input_edit.setText(d)

    def _browse_output(self):
        d = QFileDialog.getExistingDirectory(self, "Output")
        if d: self.output_edit.setText(d)

    def _import_txt(self) -> None:
        fp, _ = QFileDialog.getOpenFileName(self, "Open Query File", "", "Text Files (*.txt)")
        if not fp: return
        try:
            with open(fp, encoding="utf-8", errors="ignore") as fh:
                lines = [ln.strip() for ln in fh if ln.strip() and not ln.strip().startswith("[")]
            self.query_edit.setPlainText("\n".join(lines))
            QMessageBox.information(self, "Imported", f"Loaded {len(lines)} queries.")
        except Exception as exc:
            QMessageBox.critical(self, "Error", f"Failed to read file:\n{exc}")

    def review_tree_expand(self): self.review_tree.expandAll()
    def review_tree_collapse(self): self.review_tree.collapseAll()

    def _start(self) -> None:
        input_dir = self.input_edit.text().strip()
        output_dir = self.output_edit.text().strip()
        queries = [q.strip() for q in self.query_edit.toPlainText().split("\n") if q.strip()]

        if not input_dir or not output_dir or not queries:
            QMessageBox.warning(self, "Configuration Check", "Ensure directories and queries are defined completely.")
            return

        self.btn_run.setEnabled(False); self.btn_cancel.setEnabled(True)
        self.progress_bar.setRange(0, 0)
        self._worker = ProcessingWorker(input_dir, queries, output_dir)
        self._worker.progress_signal.connect(self._on_progress)
        self._worker.finished_signal.connect(self._on_finished)
        self._worker.start()

    def _cancel(self):
        if self._worker: self._worker.cancel()

    def _on_progress(self, current: int, total: int, msg: str):
        if self.progress_bar.maximum() == 0: self.progress_bar.setRange(0, total)
        self.progress_bar.setValue(current)
        self.status_label.setText(msg)

    def _on_finished(self, counts: dict[str, int], review_data: list[dict]):
        self.btn_run.setEnabled(True); self.btn_cancel.setEnabled(False)
        self.progress_bar.setRange(0, 100); self.progress_bar.setValue(100)
        self.status_label.setText("Batch run finished. Verification assets mapped to Review Tab.")
        self.review_records = review_data
        
        self.result_table.setRowCount(len(counts))
        for idx, (q, c) in enumerate(sorted(counts.items(), key=lambda x: x[1])):
            self.result_table.setItem(idx, 0, QTableWidgetItem(q))
            self.result_table.setItem(idx, 1, QTableWidgetItem(str(c)))

        self._rebuild_review_tree()
        self.tabs.setCurrentWidget(self.tab_review)

    def _rebuild_review_tree(self) -> None:
            self.tree_model.clear()
            self.tree_model.setHorizontalHeaderLabels(["Query Target Layout Mapping Tree"])
            
            query_buckets = defaultdict(list)
            for item in self.review_records:
                query_buckets[item["query"]].append(item)

            for query, items in query_buckets.items():
                query_node = QStandardItem(query)
                query_node.setSelectable(False)
                self.tree_model.appendRow(query_node)

                # Sort strategy: Lesser missing words float directly to the top
                sorted_items = sorted(items, key=lambda x: len(x["missing_words"]))

                for item in sorted_items:
                    p_name = Path(item["file_path"]).name
                    display_label = f"Page {item['page_idx'] + 1} -> {p_name}"
                    
                    if item["pre_approved"]:
                        display_label += " [PRE-APPROVED MATCH]"
                        page_node = QStandardItem(display_label)
                        page_node.setForeground(QBrush(QColor("#27ae60")))
                    else:
                        page_node = QStandardItem()
                        # Create the blood-red background badge for each missing word
                        missing_styled = " ".join([f'<span style="background-color:#8b0000; color:#ffffff; font-weight:bold; padding:2px; border-radius:3px;">{w}</span>' for w in item["missing_words"]])
                        
                        # FIXED: Added the missing words directly into the item display label using HTML parsing rules
                        page_node.setText(f"Page {item['page_idx'] + 1} -> {p_name} [CANDIDATE] | Missing: ")
                        
                        # Appending a secondary item or embedding HTML strings natively in text works best via tooltips or adjacent node labels. 
                        # To display raw HTML inside standard QTreeView nodes without custom delegates, we can format the text explicitly:
                        page_node.setText(f"Page {item['page_idx'] + 1} -> {p_name} [CANDIDATE] (Missing: {', '.join(item['missing_words'])})")
                        page_node.setToolTip(f"Missing terms: {', '.join(item['missing_words'])}")
                        page_node.setForeground(QBrush(QColor("#d35400")))
                    
                    page_node.setData(item, Qt.UserRole)
                    query_node.appendRow(page_node)
            
            self.review_tree.expandAll()

    def _tree_item_selected(self, index) -> None:
        node = self.tree_model.itemFromIndex(index)
        if not node: return
        item_data = node.data(Qt.UserRole)
        if not item_data: return

        self.current_review_item = item_data
        self.zoom_factor = 1.0
        self.current_rotation = 0
        self._render_selected_element()

    def _render_selected_element(self) -> None:
        if not self.current_review_item: return
        item = self.current_review_item

        if self.view_text_mode:
            self.gfx_view.hide()
            self.text_preview.show()
            
            raw_text = item["text_content"]
            if not raw_text.strip():
                self.text_preview.setPlainText("[No text layer parsed inside cache storage framework]")
                return

            # Highlight exact token matches in brilliant yellow
            tokens = [w.strip() for w in item["query"].split() if len(w.strip()) > 1]
            html_text = raw_text
            
            # Escape basic HTML characters to prevent rendering collision bugs
            html_text = html_text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
            
            for token in tokens:
                if token:
                    pattern = re.compile(re.escape(token), re.IGNORECASE)
                    html_text = pattern.sub(lambda m: f'<span style="background-color: #ffff00; color: #000000; font-weight: bold;">{m.group(0)}</span>', html_text)
            
            # Format display carriage breaks cleanly
            html_text = html_text.replace("\n", "<br>")
            self.text_preview.setHtml(f"<div style='font-family: monospace; font-size: 12px;'>{html_text}</div>")
        else:
            self.text_preview.hide()
            self.gfx_view.show()
            self.gfx_scene.clear()

            f_path = item["file_path"]
            is_pdf = Path(f_path).suffix.lower() == ".pdf"
            q_pixmap = None

            try:
                if is_pdf:
                    doc = fitz.open(_unc(f_path))
                    page = doc[item["page_idx"]]
                    pix = page.get_pixmap(dpi=150)
                    q_img = QImage(pix.samples, pix.width, pix.height, pix.stride, QImage.Format_RGB888)
                    q_pixmap = QPixmap.fromImage(q_img)
                    doc.close()
                else:
                    with Image.open(f_path) as img:
                        img_corr = ImageOps.exif_transpose(img).convert("RGB")
                        byte_arr = io.BytesIO()
                        img_corr.save(byte_arr, format='PNG')
                        q_pixmap = QPixmap()
                        q_pixmap.loadFromData(byte_arr.getvalue(), 'PNG')
            except Exception as e:
                log.error("Failed structural draw view pass: %s", e)
                return

            if q_pixmap and not q_pixmap.isNull():
                pix_item = self.gfx_scene.addPixmap(q_pixmap)
                self.gfx_scene.setSceneRect(pix_item.boundingRect())
                self._apply_transformations()
                self.gfx_view.fitInView(pix_item, Qt.KeepAspectRatio)

    def _apply_transformations(self) -> None:
        trans = QTransform()
        trans.scale(self.zoom_factor, self.zoom_factor)
        trans.rotate(self.current_rotation)
        self.gfx_view.setTransform(trans)

    def _adjust_zoom(self, factor: float) -> None:
        self.zoom_factor *= factor
        self._apply_transformations()

    def _rotate(self, degrees: int) -> None:
        self.current_rotation = (self.current_rotation + degrees) % 360
        self._apply_transformations()

    def _toggle_view_mode(self) -> None:
        self.view_text_mode = not self.view_text_mode
        self.btn_toggle_view.setText("Switch to Graphics Image View" if self.view_text_mode else "Switch to Text Layer View")
        self._render_selected_element()

    def _approve_current_item(self) -> None:
        if not self.current_review_item: return
        item = self.current_review_item
        
        if not item["pre_approved"]:
            try:
                folder = Path(self.output_edit.text().strip()) / safe_folder_name(item["query"])
                folder.mkdir(parents=True, exist_ok=True)
                p_obj = Path(item["file_path"])
                
                if p_obj.suffix.lower() == ".pdf":
                    doc = fitz.open(_unc(item["file_path"]))
                    out_doc = fitz.open()
                    out_doc.insert_pdf(doc, from_page=item["page_idx"], to_page=item["page_idx"])
                    out_doc.save(_unc(str(folder / f"{p_obj.stem}_approved_{item['file_hash']}.pdf")), garbage=4, deflate=True)
                    out_doc.close(); doc.close()
                else:
                    import shutil
                    shutil.copy2(item["file_path"], folder / f"{p_obj.stem}_approved_{item['file_hash']}{p_obj.suffix}")
                    
                item["pre_approved"] = True
                QMessageBox.information(self, "Status Synchronization", "Candidate page approved and exported to output successfully.")
                self._rebuild_review_tree()
            except Exception as e:
                QMessageBox.critical(self, "I/O Error", f"Failed manual export sequence: {e}")

    def _reject_current_item(self) -> None:
        if not self.current_review_item: return
        item = self.current_review_item
        
        if item["pre_approved"]:
            try:
                folder = Path(self.output_edit.text().strip()) / safe_folder_name(item["query"])
                p_obj = Path(item["file_path"])
                
                target_path = folder / (f"{p_obj.stem}_{item['file_hash']}.pdf" if p_obj.suffix.lower() == ".pdf" else f"{p_obj.stem}_{item['file_hash']}{p_obj.suffix}")
                if target_path.exists():
                    target_path.unlink()
                
                item["pre_approved"] = False
                QMessageBox.information(self, "Status Synchronization", "Page extraction rejected and physical file purged successfully.")
                self._rebuild_review_tree()
            except Exception as e:
                QMessageBox.critical(self, "I/O Error", f"Failed cleanup sequence: {e}")

def main() -> None:
    multiprocessing.freeze_support()
    _setup_logging()
    app = QApplication(sys.argv)
    window = ExtractorApp()
    window.showNormal()
    sys.exit(app.exec())

if __name__ == "__main__":
    main()