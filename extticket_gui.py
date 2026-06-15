# /// script
# requires-python = ">=3.10"
# dependencies = [
#     "PySide6>=6.5.0",
#     "pymupdf>=1.24.0",
#     "winrt-Windows.Media.Ocr",
#     "winrt-Windows.Storage.Streams",
#     "winrt-Windows.Graphics.Imaging",
#     "winrt-Windows.Security.Cryptography",
#     "pillow",
# ]
# ///

import os
import csv
import hashlib
import sys
import asyncio
from PySide6.QtWidgets import (QApplication, QWidget, QLabel, QLineEdit, 
                             QTextEdit, QPushButton, QVBoxLayout, QHBoxLayout, 
                             QFileDialog, QMessageBox, QProgressBar)
from PySide6.QtCore import Qt, QThread, Signal

import fitz  # PyMuPDF
from winrt.windows.media.ocr import OcrEngine
from winrt.windows.storage.streams import InMemoryRandomAccessStream
from winrt.windows.security.cryptography import CryptographicBuffer
from winrt.windows.graphics.imaging import BitmapDecoder
from PIL import Image

def get_path_hash(filepath):
    return hashlib.md5(filepath.encode('utf-8')).hexdigest()[:8]

# Async function to handle WinRT OCR for a single PIL Image
async def ocr_image_winrt(pil_img):
    import io
    img_byte_arr = io.BytesIO()
    pil_img.save(img_byte_arr, format='PNG')
    img_bytes = img_byte_arr.getvalue()
    
    winrt_buffer = CryptographicBuffer.create_from_byte_array(img_bytes)
    stream = InMemoryRandomAccessStream()
    await stream.write_async(winrt_buffer)
    stream.seek(0)
    
    decoder = await BitmapDecoder.create_async(stream)
    software_bitmap = await decoder.get_software_bitmap_async()
    
    engine = OcrEngine.try_create_from_user_profile_languages()
    if not engine:
        return ""
        
    ocr_result = await engine.recognize_async(software_bitmap)
    return ocr_result.text

def run_winrt_ocr(pil_img):
    try:
        return asyncio.run(ocr_image_winrt(pil_img))
    except Exception as e:
        print(f"OCR Error: {e}")
        return ""

def matches_query_flexibly(query, page_text):
    clean_text = page_text.lower().replace(" ", "")
    name_parts = [word.lower() for word in query.split() if len(word) > 1]
    if not name_parts:
        return False
    return all(part in clean_text for part in name_parts)

def render_page_to_pil(page):
    pix = page.get_pixmap(dpi=300)
    return Image.frombytes("RGB", [pix.width, pix.height], pix.samples)


class ProcessingWorker(QThread):
    progress_signal = Signal(str)
    finished_signal = Signal(dict)
    error_signal = Signal(str)

    def __init__(self, input_dir, queries, output_dir):
        super().__init__()
        self.input_dir = input_dir
        self.queries = queries
        self.output_dir = output_dir

    def run(self):
        try:
            pdf_files = []
            for root_dir, _, files in os.walk(self.input_dir):
                for file in files:
                    if file.lower().endswith('.pdf'):
                        pdf_files.append(os.path.join(root_dir, file))
            
            if not pdf_files:
                self.error_signal.emit("No PDF files found in the input directory.")
                return

            query_match_counts = {query: 0 for query in self.queries}

            for idx, pdf_path in enumerate(pdf_files):
                pdf_name = os.path.splitext(os.path.basename(pdf_path))[0]
                path_hash = get_path_hash(pdf_path)
                self.progress_signal.emit(f"Processing ({idx+1}/{len(pdf_files)}): {os.path.basename(pdf_path)}")
                
                abs_pdf_path = os.path.abspath(pdf_path)
                if not abs_pdf_path.startswith("\\\\?\\"):
                    abs_pdf_path = "\\\\?\\" + abs_pdf_path
                
                doc = fitz.open(abs_pdf_path)
                total_pages = len(doc)
                
                total_extracted_chars = sum(len(page.get_text() or "") for page in doc)
                force_ocr = total_extracted_chars < 300
                ocr_pages_cache = {}

                if force_ocr:
                    self.progress_signal.emit(f"-> Low text layer found. OCRing via WinRT...")
                    for p_idx in range(total_pages):
                        pil_img = render_page_to_pil(doc[p_idx])
                        ocr_pages_cache[p_idx] = run_winrt_ocr(pil_img)
                
                for query in self.queries:
                    out_doc = fitz.open()
                    pages_matched = 0
                    
                    for page_num in range(total_pages):
                        page_text = ocr_pages_cache.get(page_num, "") if force_ocr else (doc[page_num].get_text() or "")
                        
                        if matches_query_flexibly(query, page_text):
                            out_doc.insert_pdf(doc, from_page=page_num, to_page=page_num)
                            pages_matched += 1
                    
                    if pages_matched > 0:
                        query_match_counts[query] += pages_matched
                        clean_query_folder = "".join(i for i in query if i.isalnum() or i in (' ', '_', '-')).strip()
                        target_folder = os.path.join(self.output_dir, clean_query_folder)
                        os.makedirs(target_folder, exist_ok=True)
                        
                        output_filename = f"{pdf_name}_{path_hash}.pdf"
                        output_path = os.path.join(target_folder, output_filename)
                        
                        abs_output_path = os.path.abspath(output_path)
                        if not abs_output_path.startswith("\\\\?\\"):
                            abs_output_path = "\\\\?\\" + abs_output_path
                            
                        out_doc.save(abs_output_path)
                        out_doc.close()
                    else:
                        out_doc.close()
                
                doc.close()

            csv_file_path = os.path.join(self.output_dir, "query_match_counts.csv")
            abs_csv_path = os.path.abspath(csv_file_path)
            if not abs_csv_path.startswith("\\\\?\\"):
                abs_csv_path = "\\\\?\\" + abs_csv_path
                
            with open(abs_csv_path, 'w', newline='', encoding='utf-8') as csv_file:
                writer = csv.writer(csv_file)
                writer.writerow(["query", "page match count"])
                for query, count in query_match_counts.items():
                    writer.writerow([query, count])

            self.finished_signal.emit(query_match_counts)

        except Exception as e:
            self.error_signal.emit(str(e))


class ExtractorApp(QWidget):
    def __init__(self):
        super().__init__()
        self.init_ui()

    def init_ui(self):
        self.setWindowTitle("PDF Multi-Query Extractor (PySide6)")
        
        # --- Clean Window Initialization Fix ---
        # Instead of generic resizing, we assign an ideal default footprint
        # and enforce a maximum width restriction so it cannot expand uncontrollably.
        self.setMinimumSize(550, 600)
        self.setMaximumWidth(750) 

        layout = QVBoxLayout()

        # Input Directory Selection
        h_layout1 = QHBoxLayout()
        self.input_label = QLineEdit()
        self.input_label.setPlaceholderText("Select input directory containing PDFs...")
        self.input_label.setReadOnly(True)
        btn_input = QPushButton("Browse Input")
        btn_input.clicked.connect(self.browse_input)
        h_layout1.addWidget(self.input_label)
        h_layout1.addWidget(btn_input)
        layout.addLayout(h_layout1)

        # Output Directory Selection
        h_layout2 = QHBoxLayout()
        self.output_label = QLineEdit()
        self.output_label.setPlaceholderText("Select output destination folder...")
        self.output_label.setReadOnly(True)
        btn_output = QPushButton("Browse Output")
        btn_output.clicked.connect(self.browse_output)
        h_layout2.addWidget(self.output_label)
        h_layout2.addWidget(btn_output)
        layout.addLayout(h_layout2)

        # Inline Query Text Edit Box
        layout.addWidget(QLabel("Queries / Search terms (One word/phrase per row):"))
        self.query_text_edit = QTextEdit()
        self.query_text_edit.setPlaceholderText("Type or paste your queries inline directly here...\nExample:\nIQBAL MAULANA FAUZI\nPATRICK STAR")
        layout.addWidget(self.query_text_edit)

        # Optional TXT Import Button
        btn_import_txt = QPushButton("Or Import Queries from .txt File")
        btn_import_txt.clicked.connect(self.import_txt_queries)
        layout.addWidget(btn_import_txt)

        # Progress / Status Section
        self.status_label = QLabel("Status: Ready")
        layout.addWidget(self.status_label)
        
        self.progress_bar = QProgressBar()
        self.progress_bar.setTextVisible(False)
        layout.addWidget(self.progress_bar)

        # Main Start Processing Button
        self.btn_run = QPushButton("Start Processing")
        self.btn_run.setStyleSheet("font-weight: bold; background-color: #2b78e4; color: white; padding: 8px;")
        self.btn_run.clicked.connect(self.start_processing)
        layout.addWidget(self.btn_run)

        self.setLayout(layout)

    def browse_input(self):
        dir_path = QFileDialog.getExistingDirectory(self, "Select Input Directory")
        if dir_path:
            self.input_label.setText(dir_path)

    def browse_output(self):
        dir_path = QFileDialog.getExistingDirectory(self, "Select Output Directory")
        if dir_path:
            self.output_label.setText(dir_path)

    def import_txt_queries(self):
        file_path, _ = QFileDialog.getOpenFileName(self, "Open Query File", "", "Text Files (*.txt)")
        if file_path:
            try:
                with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                    lines = [line.strip() for line in f if line.strip() and not line.strip().startswith('[')]
                self.query_text_edit.setPlainText("\n".join(lines))
                QMessageBox.information(self, "Imported", f"Successfully loaded {len(lines)} queries inline.")
            except Exception as e:
                QMessageBox.critical(self, "Error", f"Failed to read file: {e}")

    def start_processing(self):
        input_dir = self.input_label.text()
        output_dir = self.output_label.text()
        
        raw_queries = self.query_text_edit.toPlainText().split('\n')
        queries = [q.strip() for q in raw_queries if q.strip()]

        if not input_dir or not output_dir:
            QMessageBox.warning(self, "Validation Error", "Please select both Input and Output folders.")
            return
        if not queries:
            QMessageBox.warning(self, "Validation Error", "Please enter at least one query row.")
            return

        self.btn_run.setEnabled(False)
        self.progress_bar.setRange(0, 0)
        
        self.worker = ProcessingWorker(input_dir, queries, output_dir)
        self.worker.progress_signal.connect(self.update_status)
        self.worker.finished_signal.connect(self.on_finished)
        self.worker.error_signal.connect(self.on_error)
        self.worker.start()

    def update_status(self, text):
        self.status_label.setText(f"Status: {text}")

    def on_error(self, err_msg):
        self.progress_bar.setRange(0, 100)
        self.progress_bar.setValue(0)
        self.btn_run.setEnabled(True)
        self.status_label.setText("Status: Error encountered.")
        QMessageBox.critical(self, "Error", err_msg)

    def on_finished(self, summary_counts):
        self.progress_bar.setRange(0, 100)
        self.progress_bar.setValue(100)
        self.btn_run.setEnabled(True)
        self.status_label.setText("Status: Extraction Complete!")
        QMessageBox.information(self, "Success", "Processing complete! Metrics saved to query_match_counts.csv")


def main():
    app = QApplication(sys.argv)
    window = ExtractorApp()
    window.show()
    sys.exit(app.exec())

if __name__ == "__main__":
    main()