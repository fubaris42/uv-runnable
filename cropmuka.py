#!/usr/bin/env python3
# /// script
# requires-python = "==3.13"
# dependencies = [
#     "deepface",
#     "numpy",
#     "onnx",
#     "onnxruntime",
#     "pillow",
#     "tf-keras",
# ]
# ///

from pathlib import Path
from PIL import Image, ImageOps  # Added ImageOps here
import numpy as np
from deepface import DeepFace

# Config
SUPPORTED_EXT = {".png", ".jpg", ".jpeg"}
DEEPFACE_DETECTOR = (
    "retinaface"  # Options: 'opencv', 'ssd', 'dlib', 'mtcnn', 'retinaface', 'mediapipe'
)

PORTRAIT_ASPECT_RATIO = 3 / 4
VERTICAL_EXPANSION_FACTOR = 1.8
FACE_HORIZONTAL_PADDING = 1.1
FACE_VERTICAL_ANCHOR = 0.23

print(f"DeepFace initialized with detector backend: {DEEPFACE_DETECTOR}")


def get_face_bbox(img: Image.Image) -> tuple[int, int, int, int] | None:
    """
    Detects the largest face in the LEFT HALF of the image using DeepFace.
    This speeds up detection and prevents memory crashes on 2-page scans.
    Returns (x0, y0, x1, y1) in PIL format (left, top, right, bottom).
    """
    img_width, img_height = img.size
    
    # Crop the image to only the left half
    left_half_width = int(img_width * 0.5)
    left_half = img.crop((0, 0, left_half_width, img_height))
    
    img_np = np.array(left_half.convert("RGB"))

    try:
        detected_faces = DeepFace.extract_faces(
            img_path=img_np,
            detector_backend=DEEPFACE_DETECTOR,
            enforce_detection=False,
            align=False,
        )

        if not detected_faces or not any("facial_area" in d for d in detected_faces):
            return None

        # Find the largest face in that left half
        largest_face_data = max(
            detected_faces, key=lambda d: d["facial_area"]["w"] * d["facial_area"]["h"]
        )

        area = largest_face_data["facial_area"]
        x, y, w, h = area["x"], area["y"], area["w"], area["h"]

        # Because we sliced from the top-left (0,0), these coordinates 
        # are exactly the same on the original image!
        return (x, y, x + w, y + h)

    except Exception as e:
        print(f"DeepFace detection failed on image: {e}")
        return None


def calculate_3_4_crop(
    face_bbox: tuple[int, int, int, int],
    img_width: int,
    img_height: int,
) -> tuple[int, int, int, int]:
    """
    Calculates a 3:4 aspect ratio bounding box based on the face_bbox,
    using global tuning constants for portrait composition.
    """
    x0_face, y0_face, x1_face, y1_face = face_bbox
    w_face = x1_face - x0_face
    h_face = y1_face - y0_face

    H_crop_initial = int(h_face * VERTICAL_EXPANSION_FACTOR)

    W_crop = int(H_crop_initial * PORTRAIT_ASPECT_RATIO)

    if W_crop < w_face * FACE_HORIZONTAL_PADDING:
        W_crop = int(w_face * FACE_HORIZONTAL_PADDING)
        H_crop = int(W_crop / PORTRAIT_ASPECT_RATIO)
    else:
        H_crop = H_crop_initial

    y0_crop = int(y0_face - H_crop * FACE_VERTICAL_ANCHOR)
    y1_crop = y0_crop + H_crop

    cx_face = (x0_face + x1_face) / 2
    x0_crop = int(cx_face - W_crop / 2)
    x1_crop = x0_crop + W_crop

    dx = 0
    if x0_crop < 0:
        dx = -x0_crop
    elif x1_crop > img_width:
        dx = img_width - x1_crop
    x0_crop += dx
    x1_crop += dx

    dy = 0
    if y0_crop < 0:
        dy = -y0_crop
    elif y1_crop > img_height:
        dy = img_height - y1_crop
    y0_crop += dy
    y1_crop += dy

    x0_final = max(0, int(x0_crop))
    y0_final = max(0, int(y0_crop))
    x1_final = min(img_width, int(x1_crop))
    y1_final = min(img_height, int(y1_crop))

    return (x0_final, y0_final, x1_final, y1_final)


def crop_face_portrait_and_save(input_path: Path, output_path: Path):
    """
    Opens an image, applies EXIF rotation, finds the face bounding box, 
    calculates a 3:4 crop centered on the face, and saves it.
    """
    try:
        # 1. Open the image
        img = Image.open(input_path)
        
        # 2. Fix the EXIF rotation issue before doing anything else!
        img = ImageOps.exif_transpose(img)
        
        # 3. Convert to RGB for DeepFace
        img = img.convert("RGB")
        
        img_width, img_height = img.size

        face_bbox = get_face_bbox(img)

        if face_bbox:
            crop_bbox = calculate_3_4_crop(face_bbox, img_width, img_height)

            cropped = img.crop(crop_bbox)

            output_extension = input_path.suffix.upper()[1:]
            output_format = (
                "JPEG" if output_extension in ("JPG", "JPEG") else output_extension
            )

            cropped.save(output_path, format=output_format)

            print(
                f"Cropped (3:4, Face-anchored) and saved: {input_path.relative_to(Path.cwd())} → {output_path.name}"
            )
        else:
            print(f"No face found in {input_path.name}, skipped.")

    except Exception as e:
        print(f"Failed to process {input_path.name}: {e}")


def process_directory(input_dir: Path, output_dir: Path):
    """
    Recursively scans the input directory, processes supported images,
    and saves them to the output directory while maintaining the relative structure.
    """
    output_dir.mkdir(parents=True, exist_ok=True)

    print(f"Scanning directory: {input_dir}")
    print(f"Output directory:   {output_dir}")
    print("-" * 50)

    for source_path in input_dir.rglob("*"):

        if source_path.is_relative_to(output_dir):
            continue

        if source_path.is_dir():
            continue

        if source_path.suffix.lower() in SUPPORTED_EXT:
            rel_path = source_path.parent.relative_to(input_dir)
            target_dir = output_dir / rel_path
            target_dir.mkdir(parents=True, exist_ok=True)

            target_file_path = target_dir / source_path.name

            crop_face_portrait_and_save(source_path, target_file_path)


if __name__ == "__main__":
    input_directory = Path.cwd()
    output_directory = input_directory / "deepface_3_4_portrait_crops"

    process_directory(input_directory, output_directory)

    print("-" * 50)
    print("Processing complete.")