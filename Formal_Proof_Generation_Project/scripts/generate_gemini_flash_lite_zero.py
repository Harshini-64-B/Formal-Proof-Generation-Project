import os
import time
import csv
import re
from pathlib import Path

from google import genai

# ============================================================
# PATH CONFIGURATION
# ============================================================

# This script is located at:
#
# Formal_Proof_Generation_Project/
# └── scripts/
#     └── generate_gemini_flash_lite_zero.py
#
# Therefore:
#
# SCRIPT_DIR  = Formal_Proof_Generation_Project/scripts
# PROJECT_DIR = Formal_Proof_Generation_Project
#
# Theorem files:
#   Formal_Proof_Generation_Project/theorems/
#
# Gemini Flash-Lite zero-shot outputs:
#   Formal_Proof_Generation_Project/outputs/gemini_flash_lite_zero/
#
# Gemini Flash-Lite zero-shot metadata:
#   Formal_Proof_Generation_Project/gemini_flash_lite_zero_metadata.csv
# ============================================================

SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_DIR = SCRIPT_DIR.parent

THEOREMS_DIR = PROJECT_DIR / "theorems"

OUTPUT_DIR = PROJECT_DIR / "outputs" / "gemini_flash_lite_zero"
# Create the output directory if it does not already exist
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)


METADATA_FILE = (
    PROJECT_DIR / "gemini_flash_lite_zero_metadata.csv"
)


# ============================================================
# EXPERIMENT CONFIGURATION
# ============================================================

DOMAINS = [
    "Lists",
    "Nat",
    "Prop",
    "Group",
]


# ============================================================
# GEMINI CONFIGURATION
# ============================================================

MODEL = "gemini-3.5-flash-lite"

# Read API key from environment variable.
# Do not put the actual API key in this file.

API_KEY = os.getenv("GEMINI_API_KEY")

if not API_KEY:
    raise RuntimeError(
        "\nGEMINI_API_KEY is not set.\n"
        "Set your Google Gemini API key as an environment "
        "variable before running this script.\n"
    )

# Create Gemini client.
client = genai.Client(api_key=API_KEY)

# Delay between requests
REQUEST_DELAY = 2


# ============================================================
# PROMPT
# ============================================================

def build_prompt(file_text):
    """
    Extract only the theorem declaration.

    Imports and namespaces are ignored.
    """

    match = re.search(
        r"(?ms)^theorem\s+.*?:=\s*by\b.*?\bsorry\b",
        file_text,
    )

    if not match:
        raise ValueError(
            "Could not find a theorem declaration with "
            "':= by ... sorry'."
        )

    theorem_text = match.group(0).strip()

    return (
    "Complete the following Lean 4 theorem by replacing `sorry` with a valid proof.\n"
    "Return exactly ONE completed theorem.\n"
    "Return the complete theorem declaration, including the theorem name, "
    "arguments, statement, and proof.\n"
    "The proof must use the `:= by` format.\n"
    "Do not change the theorem name, arguments, or statement.\n"
    "Do not provide alternative proofs or multiple versions of the theorem.\n"
    "Do not include explanations, comments, introductory text, concluding text, "
    "or Markdown code fences.\n"
    "Return only the completed Lean theorem.\n\n"
    "Theorem to complete:\n"
    + theorem_text
)


# ============================================================
# METADATA CSV
# ============================================================

CSV_FIELDS = [
    "model",
    "prompt_type",
    "domain",
    "theorem_file",
    "output_file",
    "prompt_tokens",
    "completion_tokens",
    "total_tokens",
    "latency_seconds",
]


def initialize_metadata_csv():
    """
    Create the metadata CSV file if it does not exist.

    If the CSV already exists, it is left unchanged.
    """

    if not METADATA_FILE.exists():

        with METADATA_FILE.open(
            "w",
            newline="",
            encoding="utf-8",
        ) as csv_file:

            writer = csv.DictWriter(
                csv_file,
                fieldnames=CSV_FIELDS,
            )

            writer.writeheader()


def append_metadata(
    domain,
    theorem_file,
    output_file,
    usage,
):
    """
    Append metadata for one successfully generated theorem
    to the CSV file immediately after generation.
    """

    with METADATA_FILE.open(
        "a",
        newline="",
        encoding="utf-8",
    ) as csv_file:

        writer = csv.DictWriter(
            csv_file,
            fieldnames=CSV_FIELDS,
        )

        writer.writerow(
            {
                "model": MODEL,
                "prompt_type": "zero",
                "domain": domain,
                "theorem_file": theorem_file.name,
                "output_file": output_file.name,
                "prompt_tokens": usage.get(
                    "prompt_tokens",
                    "N/A",
                ),
                "completion_tokens": usage.get(
                    "completion_tokens",
                    "N/A",
                ),
                "total_tokens": usage.get(
                    "total_tokens",
                    "N/A",
                ),
                "latency_seconds": usage.get(
                    "latency_seconds",
                    "N/A",
                ),
            }
        )


# ============================================================
# GEMINI API REQUEST
# ============================================================

def generate_proof(prompt):
    """
    Send one theorem prompt to Gemini.

    Returns:
        response_text
        usage
    """

    start_time = time.perf_counter()

    response = client.models.generate_content(
        model=MODEL,
        contents=prompt,
        config={
            "temperature": 0,
        },
    )

    latency = time.perf_counter() - start_time

    response_text = response.text.strip()

    # Remove Markdown code fences
    response_text = re.sub(r"^```(?:lean)?\s*", "", response_text)
    response_text = re.sub(r"\s*```$", "", response_text)

    # Remove any text before the completed theorem
    theorem_match = re.search(
        r"\btheorem\s+",
        response_text,
    )

    if theorem_match:
        response_text = response_text[theorem_match.start():]

    response_text = response_text.strip()

    if not response_text:
        raise RuntimeError(
            "Gemini returned an empty response."
        )

    usage_metadata = response.usage_metadata

    usage = {
        "prompt_tokens": getattr(
            usage_metadata,
            "prompt_token_count",
            "N/A",
        ),
        "completion_tokens": getattr(
            usage_metadata,
            "candidates_token_count",
            "N/A",
        ),
        "total_tokens": getattr(
            usage_metadata,
            "total_token_count",
            "N/A",
        ),
        "latency_seconds": latency,
    }

    return response_text, usage


# ============================================================
# SELECT THE SAME 10 THEOREMS
# ============================================================

def get_selected_theorems():
    """
    Select the same deterministic set of theorem files
    for the Gemini experiment.

    Theorems are taken in sorted order from:
        Nat
        Prop
        Group

    Only MAX_THEOREMS files are selected.
    """

    selected = []

    for domain in DOMAINS:

        source_dir = THEOREMS_DIR / domain

        if not source_dir.exists():
            raise FileNotFoundError(
                f"Theorem directory not found:\n{source_dir}"
            )

        theorem_files = sorted(
            source_dir.glob("*.lean")
        )

        for theorem_file in theorem_files:

            selected.append(
                (domain, theorem_file)
            )

    return selected


# ============================================================
# PROCESS THEOREMS
# ============================================================

def process_theorems():

    selected_theorems = get_selected_theorems()

    print()
    print("=" * 70)
    print("SELECTED THEOREMS")
    print("=" * 70)

    for number, (domain, theorem_file) in enumerate(
        selected_theorems,
        start=1,
    ):
        print(
            f"{number:02d}. "
            f"{domain}/{theorem_file.name}"
        )

    print("=" * 70)
    print()

    for number, (domain, theorem_file) in enumerate(
        selected_theorems,
        start=1,
    ):

        output_file = OUTPUT_DIR / theorem_file.name

        print(
            f"[{number:02d}/{len(selected_theorems):02d}] "
            f"{domain}/{theorem_file.name}"
        )

        # ----------------------------------------------------
        # Skip already-generated responses
        # ----------------------------------------------------

        if output_file.exists():

            print(
                "       Already exists -> skipped"
            )

            continue

        # ----------------------------------------------------
        # Read theorem file
        # ----------------------------------------------------

        try:

            file_text = theorem_file.read_text(
                encoding="utf-8"
            ).strip()

        except Exception as exc:

            print(
                f"       ERROR reading file: {exc}"
            )

            continue

        # ----------------------------------------------------
        # Build prompt
        # ----------------------------------------------------

        try:

            prompt = build_prompt(file_text)

        except Exception as exc:

            print(
                f"       ERROR building prompt: {exc}"
            )

            continue

        # ----------------------------------------------------
        # Generate response
        # ----------------------------------------------------

        try:

            print(
                "       Sending request to Gemini Flash-Lite..."
            )

            response_text, usage = generate_proof(
                prompt
            )

        except Exception as exc:

            print(
                f"       ERROR: {exc}"
            )

            continue

        # ----------------------------------------------------
        # Save raw model response
        # ----------------------------------------------------

        output_file.write_text(
            response_text,
            encoding="utf-8",
        )

        print(
            f"       Saved -> {output_file}"
        )

        # ----------------------------------------------------
        # Display metadata
        # ----------------------------------------------------

        prompt_tokens = usage.get(
            "prompt_tokens",
            "N/A",
        )

        completion_tokens = usage.get(
            "completion_tokens",
            "N/A",
        )

        total_tokens = usage.get(
            "total_tokens",
            "N/A",
        )

        latency = usage.get(
            "latency_seconds",
            "N/A",
        )

        print(
            f"       Prompt tokens     : "
            f"{prompt_tokens}"
        )

        print(
            f"       Completion tokens : "
            f"{completion_tokens}"
        )

        print(
            f"       Total tokens      : "
            f"{total_tokens}"
        )

        if isinstance(latency, float):

            print(
                f"       Latency           : "
                f"{latency:.2f} seconds"
            )

        # ----------------------------------------------------
        # Save metadata
        # ----------------------------------------------------

        append_metadata(
            domain=domain,
            theorem_file=theorem_file,
            output_file=output_file,
            usage=usage,
        )

        print(
            f"       Metadata saved -> "
            f"{METADATA_FILE}"
        )

        # ----------------------------------------------------
        # Wait before next request
        # ----------------------------------------------------

        if number < len(selected_theorems):
            time.sleep(REQUEST_DELAY)


# ============================================================
# MAIN
# ============================================================

def main():

    print("=" * 70)
    print("GEMINI 3.5 FLASH-LITE ZERO-SHOT FORMAL PROOF GENERATION")
    print("=" * 70)

    print(
        f"Project directory : {PROJECT_DIR}"
    )

    print(
        f"Theorem directory : {THEOREMS_DIR}"
    )

    print(
        f"Output directory  : {OUTPUT_DIR}"
    )

    print(
        f"Metadata CSV      : {METADATA_FILE}"
    )

    print(
        f"Model             : {MODEL}"
    )

    print(
        f"Domains           : {', '.join(DOMAINS)}"
    )


    print("=" * 70)

    # --------------------------------------------------------
    # Verify directories
    # --------------------------------------------------------

    if not THEOREMS_DIR.exists():

        raise FileNotFoundError(
            f"Theorems directory not found:\n"
            f"{THEOREMS_DIR}"
        )

    if not OUTPUT_DIR.exists():

        raise FileNotFoundError(
            f"Expected output directory does not exist:\n"
            f"{OUTPUT_DIR}"
        )

    # --------------------------------------------------------
    # Initialize metadata CSV
    # --------------------------------------------------------

    initialize_metadata_csv()

    # --------------------------------------------------------
    # Process selected theorems
    # --------------------------------------------------------

    process_theorems()

    # --------------------------------------------------------
    # Final summary
    # --------------------------------------------------------

    print()
    print("=" * 70)
    print("GEMINI 3.5 FLASH-LITE ZERO-SHOT GENERATION COMPLETE")
    print("=" * 70)

    print(
        f"Outputs saved in:"
    )

    print(
        f"  {OUTPUT_DIR}"
    )

    print(
        f"Metadata saved in:"
    )

    print(
        f"  {METADATA_FILE}"
    )

    print("=" * 70)


if __name__ == "__main__":
    main()