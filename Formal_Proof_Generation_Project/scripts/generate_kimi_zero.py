import os
import time
import csv
import re
from pathlib import Path

import requests


# ============================================================
# PATH CONFIGURATION
# ============================================================

# This script is located at:
#
# Formal_Proof_Generation_Project/
# └── scripts/
#     └── generate_kimi_zero.py
#
# Therefore:
#
# SCRIPT_DIR  = Formal_Proof_Generation_Project/scripts
# PROJECT_DIR = Formal_Proof_Generation_Project
#
# Theorem files:
#   Formal_Proof_Generation_Project/theorems/
#
# Kimi zero-shot outputs:
#   Formal_Proof_Generation_Project/outputs/kimi_zero/
#
# Kimi zero-shot metadata:
#   Formal_Proof_Generation_Project/results/kimi_zero_metadata.csv
# ============================================================

SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_DIR = SCRIPT_DIR.parent

THEOREMS_DIR = PROJECT_DIR / "theorems"
OUTPUT_DIR = PROJECT_DIR / "outputs" / "kimi_zero"

METADATA_FILE = PROJECT_DIR / "kimi_zero_metadata.csv"


# ============================================================
# DOMAINS TO PROCESS
# ============================================================

# Lists are intentionally excluded.

DOMAINS = [
    "Nat",
    "Prop",
    "Group",
]


# ============================================================
# OPENROUTER CONFIGURATION
# ============================================================

API_URL = "https://openrouter.ai/api/v1/chat/completions"

# Free Kimi model
MODEL = "moonshotai/kimi-k2.6:free"

# Read API key from environment variable.
# Do not put the actual API key in this file.

API_KEY = os.getenv("OPENROUTER_API_KEY")

if not API_KEY:
    raise RuntimeError(
        "\nOPENROUTER_API_KEY is not set.\n"
        "Set your OpenRouter API key as an environment "
        "variable before running this script.\n"
    )


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
            "Could not find a theorem declaration with ':= by ... sorry'."
        )

    theorem_text = match.group(0).strip()

    return (
        "Give the proof for the following theorem in formal language.\n"
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
# KIMI API REQUEST
# ============================================================

def generate_proof(prompt):
    """
    Send one theorem prompt to Kimi through OpenRouter.

    Returns:
        response_text
        usage
    """

    headers = {
        "Authorization": f"Bearer {API_KEY}",
        "Content-Type": "application/json",
    }

    payload = {
        "model": MODEL,
        "messages": [
            {
                "role": "user",
                "content": prompt,
            }
        ],
        "temperature": 0,
    }

    start_time = time.perf_counter()

    response = requests.post(
        API_URL,
        headers=headers,
        json=payload,
        timeout=300,
    )

    latency = time.perf_counter() - start_time

    response.raise_for_status()

    data = response.json()

    try:
        response_text = data["choices"][0]["message"]["content"]
    except (KeyError, IndexError, TypeError) as exc:
        raise RuntimeError(
            "Unexpected response received from OpenRouter:\n"
            f"{data}"
        ) from exc

    usage = data.get("usage", {}).copy()

    usage["latency_seconds"] = latency

    return response_text, usage


# ============================================================
# PROCESS ONE DOMAIN
# ============================================================

def process_domain(domain):
    """
    Read all theorem files from one domain.

    The generated responses are saved directly in:
        outputs/kimi_zero/

    No domain-wise output subdirectories are created.

    Metadata is continuously appended to:
        results/kimi_zero_metadata.csv
    """

    print()
    print("=" * 70)
    print(f"PROCESSING {domain}")
    print("=" * 70)

    source_dir = THEOREMS_DIR / domain

    if not source_dir.exists():
        raise FileNotFoundError(
            f"Theorem directory not found:\n{source_dir}"
        )

    theorem_files = sorted(
        source_dir.glob("*.lean")
    )

    print(f"Source      : {source_dir}")
    print(f"Theorems    : {len(theorem_files)}")
    print(f"Output      : {OUTPUT_DIR}")
    print(f"Metadata    : {METADATA_FILE}")
    print()

    for number, theorem_file in enumerate(
        theorem_files,
        start=1,
    ):

        # Same theorem filename is used in kimi_zero.
        output_file = OUTPUT_DIR / theorem_file.name

        print(
            f"[{number:02d}/{len(theorem_files):02d}] "
            f"{theorem_file.name}"
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
                "       Sending request to Kimi..."
            )

            response_text, usage = generate_proof(
                prompt
            )

        except requests.HTTPError as exc:

            print(
                "       ERROR: OpenRouter request failed."
            )

            if exc.response is not None:

                print(
                    f"       HTTP status: "
                    f"{exc.response.status_code}"
                )

                print(
                    f"       Response: "
                    f"{exc.response.text}"
                )

            continue

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
        # Display metadata returned by API
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
        # Save metadata to CSV
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

        time.sleep(REQUEST_DELAY)


# ============================================================
# MAIN
# ============================================================

def main():

    print("=" * 70)
    print("KIMI ZERO-SHOT FORMAL PROOF GENERATION")
    print("=" * 70)

    print(f"Project directory : {PROJECT_DIR}")
    print(f"Theorem directory : {THEOREMS_DIR}")
    print(f"Output directory  : {OUTPUT_DIR}")
    print(f"Metadata CSV      : {METADATA_FILE}")
    print(f"Model             : {MODEL}")
    print(f"Domains           : {', '.join(DOMAINS)}")

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
            f"Expected kimi_zero directory does not exist:\n"
            f"{OUTPUT_DIR}"
        )

    # --------------------------------------------------------
    # Initialize metadata CSV
    # --------------------------------------------------------

    initialize_metadata_csv()

    # --------------------------------------------------------
    # Process only Nat, Prop and Group
    # --------------------------------------------------------

    for domain in DOMAINS:
        process_domain(domain)

    # --------------------------------------------------------
    # Final summary
    # --------------------------------------------------------

    print()
    print("=" * 70)
    print("KIMI ZERO-SHOT GENERATION COMPLETE")
    print("=" * 70)

    print(f"Outputs saved in:")
    print(f"  {OUTPUT_DIR}")

    print(f"Metadata saved in:")
    print(f"  {METADATA_FILE}")

    print()
    print("Processed:")
    print("  Nat")
    print("  Prop")
    print("  Group")
    print()
    print("Lists: NOT processed")
    print("=" * 70)


if __name__ == "__main__":
    main()