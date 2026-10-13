import os
import time
import csv
import re
from pathlib import Path

from google import genai


# ============================================================
# PATH CONFIGURATION
# ============================================================

SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_DIR = SCRIPT_DIR.parent.parent

THEOREMS_DIR = PROJECT_DIR / "theorems"
EXAMPLES_DIR = PROJECT_DIR / "examples"

OUTPUT_DIR = PROJECT_DIR / "outputs" / "gemini_flash_lite_one"
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

METADATA_FILE = (
    PROJECT_DIR / "gemini_flash_lite_one_metadata.csv"
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
# DOMAIN LEAN ENVIRONMENT
# ============================================================

DOMAIN_IMPORTS = {
    "list": [
        "import Mathlib.Data.List.Basic",
    ],
    "nat": [
        "import Mathlib.Data.Nat.Basic",
        "import Mathlib.Data.Nat.Choose.Basic",
        "import Mathlib.Data.Nat.Factorial.Basic",
    ],
    "prop": [
        "import Mathlib.Logic.Basic",
    ],
    "group": [
        "import Mathlib.Algebra.Group.Basic",
    ],
}


DOMAIN_NAMESPACES = {
    "list": None,
    "nat": None,
    "prop": {
        "start": "namespace Logic_Prop",
        "end": "end Logic_Prop",
    },
    "group": {
        "start": "namespace Algebra_Group",
        "end": "end Algebra_Group",
    },
}


def get_domain_environment(domain):
    """
    Return the Lean imports and namespace environment
    corresponding to the theorem's dataset domain.

    The domain naming follows the dataset/Verify All logic:
        Lists -> list
        Nat   -> nat
        Prop  -> prop
        Group -> group
    """

    normalized_domain = domain.strip().lower()

    if normalized_domain == "lists":
        normalized_domain = "list"

    if normalized_domain not in DOMAIN_IMPORTS:
        raise ValueError(
            f"Unknown domain: {domain}"
        )

    imports = DOMAIN_IMPORTS[normalized_domain]
    namespace_info = DOMAIN_NAMESPACES.get(
        normalized_domain
    )

    environment_lines = []

    # Required imports
    environment_lines.extend(imports)

    # Required namespace
    if namespace_info is not None:
        environment_lines.append("")
        environment_lines.append(
            namespace_info["start"]
        )
        environment_lines.append("...")
        environment_lines.append(
            namespace_info["end"]
        )

    return "\n".join(environment_lines)


# ============================================================
# GEMINI FLASH LITE CONFIGURATION
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
REQUEST_DELAY = 4


# ============================================================
# EXAMPLE SELECTION
# ============================================================

def get_first_example(domain):
    """
    Select the first example theorem from the corresponding
    domain folder.

    Examples are selected in sorted filename order.
    """

    example_dir = EXAMPLES_DIR / domain

    if not example_dir.exists():
        raise FileNotFoundError(
            f"Example directory not found:\n{example_dir}"
        )

    example_files = sorted(
        example_dir.glob("*.lean")
    )

    if not example_files:
        raise FileNotFoundError(
            f"No example .lean files found in:\n{example_dir}"
        )

    return example_files[0]


# ============================================================
# PROMPT
# ============================================================

def extract_theorem(file_text):
    """
    Extract the theorem declaration from a Lean file.

    This is used for both the example theorem and the
    target theorem.
    """

    match = re.search(
        r"(?ms)^theorem\s+.*",
        file_text,
    )

    if not match:
        raise ValueError(
            "Could not find a theorem declaration "
            "starting with 'theorem'."
        )

    return match.group(0).strip()


def build_prompt(domain, example_text, theorem_text):
    """
    Build the one-shot prompt using:

        1. The required Lean environment for the domain
        2. One completed example theorem
        3. The target theorem

    The model is explicitly instructed to return only the
    completed target theorem.
    """

    example_theorem = extract_theorem(example_text)
    target_theorem = extract_theorem(theorem_text)

    environment = get_domain_environment(domain)

    return (
    "Complete the following Lean 4 theorem by replacing `sorry` "
    "with a valid, compilable proof.\n\n"
    "Lean environment:\n"
    + environment
    + "\n\n"
    "Use this environment when constructing the proof. "
    "Do not output the imports or namespace declarations.\n\n"
    "Example theorem:\n"
    + example_theorem
    + "\n\n"
    "Target theorem:\n"
    + target_theorem
    + "\n\n"
    "Return ONLY the completed target theorem in this format:\n"
    "theorem <theorem_name> <arguments> : <statement> := by\n"
    "  proof\n\n"
    "Rules:\n"
    "- You MUST replace `sorry` with an actual Lean proof.\n"
    "- `sorry`, `by sorry`, `_`, `admit`, and `by admit` are strictly forbidden.\n"
    "- Do not leave the theorem incomplete or return the original theorem unchanged.\n"
    "- The proof must contain one or more actual Lean tactics or proof terms.\n"
    "- Make a genuine attempt to prove the theorem using the provided Lean environment.\n"
    "- If your first proof approach does not work, try another valid proof approach before returning the answer.\n"
    "- Include the complete target theorem with its original name, arguments, and statement.\n"
    "- Use `:= by` and put the proof on the following lines, indented by two spaces.\n"
    "- Output only the theorem: no plain text, explanations, comments, alternatives, or multiple versions.\n"
    "- Do not use Markdown/code fences, imports, or namespace declarations.\n"
    "- Do not change the target theorem.\n\n"
    "The returned theorem must be a completed proof, not a proof placeholder.\n"
    "Return only the completed target theorem."
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
                "prompt_type": "one",
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
# GEMINI FLASH LITE API REQUEST
# ============================================================

def generate_proof(prompt):
    """
    Send one theorem prompt to Gemini Flash Lite.

    Returns:
        response_text
        usage
    """

    start_time = time.perf_counter()

    response = client.models.generate_content(
        model=MODEL,
        contents=prompt,
    )

    latency = time.perf_counter() - start_time

    response_text = response.text.strip()

    # Remove Markdown code fences if the model ignores
    # the prompt and returns them anyway.
    response_text = re.sub(
        r"^```(?:lean)?\s*",
        "",
        response_text,
        flags=re.IGNORECASE,
    )

    response_text = re.sub(
        r"\s*```$",
        "",
        response_text,
    )

    # Remove any text before the completed theorem.
    theorem_match = re.search(
        r"\btheorem\s+",
        response_text,
    )

    if theorem_match:
        response_text = response_text[
            theorem_match.start():
        ]

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
# SELECT THE THEOREMS
# ============================================================

def get_selected_theorems():
    """
    Select all theorem files from all domains.

    Theorems are taken in sorted order from:
        Lists
        Nat
        Prop
        Group
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
        # Read target theorem file
        # ----------------------------------------------------

        try:

            theorem_text = theorem_file.read_text(
                encoding="utf-8"
            ).strip()

        except Exception as exc:

            print(
                f"       ERROR reading theorem file: {exc}"
            )

            continue

        # ----------------------------------------------------
        # Read first example for this domain
        # ----------------------------------------------------

        try:

            example_file = get_first_example(domain)

            example_text = example_file.read_text(
                encoding="utf-8"
            ).strip()

            print(
                f"       One-shot example : "
                f"{domain}/{example_file.name}"
            )

        except Exception as exc:

            print(
                f"       ERROR reading example: {exc}"
            )

            continue

        # ----------------------------------------------------
        # Build prompt
        # ----------------------------------------------------

        try:

            prompt = build_prompt(
                domain,
                example_text,
                theorem_text,
            )

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
                "       Sending request to "
                "gemini-3.5-flash-lite..."
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

    print(
        "GEMINI-3.5-FLASH-LITE ONE-SHOT "
        "FORMAL PROOF GENERATION"
    )

    print("=" * 70)

    print(
        f"Project directory : {PROJECT_DIR}"
    )

    print(
        f"Theorem directory : {THEOREMS_DIR}"
    )

    print(
        f"Examples directory: {EXAMPLES_DIR}"
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

    if not EXAMPLES_DIR.exists():

        raise FileNotFoundError(
            f"Examples directory not found:\n"
            f"{EXAMPLES_DIR}"
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

    print(
        "GEMINI-3.5-FLASH-LITE ONE-SHOT "
        "GENERATION COMPLETE"
    )

    print("=" * 70)

    print(
        "Outputs saved in:"
    )

    print(
        f"  {OUTPUT_DIR}"
    )

    print(
        "Metadata saved in:"
    )

    print(
        f"  {METADATA_FILE}"
    )

    print("=" * 70)


if __name__ == "__main__":
    main()