import os
import time
import csv
import re
from pathlib import Path
from google import genai

# PATH CONFIGURATION
SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_DIR = SCRIPT_DIR.parent.parent
THEOREMS_DIR = PROJECT_DIR / "theorems"
OUTPUT_DIR = PROJECT_DIR / "outputs" / "gemini_flash_zero"
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
METADATA_FILE = PROJECT_DIR / "gemini_flash_zero_metadata.csv"

# EXPERIMENT CONFIGURATION
DOMAINS = ["Lists", "Nat", "Prop", "Group"]

# DOMAIN LEAN ENVIRONMENT
DOMAIN_IMPORTS = {
    "list": ["import Mathlib.Data.List.Basic"],
    "nat": [
        "import Mathlib.Data.Nat.Basic",
        "import Mathlib.Data.Nat.Choose.Basic",
        "import Mathlib.Data.Nat.Factorial.Basic",
    ],
    "prop": ["import Mathlib.Logic.Basic"],
    "group": ["import Mathlib.Algebra.Group.Basic"],
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
    normalized_domain = domain.strip().lower()

    if normalized_domain == "lists":
        normalized_domain = "list"

    if normalized_domain not in DOMAIN_IMPORTS:
        raise ValueError(f"Unknown domain: {domain}")

    environment_lines = list(DOMAIN_IMPORTS[normalized_domain])
    namespace_info = DOMAIN_NAMESPACES.get(normalized_domain)

    if namespace_info is not None:
        environment_lines.extend([
            "",
            namespace_info["start"],
            "...",
            namespace_info["end"],
        ])

    return "\n".join(environment_lines)


# GEMINI FLASH CONFIGURATION
MODEL = "gemini-3.5-flash"
API_KEY = os.getenv("GEMINI_API_KEY")

if not API_KEY:
    raise RuntimeError(
        "\nGEMINI_API_KEY is not set.\n"
        "Set your Google Gemini API key as an environment variable before running this script.\n"
    )

client = genai.Client(api_key=API_KEY)
REQUEST_DELAY = 4


# PROMPT
def extract_theorem(file_text):
    match = re.search(r"(?ms)^theorem\s+.*", file_text)

    if not match:
        raise ValueError(
            "Could not find a theorem declaration starting with 'theorem'."
        )

    theorem_text = match.group(0).strip()
    theorem_text = re.split(
        r"(?m)^(?:end\b|namespace\b|theorem\b|lemma\b|example\b)",
        theorem_text,
    )[0].strip()

    return theorem_text


def build_prompt(domain, file_text):
    theorem_text = extract_theorem(file_text)
    environment = get_domain_environment(domain)

    return (
        "Complete the following Lean 4 theorem by replacing `sorry` with a valid, compilable proof.\n\n"
        "Lean environment:\n"
        f"{environment}\n\n"
        "Use this environment when constructing the proof. Do not output the imports or namespace declarations.\n\n"
        "Target theorem:\n"
        f"{theorem_text}\n\n"
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


# METADATA CSV
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


def append_metadata(domain, theorem_file, output_file, usage):
    with METADATA_FILE.open(
        "a",
        newline="",
        encoding="utf-8",
    ) as csv_file:
        writer = csv.DictWriter(
            csv_file,
            fieldnames=CSV_FIELDS,
        )
        writer.writerow({
            "model": MODEL,
            "prompt_type": "zero",
            "domain": domain,
            "theorem_file": theorem_file.name,
            "output_file": output_file.name,
            "prompt_tokens": usage.get("prompt_tokens", "N/A"),
            "completion_tokens": usage.get("completion_tokens", "N/A"),
            "total_tokens": usage.get("total_tokens", "N/A"),
            "latency_seconds": usage.get("latency_seconds", "N/A"),
        })


# GEMINI FLASH API REQUEST
def generate_proof(prompt):
    start_time = time.perf_counter()

    response = client.models.generate_content(
        model=MODEL,
        contents=prompt,
        config={"temperature": 0},
    )

    latency = time.perf_counter() - start_time
    response_text = (response.text or "").strip()

    response_text = re.sub(
        r"^\s*```(?:lean)?\s*",
        "",
        response_text,
        flags=re.IGNORECASE,
    )
    response_text = re.sub(
        r"\s*```\s*$",
        "",
        response_text,
    )

    theorem_match = re.search(r"\btheorem\s+", response_text)

    if theorem_match:
        response_text = response_text[theorem_match.start():]

    response_text = response_text.strip()

    if not response_text:
        raise RuntimeError("Gemini returned an empty response.")

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


# SELECT THEOREMS
def get_selected_theorems():
    selected = []

    for domain in DOMAINS:
        source_dir = THEOREMS_DIR / domain

        if not source_dir.exists():
            raise FileNotFoundError(
                f"Theorem directory not found:\n{source_dir}"
            )

        for theorem_file in sorted(source_dir.glob("*.lean")):
            selected.append((domain, theorem_file))

    return selected


# PROCESS THEOREMS
def process_theorems():
    selected_theorems = get_selected_theorems()

    print("\n" + "=" * 70)
    print("SELECTED THEOREMS")
    print("=" * 70)

    for number, (domain, theorem_file) in enumerate(
        selected_theorems,
        start=1,
    ):
        print(f"{number:02d}. {domain}/{theorem_file.name}")

    print("=" * 70 + "\n")

    for number, (domain, theorem_file) in enumerate(
        selected_theorems,
        start=1,
    ):
        output_file = OUTPUT_DIR / theorem_file.name

        print(
            f"[{number:02d}/{len(selected_theorems):02d}] "
            f"{domain}/{theorem_file.name}"
        )

        if output_file.exists():
            print("       Already exists -> skipped")
            continue

        try:
            file_text = theorem_file.read_text(
                encoding="utf-8"
            ).strip()
        except Exception as exc:
            print(f"       ERROR reading file: {exc}")
            continue

        try:
            prompt = build_prompt(domain, file_text)
        except Exception as exc:
            print(f"       ERROR building prompt: {exc}")
            continue

        try:
            print(f"       Sending request to {MODEL}...")
            response_text, usage = generate_proof(prompt)
        except Exception as exc:
            print(f"       ERROR: {exc}")
            continue

        output_file.write_text(
            response_text,
            encoding="utf-8",
        )

        print(f"       Saved -> {output_file}")
        print(f"       Prompt tokens     : {usage.get('prompt_tokens', 'N/A')}")
        print(f"       Completion tokens : {usage.get('completion_tokens', 'N/A')}")
        print(f"       Total tokens      : {usage.get('total_tokens', 'N/A')}")

        latency = usage.get("latency_seconds", "N/A")

        if isinstance(latency, (int, float)):
            print(f"       Latency           : {latency:.2f} seconds")

        append_metadata(
            domain,
            theorem_file,
            output_file,
            usage,
        )

        print(f"       Metadata saved -> {METADATA_FILE}")

        if number < len(selected_theorems):
            time.sleep(REQUEST_DELAY)


# MAIN
def main():
    print("=" * 70)
    print("GEMINI 3.5 FLASH ZERO-SHOT FORMAL PROOF GENERATION")
    print("=" * 70)

    print(f"Project directory : {PROJECT_DIR}")
    print(f"Theorem directory : {THEOREMS_DIR}")
    print(f"Output directory  : {OUTPUT_DIR}")
    print(f"Metadata CSV      : {METADATA_FILE}")
    print(f"Model             : {MODEL}")
    print(f"Domains           : {', '.join(DOMAINS)}")

    print("=" * 70)

    if not THEOREMS_DIR.exists():
        raise FileNotFoundError(
            f"Theorems directory not found:\n{THEOREMS_DIR}"
        )

    initialize_metadata_csv()
    process_theorems()

    print("\n" + "=" * 70)
    print("GEMINI 3.5 FLASH ZERO-SHOT GENERATION COMPLETE")
    print("=" * 70)

    print(f"Outputs saved in:\n  {OUTPUT_DIR}")
    print(f"Metadata saved in:\n  {METADATA_FILE}")

    print("=" * 70)


if __name__ == "__main__":
    main()