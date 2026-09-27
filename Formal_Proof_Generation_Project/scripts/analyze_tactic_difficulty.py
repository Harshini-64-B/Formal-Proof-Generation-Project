from pathlib import Path
import csv
import re
from collections import Counter, defaultdict


# ============================================================
# PATH CONFIGURATION
# ============================================================

SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_DIR = SCRIPT_DIR.parent
PROJECT_ROOT = PROJECT_DIR.parent

# Original Lean source files are inside:
# LeanCopilotTest/LeanCopilotTest/
LEAN_SOURCE_DIR = PROJECT_ROOT / "LeanCopilotTest"

SOURCE_FILES = {
    "list": LEAN_SOURCE_DIR / "list_proofs.lean",
    "nat": LEAN_SOURCE_DIR / "nat_proofs.lean",
    "prop": LEAN_SOURCE_DIR / "prop_proofs.lean",
    "group": LEAN_SOURCE_DIR / "group_proofs.lean",
}

# Analysis output directory:
# Formal_Proof_Generation_Project/scripts/
#     difficulty_analysis_summary/
DIFFICULTY_ANALYSIS_DIR = (
    SCRIPT_DIR / "difficulty_analysis_summary"
)

DIFFICULTY_ANALYSIS_DIR.mkdir(
    parents=True,
    exist_ok=True
)


# ============================================================
# EXPECTED THEOREM COUNTS
# ============================================================

EXPECTED_COUNTS = {
    "list": 50,
    "nat": 34,
    "prop": 33,
    "group": 33,
}


# ============================================================
# DIFFICULTY CLASSIFICATION
# ============================================================

def get_difficulty(tactic_count):
    """
    Difficulty classification based on tactic count.

    1-3  -> easy
    4-6  -> medium
    >6   -> hard
    """

    if tactic_count <= 3:
        return "easy"

    elif tactic_count <= 6:
        return "medium"

    else:
        return "hard"


# ============================================================
# TACTIC KEYWORDS
# ============================================================

TACTIC_KEYWORDS = {
    "apply",
    "by_cases",
    "by_contra",
    "cases",
    "constructor",
    "contradiction",
    "exact",
    "funext",
    "have",
    "induction",
    "intro",
    "left",
    "obtain",
    "rcases",
    "repeat",
    "rfl",
    "rintro",
    "rw",
    "simp",
    "simp_all",
    "split",
    "split_ifs",
    "subst",
    "unfold",
    "contrapose",
    "contrapose!",
    "lia",
}


# ============================================================
# REMOVE COMMENTS AND STRING LITERALS
# ============================================================

def remove_comments_and_strings(text):
    """
    Remove Lean comments and string literals.

    Handles:
        -- single-line comments
        /- block comments -/
        nested block comments
        "string literals"

    Newlines are preserved where possible.
    """

    result = []

    i = 0
    n = len(text)

    in_line_comment = False
    block_comment_depth = 0
    in_string = False

    while i < n:

        # ----------------------------------------------------
        # Inside single-line comment
        # ----------------------------------------------------

        if in_line_comment:

            if text[i] == "\n":
                in_line_comment = False
                result.append("\n")

            i += 1
            continue

        # ----------------------------------------------------
        # Inside block comment
        # ----------------------------------------------------

        if block_comment_depth > 0:

            if text.startswith("/-", i):
                block_comment_depth += 1
                i += 2
                continue

            if text.startswith("-/", i):
                block_comment_depth -= 1
                i += 2
                continue

            if text[i] == "\n":
                result.append("\n")

            i += 1
            continue

        # ----------------------------------------------------
        # Inside string
        # ----------------------------------------------------

        if in_string:

            if text[i] == "\\":
                i += 2
                continue

            if text[i] == '"':
                in_string = False

            i += 1
            continue

        # ----------------------------------------------------
        # Start single-line comment
        # ----------------------------------------------------

        if text.startswith("--", i):
            in_line_comment = True
            i += 2
            continue

        # ----------------------------------------------------
        # Start block comment
        # ----------------------------------------------------

        if text.startswith("/-", i):
            block_comment_depth = 1
            i += 2
            continue

        # ----------------------------------------------------
        # Start string
        # ----------------------------------------------------

        if text[i] == '"':
            in_string = True
            i += 1
            continue

        # ----------------------------------------------------
        # Normal character
        # ----------------------------------------------------

        result.append(text[i])
        i += 1

    return "".join(result)


# ============================================================
# EXTRACT THEOREMS AND PROOF BODIES
# ============================================================

def extract_theorem_proofs(text):
    """
    Extract theorem names and proof bodies.

    Expected form:

        theorem theorem_name ... := by
            ...
    """

    clean_text = remove_comments_and_strings(text)

    theorem_pattern = re.compile(
        r"(?m)^\s*theorem\s+([A-Za-z0-9_!?']+)"
    )

    matches = list(
        theorem_pattern.finditer(clean_text)
    )

    theorems = []

    for index, match in enumerate(matches):

        theorem_name = match.group(1)

        theorem_start = match.start()

        if index + 1 < len(matches):
            theorem_end = matches[index + 1].start()
        else:
            theorem_end = len(clean_text)

        theorem_text = clean_text[
            theorem_start:theorem_end
        ]

        # ----------------------------------------------------
        # Find := by
        # ----------------------------------------------------

        proof_match = re.search(
            r":=\s*by\b",
            theorem_text
        )

        if proof_match is None:
            continue

        proof_start = proof_match.end()

        proof_body = theorem_text[
            proof_start:
        ]

        theorems.append({
            "name": theorem_name,
            "proof": proof_body,
        })

    return theorems


# ============================================================
# COUNT TACTICS
# ============================================================

def find_tactics(proof):
    """
    Find occurrences of the verified tactic keywords.

    Tactic arguments are not counted separately.

    Example:

        simp [List.length_append]

    counts as:

        simp = 1

    Example:

        intro h <;> simp

    counts as:

        intro = 1
        simp  = 1

    Total = 2
    """

    sorted_tactics = sorted(
        TACTIC_KEYWORDS,
        key=len,
        reverse=True
    )

    pattern = re.compile(
        r"(?<![A-Za-z0-9_'])("
        + "|".join(
            re.escape(tactic)
            for tactic in sorted_tactics
        )
        + r")(?![A-Za-z0-9_'])"
    )

    return pattern.findall(proof)


def count_tactics(proof):
    """
    Return the tactic count and the individual tactics.
    """

    tactic_names = find_tactics(proof)

    return len(tactic_names), tactic_names


# ============================================================
# ANALYZE ONE SOURCE FILE
# ============================================================

def analyze_source_file(
    source_file,
    domain,
):

    if not source_file.exists():

        raise FileNotFoundError(
            f"Source file not found:\n{source_file}"
        )

    text = source_file.read_text(
        encoding="utf-8"
    )

    theorem_proofs = extract_theorem_proofs(
        text
    )

    expected_count = EXPECTED_COUNTS[
        domain
    ]

    if len(theorem_proofs) != expected_count:

        raise RuntimeError(
            f"{source_file.name}: expected "
            f"{expected_count} theorem proofs, "
            f"but found {len(theorem_proofs)}."
        )

    results = []

    for theorem in theorem_proofs:

        tactic_count, tactic_names = (
            count_tactics(
                theorem["proof"]
            )
        )

        difficulty = get_difficulty(
            tactic_count
        )

        results.append({
            "theorem_name":
                theorem["name"],

            "file_name":
                theorem["name"] + ".lean",

            "domain":
                domain,

            "tactic_count":
                tactic_count,

            "difficulty":
                difficulty,

            "tactics":
                ", ".join(tactic_names),
        })

    return results


# ============================================================
# PRINT THEOREM-WISE TABLE
# ============================================================

def print_theorem_table(results):

    print()
    print("=" * 115)
    print(
        "THEOREM-WISE TACTIC COUNT AND DIFFICULTY"
    )
    print("=" * 115)

    print(
        f"{'ID':>4}  "
        f"{'Theorem Name':<50} "
        f"{'Domain':<8} "
        f"{'Tactics':>7} "
        f"{'Difficulty':<10}"
    )

    print("-" * 115)

    for index, result in enumerate(
        results,
        start=1
    ):

        theorem_name = result[
            "theorem_name"
        ]

        if len(theorem_name) > 50:
            theorem_name = (
                theorem_name[:47] + "..."
            )

        print(
            f"{index:>4}  "
            f"{theorem_name:<50} "
            f"{result['domain']:<8} "
            f"{result['tactic_count']:>7} "
            f"{result['difficulty']:<10}"
        )

    print("=" * 115)


# ============================================================
# PRINT OVERALL DIFFICULTY SUMMARY
# ============================================================

def print_difficulty_summary(results):

    difficulty_counts = Counter(
        result["difficulty"]
        for result in results
    )

    total = len(results)

    print()
    print("=" * 65)
    print("OVERALL DIFFICULTY DISTRIBUTION")
    print("=" * 65)

    print(
        f"{'Difficulty':<15}"
        f"{'Count':>10}"
        f"{'Percentage':>15}"
    )

    print("-" * 65)

    for difficulty in [
        "easy",
        "medium",
        "hard",
    ]:

        count = difficulty_counts[
            difficulty
        ]

        percentage = (
            count / total * 100
            if total > 0
            else 0
        )

        print(
            f"{difficulty:<15}"
            f"{count:>10}"
            f"{percentage:>14.2f}%"
        )

    print("-" * 65)

    print(
        f"{'TOTAL':<15}"
        f"{total:>10}"
        f"{100.00:>14.2f}%"
    )

    print("=" * 65)


# ============================================================
# PRINT DOMAIN-WISE STATISTICS
# ============================================================

def print_domain_statistics(results):

    domain_data = defaultdict(list)

    for result in results:

        domain_data[
            result["domain"]
        ].append(result)

    print()
    print("=" * 110)
    print("DOMAIN-WISE STATISTICS")
    print("=" * 110)

    print(
        f"{'Domain':<10}"
        f"{'Total':>8}"
        f"{'Easy':>8}"
        f"{'Medium':>10}"
        f"{'Hard':>8}"
        f"{'Avg Tactics':>14}"
        f"{'Min':>8}"
        f"{'Max':>8}"
    )

    print("-" * 110)

    for domain in [
        "list",
        "nat",
        "prop",
        "group",
    ]:

        domain_results = domain_data.get(
            domain,
            []
        )

        if not domain_results:
            continue

        counts = Counter(
            result["difficulty"]
            for result in domain_results
        )

        tactic_counts = [
            result["tactic_count"]
            for result in domain_results
        ]

        average = (
            sum(tactic_counts)
            / len(tactic_counts)
        )

        print(
            f"{domain:<10}"
            f"{len(domain_results):>8}"
            f"{counts['easy']:>8}"
            f"{counts['medium']:>10}"
            f"{counts['hard']:>8}"
            f"{average:>14.2f}"
            f"{min(tactic_counts):>8}"
            f"{max(tactic_counts):>8}"
        )

    print("=" * 110)


# ============================================================
# PRINT TACTIC COUNT DISTRIBUTION
# ============================================================

def print_tactic_distribution(results):

    counts = Counter(
        result["tactic_count"]
        for result in results
    )

    print()
    print("=" * 65)
    print("TACTIC COUNT DISTRIBUTION")
    print("=" * 65)

    print(
        f"{'Tactic Count':<20}"
        f"{'Number of Theorems':>20}"
    )

    print("-" * 65)

    for tactic_count in sorted(counts):

        print(
            f"{tactic_count:<20}"
            f"{counts[tactic_count]:>20}"
        )

    print("=" * 65)


# ============================================================
# WRITE DETAILED CSV
# ============================================================

def write_summary_csv(results):

    output_file = (
        DIFFICULTY_ANALYSIS_DIR
        / "tactic_analysis.csv"
    )

    fieldnames = [
        "ID",
        "theorem_name",
        "file_name",
        "domain",
        "tactic_count",
        "difficulty",
        "tactics",
    ]

    with open(
        output_file,
        "w",
        newline="",
        encoding="utf-8",
    ) as file:

        writer = csv.DictWriter(
            file,
            fieldnames=fieldnames,
        )

        writer.writeheader()

        for index, result in enumerate(
            results,
            start=1
        ):

            writer.writerow({
                "ID":
                    index,

                "theorem_name":
                    result["theorem_name"],

                "file_name":
                    result["file_name"],

                "domain":
                    result["domain"],

                "tactic_count":
                    result["tactic_count"],

                "difficulty":
                    result["difficulty"],

                "tactics":
                    result["tactics"],
            })

    return output_file


# ============================================================
# WRITE DOMAIN STATISTICS CSV
# ============================================================

def write_domain_statistics(results):

    output_file = (
        DIFFICULTY_ANALYSIS_DIR
        / "domain_statistics.csv"
    )

    domain_data = defaultdict(list)

    for result in results:

        domain_data[
            result["domain"]
        ].append(result)

    fieldnames = [
        "domain",
        "total",
        "easy",
        "medium",
        "hard",
        "average_tactics",
        "minimum_tactics",
        "maximum_tactics",
    ]

    with open(
        output_file,
        "w",
        newline="",
        encoding="utf-8",
    ) as file:

        writer = csv.DictWriter(
            file,
            fieldnames=fieldnames,
        )

        writer.writeheader()

        for domain in [
            "list",
            "nat",
            "prop",
            "group",
        ]:

            domain_results = domain_data.get(
                domain,
                []
            )

            if not domain_results:
                continue

            tactic_counts = [
                result["tactic_count"]
                for result in domain_results
            ]

            counts = Counter(
                result["difficulty"]
                for result in domain_results
            )

            writer.writerow({
                "domain":
                    domain,

                "total":
                    len(domain_results),

                "easy":
                    counts["easy"],

                "medium":
                    counts["medium"],

                "hard":
                    counts["hard"],

                "average_tactics":
                    f"{sum(tactic_counts) / len(tactic_counts):.2f}",

                "minimum_tactics":
                    min(tactic_counts),

                "maximum_tactics":
                    max(tactic_counts),
            })

    return output_file


# ============================================================
# MAIN
# ============================================================

def main():

    print("=" * 100)
    print(
        "TACTIC COUNT AND DIFFICULTY ANALYSIS"
    )
    print("=" * 100)

    print(
        f"Project root       : {PROJECT_ROOT}"
    )

    print(
        f"Lean source folder : {LEAN_SOURCE_DIR}"
    )

    print(
        f"Output directory   : "
        f"{DIFFICULTY_ANALYSIS_DIR}"
    )

    print()

    # --------------------------------------------------------
    # Analyze all four original proof files
    # --------------------------------------------------------

    all_results = []

    domain_order = {
        "list": 0,
        "nat": 1,
        "prop": 2,
        "group": 3,
    }

    for domain in [
        "list",
        "nat",
        "prop",
        "group",
    ]:

        source_file = SOURCE_FILES[
            domain
        ]

        print(
            f"Analyzing {domain}: "
            f"{source_file}"
        )

        results = analyze_source_file(
            source_file,
            domain,
        )

        print(
            f"  Found {len(results)} theorem proofs."
        )

        all_results.extend(results)

    # --------------------------------------------------------
    # Verify total count
    # --------------------------------------------------------

    expected_total = sum(
        EXPECTED_COUNTS.values()
    )

    if len(all_results) != expected_total:

        raise RuntimeError(
            f"Expected {expected_total} total "
            f"theorems, but found "
            f"{len(all_results)}."
        )

    # --------------------------------------------------------
    # Sort by domain and theorem name
    # --------------------------------------------------------

    all_results.sort(
        key=lambda result: (
            domain_order[
                result["domain"]
            ],
            result["theorem_name"].lower(),
        )
    )

    # --------------------------------------------------------
    # Print results
    # --------------------------------------------------------

    print_theorem_table(
        all_results
    )

    print_difficulty_summary(
        all_results
    )

    print_domain_statistics(
        all_results
    )

    print_tactic_distribution(
        all_results
    )

    # --------------------------------------------------------
    # Write CSV files
    # --------------------------------------------------------

    detailed_csv = write_summary_csv(
        all_results
    )

    domain_csv = write_domain_statistics(
        all_results
    )

    # --------------------------------------------------------
    # Final summary
    # --------------------------------------------------------

    print()
    print("=" * 100)
    print("ANALYSIS COMPLETE")
    print("=" * 100)

    print(
        f"Total theorems analyzed : "
        f"{len(all_results)}"
    )

    print(
        f"Detailed results         : "
        f"{detailed_csv}"
    )

    print(
        f"Domain statistics        : "
        f"{domain_csv}"
    )

    print()
    print(
        "dataset.csv was NOT modified."
    )

    print("=" * 100)


if __name__ == "__main__":
    main()