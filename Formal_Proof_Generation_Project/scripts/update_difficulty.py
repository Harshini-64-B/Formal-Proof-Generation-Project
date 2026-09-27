from pathlib import Path
import csv
import shutil


# ============================================================
# PATH CONFIGURATION
# ============================================================

SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_DIR = SCRIPT_DIR.parent

DATASET_FILE = PROJECT_DIR / "dataset.csv"

ANALYSIS_DIR = (
    SCRIPT_DIR / "difficulty_analysis_summary"
)

TACTIC_ANALYSIS_FILE = (
    ANALYSIS_DIR / "tactic_analysis.csv"
)

BACKUP_FILE = (
    PROJECT_DIR / "dataset_before_difficulty_update.csv"
)


# ============================================================
# VALID DIFFICULTY LEVELS
# ============================================================

VALID_DIFFICULTIES = {
    "easy",
    "medium",
    "hard",
}


# ============================================================
# READ CSV
# ============================================================

def read_csv_file(file_path):

    if not file_path.exists():
        raise FileNotFoundError(
            f"File not found:\n{file_path}"
        )

    with open(
        file_path,
        "r",
        newline="",
        encoding="utf-8",
    ) as file:

        reader = csv.DictReader(file)

        if reader.fieldnames is None:
            raise RuntimeError(
                f"{file_path.name} does not contain a header."
            )

        rows = list(reader)

    return rows, reader.fieldnames


# ============================================================
# VALIDATE DATASET
# ============================================================

def validate_dataset(rows, fieldnames):

    required_columns = {
        "ID",
        "file_name",
        "file_path",
        "domain",
        "difficulty",
    }

    missing_columns = (
        required_columns - set(fieldnames)
    )

    if missing_columns:
        raise RuntimeError(
            "dataset.csv is missing columns: "
            + ", ".join(sorted(missing_columns))
        )

    if len(rows) != 150:
        raise RuntimeError(
            f"Expected dataset.csv to contain "
            f"150 rows, but found {len(rows)}."
        )

    ids = []

    for row in rows:

        try:
            theorem_id = int(
                row["ID"].strip()
            )
        except ValueError:
            raise RuntimeError(
                f"Invalid ID in dataset.csv: "
                f"{row['ID']}"
            )

        ids.append(theorem_id)

    if len(ids) != len(set(ids)):
        raise RuntimeError(
            "Duplicate IDs detected in dataset.csv."
        )

    if set(ids) != set(range(1, 151)):
        raise RuntimeError(
            "dataset.csv IDs are not exactly "
            "1 through 150."
        )


# ============================================================
# VALIDATE TACTIC ANALYSIS
# ============================================================

def validate_analysis(
    rows,
    fieldnames,
):

    required_columns = {
        "ID",
        "theorem_name",
        "file_name",
        "domain",
        "tactic_count",
        "difficulty",
    }

    missing_columns = (
        required_columns - set(fieldnames)
    )

    if missing_columns:
        raise RuntimeError(
            "tactic_analysis.csv is missing columns: "
            + ", ".join(sorted(missing_columns))
        )

    if len(rows) != 150:
        raise RuntimeError(
            f"Expected tactic_analysis.csv to contain "
            f"150 rows, but found {len(rows)}."
        )

    ids = []

    for row in rows:

        try:
            theorem_id = int(
                row["ID"].strip()
            )
        except ValueError:
            raise RuntimeError(
                f"Invalid ID in tactic_analysis.csv: "
                f"{row['ID']}"
            )

        ids.append(theorem_id)

        difficulty = (
            row["difficulty"]
            .strip()
            .lower()
        )

        if difficulty not in VALID_DIFFICULTIES:
            raise RuntimeError(
                f"Invalid difficulty '{difficulty}' "
                f"for theorem "
                f"{row['theorem_name']}."
            )

    if len(ids) != len(set(ids)):
        raise RuntimeError(
            "Duplicate IDs detected in "
            "tactic_analysis.csv."
        )

    if set(ids) != set(range(1, 151)):
        raise RuntimeError(
            "tactic_analysis.csv IDs are not exactly "
            "1 through 150."
        )


# ============================================================
# BUILD DIFFICULTY LOOKUP
# ============================================================

def build_difficulty_lookup(
    analysis_rows
):

    difficulty_lookup = {}

    for row in analysis_rows:

        theorem_id = int(
            row["ID"].strip()
        )

        difficulty = (
            row["difficulty"]
            .strip()
            .lower()
        )

        difficulty_lookup[
            theorem_id
        ] = difficulty

    return difficulty_lookup


# ============================================================
# UPDATE DATASET
# ============================================================

def update_dataset(
    dataset_rows,
    difficulty_lookup,
):

    updated_count = 0

    changes = []

    for row in dataset_rows:

        theorem_id = int(
            row["ID"].strip()
        )

        if theorem_id not in difficulty_lookup:
            raise RuntimeError(
                f"No difficulty analysis found "
                f"for dataset ID {theorem_id}."
            )

        old_difficulty = (
            row["difficulty"]
            .strip()
        )

        new_difficulty = difficulty_lookup[
            theorem_id
        ]

        if old_difficulty != new_difficulty:

            changes.append({
                "ID": theorem_id,
                "file_name": row["file_name"],
                "domain": row["domain"],
                "old": old_difficulty,
                "new": new_difficulty,
            })

        row["difficulty"] = new_difficulty

        updated_count += 1

    return updated_count, changes


# ============================================================
# WRITE DATASET
# ============================================================

def write_dataset(
    rows,
    fieldnames,
):

    with open(
        DATASET_FILE,
        "w",
        newline="",
        encoding="utf-8",
    ) as file:

        writer = csv.DictWriter(
            file,
            fieldnames=fieldnames,
        )

        writer.writeheader()
        writer.writerows(rows)


# ============================================================
# PRINT SUMMARY
# ============================================================

def print_summary(
    rows,
    changes,
):

    difficulty_counts = {
        "easy": 0,
        "medium": 0,
        "hard": 0,
    }

    domain_counts = {
        "list": {
            "easy": 0,
            "medium": 0,
            "hard": 0,
        },
        "nat": {
            "easy": 0,
            "medium": 0,
            "hard": 0,
        },
        "prop": {
            "easy": 0,
            "medium": 0,
            "hard": 0,
        },
        "group": {
            "easy": 0,
            "medium": 0,
            "hard": 0,
        },
    }

    for row in rows:

        difficulty = (
            row["difficulty"]
            .strip()
            .lower()
        )

        domain = (
            row["domain"]
            .strip()
            .lower()
        )

        difficulty_counts[
            difficulty
        ] += 1

        if domain in domain_counts:
            domain_counts[
                domain
            ][difficulty] += 1

    print()
    print("=" * 80)
    print("DIFFICULTY UPDATE SUMMARY")
    print("=" * 80)

    print()
    print(
        f"Total dataset entries : {len(rows)}"
    )

    print(
        f"Entries updated       : {len(changes)}"
    )

    print(
        f"Entries unchanged     : "
        f"{len(rows) - len(changes)}"
    )

    print()
    print("Overall difficulty distribution:")
    print("-" * 50)

    for difficulty in [
        "easy",
        "medium",
        "hard",
    ]:

        print(
            f"{difficulty:<10}: "
            f"{difficulty_counts[difficulty]}"
        )

    print()
    print("Domain-wise difficulty distribution:")
    print("-" * 80)

    print(
        f"{'Domain':<12}"
        f"{'Easy':>10}"
        f"{'Medium':>10}"
        f"{'Hard':>10}"
        f"{'Total':>10}"
    )

    print("-" * 80)

    for domain in [
        "list",
        "nat",
        "prop",
        "group",
    ]:

        counts = domain_counts[domain]

        total = (
            counts["easy"]
            + counts["medium"]
            + counts["hard"]
        )

        print(
            f"{domain:<12}"
            f"{counts['easy']:>10}"
            f"{counts['medium']:>10}"
            f"{counts['hard']:>10}"
            f"{total:>10}"
        )

    print("=" * 80)


# ============================================================
# MAIN
# ============================================================

def main():

    print("=" * 80)
    print("UPDATING DATASET DIFFICULTY")
    print("=" * 80)

    print()
    print(
        f"Dataset          : {DATASET_FILE}"
    )

    print(
        f"Analysis source  : {TACTIC_ANALYSIS_FILE}"
    )

    print(
        f"Backup           : {BACKUP_FILE}"
    )

    # --------------------------------------------------------
    # Read dataset
    # --------------------------------------------------------

    dataset_rows, dataset_fieldnames = (
        read_csv_file(
            DATASET_FILE
        )
    )

    print()
    print(
        f"Dataset rows read: {len(dataset_rows)}"
    )

    # --------------------------------------------------------
    # Validate dataset
    # --------------------------------------------------------

    validate_dataset(
        dataset_rows,
        dataset_fieldnames,
    )

    print(
        "Dataset validation: PASSED"
    )

    # --------------------------------------------------------
    # Read tactic analysis
    # --------------------------------------------------------

    analysis_rows, analysis_fieldnames = (
        read_csv_file(
            TACTIC_ANALYSIS_FILE
        )
    )

    print(
        f"Analysis rows read: {len(analysis_rows)}"
    )

    # --------------------------------------------------------
    # Validate tactic analysis
    # --------------------------------------------------------

    validate_analysis(
        analysis_rows,
        analysis_fieldnames,
    )

    print(
        "Tactic analysis validation: PASSED"
    )

    # --------------------------------------------------------
    # Build lookup
    # --------------------------------------------------------

    difficulty_lookup = (
        build_difficulty_lookup(
            analysis_rows
        )
    )

    # --------------------------------------------------------
    # Create backup
    # --------------------------------------------------------

    shutil.copy2(
        DATASET_FILE,
        BACKUP_FILE,
    )

    print()
    print(
        f"Backup created: {BACKUP_FILE}"
    )

    # --------------------------------------------------------
    # Update difficulty column
    # --------------------------------------------------------

    updated_count, changes = (
        update_dataset(
            dataset_rows,
            difficulty_lookup,
        )
    )

    # --------------------------------------------------------
    # Final validation before writing
    # --------------------------------------------------------

    for row in dataset_rows:

        difficulty = (
            row["difficulty"]
            .strip()
            .lower()
        )

        if difficulty not in VALID_DIFFICULTIES:
            raise RuntimeError(
                f"Invalid final difficulty "
                f"'{difficulty}' for ID "
                f"{row['ID']}."
            )

    if updated_count != 150:
        raise RuntimeError(
            f"Expected to process 150 entries, "
            f"but processed {updated_count}."
        )

    # --------------------------------------------------------
    # Write updated dataset
    # --------------------------------------------------------

    write_dataset(
        dataset_rows,
        dataset_fieldnames,
    )

    # --------------------------------------------------------
    # Print summary
    # --------------------------------------------------------

    print_summary(
        dataset_rows,
        changes,
    )

    print()
    print(
        "dataset.csv difficulty column "
        "updated successfully."
    )

    print()
    print(
        "The difficulty values were updated "
        "for ALL 150 theorems, including "
        "the 50 List theorems."
    )

    print("=" * 80)


if __name__ == "__main__":
    main()