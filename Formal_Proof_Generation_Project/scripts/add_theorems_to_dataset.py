from pathlib import Path
import csv


# ============================================================
# PATH CONFIGURATION
# ============================================================

SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_DIR = SCRIPT_DIR.parent

DATASET_FILE = PROJECT_DIR / "dataset.csv"

THEOREMS_DIR = PROJECT_DIR / "theorems"


# ============================================================
# NEW THEOREM DOMAINS
# ============================================================

DOMAINS = {
    "nat": {
        "folder": "Nat",
        "start_id": 51,
        "expected_count": 34,
    },
    "prop": {
        "folder": "Prop",
        "start_id": 85,
        "expected_count": 33,
    },
    "group": {
        "folder": "Group",
        "start_id": 118,
        "expected_count": 33,
    },
}


# Difficulty will be assigned later.
DIFFICULTY_PLACEHOLDER = "TODO"


# ============================================================
# READ DATASET
# ============================================================

def read_dataset():

    if not DATASET_FILE.exists():
        raise FileNotFoundError(
            f"dataset.csv not found:\n{DATASET_FILE}"
        )

    with open(
        DATASET_FILE,
        "r",
        newline="",
        encoding="utf-8"
    ) as file:

        reader = csv.DictReader(file)

        fieldnames = reader.fieldnames

        if fieldnames is None:
            raise RuntimeError(
                "dataset.csv does not contain a header."
            )

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

        rows = list(reader)

    return rows, fieldnames


# ============================================================
# VALIDATE EXISTING DATASET
# ============================================================

def validate_existing_dataset(rows):

    ids = []

    for row in rows:

        try:
            theorem_id = int(row["ID"].strip())
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

    # We expect the current dataset to contain exactly
    # the original 50 List theorems.
    if len(rows) != 50:
        raise RuntimeError(
            f"Expected the dataset to currently contain "
            f"50 rows, but found {len(rows)}."
        )

    expected_ids = set(range(1, 51))

    if set(ids) != expected_ids:
        raise RuntimeError(
            "The existing dataset IDs are not exactly "
            "1 through 50."
        )


# ============================================================
# COLLECT NEW THEOREM FILES
# ============================================================

def collect_theorem_files():

    new_theorems = []

    for domain, config in DOMAINS.items():

        folder_name = config["folder"]
        folder = THEOREMS_DIR / folder_name

        if not folder.exists():
            raise FileNotFoundError(
                f"Theorem directory not found:\n{folder}"
            )

        theorem_files = sorted(
            folder.glob("*.lean"),
            key=lambda path: path.name.lower()
        )

        expected_count = config["expected_count"]

        if len(theorem_files) != expected_count:
            raise RuntimeError(
                f"{folder_name}: expected "
                f"{expected_count} theorem files, "
                f"but found {len(theorem_files)}."
            )

        for theorem_file in theorem_files:

            new_theorems.append({
                "domain": domain,
                "folder": folder_name,
                "file_name": theorem_file.name,
                "file": theorem_file,
            })

    return new_theorems


# ============================================================
# BUILD DATASET ROWS
# ============================================================

def build_new_rows(
    existing_rows,
    new_theorems,
):

    existing_ids = {
        int(row["ID"].strip())
        for row in existing_rows
    }

    if existing_ids != set(range(1, 51)):
        raise RuntimeError(
            "Existing dataset must contain IDs 1-50 "
            "before adding the new theorems."
        )

    new_rows = []

    next_id = 51

    for theorem in new_theorems:

        if next_id in existing_ids:
            raise RuntimeError(
                f"ID {next_id} already exists."
            )

        file_name = theorem["file_name"]
        domain = theorem["domain"]
        folder = theorem["folder"]

        # Path stored relative to the outer LeanCopilotTest
        # project root.
        relative_path = (
            Path("Formal_Proof_Generation_Project")
            / "theorems"
            / folder
            / file_name
        )

        file_path = str(
            relative_path
        ).replace("/", "\\")

        new_rows.append({
            "ID": str(next_id),
            "file_name": file_name,
            "file_path": file_path,
            "domain": domain,
            "difficulty": DIFFICULTY_PLACEHOLDER,
        })

        next_id += 1

    return new_rows


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
        encoding="utf-8"
    ) as file:

        writer = csv.DictWriter(
            file,
            fieldnames=fieldnames
        )

        writer.writeheader()
        writer.writerows(rows)


# ============================================================
# MAIN
# ============================================================

def main():

    print("=" * 70)
    print("ADDING NEW THEOREMS TO DATASET")
    print("=" * 70)

    print(
        f"Dataset : {DATASET_FILE}"
    )

    print(
        f"Theorems: {THEOREMS_DIR}"
    )

    print()

    # --------------------------------------------------------
    # Read existing dataset
    # --------------------------------------------------------

    existing_rows, fieldnames = read_dataset()

    print(
        f"Existing rows: {len(existing_rows)}"
    )

    # --------------------------------------------------------
    # Validate existing dataset
    # --------------------------------------------------------

    validate_existing_dataset(
        existing_rows
    )

    print(
        "Existing dataset validated: IDs 1-50."
    )

    # --------------------------------------------------------
    # Find generated theorem files
    # --------------------------------------------------------

    new_theorems = collect_theorem_files()

    print()
    print(
        f"New theorem files found: "
        f"{len(new_theorems)}"
    )

    # --------------------------------------------------------
    # Verify total
    # --------------------------------------------------------

    if len(new_theorems) != 100:
        raise RuntimeError(
            f"Expected exactly 100 new theorem files, "
            f"but found {len(new_theorems)}."
        )

    # --------------------------------------------------------
    # Build rows
    # --------------------------------------------------------

    new_rows = build_new_rows(
        existing_rows,
        new_theorems,
    )

    # --------------------------------------------------------
    # Append new rows
    # --------------------------------------------------------

    updated_rows = (
        existing_rows
        + new_rows
    )

    # --------------------------------------------------------
    # Final validation
    # --------------------------------------------------------

    if len(updated_rows) != 150:
        raise RuntimeError(
            f"Expected 150 total rows, "
            f"but got {len(updated_rows)}."
        )

    final_ids = [
        int(row["ID"])
        for row in updated_rows
    ]

    if final_ids != list(range(1, 151)):
        raise RuntimeError(
            "Final IDs are not exactly 1 through 150."
        )

    # --------------------------------------------------------
    # Write CSV
    # --------------------------------------------------------

    write_dataset(
        updated_rows,
        fieldnames,
    )

    # --------------------------------------------------------
    # Summary
    # --------------------------------------------------------

    print()
    print("=" * 70)
    print("DATASET UPDATE COMPLETE")
    print("=" * 70)

    print(
        "Existing theorems : 50"
    )

    print(
        "New Nat theorems  : 34  (IDs 51-84)"
    )

    print(
        "New Prop theorems : 33  (IDs 85-117)"
    )

    print(
        "New Group theorems: 33  (IDs 118-150)"
    )

    print()
    print(
        "Total dataset rows: 150"
    )

    print()
    print(
        "Difficulty for new theorems:"
    )

    print(
        f"  {DIFFICULTY_PLACEHOLDER}"
    )

    print()
    print(
        "dataset.csv updated successfully."
    )

    print("=" * 70)


if __name__ == "__main__":
    main()