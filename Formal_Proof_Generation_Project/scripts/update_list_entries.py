from pathlib import Path
import csv


# ============================================================
# PATH CONFIGURATION
# ============================================================

SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_DIR = SCRIPT_DIR.parent

DATASET_FILE = PROJECT_DIR / "dataset.csv"

LIST_THEOREMS_DIR = (
    PROJECT_DIR
    / "theorems"
    / "Lists"
)


# Existing List theorem IDs
LIST_IDS = set(range(1, 51))


# ============================================================
# DATASET UPDATE
# ============================================================

def update_list_entries():

    if not DATASET_FILE.exists():
        raise FileNotFoundError(
            f"dataset.csv not found:\n{DATASET_FILE}"
        )

    if not LIST_THEOREMS_DIR.exists():
        raise FileNotFoundError(
            f"Lists directory not found:\n"
            f"{LIST_THEOREMS_DIR}"
        )

    # --------------------------------------------------------
    # Read dataset
    # --------------------------------------------------------

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

    # --------------------------------------------------------
    # Update the 50 existing List entries
    # --------------------------------------------------------

    updated_count = 0

    for row in rows:

        try:
            theorem_id = int(row["ID"].strip())
        except ValueError:
            continue

        # Identify List theorems using their existing IDs.
        if theorem_id not in LIST_IDS:
            continue

        file_name = row["file_name"].strip()

        if not file_name:
            raise RuntimeError(
                f"Empty file_name for ID {theorem_id}"
            )

        theorem_file = (
            LIST_THEOREMS_DIR
            / file_name
        )

        # ----------------------------------------------------
        # Verify theorem file exists
        # ----------------------------------------------------

        if not theorem_file.exists():
            raise FileNotFoundError(
                f"Theorem file for ID {theorem_id} "
                f"was not found:\n{theorem_file}"
            )

        # ----------------------------------------------------
        # Update domain
        # ----------------------------------------------------

        row["domain"] = "list"

        # ----------------------------------------------------
        # Update file path
        # ----------------------------------------------------

        relative_path = (
            Path("Formal_Proof_Generation_Project")
            / "theorems"
            / "Lists"
            / file_name
        )

        row["file_path"] = str(
            relative_path
        ).replace("/", "\\")

        updated_count += 1

    # --------------------------------------------------------
    # Verify exactly 50 entries were updated
    # --------------------------------------------------------

    if updated_count != 50:
        raise RuntimeError(
            f"Expected to update 50 List entries, "
            f"but found {updated_count}."
        )

    # --------------------------------------------------------
    # Write updated dataset
    # --------------------------------------------------------

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

    # --------------------------------------------------------
    # Summary
    # --------------------------------------------------------

    print("=" * 60)
    print("LIST DATASET UPDATE COMPLETE")
    print("=" * 60)

    print(f"Dataset : {DATASET_FILE}")
    print(f"Updated : {updated_count} List entries")

    print()
    print("Changes made:")
    print("  domain    -> list")
    print(
        "  file_path -> "
        "Formal_Proof_Generation_Project/"
        "theorems/Lists/<file_name>"
    )

    print()
    print("Unchanged:")
    print("  ID")
    print("  file_name")
    print("  difficulty")

    print()
    print("No new theorem rows were added.")

    print("=" * 60)


# ============================================================
# MAIN
# ============================================================

if __name__ == "__main__":
    update_list_entries()