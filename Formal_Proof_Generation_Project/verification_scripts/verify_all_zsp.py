#!/usr/bin/env python3

import subprocess
import csv
from pathlib import Path
from collections import defaultdict, Counter
import matplotlib.pyplot as plt
import pandas as pd
from openpyxl.utils import get_column_letter

# --------------------------------------------------
# Configuration
# --------------------------------------------------

OUTPUT_DIR = Path("Formal_Proof_Generation_Project/outputs")
RESULTS_DIR = Path("Formal_Proof_Generation_Project/results")
DATASET_FILE = Path("Formal_Proof_Generation_Project/dataset.csv")

RESULTS_DIR.mkdir(parents=True, exist_ok=True)

MODEL_FOLDERS = [
    "gemini_flash_lite_zero",
    "gemini_flash_zero",
    "gemma_zero",
]

# --------------------------------------------------
# Read theorem metadata
# --------------------------------------------------

dataset = pd.read_csv(DATASET_FILE)

theorem_domains = dict(
    zip(
        dataset["file_name"].astype(str),
        dataset["domain"].astype(str).str.strip().str.lower().replace({"lists": "list"})
    )
)

# --------------------------------------------------
# Domain-specific imports
# --------------------------------------------------

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

# --------------------------------------------------
# Domain-specific namespaces
# --------------------------------------------------

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

# --------------------------------------------------
# Verify one Lean file
# --------------------------------------------------

def verify(file_path, domain):
    """
    Returns:
        success (bool)
        error_message (str)
    """

    required_imports = DOMAIN_IMPORTS.get(domain)

    if required_imports is None:
        return False, f"Unknown domain: {domain}"

    try:
        # Read original file
        original_text = file_path.read_text(encoding="utf-8")

        # Add any missing domain-specific imports
        missing_imports = [
            imp for imp in required_imports
            if imp not in original_text
        ]

        if missing_imports:
            temp_text = (
                "\n".join(missing_imports)
                + "\n\n"
                + original_text
            )
        else:
            temp_text = original_text

        # Add namespace for domains that require one
        namespace_info = DOMAIN_NAMESPACES.get(domain)

        if namespace_info is not None:
            namespace_start = namespace_info["start"]
            namespace_end = namespace_info["end"]

            # Only add the namespace if it is not already present
            if namespace_start not in temp_text:
                temp_text = (
                    temp_text
                    + "\n\n"
                    + namespace_start
                    + "\n"
                    + namespace_end
                    + "\n"
                )

                # Put the namespace around the theorem content
                lines = temp_text.splitlines()

                import_end = 0

                for i, line in enumerate(lines):
                    if line.startswith("import "):
                        import_end = i + 1

                import_part = lines[:import_end]
                theorem_part = lines[import_end:]

                temp_text = (
                    "\n".join(import_part)
                    + "\n\n"
                    + namespace_start
                    + "\n"
                    + "\n".join(theorem_part[:-2])
                    + "\n"
                    + namespace_end
                    + "\n"
                )

        # Create a temporary Lean file
        temp_file = file_path.with_suffix(".verify.lean")
        temp_file.write_text(temp_text, encoding="utf-8")

        try:
            result = subprocess.run(
                ["lake", "env", "lean", str(temp_file)],
                capture_output=True,
                text=True,
                timeout=120
            )

            success = result.returncode == 0

            if success:
                return True, ""

            return False, result.stdout.strip()

        finally:
            # Always delete the temporary file
            if temp_file.exists():
                temp_file.unlink()

    except subprocess.TimeoutExpired:
        return False, "Timeout"

    except Exception as e:
        return False, str(e)


# --------------------------------------------------
# Classify Lean errors
# --------------------------------------------------

def classify_error(error):
    """
    Classify common Lean verification failures.
    """

    e = error.lower()

    if e == "":
        return ""

    if "timeout" in e:
        return "Timeout"

    if "no goals to be solved" in e:
        return "No Goals to be Solved"

    if "unknown identifier" in e:
        return "Unknown Identifier"

    if "unknown constant" in e:
        return "Unknown Constant"

    if "application type mismatch" in e:
        return "Application Type Mismatch"

    if "type mismatch" in e:
        return "Type Mismatch"

    if "unsolved goals" in e:
        return "Unsolved Goals"

    if "tactic" in e and "failed" in e:
        return "Tactic Failure"

    if "unexpected token" in e:
        return "Syntax Error"

    if "expected" in e and "got" in e:
        return "Syntax Error"

    if "invalid field" in e:
        return "Invalid Field"

    return "Other"


# --------------------------------------------------
# Main
# --------------------------------------------------

results = []

summary = defaultdict(lambda: {"total": 0, "success": 0})

failures = []

for folder in MODEL_FOLDERS:

    folder_path = OUTPUT_DIR / folder

    if not folder_path.exists():
        print(f"Skipping missing folder: {folder}")
        continue

    for file in sorted(folder_path.glob("*.lean")):

        domain = theorem_domains.get(file.name)

        if domain is None:
            print(
                f"Skipping {file.name}: "
                f"domain not found in dataset.csv"
            )
            continue

        success, error = verify(file, domain)

        summary[folder]["total"] += 1

        if success:
            summary[folder]["success"] += 1

        else:
            failures.append({
                "folder": folder,
                "file": file.name,
                "error_type": classify_error(error),
                "error": error
            })

        results.append({
            "folder": folder,
            "file": file.name,
            "status": "PASS" if success else "FAIL",
            "error": error
        })

        print(
            f"{folder:12} "
            f"{file.name:25} "
            f"{'PASS' if success else 'FAIL'}"
        )

# --------------------------------------------------
# Write verification_results.csv
# --------------------------------------------------

with open(
    RESULTS_DIR / "verification_results.csv",
    "w",
    newline="",
    encoding="utf-8"
) as f:

    writer = csv.DictWriter(
        f,
        fieldnames=["folder", "file", "status", "error"]
    )

    writer.writeheader()

    for row in results:
        writer.writerow(row)

# --------------------------------------------------
# Write summary_table.csv
# --------------------------------------------------

with open(
    RESULTS_DIR / "summary_table.csv",
    "w",
    newline="",
    encoding="utf-8"
) as f:

    writer = csv.writer(f)

    writer.writerow([
        "Folder",
        "Total",
        "Passed",
        "Failed",
        "Success Rate (%)"
    ])

    for folder in MODEL_FOLDERS:

        if folder not in summary:
            continue

        total = summary[folder]["total"]
        passed = summary[folder]["success"]
        failed = total - passed

        rate = 100 * passed / total if total else 0

        writer.writerow([
            folder,
            total,
            passed,
            failed,
            f"{rate:.2f}"
        ])

# --------------------------------------------------
# Write failure_analysis.csv
# --------------------------------------------------

with open(
    RESULTS_DIR / "failure_analysis.csv",
    "w",
    newline="",
    encoding="utf-8"
) as f:

    writer = csv.DictWriter(
        f,
        fieldnames=[
            "folder",
            "file",
            "error_type",
            "error"
        ]
    )

    writer.writeheader()

    for row in failures:
        writer.writerow(row)

# --------------------------------------------------
# Per-model Results
# --------------------------------------------------

print("\nPer-model Results")
print("-" * 50)

for folder in MODEL_FOLDERS:

    if folder not in summary:
        continue

    total = summary[folder]["total"]
    passed = summary[folder]["success"]
    failed = total - passed

    rate = 100 * passed / total if total else 0

    print(
        f"{folder:12} "
        f"{passed:3}/{total:<3} "
        f"Passed  "
        f"Failed: {failed:<3} "
        f"Success: {rate:.2f}%"
    )

# --------------------------------------------------
# Error Summary (Overall)
# --------------------------------------------------

error_counts = Counter(
    row["error_type"]
    for row in failures
)

print("\nOverall Error Summary")
print("-" * 40)

for error_type, count in sorted(error_counts.items()):
    print(f"{error_type:25} {count}")

# --------------------------------------------------
# Error Summary by Model / Prompt
# --------------------------------------------------

error_summary = defaultdict(Counter)

for row in failures:
    folder = row["folder"]
    error_type = row["error_type"]

    error_summary[folder][error_type] += 1

print("\nError Summary by Model / Prompt")
print("-" * 50)

for folder in MODEL_FOLDERS:

    if folder not in error_summary:
        continue

    print(f"\n{folder.upper()}")

    total_errors = sum(
        error_summary[folder].values()
    )

    for error_type, count in sorted(
        error_summary[folder].items(),
        key=lambda x: (-x[1], x[0])
    ):
        print(
            f"  {error_type:25} {count}"
        )

    print(f"  Total Errors: {total_errors}")

# --------------------------------------------------
# Write error_summary_by_prompt_model.csv
# --------------------------------------------------

with open(
    RESULTS_DIR / "error_summary_by_prompt_model.csv",
    "w",
    newline="",
    encoding="utf-8"
) as f:

    writer = csv.writer(f)

    writer.writerow([
        "Model",
        "Prompt Type",
        "Error Category",
        "Count"
    ])

    for folder in MODEL_FOLDERS:

        if folder not in error_summary:
            continue

        parts = folder.split("_")

        model = parts[0]
        prompt = "_".join(parts[1:])

        for error_type, count in sorted(
            error_summary[folder].items(),
            key=lambda x: (-x[1], x[0])
        ):
            writer.writerow([
                model.upper(),
                prompt,
                error_type,
                count
            ])

# --------------------------------------------------
# Final Results
# --------------------------------------------------

print("\nVerification complete.")

print(f"Verified {len(results)} files.")

total_pass = sum(
    s["success"]
    for s in summary.values()
)

total_files = sum(
    s["total"]
    for s in summary.values()
)

print(
    f"Passed: {total_pass}/{total_files}"
)

overall_rate = 100 * total_pass / total_files if total_files else 0

print(
    f"Success rate: "
    f"{overall_rate:.2f}%"
)

# --------------------------------------------------
# Overall Error Graph
# --------------------------------------------------

if error_counts:

    plt.figure(figsize=(8, 5))

    labels = list(error_counts.keys())
    values = list(error_counts.values())

    plt.bar(labels, values)

    plt.title("Overall Error Distribution")
    plt.xlabel("Error Category")
    plt.ylabel("Count")

    plt.xticks(
        rotation=45,
        ha="right"
    )

    plt.tight_layout()

    plt.savefig(
        RESULTS_DIR / "overall_error_distribution.png",
        dpi=300,
        bbox_inches="tight"
    )

    plt.close()

# --------------------------------------------------
# Error Graph per Model
# --------------------------------------------------

for folder in MODEL_FOLDERS:

    if folder not in error_summary:
        continue

    counts = error_summary[folder]

    plt.figure(figsize=(8, 5))

    plt.bar(
        list(counts.keys()),
        list(counts.values())
    )

    plt.title(
        f"Error Distribution - {folder}"
    )

    plt.xlabel("Error Category")
    plt.ylabel("Count")

    plt.xticks(
        rotation=45,
        ha="right"
    )

    plt.tight_layout()

    plt.savefig(
        RESULTS_DIR / f"{folder}_error_distribution.png",
        dpi=300,
        bbox_inches="tight"
    )

    plt.close()

# --------------------------------------------------
# Pass vs Fail Graph
# --------------------------------------------------

models = []
passed = []
failed = []

for folder in MODEL_FOLDERS:

    if folder not in summary:
        continue

    models.append(folder)

    passed.append(
        summary[folder]["success"]
    )

    failed.append(
        summary[folder]["total"]
        - summary[folder]["success"]
    )

x = range(len(models))

width = 0.35

plt.figure(figsize=(9, 5))

plt.bar(
    [i - width / 2 for i in x],
    passed,
    width,
    label="Passed"
)

plt.bar(
    [i + width / 2 for i in x],
    failed,
    width,
    label="Failed"
)

plt.xticks(
    x,
    models,
    rotation=20
)

plt.ylabel("Number of Theorems")

plt.title(
    "Verification Results by Model"
)

plt.legend()

plt.tight_layout()

plt.savefig(
    RESULTS_DIR / "model_pass_fail.png",
    dpi=300,
    bbox_inches="tight"
)

plt.close()

# ==============================================================
# ZERO-SHOT STATISTICS + ACCURACY + ERROR ANALYSIS
# Added without removing/changing the existing code above.
# ==============================================================

ZERO_SHOT_EXCEL = RESULTS_DIR / "zero_shot_results.xlsx"


# --------------------------------------------------------------
# Read theorem metadata from dataset.csv
# --------------------------------------------------------------

# Dataset fields:
# ID, file_name, file_path, domain, difficulty
#
# domain values:
#   list, nat, group, prop
#
# difficulty values:
#   easy, medium, hard

theorem_metadata = dataset.copy()

theorem_metadata["_file_key"] = theorem_metadata["file_name"].astype(str)
theorem_metadata["_domain"] = (
    theorem_metadata["domain"].astype(str).str.strip().str.lower()
)
theorem_metadata["_difficulty"] = (
    theorem_metadata["difficulty"].astype(str).str.strip().str.lower()
)

# Validate the expected values.
valid_domains = {"list", "nat", "group", "prop"}
valid_difficulties = {"easy", "medium", "hard"}

invalid_domains = set(theorem_metadata["_domain"]) - valid_domains
invalid_difficulties = set(theorem_metadata["_difficulty"]) - valid_difficulties

if invalid_domains:
    raise ValueError(
        f"Unexpected domain values in dataset.csv: {sorted(invalid_domains)}"
    )

if invalid_difficulties:
    raise ValueError(
        f"Unexpected difficulty values in dataset.csv: "
        f"{sorted(invalid_difficulties)}"
    )


# --------------------------------------------------------------
# Build a dataframe containing every verification result
# --------------------------------------------------------------

verification_df = pd.DataFrame(results)

if verification_df.empty:
    raise ValueError("No verification results were generated.")

verification_df["model"] = verification_df["folder"]

# Merge domain and difficulty from dataset.csv.
verification_df = verification_df.merge(
    theorem_metadata[["_file_key", "_domain", "_difficulty"]],
    left_on="file",
    right_on="_file_key",
    how="left"
)

verification_df.rename(
    columns={
        "_domain": "domain",
        "_difficulty": "difficulty"
    },
    inplace=True
)

verification_df.drop(columns=["_file_key"], inplace=True)

missing_metadata = verification_df[
    verification_df["domain"].isna() | verification_df["difficulty"].isna()
]

if not missing_metadata.empty:
    missing_files = sorted(missing_metadata["file"].astype(str).unique())
    raise ValueError(
        "Domain/difficulty metadata is missing in dataset.csv for: "
        + ", ".join(missing_files)
    )

# Keep the exact dataset labels:
# domains = list, nat, group, prop
# difficulties = easy, medium, hard


# --------------------------------------------------------------
# Helper functions for cross-tabulation
# --------------------------------------------------------------

def count_table(df, row_col, col_col):
    """
    Number of theorems for each row x column combination.
    """
    table = pd.crosstab(
        df[row_col],
        df[col_col],
        dropna=False
    )

    return table


def percentage_table(df, row_col, col_col):
    """
    Row-wise percentage.

    For example, in Model x Domain %, each model's domain counts
    are divided by the total number of theorems for that model.
    """
    counts = count_table(df, row_col, col_col)

    row_totals = counts.sum(axis=1)
    row_totals = row_totals.where(row_totals != 0)

    percentages = counts.div(row_totals, axis=0) * 100

    return percentages.fillna(0).round(2)


# --------------------------------------------------------------
# 1. Model x Level of Difficulty - Values
# --------------------------------------------------------------

model_x_difficulty_values = count_table(
    verification_df,
    "model",
    "difficulty"
)


# --------------------------------------------------------------
# 2. Model x Level of Difficulty - %
# --------------------------------------------------------------

model_x_difficulty_percent = percentage_table(
    verification_df,
    "model",
    "difficulty"
)


# --------------------------------------------------------------
# 3. Domain x Level of Difficulty - Values
# --------------------------------------------------------------

domain_x_difficulty_values = count_table(
    verification_df,
    "domain",
    "difficulty"
)


# --------------------------------------------------------------
# 4. Domain x Level of Difficulty - %
# --------------------------------------------------------------

domain_x_difficulty_percent = percentage_table(
    verification_df,
    "domain",
    "difficulty"
)


# --------------------------------------------------------------
# 5. Model x Domain - Values
# --------------------------------------------------------------

model_x_domain_values = count_table(
    verification_df,
    "model",
    "domain"
)


# --------------------------------------------------------------
# 6. Model x Domain - %
# --------------------------------------------------------------

model_x_domain_percent = percentage_table(
    verification_df,
    "model",
    "domain"
)


# --------------------------------------------------------------
# Accuracy helper
# --------------------------------------------------------------

def accuracy_table(df, row_col, col_col):
    """
    Calculates PASS accuracy (%) for each row x column combination.

    Accuracy = number of PASS results / total results * 100
    """

    total = pd.crosstab(
        df[row_col],
        df[col_col],
        dropna=False
    )

    passed = pd.crosstab(
        df.loc[df["status"] == "PASS", row_col],
        df.loc[df["status"] == "PASS", col_col],
        dropna=False
    )

    # Make sure PASS table has exactly the same rows/columns as total.
    passed = passed.reindex(
        index=total.index,
        columns=total.columns,
        fill_value=0
    )

    safe_total = total.where(total != 0)
    accuracy = passed.div(safe_total) * 100

    return accuracy.fillna(0).round(2)


# --------------------------------------------------------------
# Accuracy 1. Model x Domain
# --------------------------------------------------------------

accuracy_model_x_domain = accuracy_table(
    verification_df,
    "model",
    "domain"
)


# --------------------------------------------------------------
# Accuracy 2. Model x Level of Difficulty
# --------------------------------------------------------------

accuracy_model_x_difficulty = accuracy_table(
    verification_df,
    "model",
    "difficulty"
)


# --------------------------------------------------------------
# Excel formatting helper
# --------------------------------------------------------------

def format_excel_sheet(writer, dataframe, sheet_name):
    """
    Write a dataframe and apply basic readable formatting.
    """
    dataframe.to_excel(
        writer,
        sheet_name=sheet_name,
        index=True
    )

    worksheet = writer.sheets[sheet_name]

    # Freeze the first row and first column.
    worksheet.freeze_panes = "B2"

    # Adjust column widths.
    for column_cells in worksheet.columns:
        max_length = 0

        for cell in column_cells:
            value = "" if cell.value is None else str(cell.value)
            max_length = max(max_length, len(value))

        column_letter = column_cells[0].column_letter
        worksheet.column_dimensions[column_letter].width = min(
            max(max_length + 2, 12),
            30
        )


# --------------------------------------------------------------
# Write zero_shot_results.xlsx
#
# Sheet 1:
#   1. Model x Difficulty - Values
#   2. Model x Difficulty - %
#   3. Domain x Difficulty - Values
#   4. Domain x Difficulty - %
#   5. Model x Domain - Values
#   6. Model x Domain - %
#
# Sheet 2:
#   7. Accuracy - Model x Domain
#   8. Accuracy - Model x Difficulty
# --------------------------------------------------------------

with pd.ExcelWriter(
    ZERO_SHOT_EXCEL,
    engine="openpyxl"
) as writer:

    # Sheet 1 contains the six requested statistics tables.
    sheet1_tables = [
        (
            model_x_difficulty_values,
            "Model x Difficulty - Values"
        ),
        (
            model_x_difficulty_percent,
            "Model x Difficulty - %"
        ),
        (
            domain_x_difficulty_values,
            "Domain x Difficulty - Values"
        ),
        (
            domain_x_difficulty_percent,
            "Domain x Difficulty - %"
        ),
        (
            model_x_domain_values,
            "Model x Domain - Values"
        ),
        (
            model_x_domain_percent,
            "Model x Domain - %"
        ),
    ]

    # Put the six tables one below another in Sheet 1.
    row_position = 0

    for table, title in sheet1_tables:

        pd.DataFrame([title]).to_excel(
            writer,
            sheet_name="Statistics",
            startrow=row_position,
            startcol=0,
            index=False,
            header=False
        )

        table.to_excel(
            writer,
            sheet_name="Statistics",
            startrow=row_position + 1,
            startcol=0,
            index=True
        )

        row_position += len(table) + 4

    # Sheet 2 contains the two requested accuracy tables.
    sheet2_tables = [
        (
            accuracy_model_x_domain,
            "Accuracy - Model x Domain"
        ),
        (
            accuracy_model_x_difficulty,
            "Accuracy - Model x Difficulty"
        ),
    ]

    row_position = 0

    for table, title in sheet2_tables:

        pd.DataFrame([title]).to_excel(
            writer,
            sheet_name="Accuracy",
            startrow=row_position,
            startcol=0,
            index=False,
            header=False
        )

        table.to_excel(
            writer,
            sheet_name="Accuracy",
            startrow=row_position + 1,
            startcol=0,
            index=True
        )

        row_position += len(table) + 4

    # Basic formatting for both sheets.
    for sheet_name in ["Statistics", "Accuracy"]:

        worksheet = writer.sheets[sheet_name]
        worksheet.freeze_panes = "B2"

        for column_cells in worksheet.columns:

            max_length = 0

            for cell in column_cells:
                value = "" if cell.value is None else str(cell.value)
                max_length = max(max_length, len(value))

            column_letter = get_column_letter(
                column_cells[0].column
            )

            worksheet.column_dimensions[column_letter].width = min(
                max(max_length + 2, 12),
                35
            )


# --------------------------------------------------------------
# Error summaries by Model x Domain,
# Model x Difficulty, and Domain x Difficulty
# --------------------------------------------------------------

# Existing error summary is model-wise.
# We keep it unchanged and add the three requested breakdowns.

error_df = pd.DataFrame(failures)

if not error_df.empty:

    error_df = error_df.merge(
        theorem_metadata[["_file_key", "_domain", "_difficulty"]],
        left_on="file",
        right_on="_file_key",
        how="left"
    )

    error_df["domain"] = (
        error_df["_domain"]
        .astype(str)
        .str.capitalize()
    )

    error_df["difficulty"] = (
        error_df["_difficulty"]
        .astype(str)
        .str.capitalize()
    )

    error_df.drop(
        columns=["_file_key", "_domain", "_difficulty"],
        inplace=True
    )

    # ----------------------------------------------------------
    # Model x Domain x Error Category
    # ----------------------------------------------------------

    error_model_x_domain = (
        error_df
        .groupby(
            ["folder", "domain", "error_type"]
        )
        .size()
        .reset_index(name="Count")
        .rename(columns={"folder": "Model"})
        .sort_values(
            ["Model", "domain", "Count", "error_type"],
            ascending=[True, True, False, True]
        )
    )

    # ----------------------------------------------------------
    # Model x Difficulty x Error Category
    # ----------------------------------------------------------

    error_model_x_difficulty = (
        error_df
        .groupby(
            ["folder", "difficulty", "error_type"]
        )
        .size()
        .reset_index(name="Count")
        .rename(columns={"folder": "Model"})
        .sort_values(
            ["Model", "difficulty", "Count", "error_type"],
            ascending=[True, True, False, True]
        )
    )

    # ----------------------------------------------------------
    # Domain x Difficulty x Error Category
    # ----------------------------------------------------------

    error_domain_x_difficulty = (
        error_df
        .groupby(
            ["domain", "difficulty", "error_type"]
        )
        .size()
        .reset_index(name="Count")
        .sort_values(
            ["domain", "difficulty", "Count", "error_type"],
            ascending=[True, True, False, True]
        )
    )

else:

    error_model_x_domain = pd.DataFrame(
        columns=["Model", "domain", "error_type", "Count"]
    )

    error_model_x_difficulty = pd.DataFrame(
        columns=["Model", "difficulty", "error_type", "Count"]
    )

    error_domain_x_difficulty = pd.DataFrame(
        columns=["domain", "difficulty", "error_type", "Count"]
    )


# --------------------------------------------------------------
# Save the three new error-analysis CSV files
# --------------------------------------------------------------

error_model_x_domain.to_csv(
    RESULTS_DIR / "error_summary_by_model_domain.csv",
    index=False
)

error_model_x_difficulty.to_csv(
    RESULTS_DIR / "error_summary_by_model_difficulty.csv",
    index=False
)

error_domain_x_difficulty.to_csv(
    RESULTS_DIR / "error_summary_by_domain_difficulty.csv",
    index=False
)


# --------------------------------------------------------------
# Console output for the new statistics
# --------------------------------------------------------------

print("\nZero-shot Statistics")
print("=" * 60)

print("\nModel x Difficulty - Values")
print(model_x_difficulty_values)

print("\nModel x Difficulty - %")
print(model_x_difficulty_percent)

print("\nDomain x Difficulty - Values")
print(domain_x_difficulty_values)

print("\nDomain x Difficulty - %")
print(domain_x_difficulty_percent)

print("\nModel x Domain - Values")
print(model_x_domain_values)

print("\nModel x Domain - %")
print(model_x_domain_percent)

print("\nAccuracy - Model x Domain (%)")
print(accuracy_model_x_domain)

print("\nAccuracy - Model x Difficulty (%)")
print(accuracy_model_x_difficulty)

print("\nAdditional error summaries saved:")
print("  error_summary_by_model_domain.csv")
print("  error_summary_by_model_difficulty.csv")
print("  error_summary_by_domain_difficulty.csv")

print(f"\nExcel workbook saved to:")
print(f"  {ZERO_SHOT_EXCEL}")
