import subprocess
import csv
from pathlib import Path
from collections import defaultdict, Counter
import matplotlib.pyplot as plt
import pandas as pd
from openpyxl.utils import get_column_letter

OUTPUT_DIR = Path("Formal_Proof_Generation_Project/outputs")
RESULTS_DIR = Path("Formal_Proof_Generation_Project/results/one shot results")
DATASET_FILE = Path("Formal_Proof_Generation_Project/dataset.csv")
RESULTS_DIR.mkdir(parents=True, exist_ok=True)

MODEL_FOLDERS = [
    "gemini_flash_lite_one",
    # "gemini_flash_one",
    "gemma_one",
]

dataset = pd.read_csv(DATASET_FILE)

theorem_domains = dict(
    zip(
        dataset["file_name"].astype(str),
        dataset["domain"]
        .astype(str)
        .str.strip()
        .str.lower()
        .replace({"lists": "list"})
    )
)

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
        original_text = file_path.read_text(encoding="utf-8")

        missing_imports = [
            imp
            for imp in required_imports
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

        namespace_info = DOMAIN_NAMESPACES.get(domain)

        if namespace_info is not None:
            namespace_start = namespace_info["start"]
            namespace_end = namespace_info["end"]

            if namespace_start not in temp_text:
                temp_text = (
                    temp_text
                    + "\n\n"
                    + namespace_start
                    + "\n"
                    + namespace_end
                    + "\n"
                )

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

            error_output = result.stdout.strip()

            if not error_output:
                error_output = result.stderr.strip()

            return False, error_output

        finally:
            if temp_file.exists():
                temp_file.unlink()

    except subprocess.TimeoutExpired:
        return False, "Timeout"

    except Exception as e:
        return False, str(e)

def classify_error(error):
    """
    Classify a Lean verification failure based on the
    FIRST actual error message reported by Lean.
    """
    if not error:
        return ""

    for line in error.splitlines():
        line_lower = line.lower().strip()

        if not line_lower or "error:" not in line_lower:
            continue

        message = line_lower.split("error:", 1)[1].strip()

        if "unknown tactic" in message:
            return "Unknown / Unsupported Tactic"

        if (
            "unknown theorem" in message
            or "unknown constant" in message
            or "unknown identifier" in message
        ):
            return "Unknown Theorem / Constant / Identifier"

        if (
            "did not find instance of the pattern" in message
            or "pattern is not found" in message
        ):
            return "Rewrite Failure"

        if (
            "application type mismatch" in message
            or "type mismatch" in message
        ):
            return "Type Mismatch / Wrong Argument"

        if (
            "simp recursion" in message
            or (
                "maximum recursion depth" in message
                and "simp" in message
            )
        ):
            return "Simp Recursion / Looping"

        if (
            "simp" in message
            and (
                "failed" in message
                or "no progress" in message
            )
        ):
            return "Simp Failure / No Progress"

        if (
            "failed to synthesize" in message
            or "typeclass" in message
        ):
            return "Missing Typeclass / Insufficient Assumptions"

        if (
            "invalid field" in message
            or "invalid projection" in message
        ):
            return "Invalid Field / Projection"

        if (
            "fail to show termination" in message
            or "failed to prove termination" in message
            or "decreasing argument" in message
        ):
            return "Invalid Recursive Definition / Termination"

        if "unsolved goals" in message:
            return "Unsolved Goals"

        if "incomplete" in message and "branch" in message:
            return "Incomplete Tactic Branches"

        if (
            any(
                tactic in message
                for tactic in (
                    "omega",
                    "linarith",
                    "nlinarith",
                    "norm_num"
                )
            )
            and "failed" in message
        ):
            return "Arithmetic Tactic Failure"

        if "no goals to be solved" in message:
            return "Extra Tactic after Solved"

        if "tactic" in message and "failed" in message:
            return "Tactic Application / Strategy Failure"

        if (
            "unexpected token" in message
            or "syntax error" in message
            or (
                "expected" in message
                and "got" in message
            )
        ):
            return "Syntax / Malformed Proof Structure"

        return "Other"

    return "Other"

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

error_counts = Counter(
    row["error_type"]
    for row in failures
)

print("\nOverall Error Summary")
print("-" * 40)

for error_type, count in sorted(error_counts.items()):
    print(f"{error_type:25} {count}")

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

overall_rate = (
    100 * total_pass / total_files
    if total_files
    else 0
)

print(
    f"Success rate: "
    f"{overall_rate:.2f}%"
)

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

ONE_SHOT_EXCEL = RESULTS_DIR / "one_shot_results.xlsx"

theorem_metadata = dataset.copy()

theorem_metadata["_file_key"] = (
    theorem_metadata["file_name"].astype(str)
)

theorem_metadata["_domain"] = (
    theorem_metadata["domain"]
    .astype(str)
    .str.strip()
    .str.lower()
)

theorem_metadata["_difficulty"] = (
    theorem_metadata["difficulty"]
    .astype(str)
    .str.strip()
    .str.lower()
)

valid_domains = {
    "list",
    "nat",
    "group",
    "prop"
}

valid_difficulties = {
    "easy",
    "medium",
    "hard"
}

invalid_domains = (
    set(theorem_metadata["_domain"])
    - valid_domains
)

invalid_difficulties = (
    set(theorem_metadata["_difficulty"])
    - valid_difficulties
)

if invalid_domains:
    raise ValueError(
        f"Unexpected domain values in dataset.csv: "
        f"{sorted(invalid_domains)}"
    )

if invalid_difficulties:
    raise ValueError(
        f"Unexpected difficulty values in dataset.csv: "
        f"{sorted(invalid_difficulties)}"
    )

verification_df = pd.DataFrame(results)

if verification_df.empty:
    raise ValueError(
        "No verification results were generated."
    )

verification_df["model"] = verification_df["folder"]

verification_df = verification_df.merge(
    theorem_metadata[
        [
            "_file_key",
            "_domain",
            "_difficulty"
        ]
    ],
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

verification_df.drop(
    columns=["_file_key"],
    inplace=True
)

missing_metadata = verification_df[
    verification_df["domain"].isna()
    | verification_df["difficulty"].isna()
]

if not missing_metadata.empty:
    missing_files = sorted(
        missing_metadata["file"]
        .astype(str)
        .unique()
    )

    raise ValueError(
        "Domain/difficulty metadata is missing in "
        "dataset.csv for: "
        + ", ".join(missing_files)
    )

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

    For example, in Model x Domain %, each model's
    domain counts are divided by the total number of
    theorems for that model.
    """
    counts = count_table(
        df,
        row_col,
        col_col
    )

    row_totals = counts.sum(axis=1)

    row_totals = row_totals.where(
        row_totals != 0
    )

    percentages = (
        counts.div(
            row_totals,
            axis=0
        )
        * 100
    )

    return percentages.fillna(0).round(2)

model_x_difficulty_values = count_table(
    verification_df,
    "model",
    "difficulty"
)

model_x_difficulty_percent = percentage_table(
    verification_df,
    "model",
    "difficulty"
)

domain_x_difficulty_values = count_table(
    verification_df,
    "domain",
    "difficulty"
)

domain_x_difficulty_percent = percentage_table(
    verification_df,
    "domain",
    "difficulty"
)

model_x_domain_values = count_table(
    verification_df,
    "model",
    "domain"
)

model_x_domain_percent = percentage_table(
    verification_df,
    "model",
    "domain"
)

def accuracy_table(df, row_col, col_col):
    """
    Calculates PASS accuracy (%) for each row x column
    combination.

    Accuracy =
        number of PASS results / total results * 100
    """
    total = pd.crosstab(
        df[row_col],
        df[col_col],
        dropna=False
    )

    passed = pd.crosstab(
        df.loc[
            df["status"] == "PASS",
            row_col
        ],
        df.loc[
            df["status"] == "PASS",
            col_col
        ],
        dropna=False
    )

    passed = passed.reindex(
        index=total.index,
        columns=total.columns,
        fill_value=0
    )

    safe_total = total.where(
        total != 0
    )

    accuracy = (
        passed.div(safe_total)
        * 100
    )

    return accuracy.fillna(0).round(2)

accuracy_model_x_domain = accuracy_table(
    verification_df,
    "model",
    "domain"
)

accuracy_model_x_difficulty = accuracy_table(
    verification_df,
    "model",
    "difficulty"
)

def format_excel_sheet(
    writer,
    dataframe,
    sheet_name
):
    """
    Write a dataframe and apply basic readable formatting.
    """
    dataframe.to_excel(
        writer,
        sheet_name=sheet_name,
        index=True
    )

    worksheet = writer.sheets[sheet_name]

    worksheet.freeze_panes = "B2"

    for column_cells in worksheet.columns:
        max_length = 0

        for cell in column_cells:
            value = (
                ""
                if cell.value is None
                else str(cell.value)
            )

            max_length = max(
                max_length,
                len(value)
            )

        column_letter = (
            column_cells[0].column_letter
        )

        worksheet.column_dimensions[
            column_letter
        ].width = min(
            max(max_length + 2, 12),
            30
        )

with pd.ExcelWriter(
    ONE_SHOT_EXCEL,
    engine="openpyxl"
) as writer:
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

        row_position += (
            len(table) + 4
        )

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

        row_position += (
            len(table) + 4
        )

    for sheet_name in [
        "Statistics",
        "Accuracy"
    ]:
        worksheet = writer.sheets[sheet_name]

        worksheet.freeze_panes = "B2"

        for column_cells in worksheet.columns:
            max_length = 0

            for cell in column_cells:
                value = (
                    ""
                    if cell.value is None
                    else str(cell.value)
                )

                max_length = max(
                    max_length,
                    len(value)
                )

            column_letter = get_column_letter(
                column_cells[0].column
            )

            worksheet.column_dimensions[
                column_letter
            ].width = min(
                max(max_length + 2, 12),
                35
            )

error_df = pd.DataFrame(failures)

if not error_df.empty:
    error_df = error_df.merge(
        theorem_metadata[
            [
                "_file_key",
                "_domain",
                "_difficulty"
            ]
        ],
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
        columns=[
            "_file_key",
            "_domain",
            "_difficulty"
        ],
        inplace=True
    )

    error_model_x_domain = (
        error_df
        .groupby(
            [
                "folder",
                "domain",
                "error_type"
            ]
        )
        .size()
        .reset_index(name="Count")
        .rename(
            columns={
                "folder": "Model"
            }
        )
        .sort_values(
            [
                "Model",
                "domain",
                "Count",
                "error_type"
            ],
            ascending=[
                True,
                True,
                False,
                True
            ]
        )
    )

    error_model_x_difficulty = (
        error_df
        .groupby(
            [
                "folder",
                "difficulty",
                "error_type"
            ]
        )
        .size()
        .reset_index(name="Count")
        .rename(
            columns={
                "folder": "Model"
            }
        )
        .sort_values(
            [
                "Model",
                "difficulty",
                "Count",
                "error_type"
            ],
            ascending=[
                True,
                True,
                False,
                True
            ]
        )
    )

    error_domain_x_difficulty = (
        error_df
        .groupby(
            [
                "domain",
                "difficulty",
                "error_type"
            ]
        )
        .size()
        .reset_index(name="Count")
        .sort_values(
            [
                "domain",
                "difficulty",
                "Count",
                "error_type"
            ],
            ascending=[
                True,
                True,
                False,
                True
            ]
        )
    )

else:
    error_model_x_domain = pd.DataFrame(
        columns=[
            "Model",
            "domain",
            "error_type",
            "Count"
        ]
    )

    error_model_x_difficulty = pd.DataFrame(
        columns=[
            "Model",
            "difficulty",
            "error_type",
            "Count"
        ]
    )

    error_domain_x_difficulty = pd.DataFrame(
        columns=[
            "domain",
            "difficulty",
            "error_type",
            "Count"
        ]
    )

error_model_x_domain.to_csv(
    RESULTS_DIR /
    "error_summary_by_model_domain.csv",
    index=False
)

error_model_x_difficulty.to_csv(
    RESULTS_DIR /
    "error_summary_by_model_difficulty.csv",
    index=False
)

error_domain_x_difficulty.to_csv(
    RESULTS_DIR /
    "error_summary_by_domain_difficulty.csv",
    index=False
)

print("\nOne-shot Statistics")
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

print(
    "  error_summary_by_model_domain.csv"
)

print(
    "  error_summary_by_model_difficulty.csv"
)

print(
    "  error_summary_by_domain_difficulty.csv"
)

print("\nExcel workbook saved to:")
print(f"  {ONE_SHOT_EXCEL}")