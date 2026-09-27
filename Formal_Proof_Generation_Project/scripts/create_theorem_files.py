from pathlib import Path
import re
import subprocess
import tempfile


# ============================================================
# PATH CONFIGURATION
# ============================================================

# This script is located at:
#
# LeanCopilotTest/
# └── Formal_Proof_Generation_Project/
#     └── create_theorem_files.py
#
# Therefore:
#   SCRIPT_DIR   = Formal_Proof_Generation_Project
#   PROJECT_ROOT = outer LeanCopilotTest
#   LEAN_SOURCE  = outer LeanCopilotTest/LeanCopilotTest
#

SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_DIR = SCRIPT_DIR.parent
PROJECT_ROOT = PROJECT_DIR.parent

LEAN_SOURCE_DIR = PROJECT_ROOT / "LeanCopilotTest"
THEOREMS_DIR = PROJECT_DIR / "theorems"


# Source theorem files
SOURCE_FILES = {
    "Nat": LEAN_SOURCE_DIR / "nat_proofs.lean",
    "Prop": LEAN_SOURCE_DIR / "prop_proofs.lean",
    "Group": LEAN_SOURCE_DIR / "group_proofs.lean",
}


# Expected number of theorems
EXPECTED_COUNTS = {
    "Nat": 34,
    "Prop": 33,
    "Group": 33,
}


# Imports that must never appear in generated files
EXCLUDED_IMPORTS = {
    "import LeanCopilot",
}


# ============================================================
# IMPORT EXTRACTION
# ============================================================

def extract_imports(lines):
    """
    Extract import statements appearing at the beginning
    of a Lean source file.

    Example:
        import Mathlib.Data.Nat.Basic
        import Mathlib.Tactic
    """

    imports = []

    for line in lines:
        stripped = line.strip()

        if not stripped:
            continue

        if stripped.startswith("--"):
            continue

        if stripped.startswith("import "):
            if stripped not in EXCLUDED_IMPORTS:
                imports.append(stripped)
        else:
            break

    return imports


# ============================================================
# NAMESPACE EXTRACTION
# ============================================================

def extract_namespace(lines):
    """
    Extract namespace declarations appearing before the
    first theorem.

    For example:

        namespace Logic_Prop

    or:

        namespace Algebra_group
    """

    namespace_lines = []

    for line in lines:
        stripped = line.strip()

        if stripped.startswith("theorem "):
            break

        if stripped.startswith("namespace "):
            namespace_lines.append(stripped)

    return namespace_lines


# ============================================================
# THEOREM EXTRACTION
# ============================================================

def extract_theorems(text):
    """
    Extract theorem declarations from a Lean source file.

    For every theorem, keep everything from:

        theorem <name>

    through the line ending with:

        := by

    The original proof is discarded.
    """

    lines = text.splitlines()

    theorem_starts = []

    for index, line in enumerate(lines):
        if re.match(r"^\s*theorem\s+", line):
            theorem_starts.append(index)

    theorems = []

    for theorem_index, start in enumerate(theorem_starts):

        if theorem_index + 1 < len(theorem_starts):
            end_limit = theorem_starts[theorem_index + 1]
        else:
            end_limit = len(lines)

        theorem_lines = lines[start:end_limit]

        declaration_end = None

        for index, line in enumerate(theorem_lines):

            if re.search(r":=\s*by\s*$", line.strip()):
                declaration_end = index
                break

        if declaration_end is None:
            raise RuntimeError(
                f"Could not find ':= by' for theorem "
                f"starting at source line {start + 1}."
            )

        declaration = "\n".join(
            theorem_lines[:declaration_end + 1]
        ).strip()

        # The theorem name is the token immediately after "theorem".
        match = re.match(
            r"^theorem\s+([^\s(:]+)",
            declaration
        )

        if not match:
            raise RuntimeError(
                "Could not determine theorem name from:\n\n"
                + declaration
            )

        theorem_name = match.group(1)

        theorems.append({
            "name": theorem_name,
            "declaration": declaration,
        })

    return theorems


# ============================================================
# FILE CONTENT GENERATION
# ============================================================

def build_file_content(
    imports,
    namespace_lines,
    declaration,
):
    """
    Construct the standalone theorem file.

    The original proof is replaced with:

        := by
          sorry
    """

    content = []

    # Imports
    content.extend(imports)

    content.append("")

    # Namespace
    for namespace in namespace_lines:
        content.append(namespace)

    if namespace_lines:
        content.append("")

    # Theorem declaration
    content.append(declaration)

    # Required placeholder proof
    content.append("  sorry")

    # Close namespace
    if namespace_lines:
        content.append("")

        for namespace in reversed(namespace_lines):
            namespace_name = namespace[len("namespace "):].strip()
            content.append(f"end {namespace_name}")

    content.append("")

    return "\n".join(content)


# ============================================================
# LEAN COMPILATION
# ============================================================

def run_lean(file_path):
    """
    Compile a Lean file using the outer project's Lake
    environment.

    lakefile.toml is located at PROJECT_ROOT.
    """

    result = subprocess.run(
        [
            "lake",
            "env",
            "lean",
            str(file_path),
        ],
        cwd=PROJECT_ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )

    return result.returncode == 0


# ============================================================
# IMPORT MINIMIZATION
# ============================================================

def find_necessary_imports(
    initial_imports,
    namespace_lines,
    declaration,
):
    """
    Determine a sufficient set of imports for one theorem.

    Process:

        1. Start with all imports from the source file.
        2. Verify that the theorem compiles.
        3. Try removing one import.
        4. Compile again.
        5. If compilation succeeds, permanently remove
           that import.
        6. Continue until no more imports can be removed.

    This gives a greedy minimal sufficient import set.
    """

    current_imports = list(initial_imports)

    # --------------------------------------------------------
    # First verify that the theorem works with all imports.
    # --------------------------------------------------------

    with tempfile.TemporaryDirectory(
        dir=PROJECT_ROOT
    ) as temp_dir:

        temp_dir = Path(temp_dir)
        test_file = temp_dir / "import_test.lean"

        test_file.write_text(
            build_file_content(
                current_imports,
                namespace_lines,
                declaration,
            ),
            encoding="utf-8",
        )

        if not run_lean(test_file):

            raise RuntimeError(
                "\nThe following theorem could not compile "
                "even with all source imports:\n\n"
                f"{declaration}\n\n"
                "Please inspect this theorem manually."
            )

    # --------------------------------------------------------
    # Try removing imports one at a time.
    # --------------------------------------------------------

    changed = True

    while changed:

        changed = False

        for import_statement in list(current_imports):

            candidate_imports = [
                imp
                for imp in current_imports
                if imp != import_statement
            ]

            with tempfile.TemporaryDirectory(
                dir=PROJECT_ROOT
            ) as temp_dir:

                temp_dir = Path(temp_dir)
                test_file = temp_dir / "import_test.lean"

                test_file.write_text(
                    build_file_content(
                        candidate_imports,
                        namespace_lines,
                        declaration,
                    ),
                    encoding="utf-8",
                )

                if run_lean(test_file):

                    current_imports = candidate_imports
                    changed = True

    return current_imports


# ============================================================
# PROCESS ONE DOMAIN
# ============================================================

def process_domain(domain, source_file):
    """
    Process one theorem source file.

    Domain:
        Nat
        Prop
        Group
    """

    print()
    print("=" * 70)
    print(f"PROCESSING {domain}")
    print("=" * 70)

    # --------------------------------------------------------
    # Check source file
    # --------------------------------------------------------

    if not source_file.exists():

        raise FileNotFoundError(
            f"Source file not found:\n{source_file}"
        )

    # --------------------------------------------------------
    # Read source file
    # --------------------------------------------------------

    text = source_file.read_text(
        encoding="utf-8"
    )

    lines = text.splitlines()

    # --------------------------------------------------------
    # Extract information
    # --------------------------------------------------------

    imports = extract_imports(lines)

    namespace_lines = extract_namespace(lines)

    theorems = extract_theorems(text)

    # --------------------------------------------------------
    # Verify theorem count
    # --------------------------------------------------------

    expected_count = EXPECTED_COUNTS[domain]

    if len(theorems) != expected_count:

        raise RuntimeError(
            f"{source_file.name}: expected "
            f"{expected_count} theorems, but found "
            f"{len(theorems)}."
        )

    # --------------------------------------------------------
    # Print summary
    # --------------------------------------------------------

    print(f"Source file : {source_file}")

    print(
        f"Theorems    : {len(theorems)}"
    )

    print(
        f"Imports     : {len(imports)}"
    )

    if namespace_lines:

        print(
            "Namespace   : "
            + ", ".join(namespace_lines)
        )

    else:

        print(
            "Namespace   : none"
        )

    # --------------------------------------------------------
    # Create output directory
    # --------------------------------------------------------

    output_dir = THEOREMS_DIR / domain

    output_dir.mkdir(
        parents=True,
        exist_ok=True
    )

    # --------------------------------------------------------
    # Remove old generated files in this domain.
    #
    # This does NOT touch Lists/.
    # --------------------------------------------------------

    for old_file in output_dir.glob("*.lean"):
        old_file.unlink()

    print(
        f"Output      : {output_dir}"
    )

    print()

    # --------------------------------------------------------
    # Generate theorem files
    # --------------------------------------------------------

    for number, theorem in enumerate(
        theorems,
        start=1
    ):

        theorem_name = theorem["name"]

        print(
            f"[{number:02d}/{len(theorems):02d}] "
            f"{theorem_name}"
        )

        # Find imports required by this theorem
        necessary_imports = find_necessary_imports(
            imports,
            namespace_lines,
            theorem["declaration"],
        )

        # Build final file
        file_content = build_file_content(
            necessary_imports,
            namespace_lines,
            theorem["declaration"],
        )

        # Actual theorem name is used as filename
        output_file = (
            output_dir
            / f"{theorem_name}.lean"
        )

        output_file.write_text(
            file_content,
            encoding="utf-8"
        )

        print(
            f"       imports kept: "
            f"{len(necessary_imports)}/"
            f"{len(imports)}"
        )

    print()

    print(
        f"Finished {domain}: "
        f"{len(theorems)} files created."
    )


# ============================================================
# MAIN
# ============================================================

def main():

    print("=" * 70)
    print("LEAN THEOREM FILE GENERATOR")
    print("=" * 70)

    print(
        f"Project root : {PROJECT_ROOT}"
    )

    print(
        f"Lean source  : {LEAN_SOURCE_DIR}"
    )

    print(
        f"Output       : {THEOREMS_DIR}"
    )

    print()

    # --------------------------------------------------------
    # Verify Lean/Lake environment
    # --------------------------------------------------------

    try:

        result = subprocess.run(
            ["lake", "--version"],
            cwd=PROJECT_ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )

        if result.returncode != 0:
            raise RuntimeError

    except Exception:

        raise RuntimeError(
            "\nCould not run 'lake'.\n"
            "Make sure this script is being used with "
            "the Lean project containing lakefile.toml."
        )

    # --------------------------------------------------------
    # Process all domains
    # --------------------------------------------------------

    total_created = 0

    for domain, source_file in SOURCE_FILES.items():

        process_domain(
            domain,
            source_file
        )

        total_created += EXPECTED_COUNTS[domain]

    # --------------------------------------------------------
    # Final summary
    # --------------------------------------------------------

    print()
    print("=" * 70)
    print("DONE")
    print("=" * 70)

    print(
        f"Total theorem files created: "
        f"{total_created}"
    )

    print()

    print(
        f"Nat   : {THEOREMS_DIR / 'Nat'}"
    )

    print(
        f"Prop  : {THEOREMS_DIR / 'Prop'}"
    )

    print(
        f"Group : {THEOREMS_DIR / 'Group'}"
    )

    print()

    print(
        "dataset.csv was NOT modified."
    )

    print("=" * 70)


if __name__ == "__main__":
    main()