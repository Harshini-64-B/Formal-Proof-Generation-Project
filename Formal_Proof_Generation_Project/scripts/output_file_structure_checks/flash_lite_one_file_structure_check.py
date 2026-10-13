from pathlib import Path
import re

# Gemma model output folder
OUTPUT_DIR = Path("outputs/gemini_flash_lite_one")

def check_file(file_path):
    text = file_path.read_text(encoding="utf-8", errors="replace")
    stripped = text.strip()

    issues = []

    # 1. Empty file
    if not stripped:
        issues.append("EMPTY FILE")
        return issues

    # 2. Markdown code fences
    if "```" in text:
        issues.append("CONTAINS MARKDOWN CODE FENCE")

    # 3. Check for theorem declaration
    theorem_matches = re.findall(r"\btheorem\s+\w+", text)

    if not theorem_matches:
        issues.append("NO THEOREM DECLARATION")

    # 4. Multiple theorem declarations
    if len(theorem_matches) > 1:
        issues.append(f"MULTIPLE THEOREMS ({len(theorem_matches)})")

    # 5. Check theorem structure: theorem ... := by
    if theorem_matches:
        if not re.search(r"\btheorem\s+\w+.*?:=\s*by\b", text, re.DOTALL):
            issues.append(
                "INVALID THEOREM STRUCTURE (expected theorem ... := by)"
            )

    # 6. Check for sorry
    if re.search(r"\bsorry\b", text):
        issues.append("CONTAINS SORRY")

    # 7. Plain-text/explanatory text before theorem
    theorem_pos = re.search(r"\btheorem\s+", text)

    if theorem_pos:
        before = text[:theorem_pos.start()].strip()

        if before:
            issues.append("TEXT BEFORE THEOREM")

    # 8. Look for obvious explanatory text
    suspicious_phrases = [
        "Here is",
        "Here’s",
        "Here is the",
        "Explanation:",
        "The proof",
        "This proof",
        "Note:",
        "Alternatively",
        "Alternative proof",
        "The above",
        "This theorem",
    ]

    for phrase in suspicious_phrases:
        if phrase.lower() in text.lower():
            issues.append(
                f"CONTAINS POSSIBLE EXPLANATORY TEXT: '{phrase}'"
            )
            break

    # 9. Namespace-related content
    namespace_patterns = [
        r"\bnamespace\b",
        r"\bend\s+(Logic_Prop|Algebra_Group)\b",
        r"\bLogic_Prop\b",
        r"\bAlgebra_Group\b",
    ]

    if any(re.search(pattern, text) for pattern in namespace_patterns):
        issues.append("CONTAINS NAMESPACE-RELATED CONTENT")

    # 10. Check that it actually starts with theorem
    if not re.match(r"^\s*theorem\s+", text):
        issues.append("CONTENT DOES NOT START WITH THEOREM")

    return issues

# ---------------------------------------------------------
# Scan all Lean files
# ---------------------------------------------------------

if not OUTPUT_DIR.exists():
    print(f"ERROR: Folder not found:\n{OUTPUT_DIR}")
    exit()

lean_files = sorted(OUTPUT_DIR.rglob("*.lean"))

print(f"Folder: {OUTPUT_DIR}")
print(f"Lean files found: {len(lean_files)}")
print("=" * 70)

anomaly_count = 0

for file_path in lean_files:
    issues = check_file(file_path)

    if issues:
        anomaly_count += 1

        print(f"\n❌ {file_path.name}")
        for issue in issues:
            print(f"   - {issue}")

print("\n" + "=" * 70)

if anomaly_count == 0:
    print("✅ No obvious content anomalies found.")
else:
    print(f"⚠️ {anomaly_count} file(s) have potential anomalies.")

print(f"Total files checked: {len(lean_files)}")