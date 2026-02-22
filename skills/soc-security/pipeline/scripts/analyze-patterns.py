#!/usr/bin/env python3
"""analyze-patterns.py — Detect prohibited prose patterns, output duplication, and long checklists."""

import os
import re
import sys

# Prohibited prose patterns from the governance spec
PROHIBITED_PATTERNS = [
    (r"\bIt is important to\b", "Explanatory prose: 'It is important to...'"),
    (r"\bYou should\b", "Hedging: 'You should...'"),
    (r"\bThis is because\b", "Explanation: 'This is because...'"),
    (r"\b[Bb]asically\b", "Filler: 'Basically'"),
    (r"\b[Ee]ssentially\b", "Filler: 'Essentially'"),
    (r"\bIn order to\b", "Verbose: 'In order to' (use 'to')"),
    (r"\bKeep in mind that\b", "Meta-instruction: 'Keep in mind that...'"),
    (r"\bLet's\b", "Conversational: 'Let's'"),
    (r"\b[Ww]e can\b", "Conversational: 'we can'"),
]

# Compile patterns once
COMPILED_PATTERNS = [(re.compile(p), desc) for p, desc in PROHIBITED_PATTERNS]


def find_skill_files(repo_root):
    """Find all SKILL.md files in the repo."""
    results = []
    for dirpath, dirnames, filenames in os.walk(repo_root):
        # Skip non-skill directories
        dirnames[:] = [d for d in dirnames if d not in (".git", "node_modules", "pipeline")]
        if "SKILL.md" in filenames:
            results.append(os.path.join(dirpath, "SKILL.md"))
    return sorted(results)


def check_prose_patterns(filepath, content):
    """Check for prohibited prose patterns. Returns list of (line_num, pattern_desc)."""
    findings = []
    in_code_block = False
    for i, line in enumerate(content.splitlines(), 1):
        stripped = line.strip()
        if stripped.startswith("```"):
            in_code_block = not in_code_block
            continue
        if in_code_block:
            continue
        # Skip frontmatter
        if stripped == "---" and i <= 5:
            continue
        for pattern, desc in COMPILED_PATTERNS:
            if pattern.search(line):
                findings.append((i, desc, line.strip()))
    return findings


def check_output_duplication(filepath, content):
    """Detect schema + example duplication for the same output format."""
    findings = []
    lines = content.splitlines()
    has_schema_section = False
    has_example_section = False
    in_output_section = False

    for i, line in enumerate(lines, 1):
        stripped = line.strip().lower()
        # Detect output-related headers
        if stripped.startswith("#") and any(
            kw in stripped for kw in ("output", "response", "result")
        ):
            in_output_section = True
            has_schema_section = False
            has_example_section = False
            continue

        if in_output_section:
            # New top-level section ends the output section
            if stripped.startswith("# ") and not stripped.startswith("## "):
                in_output_section = False
                continue

            if any(kw in stripped for kw in ("schema", "structure", "fields")):
                has_schema_section = True
            if any(kw in stripped for kw in ("example", "sample")):
                has_example_section = True

            if has_schema_section and has_example_section:
                findings.append(
                    (i, "Output format has both schema description and example (keep only example)")
                )
                in_output_section = False

    return findings


def check_long_checklists(filepath, content):
    """Detect inline checklists with >10 items."""
    findings = []
    lines = content.splitlines()
    run_start = None
    run_count = 0

    for i, line in enumerate(lines, 1):
        stripped = line.strip()
        is_checklist = stripped.startswith("- [ ]") or stripped.startswith("- [x]")
        is_list_item = stripped.startswith("- ") and not is_checklist

        if is_checklist or is_list_item:
            if run_start is None:
                run_start = i
            run_count += 1
        else:
            if run_count > 10:
                findings.append(
                    (run_start, f"Inline checklist with {run_count} items (>10 — extract to reference file)")
                )
            run_start = None
            run_count = 0

    # Handle trailing run
    if run_count > 10 and run_start is not None:
        findings.append(
            (run_start, f"Inline checklist with {run_count} items (>10 — extract to reference file)")
        )

    return findings


def analyze_file(filepath, repo_root):
    """Run all analyses on a single file. Returns dict of findings."""
    rel_path = os.path.relpath(filepath, repo_root)
    try:
        with open(filepath, "r", encoding="utf-8") as f:
            content = f.read()
    except (OSError, UnicodeDecodeError) as e:
        return {"path": rel_path, "error": str(e)}

    return {
        "path": rel_path,
        "prose": check_prose_patterns(filepath, content),
        "duplication": check_output_duplication(filepath, content),
        "checklists": check_long_checklists(filepath, content),
    }


def generate_report(results):
    """Generate a markdown report from analysis results."""
    lines = ["# Pattern Analysis Report", ""]

    total_prose = 0
    total_duplication = 0
    total_checklists = 0

    for result in results:
        if "error" in result:
            lines.append(f"## {result['path']}")
            lines.append(f"Error reading file: {result['error']}")
            lines.append("")
            continue

        prose = result["prose"]
        duplication = result["duplication"]
        checklists = result["checklists"]

        if not prose and not duplication and not checklists:
            continue

        total_prose += len(prose)
        total_duplication += len(duplication)
        total_checklists += len(checklists)

        lines.append(f"## {result['path']}")
        lines.append("")

        if prose:
            lines.append("### Prohibited Prose Patterns")
            lines.append("")
            lines.append("| Line | Pattern | Context |")
            lines.append("|------|---------|---------|")
            for line_num, desc, context in prose:
                escaped = context.replace("|", "\\|")[:80]
                lines.append(f"| {line_num} | {desc} | `{escaped}` |")
            lines.append("")

        if duplication:
            lines.append("### Output Format Duplication")
            lines.append("")
            for line_num, desc in duplication:
                lines.append(f"- Line {line_num}: {desc}")
            lines.append("")

        if checklists:
            lines.append("### Long Inline Checklists")
            lines.append("")
            for line_num, desc in checklists:
                lines.append(f"- Line {line_num}: {desc}")
            lines.append("")

    # Summary
    lines.insert(2, "## Summary")
    lines.insert(3, "")
    lines.insert(4, f"| Category | Findings |")
    lines.insert(5, f"|----------|----------|")
    lines.insert(6, f"| Prohibited prose patterns | {total_prose} |")
    lines.insert(7, f"| Output format duplication | {total_duplication} |")
    lines.insert(8, f"| Long inline checklists | {total_checklists} |")
    lines.insert(9, "")

    return "\n".join(lines)


def main():
    script_dir = os.path.dirname(os.path.abspath(__file__))
    repo_root = os.path.abspath(os.path.join(script_dir, "..", ".."))

    if len(sys.argv) > 1:
        files = [os.path.abspath(f) for f in sys.argv[1:]]
    else:
        files = find_skill_files(repo_root)

    if not files:
        print("# Pattern Analysis Report\n\nNo SKILL.md files found.")
        return

    results = [analyze_file(f, repo_root) for f in files]
    report = generate_report(results)
    print(report)


if __name__ == "__main__":
    main()
