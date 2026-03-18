#!/usr/bin/env python3
"""Pre-commit hook (advisory): flag prohibited prose patterns in procedure sections. WARN tier -- always exits 0."""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(__file__))
from _utils import find_repo_root, is_excluded

PROHIBITED_PATTERNS = [
    (r"it is important to", "state the action directly"),
    (r"it's important to", "state the action directly"),
    (r"you should", "use imperative: do X"),
    (r"you may want to", "use imperative: do X"),
    (r"you might want to", "use imperative: do X"),
    (r"this is because", "remove or convert to Note:"),
    (r"the reason for this", "remove or convert to Note:"),
    (r"basically", "remove filler"),
    (r"essentially", "remove filler"),
    (r"fundamentally", "remove filler"),
    (r"in other words", "remove filler"),
    (r"in order to", "replace with 'to'"),
    (r"keep in mind", "inline as Note: or remove"),
    (r"please note that", "inline as Note: or remove"),
    (r"let's", "use imperative"),
    (r"we can", "use imperative"),
    (r"we should", "use imperative"),
    (r"feel free to", "use imperative"),
    (r"don't hesitate to", "use imperative"),
]

# Sections to exclude from checking (non-procedure content where prose is acceptable)
EXCLUDED_SECTIONS = {"purpose", "context", "background", "notes", "description",
                     "overview", "when to use", "don't use"}


def find_procedure_sections(text):
    """Find line ranges that are inside procedure sections (up to next ##).

    Returns (lines_list, [(start, end), ...]).
    """
    lines = text.split("\n")
    ranges = []
    in_procedure = False
    start = None

    for i, line in enumerate(lines):
        stripped = line.strip()
        if re.match(r"^##\s+", stripped):
            section_name = re.sub(r"^##\s+", "", stripped).strip().lower()
            if in_procedure:
                ranges.append((start, i))
                in_procedure = False
            if "procedure" in section_name and section_name not in EXCLUDED_SECTIONS:
                in_procedure = True
                start = i + 1  # start after the heading line

    if in_procedure:
        ranges.append((start, len(lines)))

    return lines, ranges


def check_file(filepath, repo_root):
    """Check a SKILL.md for prohibited prose in procedure sections. Returns warnings."""
    warnings = []

    if is_excluded(filepath, repo_root):
        return warnings

    basename = os.path.basename(filepath)
    if basename != "SKILL.md":
        return warnings

    rel_path = os.path.relpath(filepath, repo_root)

    try:
        with open(filepath, "r", encoding="utf-8") as f:
            text = f.read()
    except (OSError, UnicodeDecodeError):
        return warnings

    lines, ranges = find_procedure_sections(text)
    if not ranges:
        return warnings

    compiled = [(p, re.compile(p, re.IGNORECASE), s) for p, s in PROHIBITED_PATTERNS]

    for start, end in ranges:
        for line_idx in range(start, min(end, len(lines))):
            line = lines[line_idx]
            for pattern_str, pattern_re, suggestion in compiled:
                if pattern_re.search(line):
                    warnings.append(
                        f"{rel_path}:{line_idx + 1}: prohibited prose "
                        f"pattern '{pattern_str}' found -> {suggestion}"
                    )

    return warnings


def main():
    if len(sys.argv) < 2:
        sys.exit(0)

    repo_root = find_repo_root()
    all_warnings = []

    for filepath in sys.argv[1:]:
        filepath = os.path.abspath(filepath)
        warnings = check_file(filepath, repo_root)
        all_warnings.extend(warnings)

    for w in all_warnings:
        print(f"WARNING: {w}", file=sys.stderr)

    # Advisory only -- always exit 0
    sys.exit(0)


if __name__ == "__main__":
    main()
