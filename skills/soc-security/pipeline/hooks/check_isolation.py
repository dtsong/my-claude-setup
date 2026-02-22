#!/usr/bin/env python3
"""Pre-commit hook: ensure specialist skills don't cross-reference siblings. HARD tier."""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(__file__))
from _utils import find_repo_root, classify_file, is_excluded


def find_sibling_specialists(filepath, repo_root):
    """Find sibling specialist directories for a specialist skill."""
    parts = filepath.replace("\\", "/").split("/")

    # Find the "skills" component in the path
    skills_idx = None
    for i, part in enumerate(parts):
        if part == "skills":
            skills_idx = i
            break

    if skills_idx is None:
        return set(), None

    # The specialist name is the directory right after skills/
    if skills_idx + 1 >= len(parts) - 1:
        return set(), None

    specialist_name = parts[skills_idx + 1]
    skills_parent = "/".join(parts[:skills_idx + 1])

    siblings = set()
    try:
        for entry in os.listdir(skills_parent):
            entry_path = os.path.join(skills_parent, entry)
            if os.path.isdir(entry_path) and entry != specialist_name:
                siblings.add(entry)
    except OSError:
        return set(), specialist_name

    return siblings, specialist_name


def check_file(filepath, repo_root):
    """Check a specialist SKILL.md for sibling cross-references.

    Returns (errors, warnings).
    """
    errors = []
    warnings = []

    if is_excluded(filepath, repo_root):
        return errors, warnings

    file_type = classify_file(filepath, repo_root)
    if file_type != "specialist":
        return errors, warnings

    rel_path = os.path.relpath(filepath, repo_root)
    siblings, specialist_name = find_sibling_specialists(filepath, repo_root)

    if not siblings:
        return errors, warnings

    try:
        with open(filepath, "r", encoding="utf-8") as f:
            lines = f.readlines()
    except (OSError, UnicodeDecodeError) as e:
        errors.append(f"{rel_path}: could not read file: {e}")
        return errors, warnings

    # Build patterns to detect cross-references
    for line_num, line in enumerate(lines, start=1):
        for sibling in siblings:
            # Match patterns like ../sibling-name/SKILL.md or ../sibling-name/references/
            pattern = re.compile(
                r"\.\./?" + re.escape(sibling) + r"(/|\.md|/SKILL\.md|/references/)"
            )
            # Also match skills/sibling-name references
            alt_patterns = [
                f"{sibling}/SKILL.md",
                f"{sibling}/references/",
                f"skills/{sibling}",
            ]
            if pattern.search(line):
                errors.append(
                    f"{rel_path}:{line_num}: cross-reference to sibling "
                    f"specialist '{sibling}' violates isolation rule "
                    f"(source: {specialist_name}, target: {sibling}). "
                    f"Use handoff protocol instead."
                )
            else:
                for alt in alt_patterns:
                    if alt in line:
                        errors.append(
                            f"{rel_path}:{line_num}: cross-reference to sibling "
                            f"specialist '{sibling}' violates isolation rule "
                            f"(source: {specialist_name}, target: {sibling}). "
                            f"Use handoff protocol instead."
                        )
                        break

    return errors, warnings


def main():
    if len(sys.argv) < 2:
        sys.exit(0)

    repo_root = find_repo_root()
    all_errors = []
    all_warnings = []

    for filepath in sys.argv[1:]:
        filepath = os.path.abspath(filepath)
        errors, warnings = check_file(filepath, repo_root)
        all_errors.extend(errors)
        all_warnings.extend(warnings)

    for w in all_warnings:
        print(f"WARNING: {w}", file=sys.stderr)

    for e in all_errors:
        print(f"FAIL: {e}", file=sys.stderr)

    sys.exit(1 if all_errors else 0)


if __name__ == "__main__":
    main()
