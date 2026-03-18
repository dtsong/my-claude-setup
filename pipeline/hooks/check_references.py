#!/usr/bin/env python3
"""Pre-commit hook: verify referenced files exist relative to SKILL.md or repo root. HARD tier."""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(__file__))
from _utils import find_repo_root, is_excluded

# Patterns to match file references in SKILL.md:
# 1. Backtick-wrapped paths: `references/foo.md`, `path/to/dir/`
# 2. Table rows with file paths: | references/foo.md | or | `references/foo.md` |
# 3. Bare paths starting with known prefixes
BACKTICK_PATH_RE = re.compile(r"`([^`]+(?:\.md|/))`")
TABLE_PATH_RE = re.compile(r"\|\s*`?([^|`\s]+(?:\.md|/))`?\s*\|")
BARE_PATH_RE = re.compile(r"(?:^|\s)((?:references|shared-references)/[^\s)>\]]+(?:\.md|/))")


def find_references(text):
    """Find all file path references in text. Returns list of (line_num, path)."""
    refs = []
    seen = set()

    for line_num, line in enumerate(text.split("\n"), start=1):
        # Backtick-wrapped paths
        for match in BACKTICK_PATH_RE.finditer(line):
            path = match.group(1)
            if _looks_like_file_path(path):
                key = (line_num, path)
                if key not in seen:
                    seen.add(key)
                    refs.append((line_num, path))

        # Table entries
        for match in TABLE_PATH_RE.finditer(line):
            path = match.group(1)
            if _looks_like_file_path(path):
                key = (line_num, path)
                if key not in seen:
                    seen.add(key)
                    refs.append((line_num, path))

        # Bare paths starting with references/ or shared-references/
        for match in BARE_PATH_RE.finditer(line):
            path = match.group(1)
            key = (line_num, path)
            if key not in seen:
                seen.add(key)
                refs.append((line_num, path))

    return refs


def _looks_like_file_path(s):
    """Heuristic: does this string look like a relative file path?"""
    # Must contain a / (directory separator)
    if "/" not in s:
        return False
    # Filter out URLs
    if s.startswith("http://") or s.startswith("https://"):
        return False
    # Filter out things that are clearly not paths
    if " " in s:
        return False
    return True


def check_file(filepath, repo_root):
    """Check a single SKILL.md for broken references. Returns (errors, warnings)."""
    errors = []
    warnings = []

    if is_excluded(filepath, repo_root):
        return errors, warnings

    basename = os.path.basename(filepath)
    if basename != "SKILL.md":
        return errors, warnings

    rel_path = os.path.relpath(filepath, repo_root)

    try:
        with open(filepath, "r", encoding="utf-8") as f:
            text = f.read()
    except (OSError, UnicodeDecodeError) as e:
        errors.append(f"{rel_path}: could not read file: {e}")
        return errors, warnings

    skill_dir = os.path.dirname(filepath)
    refs = find_references(text)

    # Build search paths: skill dir, repo root, shared-references dirs
    search_bases = [skill_dir]
    if repo_root:
        search_bases.append(repo_root)
        # Add shared-references subdirectories as search bases
        shared_refs = os.path.join(repo_root, "shared-references")
        if os.path.isdir(shared_refs):
            for entry in os.listdir(shared_refs):
                entry_path = os.path.join(shared_refs, entry)
                if os.path.isdir(entry_path):
                    search_bases.append(entry_path)

    for line_num, ref_path in refs:
        found = False
        for base in search_bases:
            resolved = os.path.normpath(os.path.join(base, ref_path))
            if os.path.exists(resolved):
                found = True
                break

        if not found:
            errors.append(
                f"{rel_path}:{line_num}: broken reference '{ref_path}'"
            )

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
