#!/usr/bin/env python3
"""Pre-commit hook (advisory): warn when skill files exceed token/word targets. WARN tier -- always exits 0."""

import os
import sys

sys.path.insert(0, os.path.dirname(__file__))
from _utils import (
    find_repo_root, load_budgets, classify_file,
    count_body_words, estimate_tokens, get_budget_limits,
    WARN_THRESHOLD,
)


def check_file(filepath, repo_root, budgets):
    """Check a single file against its budget target. Returns warnings list."""
    warnings = []

    classification = classify_file(filepath, repo_root)
    if classification == "skip":
        return warnings

    rel_path = os.path.relpath(filepath, repo_root).replace("\\", "/")

    try:
        with open(filepath, "r", encoding="utf-8") as f:
            text = f.read()
    except (OSError, UnicodeDecodeError) as e:
        warnings.append(f"{rel_path}: could not read file: {e}")
        return warnings

    word_count = len(text.split())
    token_estimate = estimate_tokens(word_count)

    max_words, max_tokens = get_budget_limits(rel_path, classification, budgets)
    if max_words is None:
        return warnings

    word_ratio = word_count / max_words if max_words > 0 else 0

    if word_ratio > 1.0:
        overage = word_count - max_words
        warnings.append(
            f"WARNING: {rel_path} [{classification}]: {word_count} words "
            f"(~{token_estimate} tokens) exceeds target of {max_words} words "
            f"by {overage} words ({word_ratio:.0%}). "
            f"Refactor: extract checklists, kill prose, deduplicate output specs."
        )
    elif word_ratio > WARN_THRESHOLD:
        headroom = max_words - word_count
        warnings.append(
            f"INFO: {rel_path} [{classification}]: {word_count} words "
            f"(~{token_estimate} tokens) at {word_ratio:.0%} of {max_words} word target "
            f"-- {headroom} words of headroom remaining."
        )

    return warnings


def main():
    if len(sys.argv) < 2:
        sys.exit(0)

    repo_root = find_repo_root()
    budgets = load_budgets(repo_root)

    all_warnings = []

    for filepath in sys.argv[1:]:
        filepath = os.path.abspath(filepath)
        file_warnings = check_file(filepath, repo_root, budgets)
        all_warnings.extend(file_warnings)

    for w in all_warnings:
        print(w, file=sys.stderr)

    if all_warnings:
        print(
            "\nTo document a target override, add an entry to "
            "pipeline/config/budgets.json with your rationale.",
            file=sys.stderr,
        )

    # Advisory only -- always exit 0
    sys.exit(0)


if __name__ == "__main__":
    main()
