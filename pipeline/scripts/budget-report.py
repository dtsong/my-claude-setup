#!/usr/bin/env python3
"""budget-report.py — Generate a summary table of all files vs their token budgets."""

import json
import math
import os
import sys

TOKEN_RATIO = 1.33


def find_repo_root(start):
    d = os.path.abspath(start)
    while True:
        if os.path.isdir(os.path.join(d, "pipeline", "config")):
            return d
        parent = os.path.dirname(d)
        if parent == d:
            return None
        d = parent


def load_budgets(repo_root):
    config_path = os.path.join(repo_root, "pipeline", "config", "budgets.json")
    with open(config_path, "r") as f:
        return json.load(f)


def classify_file(filepath, repo_root):
    """Classify a file as coordinator, specialist, reference, standalone, or skip."""
    rel = os.path.relpath(filepath, repo_root).replace("\\", "/")
    parts = rel.split("/")
    basename = os.path.basename(rel)

    if "references" in parts or "shared-references" in parts:
        if basename.endswith(".md"):
            return "reference"

    if basename != "SKILL.md":
        return "skip"

    skill_dir = os.path.dirname(filepath)

    if os.path.isdir(os.path.join(skill_dir, "skills")):
        return "coordinator"

    if "skills" in parts:
        return "specialist"

    return "standalone"


def get_budget_limits(rel_path, classification, budgets):
    overrides = budgets.get("overrides", {})
    normalized = rel_path.replace("\\", "/")

    if normalized in overrides:
        override = overrides[normalized]
        word_key = classification + "_max_words"
        token_key = classification + "_max_tokens"
        if word_key in override:
            return override[word_key], override[token_key]

    word_key = classification + "_max_words"
    token_key = classification + "_max_tokens"
    return budgets.get(word_key), budgets.get(token_key)


def find_all_files(repo_root):
    """Find all SKILL.md, references/*.md, and shared-references/**/*.md files."""
    results = []

    for dirpath, dirnames, filenames in os.walk(repo_root):
        dirnames[:] = [d for d in dirnames if d not in (".git", "node_modules")]
        rel_dir = os.path.relpath(dirpath, repo_root)

        # Skip pipeline directory itself (but not its contents we need)
        if rel_dir.startswith("pipeline") and "shared-references" not in rel_dir:
            continue

        for fn in filenames:
            filepath = os.path.join(dirpath, fn)
            rel = os.path.relpath(filepath, repo_root).replace("\\", "/")

            # Include SKILL.md files
            if fn == "SKILL.md":
                results.append(filepath)
            # Include reference files
            elif fn.endswith(".md") and ("references/" in rel or "shared-references/" in rel):
                results.append(filepath)

    return sorted(results)


def generate_report(files, repo_root, budgets):
    rows = []

    for filepath in files:
        rel_path = os.path.relpath(filepath, repo_root).replace("\\", "/")
        classification = classify_file(filepath, repo_root)

        if classification == "skip":
            continue

        try:
            with open(filepath, "r", encoding="utf-8") as f:
                text = f.read()
        except (OSError, UnicodeDecodeError):
            rows.append({
                "path": rel_path,
                "words": 0,
                "tokens": 0,
                "limit": "N/A",
                "status": "ERROR",
                "headroom": "N/A",
                "classification": classification,
            })
            continue

        words = len(text.split())
        tokens = int(math.ceil(words * TOKEN_RATIO))
        max_words, max_tokens = get_budget_limits(rel_path, classification, budgets)

        if max_tokens is None:
            rows.append({
                "path": rel_path,
                "words": words,
                "tokens": tokens,
                "limit": "N/A",
                "status": "SKIP",
                "headroom": "N/A",
                "classification": classification,
            })
            continue

        ratio = tokens / max_tokens if max_tokens > 0 else 0
        headroom = max_tokens - tokens

        if ratio > 1.0:
            status = "OVER"
        elif ratio > 0.90:
            status = "WARN"
        else:
            status = "OK"

        rows.append({
            "path": rel_path,
            "words": words,
            "tokens": tokens,
            "limit": max_tokens,
            "status": status,
            "headroom": headroom,
            "classification": classification,
        })

    # Generate markdown table
    lines = [
        "# Token Budget Report",
        "",
        "| File | Type | Words | ~Tokens | Limit | Status | Headroom |",
        "|------|------|------:|--------:|------:|--------|--------:|",
    ]

    ok_count = 0
    warn_count = 0
    over_count = 0

    for row in rows:
        limit_str = str(row["limit"]) if isinstance(row["limit"], int) else row["limit"]
        headroom_str = str(row["headroom"]) if isinstance(row["headroom"], int) else row["headroom"]
        lines.append(
            f"| {row['path']} | {row['classification']} | {row['words']} | "
            f"{row['tokens']} | {limit_str} | {row['status']} | {headroom_str} |"
        )
        if row["status"] == "OK":
            ok_count += 1
        elif row["status"] == "WARN":
            warn_count += 1
        elif row["status"] == "OVER":
            over_count += 1

    lines.append("")
    lines.append(f"**Summary:** {ok_count} OK, {warn_count} WARN, {over_count} OVER ({len(rows)} files total)")
    lines.append("")

    return "\n".join(lines)


def main():
    script_dir = os.path.dirname(os.path.abspath(__file__))
    repo_root = find_repo_root(script_dir)
    if repo_root is None:
        print("ERROR: could not find repo root", file=sys.stderr)
        sys.exit(1)

    budgets = load_budgets(repo_root)

    if len(sys.argv) > 1:
        files = [os.path.abspath(f) for f in sys.argv[1:]]
    else:
        files = find_all_files(repo_root)

    report = generate_report(files, repo_root, budgets)
    print(report)


if __name__ == "__main__":
    main()
