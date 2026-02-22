#!/usr/bin/env python3
"""context-load-analysis.py — Analyze context load per skill and simulate worst-case scenarios."""

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


def word_count(filepath):
    try:
        with open(filepath, "r", encoding="utf-8") as f:
            return len(f.read().split())
    except (OSError, UnicodeDecodeError):
        return 0


def token_estimate(words):
    return int(math.ceil(words * TOKEN_RATIO))


def find_skill_dirs(repo_root):
    """Find all *-skill/ directories."""
    results = []
    for entry in sorted(os.listdir(repo_root)):
        if entry.endswith("-skill") and os.path.isdir(os.path.join(repo_root, entry)):
            results.append(os.path.join(repo_root, entry))
    return results


def find_md_files(directory):
    """Find all .md files in a directory tree."""
    results = []
    for dirpath, dirnames, filenames in os.walk(directory):
        dirnames[:] = [d for d in dirnames if d not in (".git", "node_modules", "eval-cases")]
        for fn in sorted(filenames):
            if fn.endswith(".md"):
                results.append(os.path.join(dirpath, fn))
    return results


def analyze_standalone(skill_dir, repo_root):
    """Analyze a standalone skill's context load."""
    skill_name = os.path.basename(skill_dir)
    skill_md = os.path.join(skill_dir, "SKILL.md")

    result = {
        "name": skill_name,
        "type": "standalone",
        "skill_md": {"words": 0, "tokens": 0},
        "references": [],
        "total_worst_case": 0,
    }

    if os.path.isfile(skill_md):
        words = word_count(skill_md)
        result["skill_md"] = {"words": words, "tokens": token_estimate(words)}

    # Analyze reference files
    refs_dir = os.path.join(skill_dir, "references")
    if os.path.isdir(refs_dir):
        for ref_file in find_md_files(refs_dir):
            rel_path = os.path.relpath(ref_file, repo_root)
            words = word_count(ref_file)
            tokens = token_estimate(words)
            result["references"].append({
                "path": rel_path,
                "words": words,
                "tokens": tokens,
            })

    # Worst case: SKILL.md + all references loaded simultaneously
    total = result["skill_md"]["tokens"]
    for ref in result["references"]:
        total += ref["tokens"]
    result["total_worst_case"] = total

    return result


def analyze_suite(skill_dir, repo_root):
    """Analyze a suite skill's context load."""
    skill_name = os.path.basename(skill_dir)
    coordinator_md = os.path.join(skill_dir, "SKILL.md")

    result = {
        "name": skill_name,
        "type": "suite",
        "coordinator": {"words": 0, "tokens": 0},
        "specialists": [],
        "worst_case_specialist": None,
        "total_worst_case": 0,
    }

    if os.path.isfile(coordinator_md):
        words = word_count(coordinator_md)
        result["coordinator"] = {"words": words, "tokens": token_estimate(words)}

    # Analyze each specialist
    skills_dir = os.path.join(skill_dir, "skills")
    if os.path.isdir(skills_dir):
        for spec_entry in sorted(os.listdir(skills_dir)):
            spec_dir = os.path.join(skills_dir, spec_entry)
            if not os.path.isdir(spec_dir):
                continue

            spec_md = os.path.join(spec_dir, "SKILL.md")
            spec_data = {
                "name": spec_entry,
                "skill_md": {"words": 0, "tokens": 0},
                "references": [],
                "total": 0,
            }

            if os.path.isfile(spec_md):
                words = word_count(spec_md)
                spec_data["skill_md"] = {"words": words, "tokens": token_estimate(words)}

            refs_dir = os.path.join(spec_dir, "references")
            if os.path.isdir(refs_dir):
                for ref_file in find_md_files(refs_dir):
                    rel_path = os.path.relpath(ref_file, repo_root)
                    words = word_count(ref_file)
                    tokens = token_estimate(words)
                    spec_data["references"].append({
                        "path": rel_path,
                        "words": words,
                        "tokens": tokens,
                    })

            spec_total = spec_data["skill_md"]["tokens"]
            for ref in spec_data["references"]:
                spec_total += ref["tokens"]
            spec_data["total"] = spec_total

            result["specialists"].append(spec_data)

    # Worst case: coordinator + largest specialist (with all its refs)
    largest_spec_total = 0
    largest_spec_name = None
    for spec in result["specialists"]:
        if spec["total"] > largest_spec_total:
            largest_spec_total = spec["total"]
            largest_spec_name = spec["name"]

    result["worst_case_specialist"] = largest_spec_name
    result["total_worst_case"] = result["coordinator"]["tokens"] + largest_spec_total

    return result


def generate_report(analyses, budgets):
    max_simultaneous = budgets.get("max_simultaneous_tokens", 5000)
    lines = [
        "# Context Load Analysis",
        "",
        f"Maximum simultaneous context load budget: **{max_simultaneous} tokens**",
        "",
        "## Per-Skill Breakdown",
        "",
        "| Skill | Type | SKILL.md | Refs | Worst Case | Budget | Status |",
        "|-------|------|----------|------|------------|--------|--------|",
    ]

    for a in analyses:
        skill_tokens = 0
        ref_tokens = 0

        if a["type"] == "standalone":
            skill_tokens = a["skill_md"]["tokens"]
            ref_tokens = sum(r["tokens"] for r in a["references"])
        else:
            skill_tokens = a["coordinator"]["tokens"]
            # Largest specialist
            for spec in a["specialists"]:
                spec_total = spec["skill_md"]["tokens"] + sum(r["tokens"] for r in spec["references"])
                if spec_total > ref_tokens:
                    ref_tokens = spec_total

        worst = a["total_worst_case"]
        status = "OK" if worst <= max_simultaneous else "OVER"
        lines.append(
            f"| {a['name']} | {a['type']} | {skill_tokens} | {ref_tokens} | "
            f"{worst} | {max_simultaneous} | {status} |"
        )

    lines.append("")

    # Detailed breakdown
    lines.append("## Detailed Breakdown")
    lines.append("")

    for a in analyses:
        lines.append(f"### {a['name']} ({a['type']})")
        lines.append("")

        if a["type"] == "standalone":
            lines.append(f"- SKILL.md: {a['skill_md']['words']} words / ~{a['skill_md']['tokens']} tokens")
            if a["references"]:
                lines.append("- References:")
                for ref in a["references"]:
                    lines.append(f"  - {ref['path']}: {ref['words']} words / ~{ref['tokens']} tokens")
            lines.append(f"- **Worst case (all loaded): ~{a['total_worst_case']} tokens**")
        else:
            lines.append(f"- Coordinator: {a['coordinator']['words']} words / ~{a['coordinator']['tokens']} tokens")
            if a["specialists"]:
                lines.append("- Specialists:")
                for spec in a["specialists"]:
                    lines.append(f"  - {spec['name']}: {spec['skill_md']['words']} words / ~{spec['skill_md']['tokens']} tokens")
                    for ref in spec["references"]:
                        lines.append(f"    - {ref['path']}: {ref['words']} words / ~{ref['tokens']} tokens")
                    lines.append(f"    - Subtotal: ~{spec['total']} tokens")
            if a["worst_case_specialist"]:
                lines.append(f"- **Worst case (coordinator + {a['worst_case_specialist']}): ~{a['total_worst_case']} tokens**")

        lines.append("")

    return "\n".join(lines)


def main():
    script_dir = os.path.dirname(os.path.abspath(__file__))
    repo_root = find_repo_root(script_dir)
    if repo_root is None:
        print("ERROR: could not find repo root", file=sys.stderr)
        sys.exit(1)

    budgets = load_budgets(repo_root)
    skill_dirs = find_skill_dirs(repo_root)

    analyses = []
    for skill_dir in skill_dirs:
        # Determine if suite or standalone
        if os.path.isdir(os.path.join(skill_dir, "skills")):
            analyses.append(analyze_suite(skill_dir, repo_root))
        else:
            analyses.append(analyze_standalone(skill_dir, repo_root))

    report = generate_report(analyses, budgets)
    print(report)


if __name__ == "__main__":
    main()
