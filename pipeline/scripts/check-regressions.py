#!/usr/bin/env python3
"""check-regressions.py — Compare eval results against stored baselines."""

import json
import os
import sys


def find_repo_root(start):
    d = os.path.abspath(start)
    while True:
        if os.path.isdir(os.path.join(d, "pipeline", "config")):
            return d
        parent = os.path.dirname(d)
        if parent == d:
            return None
        d = parent


def find_skill_dirs(repo_root):
    results = []
    for entry in sorted(os.listdir(repo_root)):
        if entry.endswith("-skill") and os.path.isdir(os.path.join(repo_root, entry)):
            results.append(os.path.join(repo_root, entry))
    return results


def load_json(filepath):
    try:
        with open(filepath, "r", encoding="utf-8") as f:
            return json.load(f)
    except (OSError, json.JSONDecodeError, UnicodeDecodeError):
        return None


def check_skill_regressions(skill_dir, results_dir):
    """Check a single skill for regressions. Returns list of regression descriptions."""
    skill_name = os.path.basename(skill_dir)
    baselines_dir = os.path.join(skill_dir, "eval-cases", "baselines")
    skill_results_dir = os.path.join(results_dir, skill_name)

    regressions = []

    # Skip if no baselines exist
    if not os.path.isdir(baselines_dir):
        return regressions

    # Skip if no results exist
    if not os.path.isdir(skill_results_dir):
        return regressions

    # Compare each baseline against results
    for entry in sorted(os.listdir(baselines_dir)):
        if not entry.endswith(".json"):
            continue

        baseline_path = os.path.join(baselines_dir, entry)
        result_path = os.path.join(skill_results_dir, entry)

        baseline = load_json(baseline_path)
        if baseline is None:
            continue

        result = load_json(result_path)
        if result is None:
            # No result for this baseline — skip (not a regression)
            continue

        # Compare pass/fail status
        baseline_passed = baseline.get("passed", baseline.get("status") == "passed")
        result_passed = result.get("passed", result.get("status") == "passed")

        if baseline_passed and not result_passed:
            case_name = entry.replace(".json", "")
            regressions.append(
                f"{skill_name}/{case_name}: previously PASSED, now FAILED"
            )

        # Compare individual assertions if available
        baseline_assertions = baseline.get("assertions", {})
        result_assertions = result.get("assertions", {})

        for assertion_key, baseline_value in baseline_assertions.items():
            if not baseline_value:
                continue
            result_value = result_assertions.get(assertion_key)
            if result_value is False:
                case_name = entry.replace(".json", "")
                regressions.append(
                    f"{skill_name}/{case_name}/{assertion_key}: previously PASSED, now FAILED"
                )

    return regressions


def main():
    script_dir = os.path.dirname(os.path.abspath(__file__))
    repo_root = find_repo_root(script_dir)
    if repo_root is None:
        print("ERROR: could not find repo root", file=sys.stderr)
        sys.exit(1)

    results_dir = os.path.join(repo_root, "eval-results")
    skill_dirs = find_skill_dirs(repo_root)

    all_regressions = []
    skills_checked = 0

    for skill_dir in skill_dirs:
        regressions = check_skill_regressions(skill_dir, results_dir)
        if regressions:
            all_regressions.extend(regressions)
        skills_checked += 1

    print("=== Regression Check ===")
    print(f"Skills checked: {skills_checked}")
    print()

    if all_regressions:
        print(f"REGRESSIONS FOUND: {len(all_regressions)}")
        print()
        for r in all_regressions:
            print(f"  REGRESSION: {r}")
        sys.exit(1)
    else:
        print("No regressions detected.")
        sys.exit(0)


if __name__ == "__main__":
    main()
