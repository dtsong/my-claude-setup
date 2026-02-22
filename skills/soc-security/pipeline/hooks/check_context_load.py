#!/usr/bin/env python3
"""Pre-commit hook: enforce max simultaneous context load ceiling on skill suites. HARD tier."""

import os
import sys

sys.path.insert(0, os.path.dirname(__file__))
from _utils import (
    find_repo_root, load_budgets, estimate_tokens, get_context_ceiling,
)


def get_reference_files(skill_dir):
    """Get all .md files in a skill's references/ directory."""
    refs_dir = os.path.join(skill_dir, "references")
    if not os.path.isdir(refs_dir):
        return []
    result = []
    for entry in os.listdir(refs_dir):
        if entry.endswith(".md"):
            result.append(os.path.join(refs_dir, entry))
    return result


def check_suite(suite_dir, repo_root, budgets):
    """Check a skill suite per-specialist: coordinator + specialist + its largest ref.

    At runtime only one specialist is loaded at a time, so the correct ceiling
    check is per-specialist rather than global worst case across all specialists.

    Returns list of error strings.
    """
    coordinator_path = os.path.join(suite_dir, "SKILL.md")
    if not os.path.isfile(coordinator_path):
        return []

    coord_tokens = estimate_tokens(coordinator_path)
    skills_dir = os.path.join(suite_dir, "skills")
    errors = []

    if not os.path.isdir(skills_dir):
        return []

    for entry in sorted(os.listdir(skills_dir)):
        spec_dir = os.path.join(skills_dir, entry)
        spec_skill = os.path.join(spec_dir, "SKILL.md")
        if not os.path.isfile(spec_skill):
            continue

        spec_tokens = estimate_tokens(spec_skill)

        # Find largest reference for THIS specialist only
        max_ref_tokens = 0
        max_ref_name = ""
        for ref_path in get_reference_files(spec_dir):
            tokens = estimate_tokens(ref_path)
            if tokens > max_ref_tokens:
                max_ref_tokens = tokens
                max_ref_name = os.path.relpath(ref_path, repo_root)

        total = coord_tokens + spec_tokens + max_ref_tokens
        rel_spec = os.path.relpath(spec_dir, repo_root)
        max_tokens = get_context_ceiling(rel_spec, repo_root, budgets)

        if total > max_tokens:
            detail = f"coordinator={coord_tokens}"
            detail += f" + specialist({entry})={spec_tokens}"
            if max_ref_tokens > 0:
                detail += f" + reference({max_ref_name})={max_ref_tokens}"
            errors.append(
                f"{rel_spec}: context load {total} tokens exceeds "
                f"ceiling of {max_tokens} ({detail}). "
                f"Reduce the specialist or split the largest reference file."
            )

    return errors


def main():
    if len(sys.argv) < 2:
        sys.exit(0)

    repo_root = find_repo_root()
    budgets = load_budgets(repo_root)

    # Collect unique skill directories from passed files
    checked = set()
    all_errors = []

    for filepath in sys.argv[1:]:
        filepath = os.path.abspath(filepath)

        # Walk up to find the skill directory (one containing SKILL.md)
        d = os.path.dirname(filepath)
        skill_dir = None

        if os.path.basename(filepath) == "SKILL.md":
            skill_dir = d
        else:
            candidate = d
            while candidate != repo_root and candidate != os.path.dirname(candidate):
                if os.path.isfile(os.path.join(candidate, "SKILL.md")):
                    skill_dir = candidate
                    break
                candidate = os.path.dirname(candidate)

        if skill_dir is None or skill_dir in checked:
            continue
        checked.add(skill_dir)

        # Only check suites (directory with SKILL.md + skills/ subdirectory)
        if os.path.isdir(os.path.join(skill_dir, "skills")):
            all_errors.extend(check_suite(skill_dir, repo_root, budgets))

    for e in all_errors:
        print(f"FAIL: {e}", file=sys.stderr)

    sys.exit(1 if all_errors else 0)


if __name__ == "__main__":
    main()
