#!/usr/bin/env python3
"""Pre-commit hook: validate SKILL.md frontmatter. HARD tier."""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(__file__))
from _utils import find_repo_root, is_excluded

try:
    import yaml
    HAS_YAML = True
except ImportError:
    HAS_YAML = False

REQUIRED_FIELDS = {"name", "description"}
VALID_OPTIONAL = {"model", "version"}
VALID_MODEL_PREFERRED = {"haiku", "sonnet", "opus"}
VALID_MODEL_REASONING = {"low", "medium", "high"}
KEBAB_RE = re.compile(r"^[a-z][a-z0-9]*(-[a-z0-9]+)*$")
MIN_DESCRIPTION_WORDS = 10


def extract_frontmatter(text):
    """Extract YAML frontmatter between --- markers. Returns (dict, error_msg)."""
    lines = text.split("\n")
    if not lines or lines[0].strip() != "---":
        return None, "no frontmatter found (file must start with ---)"

    end_idx = None
    for i in range(1, len(lines)):
        if lines[i].strip() == "---":
            end_idx = i
            break

    if end_idx is None:
        return None, "no closing --- found for frontmatter"

    yaml_text = "\n".join(lines[1:end_idx])

    if HAS_YAML:
        try:
            data = yaml.safe_load(yaml_text)
        except Exception as e:
            return None, f"invalid YAML in frontmatter: {e}"
    else:
        # Fallback: simple key: value parser
        data = {}
        for line in yaml_text.split("\n"):
            line = line.strip()
            if ":" in line and not line.startswith(" ") and not line.startswith("-"):
                key, _, value = line.partition(":")
                data[key.strip()] = value.strip()

    if not isinstance(data, dict):
        return None, "frontmatter must be a YAML mapping"

    return data, None


def check_file(filepath, repo_root):
    """Check a single SKILL.md file. Returns (errors, warnings)."""
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

    data, err = extract_frontmatter(text)
    if err:
        errors.append(f"{rel_path}: {err}")
        return errors, warnings

    # Check required fields
    for field in REQUIRED_FIELDS:
        if field not in data:
            errors.append(f"{rel_path}: missing required field '{field}'")
        elif data[field] is None or (isinstance(data[field], str) and not data[field].strip()):
            errors.append(f"{rel_path}: field '{field}' must not be empty")

    # Validate name format
    if "name" in data and data["name"]:
        name = str(data["name"])
        if not KEBAB_RE.match(name):
            errors.append(
                f"{rel_path}: 'name' must be kebab-case "
                f"(got '{name}', expected pattern: {KEBAB_RE.pattern})"
            )

    # Validate description length
    if "description" in data and data["description"]:
        desc = str(data["description"])
        word_count = len(desc.split())
        if word_count < MIN_DESCRIPTION_WORDS:
            errors.append(
                f"{rel_path}: 'description' must be >= {MIN_DESCRIPTION_WORDS} words "
                f"(got {word_count})"
            )

    # Validate model block if present
    if "model" in data and isinstance(data["model"], dict):
        model = data["model"]
        if "preferred" in model and model["preferred"] not in VALID_MODEL_PREFERRED:
            errors.append(
                f"{rel_path}: 'model.preferred' must be one of "
                f"{sorted(VALID_MODEL_PREFERRED)} (got '{model['preferred']}')"
            )
        if "minimum" in model and model["minimum"] not in VALID_MODEL_PREFERRED:
            errors.append(
                f"{rel_path}: 'model.minimum' must be one of "
                f"{sorted(VALID_MODEL_PREFERRED)} (got '{model['minimum']}')"
            )
        if "reasoning_demand" in model and model["reasoning_demand"] not in VALID_MODEL_REASONING:
            errors.append(
                f"{rel_path}: 'model.reasoning_demand' must be one of "
                f"{sorted(VALID_MODEL_REASONING)} (got '{model['reasoning_demand']}')"
            )

    # Warn on unknown top-level fields
    all_known = REQUIRED_FIELDS | VALID_OPTIONAL
    for key in data:
        if key not in all_known:
            warnings.append(f"{rel_path}: unknown frontmatter field '{key}'")

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
