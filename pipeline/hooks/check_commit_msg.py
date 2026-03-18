#!/usr/bin/env python3
"""Pre-commit hook (commit-msg): validate commit message format. HARD tier."""

import re
import sys

VALID_TYPES = {
    "skill",
    "skill-fix",
    "skill-ref",
    "skill-eval",
    "skill-docs",
    "chore",
    "feat",
    "fix",
    "docs",
    "style",
    "refactor",
    "test",
    "ci",
    "perf",
    "build",
    "revert",
}

# type(scope): description  OR  type: description
COMMIT_RE = re.compile(
    r"^(?P<type>[a-z][a-z-]*)(?:\([^)]+\))?:\s+(?P<desc>.+)$"
)

MIN_DESCRIPTION_LENGTH = 10
MAX_SUBJECT_LENGTH = 100


def validate_message(message):
    """Validate a commit message. Returns (passed, errors)."""
    # Filter out comment lines (git default behavior)
    content_lines = [line for line in message.split("\n") if not line.startswith("#")]
    if not content_lines or not content_lines[0].strip():
        return False, ["commit message is empty"]

    subject = content_lines[0].strip()
    errors = []

    # Allow merge commits
    if subject.startswith("Merge "):
        return True, []

    match = COMMIT_RE.match(subject)
    if not match:
        errors.append(
            f"commit message must match 'type(scope): description' "
            f"or 'type: description'\n"
            f"  Got: {subject}\n"
            f"  Valid types: {', '.join(sorted(VALID_TYPES))}"
        )
        return False, errors

    commit_type = match.group("type")
    description = match.group("desc")

    if commit_type not in VALID_TYPES:
        errors.append(
            f"unknown commit type '{commit_type}'\n"
            f"  Valid types: {', '.join(sorted(VALID_TYPES))}"
        )

    if len(description) < MIN_DESCRIPTION_LENGTH:
        errors.append(
            f"commit description must be >= {MIN_DESCRIPTION_LENGTH} characters "
            f"(got {len(description)})"
        )

    if description.endswith("."):
        errors.append("description should not end with a period")

    if len(subject) > MAX_SUBJECT_LENGTH:
        errors.append(
            f"subject line too long ({len(subject)} chars, max {MAX_SUBJECT_LENGTH})"
        )

    return len(errors) == 0, errors


def main():
    if len(sys.argv) < 2:
        print("ERROR: commit message file path required", file=sys.stderr)
        sys.exit(1)

    try:
        with open(sys.argv[1], "r", encoding="utf-8") as f:
            message = f.read()
    except (OSError, UnicodeDecodeError) as e:
        print(f"ERROR: could not read commit message file: {e}", file=sys.stderr)
        sys.exit(1)

    passed, errors = validate_message(message)
    if not passed:
        print("FAIL: commit message validation failed:", file=sys.stderr)
        for error in errors:
            print(f"  {error}", file=sys.stderr)
        sys.exit(1)

    sys.exit(0)


if __name__ == "__main__":
    main()
