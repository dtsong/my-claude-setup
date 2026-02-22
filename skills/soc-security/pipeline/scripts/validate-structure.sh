#!/usr/bin/env bash
# validate-structure.sh — Verify skill directory structure meets governance spec.
# Bash 3.2 compatible (no associative arrays, no mapfile).

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
ERRORS=0

log_error() {
  echo "FAIL: $1" >&2
  ERRORS=$((ERRORS + 1))
}

log_ok() {
  echo "  OK: $1"
}

echo "=== Skill Structure Validation ==="
echo ""

# 1. Every *-skill/ directory must have SKILL.md
for skill_dir in "$REPO_ROOT"/*-skill/; do
  [ -d "$skill_dir" ] || continue
  skill_name="$(basename "$skill_dir")"

  if [ -f "$skill_dir/SKILL.md" ]; then
    log_ok "$skill_name/SKILL.md exists"
  else
    log_error "$skill_name/ is missing SKILL.md"
  fi
done

echo ""

# 2. Every *-skill/ directory must have references/
for skill_dir in "$REPO_ROOT"/*-skill/; do
  [ -d "$skill_dir" ] || continue
  skill_name="$(basename "$skill_dir")"

  if [ -d "$skill_dir/references" ]; then
    log_ok "$skill_name/references/ exists"
  else
    log_error "$skill_name/ is missing references/ directory"
  fi
done

echo ""

# 3. Eval cases must NOT be inside skill directories that get auto-loaded.
#    They should be at skill-root/eval-cases/, not inside skills/*/ or references/
for skill_dir in "$REPO_ROOT"/*-skill/; do
  [ -d "$skill_dir" ] || continue
  skill_name="$(basename "$skill_dir")"

  # Check for eval-cases inside references/ (bad)
  if [ -d "$skill_dir/references/eval-cases" ]; then
    log_error "$skill_name/references/eval-cases/ — eval cases inside auto-loaded directory"
  fi

  # Check for eval-cases inside skills/*/ subdirectories (bad for suites)
  if [ -d "$skill_dir/skills" ]; then
    for spec_dir in "$skill_dir"/skills/*/; do
      [ -d "$spec_dir" ] || continue
      spec_name="$(basename "$spec_dir")"
      if [ -d "$spec_dir/eval-cases" ]; then
        log_error "$skill_name/skills/$spec_name/eval-cases/ — eval cases inside specialist directory"
      fi
    done
  fi

  # eval-cases at skill root is fine
  if [ -d "$skill_dir/eval-cases" ]; then
    log_ok "$skill_name/eval-cases/ correctly at skill root"
  fi
done

echo ""
echo "=== Summary ==="

if [ "$ERRORS" -gt 0 ]; then
  echo "FAILED: $ERRORS error(s) found"
  exit 1
else
  echo "PASSED: All structure checks passed"
  exit 0
fi
