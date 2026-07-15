#!/usr/bin/env bash
# doc-drift-check.sh: compare real inventory counts against the numeric
# claims grep-able in README.md / ARCHITECTURE.md's directory-tree blocks.
#
# This is advisory, not a governance gate: it always exits 0. The enforcing
# checks live in pipeline/hooks/ (see mcs-validation-and-qa for what counts
# as acceptance evidence). Use this to catch stale "N agents / N skills / N
# commands" marketing-copy numbers before they mislead a new reader.
#
# Usage: doc-drift-check.sh [repo-root]
#   repo-root   Defaults to the repo containing this script (walked up from
#               its own path). Pass an explicit path to audit a checkout
#               elsewhere.
#
# Counting rules (documented so a DRIFT is reproducible, not "trust me"):
#   agents      = *.md directly in agents/ (maxdepth 1), symlinks counted
#                 (private-repo ECE personas are real registered agents).
#   commands    = *.md directly in commands/ (maxdepth 1), excluding files
#                 starting with "_" (the shared engine, not a slash command)
#                 and non-.md entries (skips the self-referential
#                 commands/commands symlink automatically).
#   skills      = SKILL.md anywhere under skills/, symlinked directories NOT
#                 followed (matches pipeline/scripts/skill-audit.py's
#                 default; pass --follow-symlinks equivalent by editing
#                 FOLLOW_SYMLINKS below if you need the private-repo total).
#   council      = SKILL.md anywhere under skills/council/.
#   departments = top-level directories under skills/council/, excluding
#                 non-department dirs (.claude, references).
#
# Claim extraction: grep -oE against fixed substrings that matched this
# repo's README.md wording as of 2026-07-02. If the README's phrasing
# changes, the corresponding line prints SKIP, not a false PASS.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="${1:-$(cd "$SCRIPT_DIR/../../../.." && pwd)}"
README="$REPO_ROOT/README.md"
ARCHITECTURE="$REPO_ROOT/ARCHITECTURE.md"

if [ ! -f "$README" ] && [ ! -f "$ARCHITECTURE" ]; then
  echo "ERROR: neither README.md nor ARCHITECTURE.md found under $REPO_ROOT" >&2
  echo "Usage: $0 [repo-root]" >&2
  exit 1
fi

count_dir_md() {
  # $1 = dir, $2 = optional -name exclude glob (e.g. "_*")
  local dir="$1" exclude="${2:-}"
  [ -d "$dir" ] || { echo 0; return; }
  if [ -n "$exclude" ]; then
    find "$dir" -maxdepth 1 -name "*.md" -not -name "$exclude" 2>/dev/null | wc -l | tr -d ' '
  else
    find "$dir" -maxdepth 1 -name "*.md" 2>/dev/null | wc -l | tr -d ' '
  fi
}

count_skill_md() {
  local dir="$1"
  [ -d "$dir" ] || { echo 0; return; }
  find "$dir" -name "SKILL.md" 2>/dev/null | wc -l | tr -d ' '
}

count_departments() {
  local dir="$REPO_ROOT/skills/council"
  [ -d "$dir" ] || { echo 0; return; }
  find "$dir" -maxdepth 1 -mindepth 1 -type d 2>/dev/null \
    | grep -vE '/(\.claude|references)$' | wc -l | tr -d ' '
}

# Extract the first number matching $1 (an -oE regex) in README then
# ARCHITECTURE. Empty string if neither file contains the pattern.
extract_claim() {
  local pattern="$1"
  local hit
  hit=$(grep -ohE "$pattern" "$README" "$ARCHITECTURE" 2>/dev/null | head -1 || true)
  echo "$hit" | grep -oE '[0-9]+' || true
}

report_line() {
  # $1=label $2=claim $3=actual $4=source-pattern (for SKIP message)
  local label="$1" claim="$2" actual="$3" pattern="$4"
  if [ -z "$claim" ]; then
    printf 'SKIP  %-12s pattern not found in README.md/ARCHITECTURE.md: /%s/ (actual=%s)\n' \
      "$label" "$pattern" "$actual"
    return
  fi
  if [ "$claim" = "$actual" ]; then
    printf 'PASS  %-12s claimed=%s actual=%s\n' "$label" "$claim" "$actual"
  else
    printf 'DRIFT %-12s claimed=%s actual=%s delta=%s\n' \
      "$label" "$claim" "$actual" "$((actual - claim))"
  fi
}

AGENTS_ACTUAL=$(count_dir_md "$REPO_ROOT/agents")
COMMANDS_ACTUAL=$(count_dir_md "$REPO_ROOT/commands" "_*")
SKILLS_ACTUAL=$(count_skill_md "$REPO_ROOT/skills")
COUNCIL_ACTUAL=$(count_skill_md "$REPO_ROOT/skills/council")
DEPARTMENTS_ACTUAL=$(count_departments)

AGENTS_CLAIM=$(extract_claim '[0-9]+ council agent personas')
COMMANDS_CLAIM=$(extract_claim '[0-9]+ slash commands')
SKILLS_CLAIM=$(extract_claim '[0-9]+ structured skill templates')
DEPARTMENTS_CLAIM=$(extract_claim '[0-9]+ departments')

echo "=== doc-drift-check: $REPO_ROOT ==="
echo "(informational only, always exits 0 -- see pipeline/hooks/ for enforcement)"
echo ""
report_line "agents" "$AGENTS_CLAIM" "$AGENTS_ACTUAL" '[0-9]+ council agent personas'
report_line "commands" "$COMMANDS_CLAIM" "$COMMANDS_ACTUAL" '[0-9]+ slash commands'
report_line "skills" "$SKILLS_CLAIM" "$SKILLS_ACTUAL" '[0-9]+ structured skill templates'
report_line "departments" "$DEPARTMENTS_CLAIM" "$DEPARTMENTS_ACTUAL" '[0-9]+ departments'
echo ""
echo "council SKILL.md files (no single doc claim to check against): $COUNCIL_ACTUAL"
echo "  cross-check: \"departments x 2-3 skills each\" implies $((DEPARTMENTS_ACTUAL * 2))-$((DEPARTMENTS_ACTUAL * 3)) at $DEPARTMENTS_ACTUAL departments"
if [ "$COUNCIL_ACTUAL" -gt "$((DEPARTMENTS_ACTUAL * 3))" ] || [ "$COUNCIL_ACTUAL" -lt "$((DEPARTMENTS_ACTUAL * 2))" ]; then
  echo "  DRIFT: $COUNCIL_ACTUAL council SKILL.md files falls outside that range"
else
  echo "  PASS: $COUNCIL_ACTUAL council SKILL.md files is within that range"
fi
