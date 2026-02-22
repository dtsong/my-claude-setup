#!/usr/bin/env bash
# run-evals.sh — Locate and run eval cases for skills.
# Bash 3.2 compatible (no associative arrays, no mapfile).

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
TARGETS="all"
MODEL="sonnet"

# Parse arguments
while [ $# -gt 0 ]; do
  case "$1" in
    --targets)
      TARGETS="$2"
      shift 2
      ;;
    --model)
      MODEL="$2"
      shift 2
      ;;
    *)
      echo "Unknown argument: $1" >&2
      echo "Usage: $0 --targets <skill1,skill2|all> --model <haiku|sonnet|opus>" >&2
      exit 1
      ;;
  esac
done

echo "=== Skill Eval Runner ==="
echo "Targets: $TARGETS"
echo "Model: $MODEL"
echo ""

# Build list of skill directories to evaluate
SKILL_DIRS=""
if [ "$TARGETS" = "all" ]; then
  for d in "$REPO_ROOT"/*-skill/; do
    [ -d "$d" ] || continue
    SKILL_DIRS="$SKILL_DIRS $d"
  done
else
  # Split comma-separated targets
  IFS=',' read -r dummy <<EOF
$TARGETS
EOF
  saved_ifs="$IFS"
  IFS=','
  for target in $TARGETS; do
    IFS="$saved_ifs"
    # Trim whitespace
    target="$(echo "$target" | sed 's/^[[:space:]]*//;s/[[:space:]]*$//')"
    # Resolve relative to repo root
    if [ -d "$REPO_ROOT/$target" ]; then
      SKILL_DIRS="$SKILL_DIRS $REPO_ROOT/$target"
    elif [ -d "$target" ]; then
      SKILL_DIRS="$SKILL_DIRS $target"
    else
      echo "WARNING: Skill directory not found: $target" >&2
    fi
  done
  IFS="$saved_ifs"
fi

# Create results directory
RESULTS_DIR="$REPO_ROOT/eval-results"
mkdir -p "$RESULTS_DIR"

TOTAL=0
FOUND=0

for skill_dir in $SKILL_DIRS; do
  [ -d "$skill_dir" ] || continue
  skill_name="$(basename "$skill_dir")"
  TOTAL=$((TOTAL + 1))

  evals_file="$skill_dir/eval-cases/evals.json"
  if [ ! -f "$evals_file" ]; then
    echo "SKIP: $skill_name — no eval-cases/evals.json"
    continue
  fi

  FOUND=$((FOUND + 1))
  echo "EVAL: $skill_name"

  # Create per-skill results directory
  skill_results="$RESULTS_DIR/$skill_name"
  mkdir -p "$skill_results"

  # Placeholder: echo the commands that would execute evals
  echo "  [placeholder] Would run: claude --model $MODEL --eval $evals_file"
  echo "  [placeholder] Results would be saved to: $skill_results/"
  echo "  [placeholder] Timestamp: $(date -u +%Y-%m-%dT%H:%M:%SZ)"

  # Write a placeholder result file
  echo "{\"skill\": \"$skill_name\", \"model\": \"$MODEL\", \"status\": \"placeholder\", \"timestamp\": \"$(date -u +%Y-%m-%dT%H:%M:%SZ)\"}" > "$skill_results/result.json"
done

echo ""
echo "=== Summary ==="
echo "Skills scanned: $TOTAL"
echo "Skills with evals: $FOUND"
echo "Results directory: $RESULTS_DIR"

exit 0
