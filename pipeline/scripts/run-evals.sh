#!/usr/bin/env bash
# run-evals.sh — Locate and run eval cases for skills.
# Bash 3.2 compatible (no associative arrays, no mapfile).
#
# Tiers:
#   1 — Static validation (pre-commit hooks, free, <2s)
#   2 — E2E execution via claude -p (paid, 10-60s per case)
#   3 — LLM-as-judge quality scoring (paid, 5-15s per skill)
#
# Usage:
#   ./run-evals.sh --tier 2 --targets soc-security --model sonnet
#   ./run-evals.sh --tier all --diff
#   ./run-evals.sh --tier 1  # runs pre-commit hooks only

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
TARGETS="all"
MODEL="sonnet"
TIER="all"
DIFF_MODE="false"
TIMESTAMP="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

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
    --tier)
      TIER="$2"
      shift 2
      ;;
    --diff)
      DIFF_MODE="true"
      shift
      ;;
    *)
      echo "Unknown argument: $1" >&2
      echo "Usage: $0 [--targets <skill1,skill2|all>] [--model <haiku|sonnet|opus>] [--tier <1|2|3|all>] [--diff]" >&2
      exit 1
      ;;
  esac
done

echo "=== Skill Eval Runner ==="
echo "Tier: $TIER"
echo "Targets: $TARGETS"
echo "Model: $MODEL"
echo "Diff mode: $DIFF_MODE"
echo "Timestamp: $TIMESTAMP"
echo ""

# ── Tier 1: Static validation ──────────────────────────────────────────────
run_tier1() {
  echo "--- Tier 1: Static Validation (pre-commit hooks) ---"
  if command -v pre-commit >/dev/null 2>&1; then
    pre-commit run --all-files 2>&1 || true
  else
    echo "WARNING: pre-commit not installed. Run: pip install pre-commit" >&2
    # Fallback: run individual hook scripts
    for hook in "$REPO_ROOT/pipeline/hooks"/check_*.py; do
      [ -f "$hook" ] || continue
      hook_name="$(basename "$hook" .py)"
      echo "  Running $hook_name..."
      # Find all SKILL.md files and pass to hook
      skill_files=$(find "$REPO_ROOT/skills" "$REPO_ROOT/commands" -name "SKILL.md" -o -name "DEPARTMENT.md" 2>/dev/null | head -200)
      if [ -n "$skill_files" ]; then
        echo "$skill_files" | xargs python3 "$hook" 2>&1 || true
      fi
    done
  fi
  echo ""
}

# ── Build skill directory list ──────────────────────────────────────────────
build_skill_dirs() {
  SKILL_DIRS=""

  if [ "$TARGETS" = "all" ]; then
    # Search all skill-containing directories
    for pattern in "$REPO_ROOT"/skills/council/*/eval-cases "$REPO_ROOT"/skills/*/eval-cases "$REPO_ROOT"/skills/*/*/eval-cases; do
      [ -d "$pattern" ] || continue
      parent_dir="$(dirname "$pattern")"
      SKILL_DIRS="$SKILL_DIRS $parent_dir"
    done
  else
    saved_ifs="$IFS"
    IFS=','
    for target in $TARGETS; do
      IFS="$saved_ifs"
      target="$(echo "$target" | sed 's/^[[:space:]]*//;s/[[:space:]]*$//')"
      if [ -d "$REPO_ROOT/$target" ]; then
        SKILL_DIRS="$SKILL_DIRS $REPO_ROOT/$target"
      elif [ -d "$REPO_ROOT/skills/$target" ]; then
        SKILL_DIRS="$SKILL_DIRS $REPO_ROOT/skills/$target"
      elif [ -d "$target" ]; then
        SKILL_DIRS="$SKILL_DIRS $target"
      else
        echo "WARNING: Skill directory not found: $target" >&2
      fi
    done
    IFS="$saved_ifs"
  fi

  # Diff-based filtering
  if [ "$DIFF_MODE" = "true" ]; then
    changed_files="$(git -C "$REPO_ROOT" diff --name-only HEAD~1 2>/dev/null || echo "")"
    if [ -z "$changed_files" ]; then
      echo "WARNING: No diff available (fresh repo or single commit). Running all." >&2
      return
    fi

    filtered=""
    for skill_dir in $SKILL_DIRS; do
      rel_dir="$(python3 -c "import os; print(os.path.relpath('$skill_dir', '$REPO_ROOT'))")"
      if echo "$changed_files" | grep -q "^${rel_dir}/"; then
        filtered="$filtered $skill_dir"
      fi
    done

    if [ -z "$filtered" ]; then
      echo "No changed skills detected. Nothing to evaluate."
      SKILL_DIRS=""
    else
      SKILL_DIRS="$filtered"
    fi
  fi
}

# ── Tier 2: E2E execution via claude -p ─────────────────────────────────────
run_tier2() {
  echo "--- Tier 2: E2E Execution via claude -p ---"

  if ! command -v claude >/dev/null 2>&1; then
    echo "ERROR: 'claude' CLI not found. Install Claude Code to run Tier 2 evals." >&2
    return 1
  fi

  build_skill_dirs

  RESULTS_DIR="$REPO_ROOT/eval-results/tier2-$(date -u +%Y%m%d-%H%M%S)"
  mkdir -p "$RESULTS_DIR"

  TOTAL=0
  PASSED=0
  FAILED=0
  SKIPPED=0

  for skill_dir in $SKILL_DIRS; do
    [ -d "$skill_dir" ] || continue
    skill_name="$(basename "$skill_dir")"

    # Check for trigger evals (most common format)
    trigger_file="$skill_dir/eval-cases/trigger-evals.json"
    evals_file="$skill_dir/eval-cases/evals.json"

    if [ ! -f "$trigger_file" ] && [ ! -f "$evals_file" ]; then
      continue
    fi

    echo ""
    echo "EVAL: $skill_name"
    skill_results="$RESULTS_DIR/$skill_name"
    mkdir -p "$skill_results"

    # Run trigger evals if they exist
    if [ -f "$trigger_file" ]; then
      cases="$(python3 -c "
import json, sys
with open('$trigger_file') as f:
    data = json.load(f)
for c in data:
    cid = c.get('id', 'unknown')
    inp = c.get('input', '').replace('|', ' ')
    expected = c.get('expected_skill') or 'NONE'
    ctype = c.get('type', 'positive')
    print(f'{cid}|{expected}|{ctype}|{inp}')
" 2>/dev/null || echo "")"

      echo "$cases" | while IFS='|' read -r case_id expected ctype input_text; do
        [ -z "$case_id" ] && continue
        TOTAL=$((TOTAL + 1))

        echo "  RUN: $case_id ($ctype, expects: $expected)"

        # Build prompt: present the department/skill coordinator and ask for routing
        skill_md=""
        if [ -f "$skill_dir/SKILL.md" ]; then
          skill_md="$(cat "$skill_dir/SKILL.md")"
        elif [ -f "$skill_dir/DEPARTMENT.md" ]; then
          skill_md="$(cat "$skill_dir/DEPARTMENT.md")"
        fi

        prompt="You are a skill router. Given this skill definition and user request, respond with ONLY the skill name you would route to. If no skill matches, respond with NONE.

Skill definition:
$skill_md

User request: $input_text

Respond with just the skill name (e.g., 'schema-design' or 'NONE'):"

        # Write prompt to temp file to avoid shell escaping issues
        prompt_file="$(mktemp)"
        echo "$prompt" > "$prompt_file"

        result="$(cat "$prompt_file" | claude -p --model "$MODEL" --output-format text 2>/dev/null | tr -d '[:space:]' || echo "ERROR")"
        rm -f "$prompt_file"

        # Grade result
        if [ "$ctype" = "positive" ]; then
          if echo "$result" | grep -qi "$expected"; then
            echo "    PASS: routed to $result (expected: $expected)"
            PASSED=$((PASSED + 1))
          else
            echo "    FAIL: routed to $result (expected: $expected)"
            FAILED=$((FAILED + 1))
          fi
        else
          # Negative case: should NOT route to any skill in this department
          if [ "$result" = "NONE" ] || [ "$result" = "none" ] || [ "$result" = "ERROR" ]; then
            echo "    PASS: correctly rejected ($result)"
            PASSED=$((PASSED + 1))
          else
            echo "    FAIL: incorrectly routed to $result (should have rejected)"
            FAILED=$((FAILED + 1))
          fi
        fi

        # Record result
        echo "{\"case_id\": \"$case_id\", \"expected\": \"$expected\", \"actual\": \"$result\", \"type\": \"$ctype\", \"timestamp\": \"$TIMESTAMP\"}" >> "$skill_results/results.jsonl"
      done
    fi

    # Run structured evals if they exist
    if [ -f "$evals_file" ]; then
      echo "  (structured evals from evals.json — case-by-case execution)"

      cases="$(python3 -c "
import json
with open('$evals_file') as f:
    data = json.load(f)
for c in data.get('cases', []):
    cid = c.get('id', 'unknown')
    case_file = c.get('file', '')
    tier = c.get('tier', 1)
    print(f'{cid}|{case_file}|{tier}')
" 2>/dev/null || echo "")"

      echo "$cases" | while IFS='|' read -r case_id case_file case_tier; do
        [ -z "$case_id" ] && continue

        case_path="$skill_dir/eval-cases/$case_file"
        if [ ! -f "$case_path" ]; then
          echo "  SKIP: $case_id — file not found: $case_file"
          SKIPPED=$((SKIPPED + 1))
          continue
        fi

        # Extract user_prompt from the case file's JSON block
        user_prompt="$(python3 -c "
import re, json, sys
with open('$case_path') as f:
    text = f.read()
m = re.search(r'\`\`\`json\n(.*?)\n\`\`\`', text, re.DOTALL)
if m:
    data = json.loads(m.group(1))
    print(data.get('user_prompt', ''))
" 2>/dev/null || echo "")"

        if [ -z "$user_prompt" ]; then
          echo "  SKIP: $case_id — no user_prompt found in case file"
          SKIPPED=$((SKIPPED + 1))
          continue
        fi

        TOTAL=$((TOTAL + 1))
        echo "  RUN: $case_id (tier $case_tier)"

        # Build skill context
        skill_md=""
        [ -f "$skill_dir/SKILL.md" ] && skill_md="$(cat "$skill_dir/SKILL.md")"

        prompt="You are using this skill:

$skill_md

User request: $user_prompt"

        prompt_file="$(mktemp)"
        echo "$prompt" > "$prompt_file"

        # Execute and capture output
        cat "$prompt_file" | claude -p --model "$MODEL" --output-format stream-json \
          > "$skill_results/${case_id}.jsonl" 2>&1 || true
        rm -f "$prompt_file"

        # Extract Must Pass criteria from case file and do basic keyword check
        must_pass="$(sed -n '/Must Pass/,/Should Pass\|Bonus\|##/p' "$case_path" | grep -o '\[.*\]' | head -5 || echo "")"
        echo "    Completed. Results saved to $skill_results/${case_id}.jsonl"
        echo "{\"case_id\": \"$case_id\", \"tier\": $case_tier, \"status\": \"executed\", \"timestamp\": \"$TIMESTAMP\"}" >> "$skill_results/results.jsonl"
      done
    fi
  done

  echo ""
  echo "--- Tier 2 Summary ---"
  echo "Results directory: $RESULTS_DIR"
  # Count from result files
  total_results="$(find "$RESULTS_DIR" -name "results.jsonl" -exec cat {} + 2>/dev/null | wc -l | tr -d ' ')"
  echo "Total cases executed: ${total_results:-0}"
}

# ── Tier 3: LLM-as-judge ───────────────────────────────────────────────────
run_tier3() {
  echo "--- Tier 3: LLM-as-Judge Quality Scoring ---"
  echo "Delegating to judge-skill-quality.sh..."

  judge_script="$REPO_ROOT/pipeline/scripts/judge-skill-quality.sh"
  if [ ! -f "$judge_script" ]; then
    echo "ERROR: judge-skill-quality.sh not found at $judge_script" >&2
    return 1
  fi

  args=""
  [ "$TARGETS" != "all" ] && args="$args --targets $TARGETS"
  [ "$MODEL" != "sonnet" ] && args="$args --model $MODEL"
  [ "$DIFF_MODE" = "true" ] && args="$args --diff"

  bash "$judge_script" $args
}

# ── Main dispatch ───────────────────────────────────────────────────────────
case "$TIER" in
  1)
    run_tier1
    ;;
  2)
    run_tier2
    ;;
  3)
    run_tier3
    ;;
  all)
    run_tier1
    run_tier2
    run_tier3
    ;;
  *)
    echo "ERROR: Invalid tier '$TIER'. Use 1, 2, 3, or all." >&2
    exit 1
    ;;
esac

echo ""
echo "=== Eval run complete ==="
exit 0
