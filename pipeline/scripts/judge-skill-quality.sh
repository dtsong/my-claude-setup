#!/usr/bin/env bash
# judge-skill-quality.sh — LLM-as-judge scoring for skill SKILL.md quality.
# Scores each SKILL.md on Clarity (1-5), Completeness (1-5), Actionability (1-5).
# Uses claude -p with a rubric derived from the Skill Governance Spec.
#
# Usage:
#   ./judge-skill-quality.sh                           # judge all skills
#   ./judge-skill-quality.sh --targets council/architect  # specific skill
#   ./judge-skill-quality.sh --diff                    # only changed skills
#   ./judge-skill-quality.sh --model haiku             # cheaper judge

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
TARGETS="all"
MODEL="sonnet"
DIFF_MODE="false"
TIMESTAMP="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

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
    --diff)
      DIFF_MODE="true"
      shift
      ;;
    *)
      echo "Unknown argument: $1" >&2
      echo "Usage: $0 [--targets <skill|all>] [--model <haiku|sonnet|opus>] [--diff]" >&2
      exit 1
      ;;
  esac
done

if ! command -v claude >/dev/null 2>&1; then
  echo "ERROR: 'claude' CLI not found. Install Claude Code to run quality judge." >&2
  exit 1
fi

echo "=== Skill Quality Judge (Tier 3) ==="
echo "Model: $MODEL"
echo "Targets: $TARGETS"
echo "Diff mode: $DIFF_MODE"
echo ""

# Build list of SKILL.md files to judge
SKILL_FILES=""

if [ "$TARGETS" = "all" ]; then
  SKILL_FILES="$(find "$REPO_ROOT/skills" "$REPO_ROOT/commands" -name "SKILL.md" -not -path "*/eval-cases/*" -not -path "*/templates/*" 2>/dev/null | sort)"
else
  saved_ifs="$IFS"
  IFS=','
  for target in $TARGETS; do
    IFS="$saved_ifs"
    target="$(echo "$target" | sed 's/^[[:space:]]*//;s/[[:space:]]*$//')"
    found=""
    for base in "$REPO_ROOT/skills/$target" "$REPO_ROOT/commands/$target" "$REPO_ROOT/$target"; do
      if [ -f "$base/SKILL.md" ]; then
        found="$base/SKILL.md"
        break
      elif [ -d "$base" ]; then
        more="$(find "$base" -name "SKILL.md" -not -path "*/eval-cases/*" -not -path "*/templates/*" 2>/dev/null)"
        if [ -n "$more" ]; then
          found="$more"
          break
        fi
      fi
    done
    if [ -n "$found" ]; then
      SKILL_FILES="$(printf '%s\n%s' "$SKILL_FILES" "$found")"
    else
      echo "WARNING: No SKILL.md found for target: $target" >&2
    fi
  done
  IFS="$saved_ifs"
fi

# Diff-based filtering
if [ "$DIFF_MODE" = "true" ]; then
  changed_files="$(git -C "$REPO_ROOT" diff --name-only HEAD~1 2>/dev/null || echo "")"
  if [ -n "$changed_files" ]; then
    filtered=""
    for skill_file in $SKILL_FILES; do
      [ -z "$skill_file" ] && continue
      skill_dir="$(dirname "$skill_file")"
      rel_dir="$(python3 -c "import os; print(os.path.relpath('$skill_dir', '$REPO_ROOT'))")"
      if echo "$changed_files" | grep -q "^${rel_dir}/"; then
        filtered="$(printf '%s\n%s' "$filtered" "$skill_file")"
      fi
    done
    SKILL_FILES="$filtered"
  fi
fi

# Results directory
RESULTS_DIR="$REPO_ROOT/eval-results/judge-$(date -u +%Y%m%d-%H%M%S)"
mkdir -p "$RESULTS_DIR"

JUDGE_PROMPT='You are a skill quality judge. Score the following SKILL.md file on three dimensions.

## Scoring Rubric

### Clarity (1-5)
1: Ambiguous instructions, unclear procedure flow, agent cannot determine next action
2: Some steps clear but key decision points are vague
3: Mostly clear, some steps need interpretation
4: Nearly all steps are unambiguous with clear decision points
5: Every step is unambiguous, decision points are explicit, edge cases addressed

### Completeness (1-5)
1: Missing critical sections (no Scope Constraints, no Input Sanitization, no procedure)
2: Has basic structure but missing important sections
3: All required sections present, some thin or lacking edge cases
4: All sections present with good coverage, minor gaps
5: All sections present with edge cases, error handling, gotchas, and references

### Actionability (1-5)
1: Agent cannot execute without significant interpretation or guessing
2: Some steps map to actions but many require judgment calls not guided by the skill
3: Agent can execute most steps directly
4: Nearly every step maps to a concrete tool call, command, or output format
5: Every step maps to a concrete tool call or output, fallbacks provided, nothing ambiguous

## Output Format
Respond in JSON only (no markdown fences, no explanation):
{"clarity": N, "completeness": N, "actionability": N, "total": N, "findings": ["specific finding 1", "specific finding 2", "specific finding 3"]}

## SKILL.md to Judge:
'

TOTAL=0
RESULTS_TABLE=""

for skill_file in $SKILL_FILES; do
  [ -z "$skill_file" ] && continue
  [ ! -f "$skill_file" ] && continue

  TOTAL=$((TOTAL + 1))
  rel_path="$(python3 -c "import os; print(os.path.relpath('$skill_file', '$REPO_ROOT'))")"
  echo "Judging: $rel_path"

  skill_content="$(cat "$skill_file")"
  full_prompt="${JUDGE_PROMPT}${skill_content}"

  prompt_file="$(mktemp)"
  echo "$full_prompt" > "$prompt_file"

  result="$(cat "$prompt_file" | claude -p --model "$MODEL" --output-format text 2>/dev/null || echo '{"clarity":0,"completeness":0,"actionability":0,"total":0,"findings":["ERROR: judge failed"]}')"
  rm -f "$prompt_file"

  # Extract scores using python for robustness
  scores="$(python3 -c "
import json, sys, re
text = '''$result'''
# Try to find JSON in the response
m = re.search(r'\{.*\}', text, re.DOTALL)
if m:
    try:
        data = json.loads(m.group())
        c = data.get('clarity', 0)
        comp = data.get('completeness', 0)
        a = data.get('actionability', 0)
        t = c + comp + a
        findings = '; '.join(data.get('findings', [])[:3])
        print(f'{c}|{comp}|{a}|{t}|{findings}')
    except json.JSONDecodeError:
        print('0|0|0|0|Parse error')
else:
    print('0|0|0|0|No JSON in response')
" 2>/dev/null || echo "0|0|0|0|Script error")"

  clarity="$(echo "$scores" | cut -d'|' -f1)"
  completeness="$(echo "$scores" | cut -d'|' -f2)"
  actionability="$(echo "$scores" | cut -d'|' -f3)"
  total="$(echo "$scores" | cut -d'|' -f4)"
  findings="$(echo "$scores" | cut -d'|' -f5)"

  echo "  Clarity: $clarity  Completeness: $completeness  Actionability: $actionability  Total: $total/15"

  # Save per-skill result
  echo "{\"skill\": \"$rel_path\", \"clarity\": $clarity, \"completeness\": $completeness, \"actionability\": $actionability, \"total\": $total, \"findings\": \"$findings\", \"timestamp\": \"$TIMESTAMP\"}" >> "$RESULTS_DIR/results.jsonl"

  RESULTS_TABLE="${RESULTS_TABLE}| $rel_path | $clarity | $completeness | $actionability | $total |\n"
done

echo ""
echo "=== Quality Judge Summary ==="
echo "Skills judged: $TOTAL"
echo "Results: $RESULTS_DIR/results.jsonl"
echo ""

if [ -n "$RESULTS_TABLE" ]; then
  echo "| Skill | Clarity | Completeness | Actionability | Total |"
  echo "|-------|---------|--------------|---------------|-------|"
  printf "$RESULTS_TABLE"
fi

exit 0
