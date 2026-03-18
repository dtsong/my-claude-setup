#!/usr/bin/env bash
set -euo pipefail

# skill-scorecard.sh — Audit skills against best practices
# Usage: skill-scorecard.sh [skills-dir]
# Outputs per-skill health scores

SKILLS_DIR="${1:-$(dirname "$0")/../skills}"
SKILLS_DIR=$(cd "$SKILLS_DIR" && pwd)

TOTAL_SKILLS=0
TOTAL_SCORE=0

echo "=== Skill Health Scorecard ==="
echo "Directory: $SKILLS_DIR"
echo ""
printf "%-35s %5s %7s %5s %7s %5s %5s %6s\n" "SKILL" "GOTCH" "DESCR" "EVALS" "SCRIPTS" "ASSETS" "SCOPE" "SCORE"
printf "%-35s %5s %7s %5s %7s %5s %5s %6s\n" "-----" "-----" "-------" "-----" "-------" "-----" "-----" "------"

for skill_dir in "$SKILLS_DIR"/*/; do
  [[ ! -d "$skill_dir" ]] && continue
  SKILL_FILE="$skill_dir/SKILL.md"
  [[ ! -f "$SKILL_FILE" ]] && continue

  SKILL_NAME=$(basename "$skill_dir")
  SCORE=0
  MAX_SCORE=6

  # 1. Gotchas section (+1)
  GOTCHAS="--"
  if grep -q "## Gotchas" "$SKILL_FILE" 2>/dev/null; then
    GOTCHAS="YES"
    SCORE=$((SCORE + 1))
  fi

  # 2. Description quality (+1 if >= 20 words)
  DESC_QUALITY="--"
  DESC=$(grep "^description:" "$SKILL_FILE" 2>/dev/null | head -1 | sed 's/^description:\s*//' | tr -d '"')
  WORD_COUNT=$(echo "$DESC" | wc -w | tr -d ' ')
  if [[ "$WORD_COUNT" -ge 20 ]]; then
    DESC_QUALITY="OK($WORD_COUNT)"
    SCORE=$((SCORE + 1))
  elif [[ "$WORD_COUNT" -gt 0 ]]; then
    DESC_QUALITY="SHORT($WORD_COUNT)"
  fi

  # 3. Eval cases (+1)
  EVALS="--"
  if [[ -d "$skill_dir/eval-cases" ]] && ls "$skill_dir/eval-cases/"*.json &>/dev/null; then
    EVAL_COUNT=$(jq 'length' "$skill_dir/eval-cases/"*.json 2>/dev/null | paste -sd+ - | bc 2>/dev/null || echo 0)
    EVALS="YES($EVAL_COUNT)"
    SCORE=$((SCORE + 1))
  fi

  # 4. Helper scripts (+1)
  SCRIPTS="--"
  if [[ -d "$skill_dir/scripts" ]] && ls "$skill_dir/scripts/"*.sh &>/dev/null; then
    SCRIPT_COUNT=$(ls "$skill_dir/scripts/"*.sh 2>/dev/null | wc -l | tr -d ' ')
    SCRIPTS="YES($SCRIPT_COUNT)"
    SCORE=$((SCORE + 1))
  fi

  # 5. Template assets (+1)
  ASSETS="--"
  if [[ -d "$skill_dir/assets" ]] && ls "$skill_dir/assets/"* &>/dev/null; then
    ASSET_COUNT=$(ls "$skill_dir/assets/"* 2>/dev/null | wc -l | tr -d ' ')
    ASSETS="YES($ASSET_COUNT)"
    SCORE=$((SCORE + 1))
  fi

  # 6. Scope constraints section (+1)
  SCOPE="--"
  if grep -q "## Scope Constraints" "$SKILL_FILE" 2>/dev/null; then
    SCOPE="YES"
    SCORE=$((SCORE + 1))
  fi

  PERCENT=$((SCORE * 100 / MAX_SCORE))
  printf "%-35s %5s %7s %5s %7s %5s %5s %5d%%\n" "$SKILL_NAME" "$GOTCHAS" "$DESC_QUALITY" "$EVALS" "$SCRIPTS" "$ASSETS" "$SCOPE" "$PERCENT"

  TOTAL_SKILLS=$((TOTAL_SKILLS + 1))
  TOTAL_SCORE=$((TOTAL_SCORE + PERCENT))
done

echo ""
if [[ $TOTAL_SKILLS -gt 0 ]]; then
  AVG=$((TOTAL_SCORE / TOTAL_SKILLS))
  echo "Total skills: $TOTAL_SKILLS"
  echo "Average health: ${AVG}%"
else
  echo "No skills found."
fi
