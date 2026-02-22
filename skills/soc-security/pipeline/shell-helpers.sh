#!/usr/bin/env bash
# Skill Governance Shell Helpers
# Source this in your shell profile: source /path/to/pipeline/shell-helpers.sh

# Quick word/token count for a file
skill-wc() {
    local file="$1"
    if [ -z "$file" ]; then
        echo "Usage: skill-wc <file>" >&2
        return 1
    fi
    local words
    words=$(wc -w < "$file" 2>/dev/null)
    if [ $? -ne 0 ]; then
        echo "Error: cannot read $file" >&2
        return 1
    fi
    local tokens=$(( words * 133 / 100 ))
    echo "$file: $words words (~$tokens tokens)"
}

# Run all pre-commit checks on a specific skill directory
skill-check() {
    local skill_dir="$1"
    if [ -z "$skill_dir" ]; then
        echo "Usage: skill-check <skill-directory>" >&2
        return 1
    fi
    local files=""
    if [ -f "$skill_dir/SKILL.md" ]; then
        files="$skill_dir/SKILL.md"
    fi
    for ref in "$skill_dir"/references/*.md; do
        if [ -f "$ref" ]; then
            files="$files $ref"
        fi
    done
    if [ -z "$files" ]; then
        echo "No SKILL.md or reference files found in $skill_dir" >&2
        return 1
    fi
    pre-commit run --files $files
}

# Run budget check on specific files
skill-budget() {
    if [ $# -eq 0 ]; then
        echo "Usage: skill-budget <file> [file...]" >&2
        return 1
    fi
    python3 pipeline/hooks/check_token_budget.py "$@"
}

# Create a new standalone skill from template
skill-new() {
    local name="$1"
    if [ -z "$name" ]; then
        echo "Usage: skill-new <skill-name>" >&2
        return 1
    fi
    local dest="${name}-skill"
    if [ -d "$dest" ]; then
        echo "Error: $dest already exists" >&2
        return 1
    fi
    cp -r pipeline/templates/standalone-skill "$dest"
    # Use perl for cross-platform sed compatibility
    perl -pi -e "s/SKILL_NAME/$name/g" "$dest/SKILL.md" "$dest/eval-cases/evals.json"
    echo "Created skill scaffold at $dest"
    echo "Next: edit $dest/SKILL.md and run skill-check $dest"
}

# Create a new skill suite from template
skill-new-suite() {
    local name="$1"
    if [ -z "$name" ]; then
        echo "Usage: skill-new-suite <suite-name>" >&2
        return 1
    fi
    local dest="${name}-skill"
    if [ -d "$dest" ]; then
        echo "Error: $dest already exists" >&2
        return 1
    fi
    cp -r pipeline/templates/skill-suite "$dest"
    perl -pi -e "s/SUITE_NAME/$name/g" "$dest/SKILL.md" "$dest/eval-cases/evals.json"
    echo "Created skill suite scaffold at $dest"
    echo "Next: edit $dest/SKILL.md and run skill-check $dest"
}

# Full compliance audit — hard checks then advisory checks
skill-audit() {
    echo "=== Skill Compliance Audit ==="
    echo ""
    echo "--- Hard Checks (structural integrity) ---"
    pre-commit run skill-frontmatter --all-files
    pre-commit run skill-references --all-files
    pre-commit run skill-isolation --all-files
    pre-commit run skill-context-load --all-files
    local hard_status=$?
    echo ""
    echo "--- Advisory Checks (quality guidance) ---"
    pre-commit run skill-token-budget --all-files
    pre-commit run skill-prose-check --all-files
    echo ""
    echo "=== Budget Report ==="
    python3 pipeline/scripts/budget-report.py
    echo ""
    echo "=== Audit Complete ==="
    return $hard_status
}

# Show context load breakdown for a suite
skill-load() {
    local suite_dir="$1"
    if [ -z "$suite_dir" ]; then
        echo "Usage: skill-load <suite-directory>" >&2
        return 1
    fi
    if [ ! -d "$suite_dir/skills" ]; then
        echo "Error: $suite_dir is not a skill suite (no skills/ subdirectory)" >&2
        return 1
    fi
    local files=""
    for f in $(find "$suite_dir" \( -name "SKILL.md" -o -path "*/references/*.md" \) -not -path "*/eval-cases/*"); do
        files="$files $f"
    done
    if [ -z "$files" ]; then
        echo "No skill files found in $suite_dir" >&2
        return 1
    fi
    python3 pipeline/hooks/check_context_load.py $files
}
