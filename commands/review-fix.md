---
description: "Review current branch, auto-fix Critical/Important findings, re-review until clean."
argument-hint: "[--max-cycles N] [--auto-only] [--no-gates]"
allowed-tools: Bash(git add:*), Bash(git commit:*), Bash(git diff:*), Bash(git status:*), Bash(git log:*), Bash(git push:*), Bash(git fetch:*), Bash(git rebase:*), Bash(git branch:*), Bash(npm:*), Bash(npx:*), Bash(uv:*), Bash(pytest:*), Bash(source ~/.nvm/nvm.sh:*), Read, Edit, Write, Glob, Grep, Skill
---

# /review-fix — Review-Fix Loop

Review the current branch, auto-fix Critical/Important findings, and re-review until clean or max cycles exhausted.

## Usage

```
/review-fix                    # Default: 3 cycles, full fixes, gates enabled
/review-fix --max-cycles 5     # Up to 5 review iterations
/review-fix --auto-only        # Only mechanical fixes, skip judgment calls
/review-fix --no-gates         # Skip quality gate re-runs after fixes
```

## Step 1: Parse Arguments

Extract from `$ARGUMENTS`:
- `--max-cycles N` (default: 3)
- `--auto-only` flag (skip ASK items)
- `--no-gates` flag (skip quality gates)

## Step 2: Auto-Detect Quality Gates

Skip this step if `--no-gates` is set.

```bash
WORKSPACE="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
```

Detect gates in order: **build → typecheck → lint → test**

| Stack | Detection | Gates |
|-------|-----------|-------|
| **Node.js** | `package.json` exists | `npm run build` (if scripts.build), `npx tsc --noEmit` (if tsconfig.json), `npm run lint` (if scripts.lint), `npm test` (if scripts.test) |
| **Python** | `pyproject.toml` exists | `ruff check .`, `ruff format --check .`, `pytest`, `mypy .` (if mypy in deps) |
| **Go** | `go.mod` exists | `go build ./...`, `go vet ./...`, `go test ./...` |
| **Rust** | `Cargo.toml` exists | `cargo build`, `cargo clippy -- -D warnings`, `cargo test` |

**Node.js commands** must be wrapped: `source ~/.nvm/nvm.sh && nvm use default --silent && <cmd>`

Verify each gate runs successfully. Remove any that fail with "command not found" and warn.

## Step 3: Review Loop

For each cycle (1 to max-cycles):

1. **Review**: Invoke `/pr-review-toolkit:review-pr all` via the Skill tool
2. **Parse**: Extract severity counts per `commands/references/ship-review-rules.md`:
   - `## Critical Issues (N found)` → N critical
   - `## Important Issues (N found)` → N important
3. **Check**: If 0 critical AND 0 important → **PASS**, break to Step 4
4. **Classify** each finding as AUTO-FIX or ASK per `commands/references/ship-review-rules.md § Fix-First Classification`
5. **Auto-fix**: Apply all AUTO-FIX items (critical first, then important). Commit:
   ```bash
   git add <changed-files>
   git commit -m "fix: auto-fix review findings (cycle $CYCLE/$MAX_CYCLES)"
   ```
6. **Ask** (skip if `--auto-only`): Batch all ASK items into one AskUserQuestion:
   ```
   Review found N findings requiring your judgment:
   1. [finding] — Options: A) ... B) ... [Recommended: A]
   Reply with your choices or 'skip all' to defer.
   ```
   Apply approved fixes. Commit:
   ```bash
   git add <changed-files>
   git commit -m "fix: address review findings (cycle $CYCLE/$MAX_CYCLES)"
   ```
7. **Gates** (skip if `--no-gates`): Re-run all detected quality gates in order. If any fail, fix and re-run once.
8. **Push**: `git push origin HEAD`
9. **Log**: Print cycle summary — critical/important counts, fixes applied, outcome
10. **Clear context**: Run `/compact` to clear conversation context before the next cycle. This ensures each review pass starts fresh and can catch issues that stale context would miss.
11. **Continue** to next cycle, or if max cycles reached → **FAIL**

## Step 4: Report

Print final summary:

```
Review-Fix Summary
──────────────────
| Cycle | Critical | Important | Auto-Fixed | Asked | Outcome |
|-------|----------|-----------|------------|-------|---------|
| 1     | 3        | 5         | 4          | 2     | FAIL    |
| 2     | 0        | 1         | 1          | 0     | FAIL    |
| 3     | 0        | 0         | —          | —     | PASS    |

Verdict: PASS (clean after 3 cycles)
```

If FAIL after max cycles, list remaining Critical/Important findings.

## Rules

- Fix critical findings before important ones within each cycle
- Re-run ALL quality gates after every fix round (unless `--no-gates`)
- Node.js commands wrapped with nvm per CLAUDE.md
- Never exceed max-cycles — mark FAIL and report remaining issues
- See `commands/references/ship-review-rules.md` for full parsing and classification rules
