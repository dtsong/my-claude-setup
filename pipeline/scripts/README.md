# pipeline/scripts

Analysis and reporting utilities for the skill-governance pipeline. These are
read-only reports — the enforcing checks live in `pipeline/hooks/`.

## skill-audit.py

Tool-agnostic skill inventory audit. Reports the signals that hold for any
`SKILL.md`-based agent: duplicate detection, always-loaded description cost,
and an inventory summary.

```bash
# Audit this repo's skills/ (default)
python3 pipeline/scripts/skill-audit.py

# Audit one or more arbitrary roots; cross-root duplicate detection
python3 pipeline/scripts/skill-audit.py --root ~/.claude/skills --root ./skills

# Machine-readable output
python3 pipeline/scripts/skill-audit.py --json

# Tune the description-cost threshold and table size
python3 pipeline/scripts/skill-audit.py --desc-token-threshold 80 --top 15
```

| Flag | Default | Purpose |
|------|---------|---------|
| `--root` | repo `skills/` | Skill root to scan (repeatable). |
| `--desc-token-threshold` | `120` | Flag descriptions above this estimated token count. |
| `--top` | `20` | Max rows in the description-cost table. |
| `--follow-symlinks` | off | Descend into symlinked skill directories. |
| `--json` | off | Emit JSON instead of Markdown. |

Notes:
- Files reached through multiple roots/symlinks are de-duplicated by real path,
  so a symlinked root (e.g. `~/.claude/skills` → this repo) won't double-count.
- Token estimates use the pipeline's `TOKEN_RATIO` (1.33), consistent with
  `budget-report.py` and `pipeline/hooks/`.
- Duplicate clusters are reported, not auto-resolved: copies across
  tools/plugins are frequently intentional — confirm before deleting.

### Origin

The auditable *principles* (inventory, duplicate detection, always-loaded
description cost) are adapted from
[steipete/agent-scripts `skill-cleaner`](https://github.com/steipete/agent-scripts/tree/main/skills/skill-cleaner).
This reimplementation drops the Codex-specific pieces — `~/.codex` discovery,
the `models_cache.json` / gpt-5.5 token budget, and session-log usage scanning —
in favor of explicit roots and no environment assumptions.

## Other scripts

| Script | Purpose |
|--------|---------|
| `budget-report.py` | Per-file token budget table vs `pipeline/config/budgets.json`. |
| `context-load-analysis.py` | Worst-case simultaneous context load per suite. |
| `analyze-patterns.py` | Cross-skill structural pattern analysis. |
| `check-regressions.py` | Detect governance regressions between runs. |
| `check-token-budgets.sh` | Shell wrapper around budget enforcement. |
| `check-portability.sh` | Portability checks for skill packaging. |
| `validate-structure.sh` | Validate skill directory structure. |
| `judge-skill-quality.sh` | Heuristic skill-quality scoring. |
| `package-skill.sh` | Package a skill for distribution. |
| `run-evals.sh` | Run skill eval suites. |
