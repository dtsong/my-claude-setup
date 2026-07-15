# pipeline/shell-helpers.sh reference

Source, don't execute: `source pipeline/shell-helpers.sh` from repo root. Every function below is a thin wrapper around a `pipeline/scripts/*.py` or `pipeline/hooks/*.py` call; read the wrapped script if a function's output is confusing.

## Functions

**`skill-wc <file>`**
Prints word count and estimated token count (`words * 1.33`, the `TOKEN_RATIO` used everywhere in `pipeline/`) for one file. No exit-code contract, informational only.

**`skill-check <skill-dir>`**
Runs `pre-commit run --files <skill-dir>/**/*.md` scoped to one skill directory, so you don't wait on a full-repo `pre-commit run --all-files`. Exit code passes through pre-commit's own (0 = all hooks in scope passed, including warn-tier ones since pre-commit itself doesn't distinguish warn from hard, only the hook script's own exit code does).

**`skill-budget <file...>`**
Calls `python3 pipeline/hooks/check_token_budget.py <file...>` directly. Always exits 0 (warn-tier); read stderr for WARNING/INFO lines, don't trust the exit code.

**`skill-audit`**
Convenience bundle: runs the four hard pre-commit hooks plus the two warn hooks against changed files, then runs `budget-report.py` for a repo-wide summary in one shot. This is the fastest way to get both "did I break a hard gate" and "what's my budget headroom" without invoking five separate commands.

**`skill-load <suite-dir>`**
Calls `python3 pipeline/hooks/check_context_load.py <suite-dir>`. Same 5,500-token ceiling and same `budgets.json` override-matching behavior as the raw hook (see `validator-false-positives.md` for the override-path-mismatch bug affecting `soc-security`).

**`skill-new <name>`**
Copies `pipeline/templates/standalone-skill/` to `<name>-skill/` at **repo root** (not under `skills/`). This is the origin of the `*-skill/`-at-root layout convention that `context-load-analysis.py` and `check-regressions.py` (`pipeline/scripts/`) scan for and this repo's actual `skills/` monorepo tree does not follow.

**`skill-new-suite <name>`**
Same as `skill-new` but copies `pipeline/templates/skill-suite/` (coordinator + specialists layout) to `<name>-skill/` at repo root.

## The `*-skill/`-at-root convention, in full

`pipeline/templates/standalone-skill/` and `pipeline/templates/skill-suite/` are designed for a repo where each top-level skill or skill-suite lives at `<repo-root>/<name>-skill/`. That is a valid, supported layout for the pipeline tooling itself (it is how the pipeline's own eval/CI scripts were originally built and tested), but it is not how this repo organizes 123+ actual skills: they live under `skills/<name>/SKILL.md` or `skills/<suite>/<specialist>/SKILL.md`, with no `-skill` suffix and no repo-root placement.

Practical consequence: if you run `skill-new my-thing`, you get a working skill scaffold, but it lands in the wrong place for this repo's conventions and won't be found by `context-load-analysis.py`/`check-regressions.py` unless you either move it under `skills/` (recommended, matches every other skill in the repo) or manually invoke `check_context_load.py`/regression tooling with an explicit path.

Do not "fix" `find_skill_dirs()` in `pipeline/scripts/context-load-analysis.py` or `check-regressions.py` to scan `skills/` instead, without confirming intent first (route to mcs-failure-archaeology): it is unclear whether the `*-skill/`-at-root convention is deliberate pipeline-tooling design predating the `skills/` monorepo restructure, or simply unmaintained.
