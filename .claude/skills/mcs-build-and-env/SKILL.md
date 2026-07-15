---
name: mcs-build-and-env
description: Use when setting up my-claude-setup on a bare macOS machine, running or scripting install.sh (presets, flags, --uninstall, --dry-run, --conflict-policy), bootstrapping the mcp/openrouter venv, diagnosing "command not found", missing-symlink, or manifest errors during install, or verifying a fresh clone is healthy before first use. Not for day-to-day running of /council, /ship, or /looper (see mcs-run-and-operate) or for settings.json axis semantics and hook wiring (see mcs-config-and-flags).
---

# mcs-build-and-env

## Overview

my-claude-setup has no build step: `install.sh` only creates symlinks from this
repo into `~/.claude/`, plus an opt-in manifest for clean uninstall.
"Environment health" means three things: prerequisite binaries on `PATH`, the
symlink tree `install.sh` creates, and one manual bootstrap step
(`mcp/openrouter`'s venv) that `install.sh` does not perform. All facts below
verified 2026-07-02 against a live checkout; re-verify commands in Provenance.

## When to use and when NOT to

Use for: fresh-machine setup, `install.sh` flag/preset questions, the
`--uninstall` trap, `mcp/openrouter` bootstrap, and pre-flight health checks
(pre-commit, skill audit, syntax checks).

Route elsewhere:
- Running `/council`, `/ship`, `/looper`, `/handover` day to day → **mcs-run-and-operate**.
- What each `settings.json` key/hook means, or why a hook is wired the way it is → **mcs-config-and-flags**.
- A specific broken hook or command mid-session → **mcs-debugging-playbook**.
- "Has this failure mode been hit before" → **mcs-failure-archaeology**.

## Step 1: Prerequisites (verified 2026-07-02, this machine's actual versions)

| Tool | Why it's needed | Version here | Note |
|---|---|---|---|
| Claude Code CLI | runs the harness | 2.1.198 | `/council`'s Workflow backend needs **≥ 2.1.154** (`commands/_council-engine.md:39`); below that it degrades to agent-teams/sequential, not a hard failure. |
| git | workspace auto-detection, clone | 2.50.1 | README's only stated prerequisite besides Claude Code. |
| python3 | **hard, undocumented** dep of `install.sh` (CSV split, manifest read/write, uninstall) and every `pipeline/hooks|scripts/*.py` | 3.14.4 (Homebrew) | Missing from README Prerequisites; without it `install.sh` dies mid-run. |
| pre-commit | governance hooks (`.pre-commit-config.yaml`) | 4.6.0 (Homebrew, own interpreter) | Only needed to commit to `skills/**`/`hooks/**`, not to run the harness. |
| jq | hard dep of `hooks/acceptance-gate.sh` (stdin JSON) | 1.8.1 | Only exercised if hooks are installed (`--preset full` or `--with-hooks-*`) and fires only on `TaskUpdate`. |
| bun | runs `claude-hud`, wired as `statusLine` | 1.3.6 at `~/.bun/bin/bun` | Only needed with `--with-settings`; path is hardcoded in `settings.json`. |
| nvm + node | **not** a repo prerequisite; owner's personal convention (`~/.claude/CLAUDE.md`: `source ~/.nvm/nvm.sh && nvm use default --silent` before any node/npm/npx) | nvm 0.40.3, node v20.20.0 | Only matters for `/new-typescript`, `/new-mcp-server` scaffolds; repo ships no Node build itself. |

## Step 2: install.sh anatomy

`install.sh` is `#!/bin/bash`, `set -euo pipefail`, 496 lines. Three presets,
strictly additive:

| Preset | Links | Default? |
|---|---|---|
| `skills` | every dir under `skills/` (except one literally named `skills`, see Gotchas) into `~/.claude/skills/<pack>` | yes, default |
| `core` | `skills` + every `commands/*.md` and `agents/*.md`, individually | no |
| `full` | `core` + every `scripts/*.sh`, `hooks/*.sh`, and every entry under `workspaces/` | no |

Config files (`settings.json`, `hooks.json`, `CLAUDE.md`) are **opt-in only**,
regardless of preset (`--with-settings`, `--with-hooks-json`,
`--with-hooks-scripts`, `--with-claude-md`). `--conflict-policy fail|skip`
(default `fail`) governs what happens when a target already exists and is not
a symlink. `--dry-run` prints the plan and exits 0 before any writes. Full
flag table, manifest JSON schema, and legacy-cleanup list:
`references/install-flags.md`.

`--uninstall` **must be the first CLI argument**: `main()` only special-cases
`"${1:-}" == "--uninstall"`; anywhere else it falls into the option parser and
dies with `Unknown option: --uninstall`. Verified:
```bash
./install.sh --preset full --uninstall   # Error: Unknown option: --uninstall
./install.sh --uninstall                 # works
```
This machine's own `~/.claude` symlinks predate the manifest system (no
`.managed/my-claude-setup.json` exists here, this-machine-only). `--uninstall`
still handles it via the legacy-cleanup path (`references/install-flags.md`).

## Step 3: Post-install bootstrap this repo needs beyond install.sh

None of this is performed by `install.sh`. Do it after any install that
touches these areas:

1. **pre-commit hooks** (only if you'll commit to `skills/**`, `hooks/**`, etc.
   in *this* repo). Undocumented as of 2026-07-02 (no doc mentions
   `pre-commit install`):
   ```bash
   pre-commit install --hook-type pre-commit --hook-type commit-msg
   ```
   `commit-msg` needs its own `--hook-type` flag: `check_commit_msg.py` is
   wired at `stages: [commit-msg]`, and a plain `pre-commit install` only
   installs the `pre-commit` stage.

2. **`mcp/openrouter` venv** (required only for the OpenRouter MCP server;
   `settings.json.mcpServers.openrouter.command` is a hardcoded path into this
   venv, `FileNotFoundError` without it). Verified working 2026-07-02:
   ```bash
   python3 -m venv mcp/openrouter/.venv
   mcp/openrouter/.venv/bin/pip install -r mcp/openrouter/requirements.txt
   export OPENROUTER_API_KEY=sk-or-...   # shell env only, never committed
   ```
   Trap: `requirements.txt` (`mcp>=1.2.0` only) does **not** include `pytest`.
   The README's test command (`python3 -m pytest .`) fails with
   `No module named pytest` until you also
   `mcp/openrouter/.venv/bin/pip install pytest` (31 pass + 1 skip without a
   live key, confirmed here).

3. **`OPENROUTER_API_KEY`**: unset in this shell as of 2026-07-02. Fail-soft:
   every call degrades to `{"error_kind": "missing_key", "fallback": "claude"}`
   instead of raising, so the harness works without it, just without
   OpenRouter routing.

4. **Optional private sibling repo `my-claude-setup-private`** (this machine
   only: `~/Development/my-claude-setup-private`, plus a second sibling
   `~/Development/llm/skills/skill-governance`). Backs 8 content symlinks
   (verified live here) that degrade to a harmless `MISSING` path without it,
   and backed the 5 telemetry hook events before issue #59 landed a fail-soft
   dispatcher (`hooks/telemetry-dispatch.sh`) that now no-ops cleanly when the
   private repo is missing. Full table and before/after #59:
   `references/private-repo-symlinks.md`.

## Gotchas

- **bash 3.2 empty-array trap (install.sh:377 class).** macOS's `/bin/bash`
  (the shebang target, regardless of a newer Homebrew bash on `PATH`) is
  3.2.57. Under `set -u`, `"${installed_pairs[@]}"` on an empty array is an
  **unbound variable** error on bash < 4.4, reachable whenever every planned
  link already conflicts under `--conflict-policy skip`. Reproduced live
  2026-07-02: `installed_pairs[@]: unbound variable`, exit 1. Not covered by
  CI (the smoke test never drives every target into conflict). WRONG: assume
  `--conflict-policy skip` always exits 0. RIGHT: treat that exit 1 as this
  trap, not a real crash: resolve conflicts first or use
  `--conflict-policy fail`.
- **Editing this repo edits your live global Claude Code config.**
  `~/.claude/settings.json`, `hooks.json`, `CLAUDE.md`, `commands`, `agents`,
  `hooks`, `scripts`, `workspaces` are symlinks into this checkout on this
  machine. There is no staging copy: a bad edit is live on the next config read.
- **Self-referential symlinks are real and gitignored, not a hallucination.**
  `commands/commands -> commands/` and `scripts/scripts -> scripts/` exist on
  disk, untracked (`.gitignore:36`, `:39`). `find`/`ls -R` without symlink
  guards will loop.
- **The skill-pack loop skips a directory literally named `skills`.**
  `[[ "$(basename "$d")" == "skills" ]] && continue` in both
  `list_skill_packs()` and `collect_links_for_preset()`: intentional
  self-symlink guard; a pack you name `skills` will silently never install.
- **`.gitignore`'s private-symlink list is aspirational, not current state.**
  4 of its entries (`skills/council/{chronicler,operator,oracle}/...`) do not
  exist on this machine as of 2026-07-02, so don't infer a symlink is live
  from the `.gitignore` entry alone; check `[ -L <path> ]` (`references/private-repo-symlinks.md`).
- **README's own Prerequisites section is incomplete.** It lists only Claude
  Code CLI + `CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1` + git. python3, jq,
  pre-commit, and bun are real hard-or-conditional dependencies documented
  nowhere in README; use the table in Step 1 instead.
- **CI only smoke-tests `skills` and `core` presets**, not `full`. See
  `references/install-flags.md` for exactly what CI does and doesn't cover.
- **`mcp/openrouter/.venv` is configuration, not build junk.** It's the exact
  interpreter `settings.json` invokes; deleting it as "clean up caches" breaks
  the MCP server with `FileNotFoundError` on next launch.

## Step 4: Verification checklist

Run in order; none of these mutate `~/.claude/` or git state.

```bash
# 1. Syntax-check every shell entry point (matches CI exactly)
bash -n install.sh
bash -n hooks/*.sh
bash -n scripts/*.sh

# 2. JSON sanity on the two opt-in config files
python3 -m json.tool settings.json >/dev/null
python3 -m json.tool hooks.json >/dev/null

# 3. Installer dry-run against an isolated target (never touches ~/.claude)
CLAUDE_DIR=/tmp/mcs-check ./install.sh --dry-run --preset core

# 4. Skill governance gate (what pre-commit will run on skills/**)
pre-commit run --all-files
# EXPECTED on a clean 2026-07-02 checkout: all hooks Passed. skill-token-budget
# and skill-prose-check are warn-tier and print advisories without failing --
# e.g. skills/data-engineering-skills/ai-data-integration (10 words over
# target) and skills/language-conventions/references/typescript.md (25 words
# over target). Pre-existing, not new breakage.

# 5. Cross-root skill audit (duplicate names/descriptions, oversized descriptions)
python3 pipeline/scripts/skill-audit.py --json
# EXPECTED: "over_threshold", "duplicate_names", "identical_bodies" stay
# empty/[] on a healthy tree; skill_count grows as skills are added.
```

A **hard**-tier failure in step 4 (any hook in `.pre-commit-config.yaml`
without `(warn)` in its name, e.g. the skill-governance checks,
`settings-schema`, `model-routing`) is real breakage, not expected noise.
See mcs-config-and-flags for what each check enforces.

## Provenance and maintenance

Last verified 2026-07-02, branch `feat/61-permissions-rewrite`. Drifts fastest:
prerequisite versions, `install.sh` line numbers, which private symlinks
currently resolve. Re-verify:

- Versions: `claude --version; git --version; python3 --version; jq --version; bun --version; pre-commit --version`
- Workflow-tool floor: `grep -n "2.1.154" commands/_council-engine.md`
- Empty-array trap line: `grep -n "installed_pairs" install.sh`
- CI preset coverage: `grep -n "preset" .github/workflows/validate.yml`
- Live private symlinks: `for p in skills/ece skills/heavy-file-ingestion skills/research-consulting-skills skills/resume-tailor skills/soc-security commands/analyze-workflow.md commands/ece.md commands/tailor.md; do [ -L "$p" ] && echo "LIVE $p"; done`
- OPENROUTER_API_KEY presence: `[ -n "${OPENROUTER_API_KEY:-}" ] && echo set || echo unset`
- mcp/openrouter tests: `cd mcp/openrouter && .venv/bin/python -m pytest . -q` (needs `pip install pytest` first, Step 3)
- Governance ceiling: `grep -n max_simultaneous_tokens pipeline/config/budgets.json`
