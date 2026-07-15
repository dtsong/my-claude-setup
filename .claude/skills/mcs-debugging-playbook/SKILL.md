---
name: mcs-debugging-playbook
description: Use when a hook, gate, or check in this repo (my-claude-setup) seems armed but does nothing, or blocks when it shouldn't - a hook that should stop a tool call doesn't, TaskUpdate-to-completed is unexpectedly denied, /council's Workflow throws "requires args", /careful or /freeze does nothing, pre-commit fails on an untouched file, the openrouter MCP tool errors, or scripts/ recurses forever. Do NOT use for "has this been tried before" (mcs-failure-archaeology) or for measuring/profiling cost and reliability (mcs-diagnostics-and-tooling).
---

# mcs-debugging-playbook

## Overview

Every hook, gate, and pre-commit check in this repo has already failed silently at least once in its history (see incident SHAs below); the fixes converged on one rule: **a blocking hook must be `PreToolUse` + write to `stderr` + `exit 2`; anything else is logged and ignored.** This skill is a live-triage runbook: reproduce the failure with a hand-crafted stdin payload before theorizing, because the harness gives almost no other signal when a hook silently no-ops.

## When to use and when NOT to

Use when you have a concrete symptom right now: something didn't block that should have, something blocked that shouldn't have, or a tool/script errored. Work top-down through the triage table below, run the discriminating command, apply the fix.

Route instead to:
- **mcs-failure-archaeology**: "has this exact bug happened before", the full chronicle, reverted approaches.
- **mcs-diagnostics-and-tooling**: measuring token cost, trigger reliability, hook coverage; you already know it's broken and want numbers, not a fix.
- **mcs-architecture-contract**: WHY a design choice exists, not "why did it just fail".
- **mcs-change-control**: how to get a fix reviewed/merged once you have it.

## The three-step hook debugging recipe

Run these in order. Do not skip to step 3 (reading `settings.json`) first: a hook that is registered correctly but wrong internally looks identical, from the config, to one that works.

**Step 1: reproduce with a hand-crafted stdin payload.** Claude Code hooks read `{tool_name, tool_input, ...}` as JSON on stdin, not environment variables (this is the exact bug class that shipped and broke `careful-mode.sh`/`freeze-mode.sh`/`skill-telemetry.sh`: see Gotchas):
```bash
echo '{"tool_name":"TaskUpdate","tool_input":{"status":"completed","taskId":"99"}}' \
  | bash hooks/acceptance-gate.sh
```

**Step 2: check exit code AND which stream the message went to**, separately:
```bash
echo '{"tool_name":"TaskUpdate","tool_input":{"status":"completed","taskId":"99"}}' \
  | bash hooks/acceptance-gate.sh >/tmp/out.log 2>/tmp/err.log
echo "exit=$?  stdout_bytes=$(wc -c </tmp/out.log)  stderr_bytes=$(wc -c </tmp/err.log)"
```
Only `exit=2` on `PreToolUse`, with the message on stderr, denies the tool. `PostToolUse` is never blocking regardless of exit code or stream, because the tool already ran.

**Step 3: check registration**, not "does the file exist":
```bash
jq '.hooks.PreToolUse' settings.json          # PreToolUse hooks (settings.json)
jq '.hooks' hooks.json                        # hooks.json only wires PreCompact today
jq -r '.hooks.PreToolUse[].matcher' settings.json   # confirm the matcher (e.g. "TaskUpdate")
grep -rn "TOOL_NAME\|TOOL_INPUT" hooks/*.sh          # any script reading env vars instead of stdin is dead
```
Verified 2026-07-02: `hooks.json` registers only `PreCompact`; `settings.json` registers `PreToolUse`/`TaskUpdate` → `acceptance-gate.sh`, plus five events (`SessionStart`, `PostToolUse`, `PostToolUseFailure`, `Stop`, `SessionEnd`) → `telemetry-dispatch.sh`. `ARCHITECTURE.md`'s "Active Hooks" table lists only PreCompact: stale, don't trust it as an inventory.

## Symptom-to-triage table

Full repro transcripts for the two densest rows (openrouter error kinds, the soc-security pre-commit pair) live in `references/deep-dive-repros.md`: read it when the one-liners here aren't enough to fix the thing.

| Symptom | Root cause | Discriminating experiment | Fix |
|---|---|---|---|
| Hook seems armed, nothing blocked | Wrong event (`PostToolUse` fires after the tool ran), wrong exit code, or message on stdout not stderr | 3-step recipe above; `jq '.hooks.PreToolUse[].matcher' settings.json` | `PreToolUse` + stderr + `exit 2` (incident `605112d`) |
| `TaskUpdate → completed` unexpectedly denied | Correct behavior: a live contract has pending/failed criteria, unless it's a dead session's contract | `bash hooks/acceptance-gate.sh <<<'{"tool_name":"TaskUpdate","tool_input":{"status":"completed"}}'` shows which contract fired and its pending count | Resolve criteria, or wait out `ACCEPTANCE_GATE_STALE_HOURS` (72h default); never hand-edit contract rows |
| `/council` Workflow throws `requires args: sessionDir, idea, roster[]` | Conductor JSON-stringified `args`; destructuring a string yields `undefined` | `grep -n "typeof args === 'string'" skills/council/references/workflows/*.template.js` | Already tolerated (`01b6081`); if it still throws, the payload is double-encoded: log raw `args` before parsing |
| Edits to `~/.claude/skills/...`, `settings.json`, `hooks.json`, `hooks/`, `scripts/`, `workspaces/` seem to "also" hit the repo | Not a coincidence: each is a symlink into this repo's working tree | `readlink ~/.claude/skills` (this machine: resolves to `skills/` at repo root, NOT `.claude/skills/`) | Treat as a direct edit to live production config; no staging step exists |
| `mcp__openrouter__consult` errors or silently falls back | Four `error_kind` values conflated by callers checking only `"error"` | `[ -n "${OPENROUTER_API_KEY:-}" ] && echo set`; `test -x mcp/openrouter/.venv/bin/python && echo venv-ok` (venv gitignored) | Branch on `error_kind`, not `"error"` truthiness: see reference |
| `pre-commit` fails on a `.md` file you didn't touch, blaming a file under `skills/soc-security/skills/` | Two bugs in checks scanning soc-security's nested suite: see reference | `python3 pipeline/hooks/check_context_load.py skills/soc-security/SKILL.md` | See reference; do not raise the global budget ceiling to paper over it |
| `/careful` or `/freeze` says "ON" but blocks nothing | `enable` only writes a state file; no `PreToolUse` hook calls `check` | `grep -rn "careful-mode\|freeze-mode\|skill-telemetry" settings.json hooks.json .claude/settings.local.json` (expect none) | None until wired; treat both as inert |
| A hook wired from the careful/freeze/skill-telemetry template still no-ops after registering | Those scripts read `TOOL_NAME`/`TOOL_INPUT` env vars; the harness delivers stdin JSON | `TOOL_NAME=Bash bash hooks/careful-mode.sh check <<<'{"tool_name":"Bash"}'` passes trivially, ignoring the payload | Rewrite to `INPUT=$(cat)` + `jq -r` like `acceptance-gate.sh` (bug class of `6bc7c1a`) |
| Walking `scripts/` (`find`, `tar`, unguarded recursive grep) hangs | `scripts/scripts` is a self-referential symlink back to `scripts/` | `readlink scripts/scripts` | `find scripts -not -path '*/scripts/scripts*'`; don't delete without confirming no consumer (owner-unconfirmed) |
| `skills/council/registry.json` counts look wrong | Writes went uncommitted for months; one shared symlink serves every workspace, so another project's session can bump counters here | `git show HEAD:skills/council/registry.json \| python3 -c "import json,sys;d=json.load(sys.stdin);print(sum(s['uses'] for dep in d['departments'].values() for s in dep['skills'].values()))"` | Not project-scoped; a count with no matching `.claude/council/sessions/` dir is expected |

## Bash traps (WRONG vs RIGHT)

**1. `grep -c` inside `$(...) || echo 0`**: `grep -c` exits 1 (not just empty) on zero matches, so `|| echo 0` inside the substitution appends a SECOND line instead of substituting:
```bash
# WRONG: captures "0\n0" on zero matches, breaks downstream arithmetic:
PENDING=$(grep -c 'pattern' file.md || echo 0)

# RIGHT: || applies to the assignment, not to what's captured:
PENDING=$(grep -c 'pattern' file.md) || PENDING=0
```
Incident: `4bb8bf2` (2026-05-10): bypassed `acceptance-gate.sh`'s arithmetic, let unverified TaskUpdates through.

**2. `git commit --only -- <paths> -m <msg>`**: `--` ends option parsing, so `-m <msg>` after it becomes a pathspec, not a flag:
```bash
# WRONG: "-m" and the message become bogus pathspecs:
git commit --only -- path/to/file.md -m "message"

# RIGHT: all flags before the -- pathspec separator:
git commit --only -m "message" -- path/to/file.md
```
Incident: `memory/HANDOVER-2026-06-22-0036.md:31` (June 22 handover).

**3. Empty array expansion under `set -u` on macOS's default `/bin/bash` (3.2)**: bash 3.2 raises "unbound variable" on `"${arr[@]}"` for a zero-element array under `set -u`; bash 4+ does not:
```bash
# WRONG under /bin/bash 3.2 + set -euo pipefail, when the array stays empty:
local -a installed_pairs=()
write_manifest "$PRESET" "${installed_pairs[@]}"   # dies: unbound variable

# RIGHT: guard the expansion:
write_manifest "$PRESET" "${installed_pairs[@]+"${installed_pairs[@]}"}"
```
Live instance: `install.sh:377`, same line: hits this whenever zero links get installed and the script runs under `/bin/bash` (3.2.57 on this machine) rather than Homebrew bash (5.3.9, unaffected). Reproduced directly, both binaries.

## Gotchas

- **Fail-open is the house style, and that is itself a trap.** `acceptance-gate.sh` deliberately `exit 0`s on any jq/parse failure. If a gate seems to "never fire," rule out silent fail-open before assuming registration is broken.
- **`ARCHITECTURE.md`'s "Active Hooks" section is stale**: documents only `PreCompact`. Trust `jq '.hooks' settings.json hooks.json` over any doc.
- **`PostToolUse` is never blocking, regardless of exit code.** The tool already ran by the time it fires; a nonzero exit only logs an error. Blocking requires `PreToolUse`.
- **Do not "fix" a false pre-commit failure by raising the global ceiling.** See `references/deep-dive-repros.md`: the soc-security failure is a key-mismatch bug, not an under-sized budget: raising the default penalizes every other suite.
- **A clean `check_isolation.py` run on soc-security proves nothing.** It computes the wrong sibling set (see reference), so it can miss a real intra-suite cross-reference just as easily as it flags a fake one.
- **A commit message saying "Refs #NN" does not close the issue.** `605112d` fixed issue #53's bug but says "Refs," not "Fixes": verify issue state independently, don't infer closure from a fix landing.

## Provenance and maintenance

Last verified: 2026-07-02, branch `feat/61-permissions-rewrite` @ `105427a`, by direct reproduction of every command in this file and `references/deep-dive-repros.md` (hook stdin repros, pre-commit scripts run standalone, `find_sibling_specialists`/`get_context_ceiling` called directly, `openrouter_client.consult` called with the key unset, the `install.sh:377` empty-array class reproduced against both `/bin/bash` 3.2.57 and Homebrew bash 5.3.9).

Re-verification, one command per volatile fact:
- Hook registration: `jq '.hooks' settings.json hooks.json`
- Live contract pending count: `bash hooks/acceptance-gate.sh <<<'{"tool_name":"TaskUpdate","tool_input":{"status":"completed"}}'`
- Args JSON-stringify tolerance: `grep -n "typeof args === 'string'" skills/council/references/workflows/*.template.js`
- careful/freeze/skill-telemetry still unregistered: `grep -rn "careful-mode\|freeze-mode\|skill-telemetry" settings.json hooks.json .claude/settings.local.json` (expect none)
- `scripts/scripts` self-symlink: `readlink scripts/scripts`
- soc-security pre-commit bugs: see `references/deep-dive-repros.md`
- bash version on this machine: `/bin/bash --version | head -1` (3.2.x = trap applies)
