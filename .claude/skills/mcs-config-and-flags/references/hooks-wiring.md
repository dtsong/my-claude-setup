# Hook wiring: hooks.json + settings.json, both files

There are **two** files that register hooks in this repo, plus one file that is present on disk but registers nothing. A mid-level engineer reading only `ARCHITECTURE.md`'s "Active Hooks" table will miss most of this: that table lists only `PreCompact` and has not been updated since before the acceptance gate or telemetry dispatcher existed.

## hooks.json (repo root)

```json
{
  "hooks": {
    "PreCompact": [
      { "matcher": "auto", "hooks": [ { "type": "command",
        "command": "bash \"$HOME/.claude/hooks/pre-compact-handover.sh\"" } ] }
    ]
  }
}
```

One event, one hook. `$HOME/.claude/hooks/` is itself a symlink into this repo's `hooks/` directory (this machine, verified via `ls -la ~/.claude/hooks`). On auto-compaction only (`matcher: "auto"`), `pre-compact-handover.sh` tails the last 500 transcript lines and shells out to `claude -p --model sonnet` to synthesize a handover doc at `<workspace>/memory/HANDOVER-<timestamp>-auto.md`, with a minimal fallback if that invocation fails. It parses the hook's JSON input with grep/sed, not `jq`: no `jq` dependency for this one script.

Re-verify: `jq '.hooks' hooks.json`.

## settings.json hooks key (6 registrations, all production)

### PreToolUse → acceptance-gate.sh (the acceptance gate)

```json
"PreToolUse": [ { "matcher": "TaskUpdate", "hooks": [ { "type": "command",
  "command": "bash \"$HOME/Development/my-claude-setup/hooks/acceptance-gate.sh\"" } ] } ]
```

Fires only on `TaskUpdate` calls, and inside the script, only when `tool_input.status == "completed"`. Reads hook payload as **stdin JSON** via `jq` (`.tool_name`, `.tool_input`). Finds the active acceptance contract by scanning four candidate glob locations (`.claude/council/sessions/*/acceptance-contract.md`, `.claude/academy/sessions/*/acceptance-contract.md`, `.claude/prd/contract-*.md`, `.claude/acceptance-contract.md`) and picking the one with the **newest mtime**, not alphabetical order, not first match. Contracts untouched for `ACCEPTANCE_GATE_STALE_HOURS` (default `72`, env-overridable) are treated as abandoned and skipped, so a dead session can never block live work. Blocks by writing to **stderr** and exiting **2**, the only combination that actually blocks a `PreToolUse` hook in this harness. Anything printed to stdout or a non-2 exit is silently non-blocking (this exact bug shipped once, see the incident note below).

Re-verify: `jq '.hooks.PreToolUse' settings.json`; `grep -n 'STALE_HOURS\|exit 2' hooks/acceptance-gate.sh`.

### SessionStart / PostToolUse / PostToolUseFailure / Stop / SessionEnd → telemetry-dispatch.sh

All five events use the identical inline wrapper:

```bash
bash -c 'f="$HOME/Development/my-claude-setup/hooks/telemetry-dispatch.sh"; [ -f "$f" ] || exit 0; exec bash "$f"'
```
with a 10-second timeout. This is the US-001/#59 rewrite (PR #67, `c562ab8`), replacing a direct call to a script living in the private sibling repo (`~/Development/my-claude-setup-private/hooks/session_telemetry.py`). `hooks/telemetry-dispatch.sh` is the fail-soft dispatcher, ~30 lines:

- Resolves the real telemetry script via `CLAUDE_TELEMETRY_HOOK` env var, defaulting to `$HOME/Development/my-claude-setup-private/hooks/session_telemetry.py` (this machine only).
- If the resolved path is unreadable: exits `0` silently on a fresh clone (no private repo, no env var set); warns on stderr but still exits `0` if `CLAUDE_TELEMETRY_HOOK` was explicitly set to a bad path, or if the private repo directory exists but the hook file inside it is missing.
- If `python3` is missing: warns on stderr, exits `1` (non-blocking, visible).
- If the child `session_telemetry.py` exits non-zero: warns on stderr, exits `1`. Never propagates the child's raw exit code, and **never** exits `2` (would block `TaskUpdate`-adjacent flows and, worse, would block `Stop`, preventing Claude from stopping).

Re-verify: `jq '.hooks.SessionStart' settings.json` (all 5 events share the same command string); `cat hooks/telemetry-dispatch.sh`; `printenv CLAUDE_TELEMETRY_HOOK` (expect unset by default).

## Present on disk, registered nowhere (decorative)

`hooks/careful-mode.sh`, `hooks/freeze-mode.sh`, `hooks/skill-telemetry.sh` exist in the repo but do not appear in `settings.json`, `hooks.json`, or `.claude/settings.local.json` (confirmed by grepping all three files for each script name, zero matches, 2026-07-02). `commands/careful.md` and `commands/freeze.md` only invoke each script's `enable` subcommand, which writes a state file (e.g. `~/.claude/.careful-mode`); nothing ever invokes the `check` subcommand that would consult that file. Even if wired as a `PreToolUse` hook today, all three scripts read `TOOL_NAME`/`TOOL_INPUT` from **environment variables**, while the current hook payload contract delivers stdin JSON (the exact bug class the acceptance gate was fixed for), so registering them as-is would still no-op.

Consequence: `scripts/skill-usage-report.sh` reads `~/.claude/telemetry/skill-usage.jsonl`, which nothing currently writes.

Re-verify: `grep -rn "careful-mode.sh\|freeze-mode.sh\|skill-telemetry.sh" settings.json hooks.json .claude/settings.local.json` (expect no output).

## Incident history (pointer, not detail)

Two prior acceptance-gate incidents (a `grep -c` arithmetic bug in `4bb8bf2`, and a PostToolUse/stdout/exit-1 mis-registration in `605112d`, issue #53) shaped the current stderr+exit-2+PreToolUse contract encoded in the script's own header comment. Full incident narrative belongs to `mcs-failure-archaeology`; this file only documents the wiring as it stands today.
