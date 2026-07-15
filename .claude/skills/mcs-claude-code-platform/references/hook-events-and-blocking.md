# Hook Events and Blocking Semantics (Deep Reference)

Verified against `settings.json`, `hooks.json`, and `hooks/*.sh` on 2026-07-02, HEAD `105427a`.

## Every hook event registered in this repo

| Event | File | Matcher | Script | Payload read via | Purpose |
|---|---|---|---|---|---|
| `PreToolUse` | `settings.json:61-71` | `"TaskUpdate"` | `hooks/acceptance-gate.sh` | stdin JSON, `jq` | Block `TaskUpdate → completed` when an acceptance contract has unverified criteria |
| `SessionStart` | `settings.json:72-83` | `""` (all) | `hooks/telemetry-dispatch.sh` | argv/stdin passthrough to the private hook | Fire-and-forget session telemetry |
| `PostToolUse` | `settings.json:84-95` | `""` (all) | `hooks/telemetry-dispatch.sh` | same | Fire-and-forget per-tool-call telemetry |
| `PostToolUseFailure` | `settings.json:104-112` | `""` (all) | `hooks/telemetry-dispatch.sh` | same | Fire-and-forget failure telemetry: registered here and present in this repo's own settings schema enum (`pipeline/config/settings.schema.json:28`, added by the settings-schema-guard work, as of 2026-07-05); **event name not independently confirmed against platform docs in this session**, re-verify: `grep -n PostToolUseFailure pipeline/config/settings.schema.json settings.json` |
| `Stop` | `settings.json:108-119` | `""` (all) | `hooks/telemetry-dispatch.sh` | same | Fire-and-forget session-stop telemetry |
| `SessionEnd` | `settings.json:120-131` | `""` (all) | `hooks/telemetry-dispatch.sh` | same | Fire-and-forget session-end telemetry |
| `PreCompact` | `hooks.json:1-13` | `"auto"` | `hooks/pre-compact-handover.sh` | stdin JSON, grep/sed | Synthesize a handover doc before automatic context compaction |

Not used anywhere in this repo (as of 2026-07-02): `UserPromptSubmit`, `Notification`, or any regex/pipe matcher syntax. Don't assume this repo demonstrates those: it doesn't.

## The blocking-semantics rule, in full

The one rule that matters, stated once, precisely: **a hook only blocks the tool call it fired on if it is registered on `PreToolUse`, writes its reason to stderr, and exits with code `2`.** Everything else is either a side effect (most events here) or a logged-but-ignored error.

- `PreToolUse` + exit `2` + stderr → tool is denied, Claude sees the stderr text as the reason.
- `PreToolUse` + any other non-zero exit → non-blocking hook error; the harness logs it, the tool still runs.
- `PostToolUse` + any exit code, any stream → **cannot** block, structurally: the tool already executed before this hook fires. There is nothing left to deny. A team member who wires a "blocking" check on `PostToolUse` has built a logger, not a gate, no matter what exit code or stream they use.
- `PreCompact`, `SessionStart`, `Stop`, `SessionEnd` in this repo are all side-effect-only (telemetry, handover generation); none of them gate anything here, and there's no repo evidence any of them *can* gate a subsequent action the way `PreToolUse` gates its own tool call.

### The `605112d` incident, verbatim mechanism

`acceptance-gate.sh` was originally registered as `PostToolUse`, and its block logic printed to **stdout** and exited **1**. Per the rule above, that is doubly non-blocking: wrong event (`PostToolUse` can't block at all) and wrong signal even if it had been `PreToolUse` (stdout + exit 1 is a logged error, not a denial). The fix (commit `605112d`, 2026-06-22, refs #53) moved the same logic to `PreToolUse` on matcher `TaskUpdate`, redirected all output to stderr (`exec 1>&2` at `acceptance-gate.sh:90`), and exits `2` on block. Current header comment (`acceptance-gate.sh:7-10`) states the lesson directly: "PreToolUse + exit 2 prevents the TaskUpdate from running; any other non-zero is a non-blocking error, so the block message MUST go to stderr with exit 2: never stdout with exit 1."

### The `4bb8bf2` incident, verbatim mechanism

`grep -c pattern file` exits `1` (not `0`) when there are zero matches: this is standard `grep` behavior, not a bug. The original code did:

```bash
# WRONG: grep -c exits 1 on zero matches, so this whole subshell's exit
# status makes `|| echo 0` fire, but it fires *inside* the command
# substitution and appends a second "0" string to the captured value.
PENDING=$(grep -c '| pending |' "$CONTRACT" || echo 0)
```

When there are zero matches, `grep -c` prints `0` to stdout *and* exits 1, so `|| echo 0` still runs and appends a second `0`, producing the two-line string `"0\n0"` inside `PENDING`. Subsequent arithmetic (`$((PENDING + FAILED))`) then fails or behaves unpredictably, and the gate could be bypassed via a hook execution error rather than an explicit pass. Fixed pattern, current code (`acceptance-gate.sh:79-82`):

```bash
# RIGHT: assign the fallback in a separate clause outside the substitution.
PENDING=$(grep -c '| pending |' "$CONTRACT" 2>/dev/null) || PENDING=0
```

This pattern generalizes: never use `$(cmd || fallback)` when `cmd`'s own stdout is part of what you're capturing and `cmd` can legitimately exit non-zero while still printing valid output (this is exactly `grep -c`'s contract). Assign the fallback outside the substitution instead.

## Payload delivery: stdin JSON, not env vars

Every hook Claude Code invokes for `PreToolUse`/`PostToolUse`/`PreCompact`/etc. receives a single JSON document on stdin (fields typically include `tool_name`, `tool_input`, `transcript_path`, `cwd`, `trigger`, depending on event). This repo has two live scripts that correctly read stdin:

- `acceptance-gate.sh:15-17`: `INPUT=$(cat)`, then `jq -r '.tool_name // empty'` / `.tool_input // empty'`.
- `pre-compact-handover.sh:9,12-18`: `INPUT="$(cat)"`, then a jq-free grep/sed field extractor (`get_json_string()`), deliberately avoiding a `jq` dependency.

Three scripts still read `TOOL_NAME`, `TOOL_INPUT`, `FILE_PATH` as **environment variables**: a contract that predates (or was simply never migrated off) the stdin-JSON delivery model:

| Script | Env vars read | Registered anywhere? |
|---|---|---|
| `hooks/careful-mode.sh` | `TOOL_NAME`, `TOOL_INPUT` (lines 25-26) | No, grep confirms zero hits in `settings.json`, `hooks.json`, `.claude/settings.local.json` |
| `hooks/freeze-mode.sh` | `TOOL_NAME`, `FILE_PATH` (lines 25-26) | No |
| `hooks/skill-telemetry.sh` | `TOOL_NAME`, `TOOL_INPUT` (lines 15, 24) | No |

This is a double-dead-end, not a live bug: even if registered today under `PreToolUse`, they'd silently no-op, since the harness delivers JSON on stdin and these scripts would find their env vars empty (`"${TOOL_NAME:-}"`, bash empty-default, not an error). "Wire up `/careful`" is two changes, not one: add the `PreToolUse` entry, and rewrite the script to parse stdin JSON like `acceptance-gate.sh` does.

## Acceptance-gate contract selection logic (mechanism only)

`acceptance-gate.sh` only fires its block logic when `tool_name == "TaskUpdate"` and `tool_input.status == "completed"` (lines 20-27): every other `TaskUpdate` call (e.g. status `in_progress`) passes through untouched. It then searches four glob patterns for `acceptance-contract.md` files (`.claude/council/sessions/*/`, `.claude/academy/sessions/*/`, `.claude/prd/contract-*.md`, `.claude/acceptance-contract.md`) and enforces whichever one has the **newest mtime**, not the alphabetically-last match: this is what stops an abandoned session's contract from blocking unrelated live work in the same repo. A contract untouched for `ACCEPTANCE_GATE_STALE_HOURS` (default 72, overridable via env) is treated as abandoned and skipped entirely. Full rationale and the non-negotiable status of this gate: `mcs-change-control`.
