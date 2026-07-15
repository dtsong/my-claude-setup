# The acceptance-gate saga

Hook: `hooks/acceptance-gate.sh`. Purpose: block `TaskUpdate -> completed` when a session's acceptance contract has unverified criteria. Four commits, three separate fail-open bugs, one final design lesson. Status: fixed since 2026-06-22, but issue #53 (which reported the last bug) is still OPEN as of 2026-07-02.

## Timeline

| Commit | Date | What broke | Root cause | Fix |
|---|---|---|---|---|
| 299a264 | 2026-02-16 | N/A (creation) | New hook: "acceptance criteria enforcement for council/academy plans". Three-layer design: contract artifact, instruction-based checks in ralf/looper/engine, PostToolUse hard-block hook. | n/a |
| 6bc7c1a | 2026-03-07 | Intermittent `PostToolUse:TaskUpdate` hook errors | Hook path in settings.json was relative, so resolution depended on CWD; `jq` hard-failed on malformed input under `set -euo pipefail`. | `$HOME`-based absolute path in settings.json. jq calls given fallbacks that **exit 0 on malformed input**: this is a deliberate fail-open decision baked in at this step. |
| 4bb8bf2 | 2026-05-10 | Gate silently bypassed via hook crash | `grep -c` exits 1 (not 0) when there are zero matches, so `PENDING=$(grep -c ... \|\| echo 0)` captured a literal `"0\n0"` (two values on two lines), which broke arithmetic at line 73 and crashed the hook. Also a malformed BRE alternation `'| pending \|\| failed |'` in the unverified-criteria listing regex. | `VAR=$(grep -c ...) || VAR=0` pattern (capture, then default, not append-a-fallback-string). Regex fixed to `grep -E '\| (pending|failed) \|'`. |
| 605112d | 2026-06-22 | Gate was fully decorative even when "working" | Two bugs. (1) Wiring: hook was registered as `PostToolUse`, wrote its block message to **stdout**, and exited 1. `PostToolUse` + any non-2 exit code is a **non-blocking** error in Claude Code: it gets logged ("non-blocking status code: No stderr output") but the tool call (`TaskUpdate -> completed`) proceeds regardless. (2) Selection: the hook picked the alphabetically-last acceptance-contract glob match, so a dead/abandoned session's contract could block a live session's work in the same repo. | Wiring: moved to `PreToolUse`, block reason written to **stderr**, exit code **2** (this is the only combination that actually denies a tool call and feeds the reason back to Claude). Selection: pick the most-recently-modified (mtime) contract across all candidate locations; skip contracts untouched more than `ACCEPTANCE_GATE_STALE_HOURS` hours (default 72). Commit message says "Refs #53" (not "Fixes"), which is why #53 never auto-closed. |

## Current wiring (verify before trusting)

`git show origin/main:settings.json`: look for `PreToolUse` matcher `TaskUpdate` calling `hooks/acceptance-gate.sh`. As of 2026-07-02 this block starts around line 54-60 of settings.json on origin/main; treat the line numbers as approximate and re-grep rather than trusting a hardcoded line reference, since US-003 (permissions rewrite, PR #69, open as of authoring) touches settings.json in the same file region.

## The design lesson (generalizes beyond this hook)

If you are writing any new enforcement hook in this repo:

1. It must run on `PreToolUse`, not `PostToolUse`, if it needs to actually deny the call.
2. It must write its reason to **stderr**, not stdout.
3. It must exit with code **2**, not 1 or any other non-zero value.
4. Any other combination is a no-op that will *look* like it's working (it prints something, the harness logs something) while doing nothing. This exact trap ate 605112d's predecessor for over 3 months (2026-03-07 to 2026-06-22).
5. Nothing tests this hook in CI. If you touch `acceptance-gate.sh` again, manually verify with a real block: run something that should be denied and confirm the process actually stops and the exit code is 2, don't just read the script.

## Related stale-open issues

`#26` is the original "[AC] Acceptance Criteria Enforcement for Council/Academy Plans" design issue that 299a264 partially implemented; it documents the four-layer design (contract artifact, instruction-based checks, PostToolUse hook, plus a fourth layer never fully realized). It remains open as a broader tracking issue, separate from #53's specific bug report. Do not conflate the two: #53 is fixed-but-unclosed, #26 is a wider open design surface (see `06-privacy-and-issues.md` for the full stale-issue rundown).

## Evidence commands

```bash
git show --stat 299a264 6bc7c1a 4bb8bf2 605112d
git show 605112d -- hooks/acceptance-gate.sh   # full diff of the fix that stuck
gh issue view 53
gh issue view 26
```
