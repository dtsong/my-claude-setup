# Idea Lifecycle Ledger

Contents: 1. Acceptance-gate saga · 2. Worked walkthrough (one idea through every stage) · 3. Extended "where good ideas came from" ledger · 4. Where time was lost

Full provenance detail behind `SKILL.md`'s compact tables.

## The acceptance-gate saga (cost of skipping adversarial refutation, in full)

`hooks/acceptance-gate.sh` blocks `TaskUpdate -> completed` when a council
acceptance contract has unverified criteria. It was rewritten three times
before it worked, because each earlier fix was accepted without adversarially
testing the exact thing it claimed to fix:

| Commit | Date | Symptom → root cause → fix |
|---|---|---|
| `299a264` | 2026-02-16 | Gate created (dogfooding pain: unenforced council/academy plans). |
| `6bc7c1a` | 2026-03-07 | Intermittent hook errors. Cause: relative path broke by CWD; `jq` hard-failed under `set -euo pipefail` on malformed input. Fix: `$HOME`-absolute path, `jq` fallbacks that exit 0 on malformed input (institutionalized fail-open, not yet fail-soft-with-signal). |
| `4bb8bf2` | 2026-05-10 | Gate silently bypassed via crash. Cause: `grep -c` exits 1 on zero matches, so `PENDING=$(grep -c ... \|\| echo 0)` captured two values and broke arithmetic; a malformed BRE alternation also broke the unverified-criteria listing. Fix: `VAR=$(grep -c ...) \|\| VAR=0` pattern, corrected regex. |
| `605112d` | 2026-06-22 | Even when it "blocked," the gate was decorative: registered as `PostToolUse`, printed to stdout, exited 1. `PostToolUse` + non-2 exit is non-blocking, so `TaskUpdate->completed` always went through; separately, contract selection took the alphabetically-last glob match, so a dead session's contract could block live work. Fix: move to `PreToolUse`, reason to stderr, `exit 2`; select contract by mtime; skip contracts untouched past `ACCEPTANCE_GATE_STALE_HOURS` (default 72h). Refs `#53` (not "Fixes"; `#53` is still OPEN as of 2026-07-02, see the "Refs instead of Fixes" anti-pattern in `SKILL.md`). |

Every earlier fix was locally plausible and untested against the actual
denial path (a real `TaskUpdate` with an unresolved contract, checking the
exit code and which stream the message landed on). `605112d`'s commit body
is the first one that states what was verified: "real block exits 2 with
stderr; stale/abandoned contracts and non-completed status updates pass."
That sentence is the adversarial-refutation discipline made explicit.

## Worked walkthrough: one idea through every stage (2026-07-02 session)

Session `claude-config-model-optimization-20260702-0003`, all artifacts under
`.claude/council/sessions/<slug>/` unless noted:

1. **Hunch.** Pre-existing pain across open issues (#53's fix landed but the
   issue stayed open; OpenRouter model IDs frozen at 2024-era values;
   `settings.json` self-contradicting on the `[1m]` context flag) plus a
   council session invoked to unify them.
2. **Council deliberation.** `design.md`: 7-row Tension Resolutions table
   (e.g. "eval harness before everything vs MVP ships now," resolved as
   "MVP ships ungated; 12-case smoke set gates the first live model flip")
   and a matching Decision Log. Committed at `c26cf08`.
3. **PRD non-goals discipline.** `prd.md` Non-Goals: "No live model flips:
   no `routed_consult` callers, no `/ship`/`/looper`/council-profile model
   changes (v1.1, gated by F11 smoke eval)"; "No OpenRouter Phase 2 lens
   relay (F6: future, gated by 38-case harness + egress safeguards)"; "No
   council-skill pruning (deferred: durable telemetry increment + 2-4 week
   window first)." Each non-goal names its own future gate, not just "later."
4. **Acceptance contract.** `acceptance-contract.md`: 26 numbered `AC-NNN`
   rows across 8 user stories (US-001..US-008), each with Method (unit-test /
   build-output / manual-check), Test, Status, Evidence, Verified-by columns,
   plus a Verification Summary table and a running `Progress: N/26 verified`
   line. GitHub tracking issue `#58` mirrors it.
5. **Gated execution.** `/ship` built a topological queue in
   `.claude/ship-state.md` (8 issues, dependency-ordered), delegating each
   issue to `/looper`. `.claude/looper-state.md` records quality gates
   (`pre-commit run --all-files`, the relevant pytest slice) and a
   Decisions Log per issue.
6. **Verification.** Each merged issue's ACs flip from `pending` to
   `verified` with a literal Evidence cell, e.g. AC-017: "`pipeline/config/
   settings.schema.json` + `pipeline/hooks/check_settings.py`... wired as
   `settings-schema` (hard) in `.pre-commit-config.yaml`; passes on current
   `settings.json`; `test_ac_017` green."
7. **Adoption.** US-001..US-004 (issues #59-#62) merged via PRs #67-#70,
   each requiring 0 Critical/0 Important from `/pr-review-toolkit:review-pr
   all` before merge. US-003's Cycle 1 caught a blanket `Bash(gh *)` grant on
   live global config as Critical; fixed before merge (scoped to
   `pr/issue/label/repo-view/auth-status` plus 4 destructive-command denies).

US-005..US-008 have since merged too (PRs #71-#74, campaign closed 2026-07-06
at 26/26); re-run the Provenance commands in `SKILL.md` for current status,
not this list.

## Extended "where good ideas came from" ledger

- **Dogfooding pain**, ranked #1 by hit rate: `acceptance-gate.sh` (real
  enforcement pain), the handover system `8a56757` (real context-loss pain
  across compactions), and `settings.local.json` as an experiment lane
  (real pain from experiments almost landing directly in live config).
- **Incident postmortem generalized into doctrine**: `#53`'s fail-open `jq`
  handling in `6bc7c1a` was itself an early, partial version of fail-soft;
  `605112d` completed the doctrine (block loudly, degrade silently only on
  genuinely absent state); by June 22 the same doctrine is explicit house
  style in `3e99a66` ("fail-soft consult: never raises, callers degrade to
  normal Claude path") and by July 2 in `hooks/telemetry-dispatch.sh`'s
  header comment, which states the contract in one sentence before the code.
- **Upstream adoption with a local-divergence record**: `9cee199` "adopt
  agentic-council v1.2.0 orchestration into vendored engine" pulled in cost
  profiles (lean/balanced/max) and backend fallback (workflow to teams to
  sequential) wholesale, then explicitly kept local divergences (22-agent
  roster instead of upstream's, nested `DEPARTMENT.md` layout, tracked
  `registry.json`) rather than silently forking without a record.
- **Deliberate deletion sweeps**: `16833bd` (5 skills, each with its own
  one-line reason: 2 duplicated native tooling, 3 duplicated a plugin);
  `12c34df` (academy theme, 38 to 21 agents, "no unique deliberation
  capability," -2,779 lines); both keep the counterfactual in the commit
  body so a later session doesn't have to reconstruct it from a diff.

## Where time was lost (extended)

- **`/careful` and `/freeze`**: fully written commands and hook scripts
  (`hooks/careful-mode.sh`, `hooks/freeze-mode.sh`) that touch a state file
  on `enable`, but no `PreToolUse` entry in `settings.json` ever calls
  `<script> check`. Enabling either currently protects nothing; verify with
  `grep -c 'careful\|freeze' settings.json` (expect `0`).
- **Telemetry before US-001**: all 5 lifecycle hook events called
  `python3 "$HOME/Development/my-claude-setup-private/hooks/session_telemetry.py"`
  directly, with no existence check, so a fresh clone without the private
  sibling repo failed on every tool call until `c562ab8` (issue #59, PR #67)
  introduced the fail-soft dispatcher.
- **Docs promising unbuilt CI stages**: `pipeline/specs/SKILL-GOVERNANCE-
  SPEC.md` §8.3 describes a 4-stage CI pipeline (lint, static-analysis,
  eval, publish); `.github/workflows/validate.yml` runs exactly two jobs
  (`validation`: shell syntax + JSON validity + installer smoke;
  `secret-scan`: gitleaks) and invokes none of `pipeline/hooks/`. Branch
  protection requires those two jobs and zero human reviews, so governance
  enforcement is local-only and bypassable with `git commit --no-verify`.
