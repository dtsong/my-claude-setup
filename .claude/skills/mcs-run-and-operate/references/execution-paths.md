# Phase 5 execution paths, /ship, /looper, and the acceptance gate (detail)

## Path A: Team Execution

Backend `teams-preferred`: shared task list, dependency unblocking, file locking, per-task plan approval are team features (`CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1`, set in this repo's `settings.json`). Without teams, the conductor drives the same `TaskCreate` dependency list sequentially: one-shot Task per unblocked item, roster `subagent_type` + routing-table `model:`, mark complete, continue.

Auto-commit per completed task: `git -C $WORKSPACE add <files>; git -C $WORKSPACE commit -m "<type>(<scope>): <description>"`.

**Verification sweep** (after all team agents finish): read `acceptance-contract.md`, run each `pending` criterion's verification command, re-assign `failed` criteria for remediation, present a summary table, **block completion until every non-manual criterion is `verified`**, then update GitHub issue checkboxes via `gh api`. This sweep is what the acceptance-gate hook backstops at the tool level (see below): the sweep is prose/process, the hook is the actual enforcement mechanism.

## Path B: Ralf Handoff

Prints `/ralf --from-prd .claude/prd/prd-<slug>.md` for the user to run manually. Nothing is invoked automatically.

## Path C: Launch Handoff

Prints `/launch "<idea>" --from-prd .claude/prd/prd-<slug>.md`. **As of 2026-07-02, `commands/launch.md` does not exist** (`ls commands/` has no `launch*`). If a council session selects this path, either the design is aspirational (a `/launch` command was planned but never shipped) or this is dead documentation. Tell the user Path C currently has no receiving command; `/ralf` is the working equivalent.

## Path D: Deep Audit

Delegates to Phase 5D. Scans `git ls-files` into audit zones, spawns 2-4 `general-purpose` agents per zone with routing-table `model:`, checkpoints/respawns on context limits, iterates until a full pass produces zero new findings. Budget floor 60K tokens/pass. Triggered automatically after Phase 4 in deep mode, directly in audit mode, or by user selection in standard/guided mode.

## Path E: GitHub Issues Export

Idempotent. Detects repo via `gh repo view`, creates (or reuses) a milestone named after the idea, creates `user-story` + `<theme>-<slug>` labels, writes `$SESSION_DIR/issues.md` as a running ledger, and for each user story: searches for an existing issue with the session label before creating a new one (skips duplicates), creates with a standard body template (User Story / Acceptance Criteria checkboxes / Testing table / Technical Notes / Dependencies / tracking footer), and appends to `issues.md` immediately after each create-or-skip. Finishes by cross-referencing all created issues back onto the acceptance-contract tracking issue.

If `gh` isn't authenticated, this path aborts with an explicit message rather than silently degrading.

## Path F: Ship

Runs Path E's 8 steps, then invokes `/ship --from-session <slug>`, which reads `issues.md` for issue numbers and auto-sets `--contract` from `acceptance-contract.md`. `/ship` then: implements each issue via `/looper`, reviews the resulting PR via `pr-review-toolkit:review-pr`, autonomously fixes findings, and merges in dependency order.

## `/ship` state: `.claude/ship-state.md`

Canonical schema: `commands/references/ship-state-schema.md`. Frontmatter: `active`, `phase` (`intake|executing|sweep|complete`), `created_at`/`updated_at`, `max_review_cycles`, `merge_strategy` (`squash|rebase|merge`), `no_merge`, `session_id` (if `--from-session`), `contract_path`. Body: an Issue Queue table (`# | Issue | Title | Status | Blocked By | PR | Impl Attempts | Review Cycles`), a per-issue Progress section, and a Decisions Log. Status values: `pending -> implementing -> pr-created -> reviewing -> (fixing ->)* review-passed -> merging -> merged`, or `blocked` / `impl-failed` / `review-failed`.

Observed in practice (2026-07-02 live run), the frontmatter also carries a `config:` block (`from_session`, `contract`, `max_review_cycles`, `merge_strategy`, `no_merge`, `max_retries`, `constraints`) nested under the documented flat keys: this is a superset of the reference schema, not a contradiction; treat the schema doc as the guaranteed floor, not the ceiling.

`--resume` on `/ship` reads this file and continues from the first non-`merged`/non-`blocked` issue in the queue.

## `/looper` state: `.claude/looper-state.md`

Schema is inline in `commands/looper.md` (no separate reference file). Frontmatter: `active`, `phase` (e.g. `planning`), `mode` (`separate`|`combined`), `created_at`/`updated_at`, `max_retries`, `constraints`. Body: Issue Queue table, Quality Gates table (`Gate | Command | Status`, gate commands are shell-verified once before use, dropped with a warning if "command not found"), Progress, Decisions Log, PRs Created table.

When `/looper` is invoked by `/ship` per-issue, the observed frontmatter also carries `contract` and `invoked_by: "ship"`, again a practical superset, not documented in `commands/looper.md` itself. `--resume` re-parses issue statuses (`completed`/`failed`/`pending`/`blocked`/`in_progress`), gate commands, and prior decisions, then continues from the first `pending`/`in_progress` issue.

Constraint syntax (`--constraints`): `skip:<name>` removes a gate whose command contains that name; `gate:<cmd>` appends a custom gate.

## How the acceptance gate actually intersects all of this

`hooks/acceptance-gate.sh` is registered `PreToolUse` / matcher `TaskUpdate` in `settings.json`. It only inspects calls where `tool_input.status == "completed"`. **Neither `/ship` nor `/looper` calls `TaskCreate`/`TaskUpdate`**: they track state entirely in their own markdown files. Only two things in this pipeline actually invoke the Task tool: Phase 4.2 task decomposition (`_council-engine.md:1107`, `TaskCreate`/`TaskUpdate` for user-story tasks) and Path A team execution's sequential-Task fallback. So the gate protects "marking a Task-tool task completed," not "merging a PR" or "closing a GitHub issue": those go through `gh api`/`gh pr merge` directly and are ungated at the hook layer (their own review-cycle logic in `/ship` is the only check).

Contract selection: most-recently-modified `acceptance-contract.md` among 4 glob candidates (`.claude/council/sessions/*/`, `.claude/academy/sessions/*/`, `.claude/prd/contract-*.md`, `.claude/acceptance-contract.md`), by mtime, not path order. Staleness: contracts untouched for `ACCEPTANCE_GATE_STALE_HOURS` (default 72) are not enforced, so a dead session cannot block new work. Block behavior: `PreToolUse` + stderr + `exit 2` (the only combination that is actually blocking in this harness; `PostToolUse` and/or `exit 1` and/or stdout are all non-blocking, per the incident history; route that story to `mcs-debugging-playbook`).
