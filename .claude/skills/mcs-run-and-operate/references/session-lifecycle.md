# Council session lifecycle (detail)

## Full mode table

Source: `commands/_council-engine.md` Mode Configuration table. Backend values: `inline` = plain Task calls; `workflow` = background Workflow run, degrades workflow -> teams -> sequential; `teams-preferred` = agent teams when available.

| Mode | Phases | Agents | Rounds | Touchpoints | Backend | Budget |
|---|---|---|---|---|---|---|
| brainstorm | 0 + inline | 3 (sonnet) | 0 | 0 | inline | n/a |
| quick | 0, 2, 3(1-round), 4(light) | 3 | 1 | 1 | inline | n/a |
| standard | 0-5 | 3-7 | 3 | 6-7 | workflow | ~750K |
| deep | 0-4, 5D | 3-7 | 3 | 5-6 | workflow | ~1.5M + ~2M audit |
| auto | 0, 2, 3, 4, 5 | 3-7 | 3 | 0 | workflow | ~750K |
| guided | 0-5 | 3-7 | 3 + gates | 8+ | workflow x2 | ~750K split |
| meeting | 0, 1(light), 2, 3-meeting | 3-7 | meeting protocol | 2-3 | teams-preferred | n/a |
| audit | 0, context, 5D | 3-5 | 0 | 2-3 | workflow | ~2M |

Auto mode auto-approves the PRD and defaults to Path F (Ship) if the user doesn't pick a path.

## Cost profiles

`$PROFILE` resolution: `--profile` flag > theme `$DEFAULT_PROFILE` (`balanced` for Council) > `balanced`. Fixed at spawn time, keyed by spawn site (`_council-engine.md:93-121`):

| Spawn site | lean | balanced | max |
|---|---|---|---|
| Brainstorm agents | sonnet | sonnet | sonnet |
| Council agents (R1-R3, Path A) | sonnet | opus | opus |
| Round 2 challenge agents | opus (fresh one-shots) | persistent agents respond | fable (fresh one-shots, retry opus on spawn error) |
| Audit agents | sonnet | sonnet | opus |
| Conductor (interview, synthesis, PRD) | inherits user's `/model`, not engine-controlled | | |

Always tier aliases (`sonnet`/`opus`/`fable`), never pinned `claude-*` IDs: they go stale and the frontmatter validator (`pipeline/hooks/check_frontmatter.py`) rejects pinned IDs in `model:` fields, though note that validator only checks SKILL.md frontmatter, not `agents/*.md` persona files (no hook enforces the engine's "validator rejects them in agent frontmatter" claim for agents).

## Resume / list / archive / cleanup

`--resume` (`_council-engine.md:1546-1571`):
1. No slug, no `--pick`: resume most recent `active` session by `updated` timestamp.
2. With slug: fuzzy-match slug prefix in the index; picker on ambiguity.
3. With `--pick`: always show an `AskUserQuestion` picker of all `active` sessions.

On resume: read `session.md` for last completed phase, `Profile:` (default `balanced` if absent, pre-v1.2 sessions), `Backend:` (re-run capability check if absent); check `audit/state.md` for an in-progress Phase 5D audit; re-spawn agents from the index's `agents` list.

`--list` prints a table from the workspace index; `--list --all` reads `~/.claude/council/global-registry.json` across every workspace on the machine. `--status` is a one-shot workspace summary. `--archive <slug>` posts the full session (interview, design, PRD, contract, decision log, and collapsible round-by-round transcripts) as a GitHub issue, then asks whether to delete local session files; guarded by "session reached at least the deliberation phase" and `gh auth status`. `--cleanup [--all]` auto-marks sessions `stale` at 7 days (`active`) or 14 days (`completed`) since `updated`, per `_council-engine.md:1709-1710`.

Status values: `active` (in progress or recently done), `completed` (all phases finished), `archived` (exported, local files may be gone), `stale` (auto-set by `--cleanup`).

## Session directory layout

`.claude/council/sessions/<slug>-<YYYYMMDD-HHmm>/`:

```
session.md                    # Phase/Profile/Backend/Selected Agents/Loaded Skills header
interview-summary.md
interview-transcript.md
assembly.md                   # Phase 2 agent scoring
deliberation/
  round1/<Agent>.md            # position, full text
  round2/<Agent>-responds-to-<Agent>.md
  round3/<Agent>.md            # converge
design.md                     # synthesis output (Phase 3)
design.html                   # F10 presentation layer, when generated
prd.md                        # Phase 4
plan.md                       # Phase 4.3 task breakdown
acceptance-contract.md        # Phase 4.1b, BDD-style AC table
test-stubs/                   # generated test skeletons per AC
issues.md                     # Path E/F only: GitHub issue map + milestone link
```

Round text (deliberation/*) never enters the conductor's own context when running on the workflow backend: the Workflow tool's synthesis agent reads it and returns only the structured design payload.

## index.json and global-registry.json

`.claude/council/index.json` (per-workspace): `{version, workspace, sessions: [{id, slug, idea, created, updated, phase, status, profile, agents, skills_used, contract_generated, contract_issue, archived_to}]}`.

`~/.claude/council/global-registry.json` (cross-workspace, this machine only): `{version, workspaces, sessions}`, a flat session list tagged with `workspace` path, aggregated across every repo on the machine that has ever run `/council`. Skill-usage counters in `skills/council/registry.json` are similarly cross-workspace: because `~/.claude/skills` symlinks into this repo, a `/council` run in any other project on the machine bumps this repo's registry counters even though it has no session directory here.

**Known desync (observed 2026-07-02):** a single session's `phase` can disagree across the three surfaces (`index.json`, its own `session.md`, `global-registry.json`) because the writes are not transactional; in the observed case two of the three diverged (`global-registry.json` was two hops stale). Always prefer `session.md` inside the session directory itself.

## `.claude/prd/` symlink convention

At Phase 4.1, after writing `$SESSION_DIR/prd.md`:

```bash
ln -sf "$SESSION_DIR/prd.md" "$WORKSPACE/.claude/prd/prd-<slug>.md"
```

and equivalently for the acceptance contract (`contract-<slug>.md`). This exists for `/ralf --from-prd .claude/prd/prd-<slug>.md` compatibility (and, per the engine comment, `/launch`, which does not currently exist as a command in this repo: see the main SKILL.md Gotchas). Because it is a real symlink, `.claude/prd/*.md` and the session's own copy are the same file; edits to either are visible in both.
