---
name: mcs-run-and-operate
description: "Use when running /council, /ship, /looper, or /handover day to day in this repo: choosing a council mode or --profile, resuming/listing/archiving a session, picking a Phase 5 execution path (team, ralf, launch, deep audit, issues export, Ship), reading or resuming .claude/ship-state.md or .claude/looper-state.md, writing a handover, or checking for an in-flight ship/council run before touching .claude/ state so you do not clobber it. Not for diagnosing why a hook or gate is silently failing (mcs-debugging-playbook) or for commit/PR/change-classification rules (mcs-change-control)."
---

# mcs-run-and-operate

## Overview

This skill is the day-to-day operator's manual for the council -> Phase 5 -> /ship or /looper -> /handover pipeline in this repo. Core principle: the pipeline's state lives in small files (`.claude/council/index.json`, a session's `session.md`, `~/.claude/council/global-registry.json`, `.claude/ship-state.md`, `.claude/looper-state.md`), those files drift out of sync with each other and with reality, and at least one other agent may be mutating them right now, so always read state before you write it.

## When to use, and when NOT to

| Situation | Use this skill? |
|---|---|
| "What does `--deep` vs `--audit` actually run?" | Yes |
| "Which Phase 5 path do I pick, and what happens after?" | Yes |
| "Is there a ship run in progress? Can I safely start a council session?" | Yes |
| "How do I write a good handover before I stop?" | Yes |
| "The acceptance gate is blocking me and I don't know why" | No, route to `mcs-debugging-playbook` |
| "Does this change need a PR, and what are the commit conventions?" | No, route to `mcs-change-control` |
| "What does the Workflow tool actually guarantee, or how does skill loading work?" | No, route to `mcs-claude-code-platform` |
| "What counts as evidence that an AC is verified?" | No, route to `mcs-validation-and-qa` |

## Council command anatomy

`/council [flags] "idea"`. `/brainstorm "idea"` is a shortcut for `/council --brainstorm "idea"`. Flag parsing is **first-match-wins** (`commands/_council-engine.md:50-74`): session-management flags exit first, then session-mode flags, in this priority order:

```
--help | --list [--all] | --status | --archive <slug> | --lock <slug> | --cleanup [--all]   # exit, no session
--resume [<slug>] [--pick]                                                                    # resume
--brainstorm | --quick | --deep | --auto | --guided | --meet | --audit | (none = standard)     # 8 modes
```

`--profile <lean|balanced|max>` is composable, resolved `--profile` > theme default (`balanced` for Council) > `balanced`, persisted on `session.md`/index.

| Mode | Rounds | Backend | Output |
|---|---|---|---|
| brainstorm | 0 | inline | chat only, no session dir |
| quick | 1 | inline | design-sketch.md, task list |
| standard (default) | 3 | workflow | full design doc, PRD, GitHub issues |
| deep | 3 | workflow | standard + mandatory deep audit |
| auto | 3 | workflow | standard, zero touchpoints, defaults to Ship path |
| guided | 3 + gates | workflow x2 | standard + approval every phase |
| meeting | meeting protocol | teams-preferred | meeting-notes.md only |
| audit | 0 | workflow | deep audit report, no design doc |

Agent/budget detail, resume/list/archive mechanics, session directory layout, and the index.json/global-registry.json schema (and known desync) are in `references/session-lifecycle.md`.

## Execution paths after a council (Phase 5)

Phase 4 produces `prd.md`, `acceptance-contract.md`, `test-stubs/`, and symlinks under `.claude/prd/`. Phase 5 then offers 6 action paths (`commands/_council-engine.md:1188-1396`); only Path A is mandatory, B-F are Council's opt-in extras:

| Path | What it does |
|---|---|
| A. Team Execution | Spawns agents on the task list (teams-preferred, degrades to sequential Task calls); ends with a contract verification sweep that blocks completion until every non-manual AC is `verified` |
| B. Ralf Handoff | Prints `/ralf --from-prd .claude/prd/prd-<slug>.md` for the user to run |
| C. Launch Handoff | Prints `/launch "<idea>" --from-prd ...`. **`/launch` is not a real command in `commands/` today**: only `/ralf` and `/ship` are |
| D. Deep Audit | Runs Phase 5D: zone-based audit, checkpoint/respawn, converges at zero new findings on a pass |
| E. GitHub Issues Export | Idempotent milestone + labeled issues + dependency links + `issues.md` ledger in the session dir |
| F. Ship | Runs Path E, then `/ship --from-session <slug>` (reads `issues.md`, auto-sets `--contract`) |

`/ship` and `/looper` each own a markdown state file with YAML frontmatter (`.claude/ship-state.md`, `.claude/looper-state.md`) that is the source of truth for resume, not the Task tool. Full path mechanics, both schemas, and how the acceptance gate actually intersects execution are in `references/execution-paths.md`.

## Session persistence

- `/handover [--tag LABEL]` writes `memory/HANDOVER-<YYYY-MM-DD-HHMM>.md` (`commands/handover.md`). Target 80-120 lines: Session Summary, What Was Done, Key Decisions (highest-value section, capture WHY), Pitfalls & Gotchas, Open Questions, Next Steps, an Important Files table, a Session Context block (branch + last 5 commits). Write a real reflection, not a blank template; say "None" rather than invent content for an empty section.
- Session-start convention (user's global CLAUDE.md): `ls -t memory/HANDOVER-*.md | head -3`, read the newest before doing anything else.
- `PreCompact` auto-handover: `hooks.json` registers `hooks/pre-compact-handover.sh` on `PreCompact`/matcher `auto` only (manual `/compact` does not trigger it). It tails the last 500 transcript lines, shells to `claude -p --model sonnet` for a summary, and writes `memory/HANDOVER-<ts>-auto.md` (minimal fallback template if that call fails or returns empty).
- The two are independent: `/handover` is a deliberate full-context save; PreCompact is a lossy safety net for context you didn't choose to compact.

## Artifact conventions (verify before trusting)

- `design.md` is committed at synthesis, in its own commit, every time observed (`docs(council): design document for <idea>`). This is conductor habit, not an engine instruction: grep `commands/_council-engine.md` for `git commit` and you get zero hits.
- `prd.md`, `plan.md`, `acceptance-contract.md`, `design.html`, `test-stubs/` are **not guaranteed** committed at all: the March `roster-gap-analysis` session only ever has `design.md` on disk (never reached Phase 4). The July session committed these together, one follow-up commit, before issue export. Check `git ls-files .claude/council/sessions/<slug>-<ts>/`; do not assume.
- `skills/council/registry.json` (skill-usage telemetry) is committed with real nonzero counts as of `dc44611` (2026-07-02); before that, HEAD always showed all-zero and any nonzero count was an uncommitted, unmerged write. Re-check `git show HEAD:skills/council/registry.json` before trusting a count.
- `.claude/ship-state.md` and `.claude/looper-state.md` are always working-tree state, never gitignored; they are live control files another agent may be editing right now.

## Live-operations rules

Before starting or resuming council/ship/looper work, run all three:

```bash
git log origin/main..HEAD --oneline                          # unpushed work another session may own
cat .claude/ship-state.md 2>/dev/null | grep -A1 '^phase:'   # ship batch mid-flight?
gh issue list --limit 20                                      # open user-story / tracking issues
```

If `.claude/ship-state.md` shows `active: true`, do not start a new `/ship` or edit its queue; `/looper` (`invoked_by: ship`) is likely already running underneath it. If a council session's `index.json` entry shows `status: active` and `phase` other than `action`/`complete`, treat it as owned unless `updated` is 7+ days old (`_council-engine.md:1709`). Never edit another session's `.claude/council/sessions/<slug>-<ts>/`; start or `--resume` your own.

## Gotchas

- **`/launch` doesn't exist.** Path C and `_council-engine.md:1020,1247` both reference it, but `commands/` only has `ralf.md` and `ship.md`. If a session picks Path C, tell the user to use `/ralf` instead.
- **The acceptance gate only fires on the `TaskUpdate` tool, not on `/ship`/`/looper`'s markdown state.** They never call `TaskCreate`/`TaskUpdate`; only Phase 4.2 task decomposition and Path A team execution do. A stuck `/ship` run is not gate-related; route the symptom to `mcs-debugging-playbook`.
- **Three state surfaces per session, frequently disagreed as of 2026-07-02:** workspace `index.json`, the session's own `session.md`, and `~/.claude/council/global-registry.json` each carry their own `phase`/`status`. Trust `session.md` first; the other two are copies that go stale.
- **`contract_issue` in `index.json` reads `null` even after the contract issue exists.** The prose step to store the URL is routinely skipped; find the issue by label (`acceptance-contract,tracking`) instead.
- **`registry.json` counts under a few weeks old, or predating `dc44611`, are not evidence of anything.** Any workspace can bump these counters (`~/.claude/skills` symlinks here) without a session directory in *this* repo.
- **WRONG:** a merged PR means its issue is fully done. **RIGHT:** cross-check the Issue Queue `Status` column and the contract's verified count; a merge can land before its ACs verify if the sweep hasn't run.
- **`--profile` typos exit hard**, no silent fallback: `Invalid profile. Usage: --profile lean|balanced|max`, no session state written.
- Editing `~/.claude/settings.json`, `~/.claude/hooks.json`, or `~/.claude/skills/*` "just to test": all three are symlinks into this repo (this machine only). Any edit deploys live the instant you save.

## Provenance and maintenance

Last verified 2026-07-02, against a repo then actively mutated by a live `/ship` run (council session `claude-config-model-optimization-20260702-0003`, issues #59-#66; completed 2026-07-06, both state files now `active: false, phase: complete`). Facts here will drift; re-run these first:

- Phase 5 path list: `grep -n "^### Path" commands/_council-engine.md`
- `/launch` existence: `ls commands/ | grep -i launch` (expect no output)
- Ship state schema: `cat commands/references/ship-state-schema.md`
- Live ship/looper status: `cat .claude/ship-state.md; cat .claude/looper-state.md`
- Unpushed work: `git log origin/main..HEAD --oneline`
- Registry commit status: `git show HEAD:skills/council/registry.json | head -5`
- Three-surface desync: `jq .phase .claude/council/index.json; grep '^Phase:' .claude/council/sessions/*/session.md`
