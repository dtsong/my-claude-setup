# Worked example: reading live run state (snapshot 2026-07-02 01:06 PT)

This walks the exact commands used to understand what the then-live `claude-config-model-optimization-20260702-0003` session and its `/ship` run were doing at authoring time. That campaign has since completed (2026-07-06: contract 26/26, PR train #67-#74 merged, ship-state `active: false, phase: complete`), so the snapshot values below are historical; the reading method is the durable part. Re-run every command against whatever run is live when you use this.

## Step 1: is anything mid-flight?

```bash
git log origin/main..HEAD --oneline
```

Snapshot output: 9 unpushed local commits ahead of `origin/main`, most recent `bb24cc5 chore: sync local main with squash-merged PR #69`. That alone says a `/ship`-style train is actively landing PRs and syncing the local branch after each squash-merge: a strong signal something is running right now, before even opening `.claude/ship-state.md`.

## Step 2: read the ship queue

```bash
cat .claude/ship-state.md
```

Frontmatter showed `active: true`, `phase: "executing"`, `config.from_session: claude-config-model-optimization-20260702-0003`, `config.contract: .claude/council/sessions/claude-config-model-optimization-20260702-0003/acceptance-contract.md`. The Issue Queue table (8 rows, topological order) showed, at this snapshot:

| Order | Issue | Status | PR |
|---|---|---|---|
| 1 | #59 (US-001) | merged | #67 |
| 2 | #60 (US-002) | merged | #68 |
| 3 | #61 (US-003) | merged | #69 |
| 4 | #62 (US-004) | queued | n/a |
| 5-8 | #64,#63,#65,#66 | queued | n/a |

Three of eight issues merged, one about to start. This table is the single source of truth for "what has landed": do not infer progress from `git log` alone, since intermediate reconcile/sync commits (`chore: sync local main with squash-merged PR #NN`) are noise around the real work commits.

## Step 3: cross-check the acceptance contract

```bash
grep -c '| verified |' .claude/council/sessions/claude-config-model-optimization-20260702-0003/acceptance-contract.md
grep -c '| pending |' .claude/council/sessions/claude-config-model-optimization-20260702-0003/acceptance-contract.md
grep -oE 'AC-[0-9]+' .claude/council/sessions/claude-config-model-optimization-20260702-0003/acceptance-contract.md | sort -u | wc -l
```

Snapshot: 9 verified, 17 pending, 26 total ACs. Matches expectation: 3/8 issues merged, each issue typically closing 2-4 ACs, so roughly a third of the contract verified is consistent with a third of the issue queue merged. If these numbers ever disagree sharply (e.g. all issues merged but most ACs still `pending`), that is a signal the verification sweep step was skipped: worth escalating, not silently trusting the merged PRs.

## Step 4: cross-check GitHub directly, don't trust local files alone

```bash
gh issue list --limit 20
gh pr list --limit 10
```

Snapshot: issues #59 and #60 do not appear in `gh issue list` output at all (default excludes closed): confirmed independently via `gh issue view 59 --json state,closedAt` (`CLOSED`, closed `2026-07-02T07:49:57Z`) and issue 60 (`CLOSED`, `2026-07-02T07:57:01Z`). `gh pr list` showed PR #69 (`feat: permissions allowlist rewrite...`, branch `feat/61-permissions-rewrite`) still `OPEN` at the moment of the first check, then `git log` a few commands later already showed it merged (`d9f6993 ... (#69)` + `bb24cc5` sync commit): the state moved between two read-only checks seconds apart. This is the concrete version of "the repo is live": do not cache any of these numbers across more than one tool call.

## Step 5: check for a second, unrelated in-flight session

```bash
cat ~/.claude/council/global-registry.json
```

Snapshot showed 4 sessions total across the machine, and only 1 of them (`claude-config-model-optimization-20260702-0003`) is from this repo: `ringbearer-observability-framework-...` and `externalize-job-triage-platform-...` sit in unrelated client workspaces, plus `klearpath-gtm-acceleration-20260702-0007` in a third workspace, phase `action`. None of these are yours to touch from inside `my-claude-setup`; they exist only because the registry is global to the machine, not the repo. This repo's own March session (`roster-gap-analysis-20260325-2041`) never appears in the global registry at all, a second, separate sync gap. The desync noted in the main skill also showed up concretely for the session that is present: it was listed with `phase: interview` in the global registry, while its own `session.md` in this repo said `Phase: action`, a two-hop-stale copy, exactly as documented.

## Takeaway checklist for this pattern

1. `git log origin/main..HEAD` first: cheap, tells you if anything is landing.
2. `.claude/ship-state.md` `phase`/Issue Queue: the authoritative "what's done" table.
3. Cross-check the contract's verified/pending counts against the queue's merged count; large mismatches mean the verification sweep step was skipped.
4. `gh issue list` / `gh pr list` for ground truth GitHub state; local files can be one merge-commit behind.
5. `~/.claude/council/global-registry.json` only if you need to know whether *other* workspaces on the machine are busy; never treat its `phase` field for *this* repo's session as authoritative, use the session's own `session.md`.
