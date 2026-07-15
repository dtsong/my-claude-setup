# Phase 1 detail: US-001..US-008 (issues #59-#66)

Table of contents: 1. Full issue map · 2. Per-AC test commands · 3. Resuming a stalled looper run

## 1. Full issue map

All 8 issues live under GitHub label `council-claude-config-model-optimization` and milestone 2, sourced from `.claude/council/sessions/claude-config-model-optimization-20260702-0003/issues.md`. Dependency order is topological, from `.claude/ship-state.md`'s Issue Queue table, not issue number order (#64 sits before #63 because both wait on #60, and #63 also waits on #62).

| Order | Issue | Story | What it changes | ACs | Depends on |
|---|---|---|---|---|---|
| 1 | #59 | US-001 fail-soft telemetry dispatcher (F3a) | Replaces 5 hook events in `settings.json` that bare-called the private-repo `session_telemetry.py` with `hooks/telemetry-dispatch.sh`: env-var override, default-path resolution, exit 0 on missing target, child failures never propagate exit 2. | AC-001..003 | none |
| 2 | #60 | US-002 session default → tier alias (F1) | Reverts `settings.json.model` from the pinned `claude-fable-5[1m]` to a tier alias; resolves the `[1m]` vs `CLAUDE_CODE_DISABLE_1M_CONTEXT=1` contradiction to one deliberate state; documents the escalation rule in `docs/model-routing.md`. | AC-004..006 | none |
| 3 | #61 | US-003 permissions rewrite (F2) | Replaces the imagined-TypeScript allowlist (`npm run`, `npx tsc`, `Write(src/**)`) with the real bash/python/markdown workload; adds a `settings.local.json` gitignored experiment lane. | AC-007..009 | none |
| 4 | #62 | US-004 OpenRouter ID refresh (F4) | Replaces stale 2024-era IDs (`gpt-4o-mini`, `gemini-flash-1.5`) in `skills/council/model-routing.json` with live-verified ones; adds `mcp/openrouter/check_models.py` as a staleness checker. | AC-010..012 | none |
| 5 | #64 | US-006 settings.json schema guard | New pre-commit hook validating `settings.json` against a JSON schema; rejects pinned IDs, `[1m]` suffixes, private-repo paths. | AC-017..019 | #60 |
| 6 | #63 | US-005 unified two-account routing table (F5) | Extends `skills/council/model-routing.json` with `tiers`/`profiles`/`spawn_sites`/`egress_policy`; see `references/routing-schema.md`. | AC-013..016 | #60, #62 |
| 7 | #65 | US-007 dormant suite extraction (F7) | Completes extraction to the sibling `my-claude-setup-private` repo. Actual outcome (PR #73): ECE, resume-tailor, soc-security were already extracted as gitignored symlinks; docx-to-pdf was the last tracked suite and moved (absorbed as private-repo commit `d93d62c`); README gained the Extracted Suites manifest. | AC-020..023 | none |
| 8 | #66 | US-008 council HTML presentation layer (F10) | Engine's design-approval synthesis touchpoint generates and opens a self-contained `design.html`; reference template lands under `skills/council/references/`; degrades to text-only on failure. | AC-024..026 | none |

Note: #58 is the acceptance-contract tracking issue. It is not implemented directly; its checkboxes mirror the contract's per-AC status and can flip ahead of an actual merge (observed on PR #70): never treat the issue body as the verification source, only the contract file is.

## 2. Per-AC test commands

Pull the exact command for any AC straight from the contract rather than trusting a paraphrase:

```bash
grep -A5 "^#### AC-0NN" .claude/council/sessions/claude-config-model-optimization-20260702-0003/acceptance-contract.md
```

Known-good commands as of 2026-07-06 (all 8 issues merged, contract 26/26; these remain the regression checks):

- **AC-001..003** (US-001): `python3 -m pytest .claude/council/sessions/claude-config-model-optimization-20260702-0003/test-stubs/test_acceptance.py -q -k "TestUS001"`
- **AC-004**: `jq -r .model settings.json` expect `opus`
- **AC-005**: `grep -c '\[1m\]' settings.json` expect `0`
- **AC-006**: `grep -q "Session Default and Escalation" docs/model-routing.md && echo present`
- **AC-007..009** (US-003): `jq '.permissions.allow' settings.json`; `jq '.permissions.deny' settings.json`; `git check-ignore .claude/settings.local.json`
- **AC-010**: `grep -cE 'gpt-4o-mini|gemini-flash-1.5' skills/council/model-routing.json` expect `0`
- **AC-011**: `python3 mcp/openrouter/check_models.py` expect exit 0
- **AC-012**: `python3 -m pytest mcp/openrouter/tests/ -q`

Formerly-stubbed tests, now real (verified 2026-07-06: zero `NotImplementedError` remains in `test-stubs/test_acceptance.py`):

- **AC-013, AC-014**: `python3 -m pytest .claude/council/sessions/claude-config-model-optimization-20260702-0003/test-stubs/test_acceptance.py -q -k "TestUS005"`
- **AC-017, AC-018**: same file, `-k "TestUS006"`.
- **AC-015, AC-016, AC-019..026**: `manual-check` or `build-output` method per the contract; no pytest node exists. Follow the contract's `Test:` cell literally when re-verifying (e.g. AC-016 is `grep -c model-routing.json commands/_council-engine.md`).

Template note for future campaigns: when a contract ships RED stubs, read the stub's docstring before authoring the real test, it states the exact GIVEN/WHEN/THEN the reviewer will hold you to; don't invent a looser assertion.

## 3. Resuming a stalled looper run

`/looper` writes `.claude/looper-state.md` scoped to whichever single issue it was last invoked on; it is not a substitute for `ship-state.md`'s queue. To resume safely:

1. `sed -n '/Issue Queue/,/^$/p' .claude/ship-state.md`, find the first row whose Status is not `merged`.
2. `gh pr list --state open --json number,headRefName,title`, check whether that issue already has an open PR (branch name convention: `feat/<issue-number>-<slug>`). If yes, resume review on that PR; do not re-invoke `/looper` to start a second implementation.
3. `git log --oneline -5 <branch>` on the candidate branch to see how far implementation got before the session ended.
4. If genuinely stalled (no PR, no recent commits, `looper-state.md` still shows that issue `in_progress` from a stale timestamp): re-invoke `/looper` scoped to that single issue, not the whole batch, re-running the full ship queue would re-litigate already-merged issues.
5. After resuming, re-run Phase 0's orientation commands once more before doing anything else; another session may have advanced the queue in the interim (this campaign has already seen mid-run commits land from a concurrent process once, per `.claude/council/sessions/.../design.md`'s own investigation notes).
