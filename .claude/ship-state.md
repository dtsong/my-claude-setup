---
active: true
phase: "executing"
started_at: "2026-07-02T01:05:00-07:00"
updated_at: "2026-07-02T01:05:00-07:00"
config:
  from_session: "claude-config-model-optimization-20260702-0003"
  contract: ".claude/council/sessions/claude-config-model-optimization-20260702-0003/acceptance-contract.md"
  max_review_cycles: 3
  merge_strategy: "squash"
  no_merge: false
  max_retries: 3
  constraints: "No em dashes in any generated content, docs, or commit messages. Repo verification surface is pre-commit + pytest only (no tsc/eslint; state this explicitly). settings.json is live via ~/.claude symlink: reconcile the existing uncommitted diff, do not clobber tui/skipWorkflowUsageWarning keys."
---

# Ship State: claude-config-model-optimization

## Issue Queue (topological order)

| Order | Issue | Title | Depends On | Status | PR | Impl Attempts | Review Cycles |
|-------|-------|-------|------------|--------|----|--------------:|--------------:|
| 1 | #59 | [US-001] Fail-soft telemetry dispatcher (F3a) | — | queued | — | 0 | 0 |
| 2 | #60 | [US-002] Session default model to tier alias, 1M conflict resolved (F1) | — | queued | — | 0 | 0 |
| 3 | #61 | [US-003] Permissions allowlist rewrite + settings.local.json lane (F2) | — | queued | — | 0 | 0 |
| 4 | #62 | [US-004] OpenRouter model ID refresh + rot prevention (F4) | — | queued | — | 0 | 0 |
| 5 | #64 | [US-006] settings.json JSON-schema pre-commit guard | #60 | queued | — | 0 | 0 |
| 6 | #63 | [US-005] Unified two-account routing table (F5) | #60, #62 | queued | — | 0 | 0 |
| 7 | #65 | [US-007] Dormant suite extraction to my-claude-setup-private (F7) | — | queued | — | 0 | 0 |
| 8 | #66 | [US-008] Council HTML presentation layer (F10) | — | queued | — | 0 | 0 |

Dependency notes: all deps are in-batch. No cycles. #58 is the acceptance-contract tracking issue (not implemented directly; checkboxes updated as criteria verify). Prior completed run (March, roster-gap #33-#41) superseded by this state.

## Progress

(none yet)

## Decisions

- 2026-07-02: Queue built from session issues.md; topological order places #64 before #63 (both wait on #60; #63 also waits on #62).
