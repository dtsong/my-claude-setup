---
active: false
phase: "complete"
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
| 6 | #63 | [US-005] Unified two-account routing table (F5) | #60, #62 | merged | #72 | 1 | 3 |
| 7 | #65 | [US-007] Dormant suite extraction to my-claude-setup-private (F7) | — | merged | #73 | 1 | 1 |
| 8 | #66 | [US-008] Council HTML presentation layer (F10) | — | merged | #74 | 1 | 2 |

Dependency notes: all deps are in-batch. No cycles. #58 is the acceptance-contract tracking issue (not implemented directly; checkboxes updated as criteria verify). Prior completed run (March, roster-gap #33-#41) superseded by this state.

## Progress

(none yet)

## Decisions

- 2026-07-02: Queue built from session issues.md; topological order places #64 before #63 (both wait on #60; #63 also waits on #62).

### #64 (US-006) - merged via PR #71
- Cycle 1 (sonnet): 1 Critical (bare-claude bypass) + 1 Important (lint tracebacks on malformed hooks). Both fixed; cycle 2: 0/0.
- Gotcha noted by reviewer: check_settings fixtures must be named *.settings.json or main() skips them.

### #63 (US-005) - merged via PR #72
- Cycle 1 (sonnet): 1 Critical (validator tracebacks on wrong-typed sections) + 2 Important (audit-row contradiction with engine max profile; effort unenforced). All fixed: _dict_section guards, R6 effort rule, audit note + docs parity.
- Cycle 2: 0 Critical, 1 Important (docstring missing R6 line); reviewer's prescribed line applied verbatim as cycle 3.
- Routing now spans: JSON source of truth + hard pre-commit validator + docs table + engine reference + yaml tier sync (stale claude-sonnet-4-6 refreshed). Selection principles from the Anthropic talk are in docs/model-routing.md.

### #65 (US-007) - merged via PR #73
- Pre-flight found ece/resume-tailor/soc-security ALREADY extracted (untracked private-repo symlinks since April/June); only docx-to-pdf was still tracked. Moved (private d93d62c, gitleaks clean), README Extracted Suites manifest added.
- Cycle 1 (sonnet): 0 Critical, 0 Important, 1 cosmetic path nit (fixed pre-merge).

### #66 (US-008) - merged via PR #74
- Cycle 1 (sonnet): 2 Important (duplicate Alchemist/Oracle lens hex; optional sections lacked payload-source guidance). Fixed; cycle 2: 0/0.

## FINAL: 8/8 merged (PRs #67-#74), contract 26/26 verified, milestone closed, issues #58-#66 closed.
