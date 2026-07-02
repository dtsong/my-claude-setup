# Plan: Claude Code Configuration + Model Optimization

Execution path: Ship (Path F). Issues exported per user story, then /ship implements, reviews, merges in dependency order. TaskCreate decomposition superseded by GitHub issues (issues.md is the task ledger).

| # | Story | Depends on | Size |
|---|-------|-----------|------|
| US-001 | F3a fail-soft telemetry dispatcher | — | XS |
| US-002 | F1 model tier alias + 1M resolution | — | XS |
| US-003 | F2 permissions rewrite + local lane | — | S |
| US-004 | F4 OpenRouter ID refresh | — | S |
| US-005 | F5 unified routing table + validator + doc | US-002, US-004 | M |
| US-006 | settings.json schema guard | US-002 | S |
| US-007 | F7 dormant suite extraction | — | M |
| US-008 | F10 council HTML presentation layer | — | S |

Ship order: US-001, US-002, US-003, US-004, US-005, US-006, US-007, US-008.
