# Interview Summary: Claude Code Configuration + Model Optimization Review

## Core Intent
Comprehensively optimize the my-claude-setup repo and live Claude Code configuration across four axes: model routing (Claude tiers + OpenRouter, folded in from the approved June 22 spec), skill-gap analysis grounded in real workload (meta-repo, web/product, data/ML), config hygiene (settings.json conflicts, permissions, hooks, env flags), and harness leverage (workflows, teams, cron, LSP, memory). Serve two billing profiles: Max plan (this account) and API-billed (work account, config since branched off).

## Key Decisions Made
- Both Max-plan and API-billed use cases must be addressed; API side gets documented lean profile, not a shared-config mechanism (work config branched off).
- OpenRouter integration (Phase 1 cheap-task routing + Phase 2 lens relay) is IN SCOPE; routing should be designed as one system spanning Claude tiers and OpenRouter models.
- Dormant suites (ECE, resume-tailor, docx-to-pdf, soc-security): user leans toward extraction to a separate private repo; deliberation should settle aggression level and mechanics.
- Execution via Ship (Path F): GitHub issues then automated implement/review/merge.

## Open Questions for Deliberation
- How aggressive should pruning be, and what is the extraction mechanism (separate repo, git branch, portable/ archive)?
- Concrete model routing table: which spawn sites get Fable/Opus/Sonnet/Haiku, and which task classes route to OpenRouter cheap models?
- Which skill gaps are worth filling for meta-repo/web/data-ML workload, vs. which existing skills to consolidate?
- Which unused harness features (auto-memory is disabled, cron/schedules, LSP plugin, fewer-permission-prompts) are worth adopting?
- settings.json conflicts: claude-fable-5[1m] pin vs CLAUDE_CODE_DISABLE_1M_CONTEXT=1; pinned model ID vs tier-alias governance rule; uncommitted diff.

## Perspective Relevance Scores
| Perspective | Score (0-5) | Rationale |
|-------------|-------------|-----------|
| Oracle | 5 | Model routing, prompt/skill engineering, OpenRouter integration: the core of the session |
| Architect | 4 | Repo structure, routing-table design, extraction mechanics, MCP integration |
| Craftsman | 4 | Skill governance compliance, DX, registry/telemetry fix, pruning quality bar |
| Strategist | 4 | Prioritization across four goals, MVP scoping of the Ship plan |
| Operator | 3 | Hooks, telemetry, cost/finops for API-billed profile |
| Skeptic | 3 | Permissions/deny-list review, risk of pruning, telemetry-to-private-repo surface |
| Scout | 3 | Precedent: current Claude Code best practices, model landscape facts |
| Alchemist | 2 | Data/ML workload informs skill gaps, but no pipelines built here |
| Chronicler | 2 | Docs/records for extracted suites; secondary |
| Guardian | 1 | Light privacy angle (telemetry); covered by Skeptic |
| Others (Artisan, Herald, Pathfinder, Sentinel, Forge, Cipher, Warden, Prover, Foundry, Accountant) | 0-1 | Out of domain |
