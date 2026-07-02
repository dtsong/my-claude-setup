# Scout Position — Claude Config & Model-Routing Optimization

## Core recommendation

Build ONE routing system keyed by spawn site AND account type, and let the economics
flip the default: on the **Max plan** cheap sub-tasks route to **native Haiku 4.5**
(rate-limit cost, zero dollars), reserving OpenRouter for **Pattern A cross-vendor
diversity only**; on the **API account** OpenRouter Pattern B genuinely saves money but
its model IDs must be refreshed first (`gpt-4o-mini` / `gemini-flash-1.5` are ~2 years
stale). Extract the dormant suites (ECE, resume-tailor, docx-to-pdf, soc-security) to a
private repo — they are ~2.2M+ of the 3.9M skills tree and add search noise, not cost at
rest.

## Key argument

External pricing evidence inverts the OpenRouter cost premise on the Max plan. OpenRouter
bills real dollars plus a flat 5.5% credit fee ([OpenRouter Pricing](https://openrouter.ai/pricing)),
while native Haiku 4.5 on Max draws only on plan rate limits. So routing "classification /
scoring / scout-research" to `openai/gpt-4o-mini` on the Max account *spends money to avoid
a free call* — the opposite of the spec's intent. The spec's Pattern B ([design spec](../../../../../docs/superpowers/specs/2026-06-22-openrouter-integration-design.md))
is sound for the API account but should default `tasks.*` to `claude` (Haiku tier) on Max.
Meanwhile the committed `model-routing.json` still names 2024-era cheap models; by June 2026
Gemini 2.5 Flash repriced to $0.30/$2.50 and the cheap frontier moved to Ling 2.6 Flash
($0.01 in), Nemotron, MiniMax M3, Qwen3.7 ([digitalapplied roundup](https://www.digitalapplied.com/blog/openrouter-new-models-june-2026-roundup-pricing-rankings),
[betonai guide](https://betonai.net/openrouter-pricing-2026-complete-guide-to-every-model-tier-and-hidden-cost/)).
`list_models()` passthrough (already designed) should feed a periodic refresh so IDs never
rot again. Separately, the uncommitted `settings.json` has a self-contradiction confirmed by
Anthropic docs: `model: "claude-fable-5[1m]"` requests the 1M variant while
`CLAUDE_CODE_DISABLE_1M_CONTEXT=1` "removes 1M model variants from the model picker"
([model-config docs](https://code.claude.com/docs/en/model-config)), and pinning a
`claude-*` ID violates this repo's own rule (council-engine line 105: always tier aliases,
never pinned IDs, which go stale). Registry data is better than reported: 10 of 67 council
skills show uses>0, so tracking works — the fix is a usage-decay report, not a rebuild.

## Risks if ignored

- **Paying to save money.** Leaving Pattern B pointed at OpenRouter on the Max plan converts
  free rate-limited Haiku calls into billed OpenRouter calls (+5.5% fee) — a net cost
  increase disguised as an optimization.
- **Stale model IDs fail silently.** `google/gemini-flash-1.5` may already be deprecated on
  OpenRouter; a routed call that 404s falls back to Claude (fail-soft works) but the "cheap
  routing" quietly never fires, so the API account overpays with Opus while believing it is
  routing cheap.
- **Config contradiction burns tokens or breaks pinning.** The `[1m]` + disable-1m conflict
  produces undefined precedence; pinned `claude-fable-5[1m]` also breaks the repo's
  no-pinned-ID governance and will go stale on the next model refresh (per GitHub #50803 the
  `--model` flag already silently drops the `[1m]` suffix).

## Dependencies on other agents' domains

- **Architect** owns the unified routing schema (extend `model-routing.json` with an
  `account: {max|api}` axis and a `haiku` tier) and the spawn-site wiring across
  council/ship/looper — my model-ID + economics evidence is an input, not the design.
- **Pragmatist / Operator** own the Max-vs-API policy call and the extract-to-private-repo
  execution (git-filter-repo history split, submodule vs. sibling clone) — I supply the
  footprint numbers and prior-art pattern only.
- **Skeptic / Security** own `OPENROUTER_API_KEY` handling and ensuring no secrets follow the
  dormant suites into the new private repo.
- **Whoever owns hooks** must reconcile the private-repo telemetry dependency
  (`session_telemetry.py` in `my-claude-setup-private`) with any extraction plan.

---

## Appendix A — Technology Radar: Harness Features (Adopt / Trial / Assess / Hold)

Category = Platform/Tool (Claude Code harness). Confidence noted per item.

| Feature | Quadrant | Confidence | Evidence / Rationale |
|---------|----------|-----------|----------------------|
| **Workflows** (council-deliberation template) | **Adopt** | High | Deterministic multi-round orchestration already proven across the council engine; sandboxed `agent()` is the substrate Phase 2 lens-relay depends on. Core, low-risk. |
| **OpenRouter multi-model — Pattern A (lens diversity)** | **Trial** | Med | Genuine cross-vendor reasoning for council lenses is the durable win. Phase 1 primitive shipped + tested; relay is unbuilt. Worth trialing on one lens. |
| **OpenRouter — Pattern B (cheap routing) on API account** | **Trial** | Med | Real savings vs Opus/Sonnet, but only after refreshing stale IDs and adding a `list_models` refresh. Gate behind account type. |
| **OpenRouter — Pattern B on Max plan** | **Hold** | High | Inverted economics: bills dollars +5.5% where native Haiku is rate-limit-free. Default `tasks.*` to Claude/Haiku on Max. |
| **Fast mode (Opus 4.8)** | **Trial** | Med | Cheap-fast tier for low-stakes main-loop sub-tasks without leaving Claude; complements Haiku routing. Verify availability on session model. |
| **Agent teams** (`CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1`) | **Trial** | Med | Council engine depends on it and it works, but it is an *experimental* flag — API can shift. Keep enabled; isolate reliance to the council engine, watch release notes. |
| **Cron / scheduled routines** (`schedule` skill, Cron* tools) | **Assess** | Low | Zero current use. Candidate: automate registry usage-decay report + handover reminders. Adds a cloud-execution dependency; experiment before adopting. |
| **Auto-memory** (disabled via `CLAUDE_CODE_DISABLE_AUTO_MEMORY=1`) | **Assess** | Med | Intentionally off in favor of the bespoke `memory/HANDOVER-*.md` protocol. Re-assess whether auto-memory could reduce handover friction; keep disabled until it demonstrably beats the manual protocol. |
| **LSP plugin — swift-lsp** | **Hold** | High | Stack mismatch: real workload is TS/React + Python + bash, not Swift. Dead weight. |
| **LSP plugin — TypeScript/Python LSP** | **Trial** | Med | Matches actual workload; would give real navigation/diagnostics value. Swap swift-lsp for a TS-appropriate LSP. |

## Appendix B — Extract-to-private-repo footprint (prior art: dotfiles "secrets/niche split")

`du -sh skills/*` (verified): `soc-security` 1.8M, `ece` 252K, `resume-tailor` 136K,
`docx-to-pdf` ~8K, plus 15 `ece-*` agents (~2K lines) and the `/ece` command. Total dormant
footprint ≈ **2.2M of the 3.9M** skills tree. Token cost *at rest* is ~zero (skills load
on-demand), so the case for extraction is **discoverability + governance-surface reduction**,
not runtime cost — matching the common dotfiles pattern of splitting niche/work-specific
config into a sibling private repo referenced by path. Recommend a sibling private repo
(`my-claude-setup-private` already exists and hosts telemetry) with a one-line record in this
repo's README, over deletion — preserves the record the user wants.

## Appendix C — Corrections to the conductor's scan

- Registry is **not** all-zero: **10/67** council skills have uses>0 — tracking works; build a
  decay/usage report, do not rebuild tracking.
- `soc-security` is **1.8M**, the single largest dormant suite (the scan implied dormant suites
  were uniformly tiny). Strengthens the extraction case.
- Agents carry **no `model:` frontmatter** (0 of 38) — subagent models are set at spawn time by
  the council engine's routing table, so the unified routing system already has a single
  chokepoint to extend rather than 38 files to edit.

## Progress Checklist (technology-radar)
- [x] Step 1 categorized (harness features = Platform/Tool)
- [x] Step 2 maturity/quadrant assigned with evidence
- [x] Step 3 ecosystem health (Anthropic docs, OpenRouter pricing, GitHub issues)
- [x] Step 4 team familiarity (single-maintainer meta-repo; TS/React/Python/bash stack)
- [x] Step 5 migration cost (extract-to-private-repo footprint quantified)
- [x] Step 6 long-term viability (experimental-flag risk; stale-ID rot; account economics)
- [x] Step 7 project alignment (Max vs API axis is the deciding constraint)

Sources: [OpenRouter Pricing](https://openrouter.ai/pricing) · [June 2026 model roundup](https://www.digitalapplied.com/blog/openrouter-new-models-june-2026-roundup-pricing-rankings) · [OpenRouter 2026 pricing guide](https://betonai.net/openrouter-pricing-2026-complete-guide-to-every-model-tier-and-hidden-cost/) · [Claude Code model-config docs](https://code.claude.com/docs/en/model-config) · [GitHub #50803 (1m suffix drop)](https://github.com/anthropics/claude-code/issues/50803)
