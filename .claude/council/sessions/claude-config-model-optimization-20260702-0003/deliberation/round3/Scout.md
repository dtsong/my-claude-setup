# Scout Final Position — Claude Config & Model-Routing Optimization

## Revised recommendation

Build ONE routing system keyed by **spawn site × account type**, and let economics flip the
default: on the **Max plan** cheap sub-tasks route to **native Haiku 4.5** (rate-limit cost,
zero dollars); on the **API account** OpenRouter Pattern B saves real money but only after its
2024-era model IDs are refreshed and a `list_models()` periodic refresh is wired. OpenRouter
**Pattern A (cross-vendor lens diversity)** downgrades from Trial to **gated Trial**: it may
run on one lens only behind a send-allowlist, ZDR + no-training flags, a kill switch, and an
actual-model audit log, and must prove measurable diversity value or collapse to Pattern B on
the API account. **Extract the dormant suites now** (ECE, resume-tailor, docx-to-pdf,
soc-security) to a sibling private repo on workload judgment, independent of any usage data.
Treat all council-skill pruning as **deferred and evidence-gated**.

## Concessions made and why

1. **Retracted "tracking works" entirely (Round 1 Appendix C's headline claim).** Craftsman
   verified and I re-verified: the *committed* `registry.json` shows **0/67** uses at HEAD
   despite 4+ prior council sessions; all 10 nonzero entries are *uncommitted writes from this
   very session* (`last_used 2026-07-02`, matching the skills we loaded). My "10/67 skills have
   uses, build a decay report" recommendation was built on session-local noise. I dropped it.
   What I keep: the engine-level increment (`_council-engine.md:672-673`) is the *right layer*
   and it *did* fire today, so a deterministic-increment fix plus a bounded window can produce
   real data. This is a fix-then-measure, not a rebuild.

2. **Conceded that zero-uses is inconclusive, not a prune signal.** I deprioritized my implicit
   Round 1 lean toward using registry counts as pruning evidence. Decision rule I now endorse:
   **any-use = keep, zero-use = inconclusive** (never auto-prune). Council-skill pruning waits
   on the full 38-case eval harness as its entry gate (per Strategist/Oracle), not on counts.

3. **Downgraded Pattern A from Trial to gated Trial.** Skeptic's egress finding is real:
   `openrouter_client.py` sends system + prompt verbatim with no redaction. I still argue
   OpenRouter *platform* controls (per-request ZDR enforcement, no-training toggle, provider
   allowlists) address the controllable half of the trust boundary, but I concede they do not
   substitute for a send-allowlist in `routing.py`. Pattern A is Critical-severity ungated,
   Medium residual when gated. The gate also happens to test Oracle's persona-transfer doubt.

4. **Accepted the eval-before-activation rule over my silence on sequencing.** I had no eval
   position in Round 1. I adopt Strategist/Oracle's converged rule: the MVP (F1 alias fix, F2
   permissions, F4 ID refresh, F5 routing doc, F3a fail-soft wrapper) changes **no live model
   behavior** and ships ungated; a 12-case smoke set gates the first `routed_consult` caller;
   the full 38-case harness gates Phase 2 relay and any prune decision.

## Non-negotiables (external constraints / standards)

1. **Refresh OpenRouter model IDs before any Pattern B activation.** `gpt-4o-mini` and
   `google/gemini-flash-1.5` are ~2 years stale; by 2026-06 Gemini 2.5 Flash repriced to
   $0.30/$2.50 and the cheap frontier moved to Ling 2.6 Flash, Nemotron, MiniMax M3, Qwen3.7.
   A stale ID 404s, silently never fires the cheap path, and the API account overpays with Opus
   while believing it routes cheap. Wire `list_models()` to a periodic refresh so IDs never rot
   again.

2. **Pattern B stays Hold on Max, Trial on API.** OpenRouter bills real dollars + a flat 5.5%
   credit fee where native Haiku 4.5 on Max is rate-limit-free. Routing `tasks.*` to OpenRouter
   on the Max account spends money to avoid a free call. Default `tasks.*` to Claude/Haiku on
   Max; enable OpenRouter Pattern B only on the API account, behind Skeptic's cost ceiling.

3. **No pinned `claude-*` model IDs in `settings.json`.** `model: "claude-fable-5[1m]"` violates
   this repo's own governance (council-engine line 105: tier aliases only) and self-contradicts
   `CLAUDE_CODE_DISABLE_1M_CONTEXT=1` (which removes 1M variants from the picker). Revert to a
   tier alias.

4. **Extraction preserves the record, does not delete.** Dormant suites move to the existing
   `my-claude-setup-private` sibling repo with a one-line pointer in this repo's README. The
   user wants the record kept; deletion is off the table.

## Implementation notes

- **Routing schema (Architect owns):** extend `skills/council/model-routing.json` with an
  `account: {max|api}` axis and a `haiku` tier. Subagents carry no `model:` frontmatter (0/38),
  so the engine routing table is the single chokepoint. Refreshed cheap-tier candidates to
  evaluate on API: `google/gemini-2.5-flash`, and frontier-cheap `ling-2.6-flash`,
  `minimax-m3`, `qwen3.7` (verify live IDs via `list_models()` at wire time).
- **F3a (joins v1 MVP):** fail-soft existence guard + vendored wrapper that removes the private
  path `$HOME/Development/my-claude-setup-private/hooks/session_telemetry.py` from public
  `settings.json` (5 event edits + one ~5-line dispatcher). Fixes break-on-clone, unblocks the
  API work account, closes the private-path leak. F3b (per-call perf, batching, alert tuning)
  → v1.1.
- **Telemetry hardening (gates real prune data):** make the engine increment durable
  (auto-commit or untracked sidecar), register a telemetry hook for standalone (non-council)
  suites which load inline via `skillContent` and are not covered by
  `skill-telemetry.sh`. Then open a **2-4 week** measurement window scoped to the council long
  tail before any council-skill prune.
- **Pattern A gate (if trialed):** send-allowlist in `routing.py` (no file contents/secrets),
  ZDR + no-training request flags, provider allowlist, kill switch, and a log asserting the
  actual vendor model returned. One lens only; kill if no measurable diversity value.
- **Harness leverage:** swap `swift-lsp` (stack mismatch) for a TS/Python LSP; keep Agent Teams
  enabled but isolate reliance to the council engine (experimental flag); Assess Cron routines
  for the usage-decay report once telemetry is durable. See Round 1 Appendix A radar.
- **Extraction footprint (verified `du -sh`):** soc-security 1.8M, ece 252K, resume-tailor
  136K, docx-to-pdf ~8K, + 15 `ece-*` agents + `/ece` command ≈ 2.2M of 3.9M skills tree.
  Case is discoverability + governance-surface reduction, not runtime cost (skills load
  on-demand). Ensure no secrets follow the suites into the private repo (Skeptic/Security).

Sources: [OpenRouter Pricing](https://openrouter.ai/pricing) · [June 2026 model roundup](https://www.digitalapplied.com/blog/openrouter-new-models-june-2026-roundup-pricing-rankings) · [OpenRouter 2026 pricing guide](https://betonai.net/openrouter-pricing-2026-complete-guide-to-every-model-tier-and-hidden-cost/) · [Claude Code model-config docs](https://code.claude.com/docs/en/model-config) · [GitHub #50803 (1m suffix drop)](https://github.com/anthropics/claude-code/issues/50803)
