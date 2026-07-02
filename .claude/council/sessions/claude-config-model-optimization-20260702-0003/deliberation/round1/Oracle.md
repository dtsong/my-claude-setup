# Oracle Position — Claude Config & Model-Routing Optimization

**Core recommendation:** Treat model selection as ONE evaluation-gated routing system keyed by `(spawn-site × profile × account-type)`, unified in `skills/council/model-routing.json` as the single source of truth, and refuse to ship any routing or pruning change that lacks a golden-set eval to prove it holds the quality bar. On the Max plan the cheap-task path should route to in-family Haiku 4.5 (free under plan, no external key, no cross-vendor dependency), not OpenRouter; OpenRouter earns its dollars only on the API-billed account and only for tasks an eval clears.

**Key argument:**
The repo already contains a mature routing spine that the incoming changes ignore. `commands/_council-engine.md` (lines 91-121) defines a spawn-site-keyed routing table with `lean/balanced/max` profiles and an explicit governance rule: *"Always use tier aliases (`sonnet`, `opus`, `fable`) — never pinned `claude-*` model IDs."* The uncommitted `settings.json` diff sets the session default to `claude-fable-5[1m]` — a pinned ID with a 1M-context suffix — which violates the repo's own rule AND conflicts with `CLAUDE_CODE_DISABLE_1M_CONTEXT=1` still set in `env` (you're paying the pin's staleness risk to request a context window the same file disables). From the cost-latency-quality lens this is the wrong default: a meta-config repo is mostly small markdown, so 1M context buys latency and (on API) token cost you won't use. Meanwhile OpenRouter Phase 1 is *further along than the handover states* — `model-routing.json`, `openrouter_client.py`, `routing.py`, README, and tests all exist and pass the fail-soft contract — but it has ZERO callers (plumbing with no consumer) and its task IDs are stale 2024 models (`openai/gpt-4o-mini`, `google/gemini-flash-1.5`). Routing a task to those "because they're cheap" is exactly the anti-pattern my discipline rejects: cheaper-is-fine is a claim you verify against an eval, not assume. On the Max plan the cost argument inverts entirely — OpenRouter calls spend real dollars while Haiku 4.5 draws on the same plan rate-limit pool for free, so cross-vendor routing there is only justified for genuine diversity experiments, never for cost. The missing piece across all four workstreams is the same: there is no eval harness, so 60 council skills sit at zero recorded uses with no way to tell a good routing/prompt change from a regression. Build the smallest possible golden-set harness FIRST (~30-50 tasks across the spawn classes: classification, scout-research, scoring, council-lens, implement, review), score against a rubric, and gate every model swap and every prune on it.

**Concrete routing design (per spawn site):**

| Spawn site | Max plan (quality ceiling / rate-limit) | API-billed (cost/session) | Notes |
|---|---|---|---|
| Session default | `opus` daily, `fable` for ceiling; drop `[1m]`; reconcile env flag | `sonnet` default, escalate manually | Tier alias only; never pinned ID |
| Council deliberation | `max` profile (opus + fable challenges) | `lean` (sonnet + opus challenges) | Already implemented — keep |
| Council audits | opus | sonnet | Already implemented |
| /ship→/looper implement | opus | sonnet | GAP: no routing today; add it |
| /ship PR review | fable/opus | sonnet, opus on repeat failure | Review quality > volume |
| OpenRouter cheap tasks (Phase 1) | route to `claude`→Haiku 4.5 (no OpenRouter) | current-gen cheap model, eval-gated | Update stale 2024 IDs |
| OpenRouter lens relay (Phase 2) | only after persona-transfer eval passes | same | "Diversity" unproven until eval |

**Risks if ignored:**
- **Quality regression invisible to you.** Pinned `[1m]` default + no eval harness means a model or prompt change silently degrades council/ship output and nothing catches it; 60 zero-use skills means you're flying blind on what quality even is today.
- **OpenRouter cost/quality trap.** Wiring `routed_consult` to stale gpt-4o-mini/gemini-flash-1.5 without an eval ships worse output; on the Max plan it also converts free rate-limit work into real API dollars for no benefit. Phase 2 lens relay claims "cross-vendor diversity" that is actually degraded lenses if Claude-tuned personas don't transfer.
- **Config self-contradiction persists.** `claude-fable-5[1m]` violates the repo's stated alias-only governance and fights `CLAUDE_CODE_DISABLE_1M_CONTEXT=1`; a governance repo that breaks its own rule in the top-level config erodes the whole spec.

**Dependencies on other domains:**
- **Architect:** owns the unified routing-config schema — routing currently lives in TWO places (`_council-engine.md` markdown table + `model-routing.json`) with no shared contract; I need one schema that `/ship`, `/looper`, and the council engine all read.
- **Skeptic:** the private-repo hard dependency (`session_telemetry.py` fires on EVERY tool use; ece/resume/soc are symlinks into `my-claude-setup-private`) plus OpenRouter as an external dependency are failure modes I need mapped and the fail-soft path verified.
- **Tuner/cost lens:** the rate-limit-vs-dollars accounting per account, and whether rate limits are actually the binding Max-plan constraint (determines if OpenRouter cheap routing is ever worth it).
- **Whoever owns pruning:** I gate disposition of the 15 ece agents / dormant suites on usage-tracking data + the eval harness, not vibes; the skills are already extracted (symlinks), so the real decision is the agents and the private-repo dependency.

---

## Appendix A — prompt-engineering skill output

### Prompt Design: OpenRouter cheap-task routing + council lens relay

**Task Definition**
- **Input:** a sub-task (classification / scout-research / scoring) or a full council-round prompt, plus a persona/system prompt.
- **Output:** the routed model's completion, returned verbatim to the caller.
- **Constraints:** must fail soft to Claude on any error; persona prompts are reused verbatim (no per-model rewrite exists today — a risk).

**Prompt versioning finding:** council personas ARE the prompts, but they are not versioned with a changelog linked to eval scores (skill Step 6 unmet). Pattern A reuses a Claude-tuned persona on a non-Claude model with no evidence the instructions transfer; instruction-following, structured-output adherence, and refusal behavior differ across vendors. Recommendation: before Phase 2, run each candidate lens persona through the golden set on both Claude and the target OpenRouter model; only promote lenses whose non-Claude score is within threshold of Claude.

**Model recommendation (cheap-task class):**
- Max plan: `claude-haiku-4-5-20251001` via `claude` routing (temp 0 for classification/scoring). Rationale: in-family, free under plan, no key, strong instruction-following; OpenRouter adds a paid external dependency for no gain.
- API account: a current-generation cheap model (the committed 2024 IDs are stale — pick at implementation from the claude-api skill / OpenRouter `list_models`), eval-gated at temp 0.

**Structured-output note:** `consult` returns free `text`; cheap tasks (classification/scoring) need parseable structured output. Add explicit JSON-schema instruction to the system prompt and a rule-based validator in the caller before trusting the value.

## Appendix B — ai-evaluation skill output

### AI Evaluation Framework — routing & config regression

**Evaluation Dimensions**

| Dimension | Weight | Scoring Method | Threshold |
|---|---|---|---|
| Task correctness | 45% | LLM-as-judge (1-5) vs golden answer | >= 4.0 |
| Format compliance | 25% | Rule-based (JSON parses, required fields) | 100% |
| Persona/instruction fidelity | 20% | LLM-as-judge on lens voice + constraints | >= 4.0 |
| Cost/latency budget | 10% | measured tokens + ms vs profile budget | within profile |

**Golden Dataset**

| Category | Count | Description |
|---|---|---|
| Common | ~20 | Representative classification / scoring / scout / council-round / implement / review tasks |
| Edge | ~10 | Empty/ambiguous input, long context, multi-constraint |
| Adversarial | ~8 | Prompt-injection in retrieved text, off-topic, contradictory context |

- **Storage:** `pipeline/evals/` (outside skill dirs per governance), version-controlled.
- **Size:** start ~38, grow to 50+; enough to make routing decisions defensible, small enough to run cheap.

**Scoring rubric (correctness LLM-as-judge):** 5 = matches golden in all aspects; 4 = minor harmless diff; 3 = correct core, issues; 2 = partial, missing key info; 1 = wrong/misleading.

**Regression pipeline:**
```
[routing/prompt/model change] -> smoke (12 cases) -> pass? -> merge
[profile release / OpenRouter wiring] -> full eval (38+) -> >= threshold? -> ship
```
Gate: composite >= 4.0 AND format 100%. This is what makes "Haiku is sufficient / gpt-4o-mini is not" a measured decision instead of a guess, and what protects the /ship pipeline from silent model-swap regressions.

**Hallucination/faithfulness checks:** for scout-research and any RAG-shaped task, validate cited references against source before accepting; flag fabricated URLs/citations.

**Production monitoring (lightweight):** the existing `registry.json` usage tracker should be extended to log the routed model + a sampled score per spawn, so drift (a model version degrading) becomes visible instead of the current all-zeros blind spot.
