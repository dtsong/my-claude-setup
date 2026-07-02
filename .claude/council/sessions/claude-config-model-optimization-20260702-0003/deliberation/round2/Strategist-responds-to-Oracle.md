# Strategist Response to Oracle

**Their position:** No routing or pruning change ships until a ~38-case golden-set eval harness exists in `pipeline/evals/`, because without it model swaps and prunes silently degrade quality; on the Max plan cheap tasks should route in-family to Haiku 4.5, not OpenRouter.

**My response:** Modify

**Reasoning:** Oracle is right that an unmeasured model swap is a guess, but wrong to apply one gate to all changes: the gate should bind on changes that alter which model answers at a live spawn site, and nothing in my MVP does that. F1 (drop the pinned `claude-fable-5[1m]` for the `fable` alias, reconcile the 1M flag) restores the repo's own governance and prior behavior; F2 (permissions rewrite) never touches a model; F4 refreshes stale 2024 IDs in a config file with zero callers; F5 is a routing *document*, not an activation. Gating these RICE 240-2000, sub-quarter-day fixes on a 2-3 day harness inverts the value order and leaves a known config conflict live in every session while we build test infrastructure for changes that cannot regress quality. So I concede the principle and resize the machinery: I add an **eval-before-activation** rule to the PRD, with a 12-case smoke set (Oracle's own regression pipeline already defines this tier) as the v1.1 precondition for the first change that actually re-routes a live call, which is wiring any caller to `routed_consult`. The full 38-case set becomes the gate for Phase 2 lens relay and for pruning decisions that Oracle wants data-driven, both already deferred in my roadmap, so the heavy harness lands exactly when the first change that needs it does. I also adopt Oracle's Max-plan point outright: cheap tasks route in-family to Haiku 4.5 on this account, which further shrinks what the smoke set must prove (no cross-vendor persona-transfer question in v1). Net effect on my Round 1 plan: MVP (F1/F2/F4/F5) unchanged and ungated; new item F11 "12-case smoke eval" enters v1.1 ahead of F3/F7 as the activation gate; F6/F8 remain Won't-now with the 38-case harness as their explicit entry criterion.

---

## Appendix — Revised sequencing under the eval-before-activation rule

| Phase | Items | Eval requirement |
|-------|-------|------------------|
| v1 (MVP) | F1 model alias fix, F2 permissions, F4 ID refresh, F5 routing table (doc + Haiku-in-family default for Max plan) | None: no live spawn site changes model |
| v1.1 | F11 smoke eval (12 cases: classification, scoring, scout, council-round), then F3 hook hardening, F7 suite extraction | F11 gates first `routed_consult` caller and any live model swap |
| v2 | F9 harness leverage, F10 tracking polish; grow smoke set toward 38 | Full set gates prune decisions Oracle wants measured |
| Future | F6 Phase 2 lens relay, F8 new skills | 38-case set + persona-transfer eval is the entry criterion |

**RICE for F11 (12-case smoke set):** Reach 30, Impact 2, Confidence 70%, Effort 0.5 day = 84. Tier 2, above F7, below F5. The 38-case build stays out of the PRD's committed scope; it is the documented prerequisite of F6/F8, so its cost is paid only if those bets are ever taken.

**What I am NOT conceding:** the MVP does not wait. A governance-violating pinned model ID that conflicts with `CLAUDE_CODE_DISABLE_1M_CONTEXT=1` is a defect in production today; fixing a defect does not require an eval harness any more than fixing a typo does.
