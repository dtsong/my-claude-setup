# Oracle Response to Strategist

**Their position:** MVP = config hygiene (F1 model pin, F2 permissions, F4 refresh stale cheap-model IDs) plus the unified two-account routing table (F5), shipped now as RICE 240-2000 quick wins; the eval harness ranks nowhere in v1, with heavier machinery deferred.

**My response:** Modify

**Reasoning:** Strategist's verified facts move me. F1 is not a model-quality change, it REVERTS an ungoverned deviation back to the repo's own alias rule; F2 is permissions plumbing; F5 is a design document. None of those alter what any live spawn site actually emits, so gating them on a 38-case harness was me applying an activation-time control to documentation-time work: sequencing error, conceded. The `routed_consult` zero-callers fact matters most: a stale ID sitting in `model-routing.json` with no consumer degrades nothing today, so even F4 can merge ungated. But the gate does not disappear, it moves to the correct boundary: the moment any spawn site FLIPS models on live traffic (a `/ship` or council profile change, `routed_consult` gaining its first caller, any Phase 2 lens relay). At that boundary, ungated swaps are silent regressions by construction, and Strategist's own success metric for F4/F5 ("fail-soft to Claude preserved") is unverifiable without at least a smoke set to define what "preserved" means. So I shrink the ask to fit the RICE frame: a 12-case smoke set (4 classification, 4 scoring/structured-output, 4 council-lens fidelity) stored in `pipeline/evals/`, ~0.5 day, shipped as an acceptance criterion INSIDE F5 rather than as a separate blocking workstream; the full 38-case harness becomes v1.1 alongside F3/F7, and it also becomes the evidence standard for F7 pruning dispositions and the explicit entry gate for F6/F8 leaving "Won't (now)." Net: Strategist's v1 ships unblocked; nothing that changes live model behavior ships unmeasured.

---

## Appendix — Revised gate placement

| Change class | Example | Eval requirement |
|---|---|---|
| Governance revert / config hygiene | F1 model alias, F2 permissions | None |
| Dormant config value, zero callers | F4 ID refresh (today) | None to merge; smoke set before first caller |
| Routing design doc | F5 table | Ships WITH 12-case smoke set as acceptance criterion (~0.5 day, inside F5's 1.0 day) |
| Live model flip at any spawn site | routed_consult first caller, /ship or council profile change | Smoke set pass (composite >= 4.0, format 100%) |
| Persona transfer / cross-vendor | F6 Phase 2 lens relay | Full harness (38+) on both vendors; stays Won't (now) until then |
| Pruning disposition | F7 and beyond | Usage data from working registry tracking, not vibes; harness for anything routing-adjacent |

RICE self-correction: scoped to 12 cases at 0.5 day riding inside F5, the smoke set's effective RICE is no longer the "money pit" my Round 1 full-harness-first sequencing implied; it inherits F5's Tier 2 slot instead of blocking Tier 1.
