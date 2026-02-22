# Eval Case: Simple Cache Timing Side-Channel Assessment

## Metadata
- **Case ID:** MA-002
- **Tier:** 1 (simple)
- **Skill Route:** microarch-attack-skill
- **Estimated Complexity:** low

## Input
```json
{
  "user_prompt": "Assess the cache timing side-channel attack surface on our shared LLC in a dual-core ARM Cortex-A76 cluster. Configuration:\n- L1D: 64KB per core, 4-way, PIPT\n- L1I: 64KB per core, 4-way\n- L2: 256KB per core, 8-way, inclusive of L1\n- LLC (L3): 2MB shared across both cores, 16-way, non-inclusive\n- No cache partitioning (CAT) deployed\n- Security domains: Core 0 runs a secure TEE (OP-TEE), Core 1 runs Linux (Normal World)\n- Both cores share the LLC without hardware partitioning\n\nWe are concerned about Prime+Probe and Flush+Reload attacks from Normal World (Core 1) observing TEE (Core 0) AES key-dependent cache access patterns in the shared LLC. SoC family: Mobile.",
  "context": "Two-core cluster with shared LLC. No cache partitioning. Cross-domain threat: Normal World observing Secure World via cache timing. Classic cache side-channel scenario. No prior analysis."
}
```

## Expected Output
MicroarchAttackFindings covering cache timing attacks on the shared LLC, including:
- Prime+Probe attack assessment on the shared L3
- Flush+Reload assessment (if shared memory pages exist across domains)
- Identification of the shared LLC as the primary attack surface
- Cross-domain impact analysis (TEE on Core 0 vs. Linux on Core 1)
- Mitigation recommendations (cache partitioning, constant-time crypto)

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output contains at least one finding for cache timing side-channel on the shared LLC
- [ ] Finding identifies the shared L3/LLC as the exploitable shared resource
- [ ] Finding specifies the cross-domain pair: Secure TEE (Core 0) vs. Normal World (Core 1)
- [ ] Every finding has a confidence tier and severity rating
- [ ] Every finding has a research reference or `[FROM TRAINING]` marker
- [ ] Attack surface classification marks cache side-channel as APPLICABLE

### Should Pass (partial credit)
- [ ] Prime+Probe attack assessed separately from Flush+Reload with distinct applicability rationale
- [ ] Absence of cache partitioning (CAT) explicitly noted as increasing attack feasibility
- [ ] Mitigation assessment recommends cache partitioning (way-based or set-based) as primary countermeasure
- [ ] AES key-dependent table lookups identified as the specific leakage source
- [ ] Residual risk documented for each finding

### Bonus
- [ ] Notes that Flush+Reload requires shared physical pages across domains, which TrustZone may prevent
- [ ] Discusses L2 inclusivity implications for eviction-based attacks propagating to LLC
- [ ] Mentions cache line granularity (64B) and its relationship to AES T-table layout for attack precision

## Raw Trace Log
