# Eval Case: Full Transient Execution Attack Surface Audit

## Metadata
- **Case ID:** MA-005
- **Tier:** 3 (complex)
- **Skill Route:** microarch-attack-skill
- **Estimated Complexity:** high

## Input
```json
{
  "user_prompt": "Conduct a full transient execution attack surface audit on our custom RISC-V application processor. This is a high-assurance SoC for government/defense applications. Full microarchitectural details:\n\nCore:\n- Custom RV64GC out-of-order core, 12 stages, 6-wide dispatch\n- Speculative window: ~150 cycles\n- Reorder buffer: 192 entries\n- 2-way SMT\n\nCache hierarchy:\n- L1D: 32KB, 8-way, VIPT, 4-cycle latency, 64B lines\n- L1I: 32KB, 8-way, VIPT\n- L2: 512KB per core, 16-way, inclusive of L1, PIPT\n- LLC: 4MB shared across 4 cores, 16-way, non-inclusive\n\nBranch prediction:\n- BTB: 4096 entries, 4-way set-associative\n- PHT: TAGE with 5 tables (4K entries each)\n- RSB: 16 entries\n- Indirect predictor: separate table, 1024 entries\n\nShared resources:\n- Fill buffers: 10 per core, shared between SMT threads\n- Store buffer: 48 entries, shared between SMT threads\n- Load queue: 72 entries, shared between SMT threads\n- TLB: L1 DTLB 64 entries (fully associative, per-thread), L2 TLB 1024 entries (shared)\n- Prefetcher: stride-based, shared between SMT threads\n\nSecurity domains:\n- S-mode (supervisor) vs U-mode (user)\n- PMP-enforced enclaves (3 enclaves, each with dedicated PMP regions)\n- Cross-enclave (enclave A vs enclave B)\n- Cross-core (LLC sharing)\n\nDeployed mitigations:\n- Fence.t instruction (custom speculation barrier, inserted by compiler at bounds checks)\n- BTB flush on context switch between security domains\n- L1D flush on enclave entry/exit\n- No SMT restrictions — both threads can run different enclaves simultaneously\n\nVendor errata: None published (custom core, no public vulnerability disclosures).\n\nWe need full catalog coverage (UARCH-001 through UARCH-020) with disposition for each entry. This is for a CC EAL5+ evaluation.",
  "context": "Custom RISC-V OoO core for high-assurance application. No public vulnerability history — all analysis is from first principles based on microarchitectural description. CC EAL5+ target requires comprehensive coverage. Multiple overlapping security domains. 2-way SMT with shared microarchitectural buffers. Full catalog sweep required."
}
```

## Expected Output
A comprehensive microarchitectural attack surface audit with:
- Full catalog coverage table (UARCH-001 through UARCH-020) with status for each entry
- MicroarchAttackFindings for every APPLICABLE/MITIGATED catalog entry
- Cross-domain impact matrix for all security domain pairs (S/U, cross-enclave, cross-core)
- Mitigation assessment for each deployed countermeasure (fence.t, BTB flush, L1D flush)
- Residual risk assessment focusing on SMT-shared buffers without thread isolation
- DocumentEnvelope with confidence summary and caveat block
- Speculative window quantification across attack classes

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Catalog coverage table present with status for every UARCH-001 through UARCH-020 entry
- [ ] At least 8 MicroarchAttackFindings produced (Spectre v1/v2, cache timing, MDS variants, branch predictor, TLB, port contention, prefetch — multiple applicable given the architecture)
- [ ] Every finding has: confidence tier, severity, research reference or `[FROM TRAINING]`, microarchitectural component, speculative window
- [ ] Every finding has mitigation assessment with residual risk
- [ ] SMT-shared buffers (fill buffer, store buffer, load queue) explicitly assessed for cross-thread data sampling
- [ ] Cross-domain impact assessed for at least 3 domain pairs (S/U, cross-enclave, cross-core)
- [ ] Caveat block present noting this is a custom core with no public vulnerability history

### Should Pass (partial credit)
- [ ] Fence.t instruction assessed for Spectre v1 effectiveness — is it equivalent to LFENCE/CSDB?
- [ ] L1D flush on enclave entry/exit assessed for completeness — does it cover L2/LLC residual state?
- [ ] BTB flush on context switch assessed — does it protect against SMT cross-thread BTB poisoning?
- [ ] Shared L2 TLB (1024 entries) assessed for TLB-based side-channels across SMT threads
- [ ] Shared prefetcher assessed for prefetch-based covert channels
- [ ] RSB depth (16 entries) assessed for underflow scenarios with deep call chains
- [ ] Confidence tiers assigned mechanically: INFERRED for most findings (architecture described but no RTL/errata)

### Bonus
- [ ] Notes that RISC-V lacks standardized speculation barrier semantics — fence.t is custom and its microarchitectural behavior must be verified
- [ ] Identifies that PMP enforcement relies on committed (not speculative) checks, creating a transient execution window before PMP violation traps
- [ ] Recommends SMT restriction for cross-enclave isolation as the highest-impact remediation
- [ ] Provides state space estimate for the reachable attack surface (192 ROB entries x 150 cycle window x shared structures)
- [ ] Notes CC EAL5+ implications: AVA_VAN.4 requires resistance to high attack potential — all INFERRED findings need lab validation

## Raw Trace Log
