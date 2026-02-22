# Eval Case: Branch Predictor Poisoning Attack Surface Analysis

## Metadata
- **Case ID:** MA-004
- **Tier:** 2 (medium)
- **Skill Route:** microarch-attack-skill
- **Estimated Complexity:** medium

## Input
```json
{
  "user_prompt": "Analyze the branch predictor attack surface on our data-center SoC with ARM Neoverse V2 cores. Configuration:\n- Out-of-order, 10+ wide decode, speculative window ~160 cycles\n- Branch predictor: TAGE-based indirect predictor, BTB (8K entries), RSB (32 entries), conditional predictor (multi-table TAGE)\n- 4-way SMT\n- L1D: 64KB per core, L2: 1MB per core, LLC: shared\n- Security domains: Cross-VM (hypervisor-managed), Cross-container (Kubernetes pods)\n- Deployed mitigations: CSV2 (hardware branch predictor hardening), SMCCC-based BTB invalidation on context switch, kernel retpoline for indirect calls\n- Branch predictor state is per-physical-core, shared across SMT threads\n\nWe need to understand the residual attack surface for Spectre v2 (BTI — Branch Target Injection) and other branch predictor attacks (BHI — Branch History Injection, RSB poisoning) given the deployed mitigations. Are CSV2 and retpoline sufficient for cross-VM isolation with 4-way SMT?",
  "context": "Data-center SoC with aggressive branch prediction. Multiple mitigations deployed but 4-way SMT shares predictor state. Need residual risk assessment. Neoverse V2 is a real ARM microarchitecture — training knowledge applicable."
}
```

## Expected Output
MicroarchAttackFindings covering branch predictor attack variants:
- Spectre v2 / BTI (Branch Target Injection) via BTB poisoning
- BHI (Branch History Injection) via history collision
- RSB poisoning / SpectreRSB for return address misprediction
- Assessment of CSV2 effectiveness against each variant
- Retpoline effectiveness assessment
- Residual risk with 4-way SMT sharing predictor state

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output contains findings for at least Spectre v2/BTI and one additional branch predictor variant (BHI or RSB)
- [ ] Each finding identifies the specific predictor structure (BTB, TAGE, RSB)
- [ ] Each finding has a confidence tier, severity rating, and research reference or `[FROM TRAINING]`
- [ ] CSV2 mitigation assessed with effectiveness statement per attack variant
- [ ] 4-way SMT predictor sharing explicitly identified as an attack surface amplifier
- [ ] Speculative window quantified (~160 cycles)

### Should Pass (partial credit)
- [ ] BTI finding assesses whether CSV2 provides full predictor partitioning or probabilistic hardening
- [ ] BHI finding notes that branch history collisions can bypass BTB-level mitigations
- [ ] RSB poisoning assessed with RSB depth (32 entries) and underflow/overflow scenarios
- [ ] Cross-VM and cross-container domain pairs assessed independently
- [ ] Residual risk summary: what remains exploitable despite CSV2 + retpoline + BTB flush

### Bonus
- [ ] Notes that retpoline is a software mitigation for indirect branches and does not protect against hardware BTB poisoning of direct branches
- [ ] Discusses TAGE predictor aliasing — the multi-table structure creates history-dependent aliasing opportunities for BHI
- [ ] Recommends core-scheduling or SMT restriction for high-security VMs as defense-in-depth given shared predictor state

## Raw Trace Log
