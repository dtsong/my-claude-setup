# Eval Case: MDS (Microarchitectural Data Sampling) Vulnerability Analysis

## Metadata
- **Case ID:** MA-003
- **Tier:** 2 (medium)
- **Skill Route:** microarch-attack-skill
- **Estimated Complexity:** medium

## Input
```json
{
  "user_prompt": "Analyze MDS (Microarchitectural Data Sampling) vulnerability exposure on our server SoC using a custom x86-64 core. Core details:\n- Out-of-order pipeline, 14 stages, speculative window ~200 cycles\n- 2-way SMT (Hyper-Threading enabled)\n- L1D: 48KB, 12-way, VIPT with store buffer (56 entries), fill buffers (12 entries), load ports (2)\n- L2: 1.25MB per core, 20-way\n- LLC: 30MB shared, 20-way\n- Store buffer shared between SMT threads on the same physical core\n- Fill buffers shared between SMT threads\n- Load ports shared between SMT threads\n- Security domains: Cross-VM (KVM hypervisor), Cross-container, User-Kernel\n- Deployed mitigations: VERW instruction issued on context switch (microcode update applied)\n- No core-scheduling (SMT threads can run different VMs simultaneously)\n\nAssess MFBDS (Fallout), MLPDS, MSBDS, and TAA variants. Determine if VERW is sufficient given SMT is enabled and threads share microarchitectural buffers.",
  "context": "Server SoC with SMT. MDS family of attacks targeting store buffer, fill buffer, and load port sampling. VERW deployed but SMT co-residency remains. Multiple security domain pairs. Custom x86-64 core — vendor mitigations may differ from Intel reference."
}
```

## Expected Output
Multiple MicroarchAttackFindings covering each MDS variant:
- MFBDS (Microarchitectural Fill Buffer Data Sampling / Fallout) — fill buffer leakage
- MLPDS (Microarchitectural Load Port Data Sampling) — load port leakage
- MSBDS (Microarchitectural Store Buffer Data Sampling) — store buffer leakage
- TAA (TSX Asynchronous Abort) — if TSX is present
- Assessment of VERW effectiveness with SMT enabled
- Cross-domain impact for each VM/container/kernel boundary
- Catalog coverage table for relevant UARCH entries

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output contains findings for at least MFBDS, MLPDS, and MSBDS variants
- [ ] Each finding identifies the specific microarchitectural buffer (fill buffer, load port, store buffer)
- [ ] Each finding has a confidence tier, severity rating, and research reference or `[FROM TRAINING]`
- [ ] VERW mitigation assessed with explicit statement on its effectiveness
- [ ] SMT co-residency risk explicitly addressed — threads sharing buffers across security domains
- [ ] Speculative window quantified (~200 cycles)

### Should Pass (partial credit)
- [ ] VERW noted as clearing buffers only on context switch, not protecting against concurrent SMT thread sampling
- [ ] Cross-domain impact matrix present: Cross-VM, Cross-container, User-Kernel pairs assessed per variant
- [ ] Residual risk documented: VERW insufficient without core scheduling or SMT disabling
- [ ] Each finding maps to the correct microarchitectural component (store-buffer, fill-buffer, port)
- [ ] Mitigation recommendation includes either disabling SMT or deploying core-scheduling (no cross-domain SMT pairing)

### Bonus
- [ ] TAA variant assessed with note on TSX availability (or asks whether TSX is present)
- [ ] Fill buffer entry count (12) and store buffer entry count (56) used to assess data sampling window size
- [ ] Notes that custom x86-64 core may have implementation-specific buffer behavior differing from Intel reference errata

## Raw Trace Log
