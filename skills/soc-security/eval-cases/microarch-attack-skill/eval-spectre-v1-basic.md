# Eval Case: Basic Spectre v1 Bounds Check Bypass Analysis

## Metadata
- **Case ID:** MA-001
- **Tier:** 1 (simple)
- **Skill Route:** microarch-attack-skill
- **Estimated Complexity:** low

## Input
```json
{
  "user_prompt": "Analyze this ARM Cortex-A55 core for Spectre v1 (bounds check bypass) exposure. The core is used in an automotive SoC with these characteristics:\n- In-order pipeline, 8 stages\n- L1D: 32KB, 4-way set-associative, VIPT\n- L1I: 32KB, 4-way set-associative\n- L2: 256KB per core, 8-way, unified\n- Branch predictor: bimodal with 2-bit saturating counters\n- No SMT/HT\n- Security domains: Secure World (TrustZone) and Normal World\n- Speculative window: ~30 cycles estimated\n\nNo deployed mitigations for Spectre v1. No prior threat model. We want to know if this in-order core is susceptible to Spectre v1 bounds check bypass via speculative loads and cache-based covert channel.",
  "context": "Single-core analysis. In-order pipeline with limited speculation. TrustZone is the primary isolation mechanism. No SMT simplifies analysis. Automotive safety-critical SoC family."
}
```

## Expected Output
A MicroarchAttackFinding for Spectre v1 (UARCH-001 or equivalent catalog entry) that:
- Correctly identifies the bounds check bypass mechanism via conditional branch misprediction
- References the L1D cache as the covert channel for data exfiltration
- Assesses the in-order pipeline's reduced but non-zero speculative window (~30 cycles)
- Evaluates cross-domain impact for Secure World to Normal World leakage
- Notes the absence of mitigations and recommends CSDB/speculation barriers
- Includes catalog coverage for at least the Spectre v1 entry

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output contains at least one MicroarchAttackFinding for Spectre v1 / bounds check bypass
- [ ] Finding references the L1D cache as the side-channel / covert channel mechanism
- [ ] Finding includes a confidence tier (GROUNDED, INFERRED, SPECULATIVE, or ABSENT)
- [ ] Finding includes a severity rating
- [ ] Finding includes a research reference or `[FROM TRAINING]` marker (e.g., Kocher et al., CVE-2017-5753)
- [ ] Speculative window is quantified or estimated (even if approximate)

### Should Pass (partial credit)
- [ ] Finding correctly notes the in-order pipeline limits but does not eliminate Spectre v1 risk
- [ ] Cross-domain impact assessed for TrustZone Secure/Normal World boundary
- [ ] Mitigation assessment present with recommendation for CSDB barriers or index masking
- [ ] Attack surface classification marks Spectre v1 as APPLICABLE (not NOT APPLICABLE)
- [ ] Residual risk documented given absence of mitigations

### Bonus
- [ ] Notes that in-order cores have narrower speculative windows, reducing but not eliminating gadget availability
- [ ] Identifies specific Arm speculation barrier instruction (CSDB) rather than generic "add barriers"
- [ ] Discusses whether VIPT L1D tagging affects the observable cache state in the covert channel

## Raw Trace Log
