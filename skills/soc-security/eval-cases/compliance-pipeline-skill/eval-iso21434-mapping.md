# Eval Case: ISO 21434 Compliance Mapping for Automotive SoC

## Metadata
- **Case ID:** CP-002
- **Tier:** 1 (simple)
- **Skill Route:** compliance-pipeline-skill
- **Estimated Complexity:** low

## Input
```json
{
  "user_prompt": "Map our automotive ADAS SoC security controls against ISO 21434 (Road Vehicles — Cybersecurity Engineering). The SoC includes:\n- Cortex-R52 safety island with lockstep execution\n- Hardware Security Module (HSM) with secure boot and key management\n- CAN-FD and Ethernet TSN interfaces to vehicle network\n- Secure debug with certificate-based authentication\n- OTA firmware update channel with dual-bank flash\n- No TARA (Threat Analysis and Risk Assessment) has been performed yet\n- Technology domain: supply-chain\n- SoC family: automotive\n\nI need a requirements extraction and compliance status for Clauses 7-9 (cybersecurity management, risk assessment methods, and concept phase).",
  "context": "Standalone mode — no upstream entities. Engineer wants Stage 1 extraction for ISO 21434 Clauses 7-9 and Stage 2 evidence mapping. No TARA has been performed, which is a foundational requirement. Spec text not provided."
}
```

## Expected Output
A compliance pipeline output covering ISO 21434 Clauses 7-9 with:
- SecurityRequirement entities for cybersecurity management, risk assessment methods, and concept-phase activities
- Evidence mapping showing HSM and secure boot as partial evidence for some requirements
- Major gap identified for missing TARA (Clause 8 dependency)
- All requirements tagged for automotive SoC family

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output contains SecurityRequirement entities for ISO 21434 Clauses 7, 8, and 9
- [ ] Missing TARA flagged as a `gap: not-met` for Clause 8 (risk assessment methods)
- [ ] Every requirement maps to `socFamily: [automotive]` and `domain: supply-chain`
- [ ] Confidence tiers assigned to every mapping — majority should be INFERRED or SPECULATIVE given no spec text
- [ ] All findings carry `[FROM TRAINING]` markers
- [ ] SPECULATIVE claims blocked from final output until engineer acknowledges

### Should Pass (partial credit)
- [ ] Clause 7 requirements include cybersecurity policy, organizational rules, and competence management
- [ ] Clause 9 concept-phase requirements reference cybersecurity goals derivation from TARA
- [ ] HSM with secure boot mapped as partial evidence for Clause 9 cybersecurity goals
- [ ] OTA update channel mapped to lifecycle cybersecurity management requirements
- [ ] Gap analysis notes that TARA absence blocks downstream compliance for Clauses 9-15

### Bonus
- [ ] CAN-FD and Ethernet TSN interfaces flagged as attack surfaces requiring Clause 8 TARA coverage
- [ ] Cross-reference to UNECE WP.29 R155 noted as related automotive cybersecurity regulation
- [ ] Lockstep Cortex-R52 assessed as safety mechanism with cybersecurity co-dependency

## Raw Trace Log
