# Eval Case: Cross-Standard Overlap Analysis (FIPS 140-3 + Common Criteria)

## Metadata
- **Case ID:** CP-003
- **Tier:** 2 (medium)
- **Skill Route:** compliance-pipeline-skill
- **Estimated Complexity:** medium

## Input
```json
{
  "user_prompt": "Analyze the overlap between FIPS 140-3 Level 2 and Common Criteria EAL4+ for our data center DPU's crypto subsystem. We need to understand which requirements are shared, which are unique to each standard, and where a single implementation artifact can satisfy both.\n\nDPU crypto subsystem details:\n- AES-256-GCM and ChaCha20-Poly1305 hardware engines\n- ECDSA P-256/P-384 for attestation signing\n- Hardware TRNG with SP 800-90B compliant conditioning\n- Key hierarchy: HUK (fused) -> CDI -> per-session keys via HKDF\n- Secure key erasure (zeroization) on tamper detect\n- Firmware-managed key lifecycle with hardware-enforced access control\n- Technology domain: confidential-ai\n- SoC family: data-center\n\nThe DPU targets both FedRAMP (requires FIPS) and international markets (requires CC certification). We want a unified compliance strategy.",
  "context": "Standalone mode. Engineer wants cross-standard analysis identifying overlap, unique requirements, and shared evidence opportunities. Two standards against one component. No prior compliance results. Spec text not provided for either standard."
}
```

## Expected Output
A cross-standard compliance analysis producing:
- SecurityRequirement entities tagged to both FIPS 140-3 and Common Criteria EAL4+
- Overlap matrix showing shared requirements (self-tests, key management, design documentation)
- Unique requirements per standard (FIPS: CAVP algorithm validation; CC: vulnerability analysis, TOE scope)
- Evidence reuse recommendations where a single artifact satisfies both standards
- Gap analysis with unified remediation plan

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output identifies requirements from both FIPS 140-3 Level 2 and Common Criteria EAL4+
- [ ] Overlap analysis explicitly maps shared areas: key management, self-tests, design assurance, lifecycle
- [ ] FIPS-unique requirements identified (at minimum: CAVP algorithm validation, module boundary definition)
- [ ] CC-unique requirements identified (at minimum: Security Target, vulnerability analysis, ADV_ARC)
- [ ] Every requirement has confidence tier — all marked `[FROM TRAINING]` given no spec text
- [ ] Cross-standard mapping does not assume evidence transfers without explicit justification

### Should Pass (partial credit)
- [ ] Key hierarchy (HUK -> CDI -> session keys) assessed against both FIPS key management (SP 800-133) and CC FCS_CKM
- [ ] Zeroization on tamper detect mapped to both FIPS physical security and CC FCS_CKM.4
- [ ] TRNG with SP 800-90B conditioning mapped as shared evidence for both standards
- [ ] Unified remediation plan identifies artifacts that serve dual purpose (e.g., design documentation serves both FIPS Level 2 and CC ADV_FSP)
- [ ] Coverage boundary clearly states what is assessed per standard

### Bonus
- [ ] FedRAMP authorization dependency chain noted (FIPS validation -> FedRAMP ATO)
- [ ] Evidence reuse assessment rates each shared artifact as High/Medium/Low reusability
- [ ] Effort estimate comparison: unified certification path vs. sequential independent certification

## Raw Trace Log
