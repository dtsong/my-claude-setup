# Eval Case: Simple FIPS 140-3 Gap Analysis for Crypto Module

## Metadata
- **Case ID:** CP-001
- **Tier:** 1 (simple)
- **Skill Route:** compliance-pipeline-skill
- **Estimated Complexity:** low

## Input
```json
{
  "user_prompt": "Run a FIPS 140-3 Level 2 gap analysis on our AES-GCM crypto accelerator module. The module is part of a client SoC with the following characteristics:\n- AES-128/256-GCM hardware engine with DMA interface\n- Key storage in OTP fuses (256-bit slots, 8 total)\n- TRNG based on ring-oscillator entropy source\n- JTAG debug port with password lock (not disabled)\n- No power-up self-test implemented\n- No conditional self-test for TRNG output\n- Firmware loads keys from OTP into key registers via APB\n- Single technology domain: secure-boot-dice\n- SoC family: client",
  "context": "Standalone mode — no upstream ThreatFinding or VerificationItem entities. Engineer wants Stage 1 requirement extraction and Stage 3 gap analysis against FIPS 140-3 Level 2. No prior ComplianceResult entities exist. Spec text not provided — use training knowledge with appropriate markers."
}
```

## Expected Output
A 3-stage compliance pipeline output covering FIPS 140-3 Level 2 requirements for a crypto module, producing SecurityRequirement and ComplianceResult entities with:
- Requirements extracted for FIPS 140-3 areas: cryptographic module specification, module interfaces, roles/services/authentication, software/firmware security, operational environment, physical security, self-tests, design assurance, key management, EMI/EMC, and lifecycle assurance
- Gap classifications for missing self-tests, JTAG exposure, and TRNG validation
- All findings marked with `[FROM TRAINING]` and `sourceGrounding: training-knowledge`

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output contains SecurityRequirement entities covering at least 6 FIPS 140-3 Level 2 areas
- [ ] Every requirement has a confidence tier (GROUNDED, INFERRED, SPECULATIVE, or ABSENT)
- [ ] Gap for missing power-up self-test classified as `gap: not-met` (evidence examined, requirement not satisfied)
- [ ] Gap for missing TRNG conditional self-test classified as `gap: not-met`
- [ ] JTAG debug port flagged as a gap — password lock does not satisfy FIPS 140-3 Level 2 physical security
- [ ] All findings carry `[FROM TRAINING]` markers since no spec text was provided
- [ ] SPECULATIVE claims presented in a review gate for engineer acknowledgment

### Should Pass (partial credit)
- [ ] Key management requirements extracted — OTP-to-register key loading path assessed
- [ ] Gap analysis includes remediation plans with effort estimates for self-test implementation
- [ ] ComplianceResult entities include `verificationStatus: llm-assessed`
- [ ] Coverage boundary explicitly states what was and was not analyzed
- [ ] Caveat block present noting LLM-generated, not certification

### Bonus
- [ ] TRNG entropy source assessed against SP 800-90B requirements (FIPS 140-3 dependency)
- [ ] DMA interface flagged as a module boundary requiring access control assessment
- [ ] Cross-reference to CMVP validation process noted as out of scope

## Raw Trace Log
