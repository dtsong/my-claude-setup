# Eval Case: DICE Attestation Compliance for Secure Boot Chain

## Metadata
- **Case ID:** CP-004
- **Tier:** 2 (medium)
- **Skill Route:** compliance-pipeline-skill
- **Estimated Complexity:** medium

## Input
```json
{
  "user_prompt": "Assess our secure boot chain against TCG DICE v1.2 attestation requirements. The boot chain is:\n\n1. ROM Boot Loader (RBL) — immutable, in mask ROM, 32KB\n   - Measures itself into UDS-derived CDI using SHA-384\n   - Loads and verifies Secondary Boot Loader (SBL) signature (ECDSA P-384)\n   - Derives CDI_1 = HMAC-SHA384(UDS, H(RBL) || H(SBL))\n\n2. Secondary Boot Loader (SBL) — in secure flash, updatable\n   - Receives CDI_1 from RBL via hardware mailbox\n   - Measures TEE firmware and derives CDI_2\n   - Generates DeviceID key pair from CDI_1\n   - Creates DeviceID certificate (self-signed)\n\n3. TEE Runtime — OP-TEE on Cortex-A78\n   - Receives CDI_2\n   - Generates Alias key pair from CDI_2\n   - Creates Alias certificate chained to DeviceID\n   - Provides attestation service to normal world via SMC interface\n\nConcerns:\n- UDS is stored in OTP fuses, readable by RBL only (hardware fuse lock after read)\n- CDI passed between stages via SRAM mailbox — not cleared after handoff\n- No DICE Protection Environment (DPE) implemented\n- DeviceID certificate is self-signed (no CA integration)\n- Technology domain: secure-boot-dice\n- SoC family: compute",
  "context": "Standalone mode. Engineer wants full 3-stage pipeline against TCG DICE v1.2. Boot chain details provided as primary evidence. Specific concerns about CDI mailbox clearing and lack of DPE. No upstream entities."
}
```

## Expected Output
A compliance pipeline output covering TCG DICE v1.2 with:
- SecurityRequirement entities for UDS protection, CDI derivation, layered measurement, certificate chain, and DPE
- Evidence mapping using the provided boot chain architecture as design-document evidence
- Critical gap for CDI mailbox not cleared after handoff (violates DICE layering principle)
- Gap for missing DPE implementation
- Gap for self-signed DeviceID without CA integration

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output extracts SecurityRequirement entities for core DICE concepts: UDS protection, CDI derivation, layered measurement, DeviceID/Alias key generation
- [ ] CDI mailbox not cleared after handoff flagged as `gap: not-met` — violates DICE layering (CDI must not be available to subsequent layers)
- [ ] Missing DPE flagged as a gap with appropriate classification
- [ ] Self-signed DeviceID certificate flagged as limiting attestation trust chain
- [ ] UDS fuse lock mechanism assessed as evidence for UDS protection requirement
- [ ] Confidence tiers assigned — boot chain details from user should yield some GROUNDED mappings

### Should Pass (partial credit)
- [ ] CDI derivation formula (HMAC-SHA384) assessed against DICE specification requirements
- [ ] Each boot stage mapped individually with per-stage compliance status
- [ ] Hardware mailbox CDI transfer assessed as an attack surface (SRAM residue after handoff)
- [ ] SMC interface for attestation service assessed as a trust boundary crossing point
- [ ] Remediation plan for CDI clearing includes specific mechanism (e.g., hardware scrub, software zeroization before jump)

### Bonus
- [ ] DICE certificate chain completeness assessed — DeviceID -> Alias -> Attestation Evidence
- [ ] Comparison to DICE with DPE vs. without DPE in terms of attestation granularity
- [ ] OP-TEE specific DICE integration patterns referenced (if from training, marked appropriately)

## Raw Trace Log
