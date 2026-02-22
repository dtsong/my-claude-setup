# Eval Case: Multi-Standard Gap Analysis with Remediation Plan

## Metadata
- **Case ID:** CP-005
- **Tier:** 3 (complex)
- **Skill Route:** compliance-pipeline-skill
- **Estimated Complexity:** high

## Input
```json
{
  "user_prompt": "Perform a multi-standard compliance gap analysis with remediation roadmap for our automotive ADAS SoC targeting three standards simultaneously:\n\n**Standards:**\n1. FIPS 140-3 Level 2 — for US government fleet deployment\n2. ISO 21434 — for EU type approval (UNECE WP.29 R155)\n3. TCG DICE v1.2 — for secure boot attestation chain\n\n**SoC Architecture:**\n- Cortex-A78AE (split/lock) application cluster running Linux\n- Cortex-R52 safety island (ASIL-D, lockstep) running AUTOSAR Classic\n- Dedicated HSM subsystem: AES-256, SHA-384, ECDSA P-384, hardware TRNG\n- DICE-based secure boot: ROM -> SBL -> TEE -> Linux\n- CAN-FD, Ethernet AVB/TSN, PCIe Gen4 interfaces\n- V2X communication module with IEEE 1609.2 certificate management\n- OTA update via dual-bank flash with rollback protection\n- Debug: Arm CoreSight with secure debug certificate authentication\n\n**Current State:**\n- TARA partially completed (vehicle interface threats only, no SoC-internal)\n- HSM has no CAVP-validated algorithms\n- DICE boot chain implemented but no DPE, no external CA integration\n- Secure debug implemented but not assessed against FIPS physical security\n- No unified compliance tracking — each standard tracked in separate spreadsheets\n\n**Request:** Produce a unified gap analysis across all three standards, identify cross-standard synergies for remediation, and provide a phased remediation roadmap with effort estimates.\n\n- Technology domains: secure-boot-dice, supply-chain\n- SoC family: automotive\n- Scope: HSM subsystem, boot chain, vehicle network interfaces, OTA update, debug",
  "context": "Standalone mode. Complex multi-standard, single SoC analysis. Partial evidence exists (TARA partial, DICE implemented but incomplete). Engineer wants cross-standard overlap identification and phased remediation. No upstream entities. Spec text not provided for any standard."
}
```

## Expected Output
A comprehensive multi-standard compliance pipeline output producing:
- SecurityRequirement entities tagged to one or more of the three standards
- Cross-standard requirement overlap matrix (e.g., key management spans all three)
- Per-standard gap analysis with gap classifications
- Unified remediation roadmap identifying cross-standard synergies
- Phased plan (Phase 1: critical gaps, Phase 2: certification prep, Phase 3: validation)
- Effort estimates per remediation item

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output contains SecurityRequirement entities for all three standards (FIPS 140-3, ISO 21434, TCG DICE)
- [ ] Cross-standard overlap identified — at minimum: key management, self-tests, design documentation, lifecycle management
- [ ] Missing CAVP validation flagged as `gap: not-met` for FIPS 140-3
- [ ] Incomplete TARA flagged as `gap: partial` for ISO 21434
- [ ] Missing DPE and CA integration flagged as gaps for TCG DICE
- [ ] Every requirement has confidence tier and `[FROM TRAINING]` markers where applicable
- [ ] SPECULATIVE claims presented in review gate before final output
- [ ] Per-family traceability maintained — all requirements tagged to automotive SoC family

### Should Pass (partial credit)
- [ ] Remediation roadmap organized in phases with dependency ordering (e.g., CAVP validation before FIPS certification)
- [ ] Cross-standard synergies identified (e.g., HSM design documentation serves FIPS, CC-equivalent for ISO 21434, and DICE trust anchor requirements)
- [ ] V2X IEEE 1609.2 certificate management assessed against all three standards
- [ ] OTA update with rollback protection mapped to ISO 21434 cybersecurity update management and DICE measurement chain
- [ ] Secure debug assessed against FIPS physical security and ISO 21434 secure development
- [ ] Effort estimates provided for remediation items (marked `[ESTIMATED]` if not engineer-provided)

### Bonus
- [ ] ASIL-D safety island assessed for cybersecurity co-dependency with ISO 21434 Clause 6 (cybersecurity and safety interplay)
- [ ] Unified compliance tracking recommendation with entity relationships across standards
- [ ] Certification timeline dependencies mapped (e.g., FIPS CMVP queue time, ISO 21434 audit scheduling, DICE conformance testing)
- [ ] PCIe Gen4 interface assessed for TDISP applicability as a future compliance extension

## Raw Trace Log
