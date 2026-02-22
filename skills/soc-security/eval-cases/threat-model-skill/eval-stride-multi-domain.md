# Eval Case: Multi-Domain STRIDE — DICE and TDISP Interaction Point

## Metadata
- **Case ID:** TM-002
- **Tier:** 2 (medium)
- **Skill Route:** threat-model-skill
- **Estimated Complexity:** medium

## Input
```json
{
  "user_prompt": "I need a STRIDE analysis on the interaction point between our DICE Layer 1 attestation engine and the TDISP device assignment module. The DICE engine produces compound device identifiers (CDIs) and attestation certificates that the TDISP module uses to prove device identity during the TDISP LOCK flow. Specifically:\n\n- DICE Layer 1 outputs: CDI, alias key pair, device certificate chain\n- TDISP consumes: device certificate for SPDM GET_CERTIFICATE response\n- Shared resource: certificate storage (dual-port SRAM, 4KB)\n- Trust boundary: DICE runs in immutable ROM; TDISP runs in mutable firmware\n- Interaction: DICE writes certs at boot; TDISP reads certs during device assignment\n\nSoC family: Data Center. Specs: DICE 1.1, TDISP 1.0, SPDM 1.3.",
  "context": "Prior DICE-only threat model TM-2025-031 exists (8 findings, all GROUNDED). No prior analysis of the DICE-TDISP interaction point. User is concerned about the trust boundary difference between immutable ROM and mutable firmware."
}
```

## Expected Output
A STRIDE analysis focused on the cross-domain interaction point, producing:
- Findings specific to the DICE-TDISP interface (not just generic DICE or TDISP threats)
- Recognition of the trust boundary asymmetry (ROM vs. mutable FW)
- Cross-domain threats that neither a DICE-only nor TDISP-only analysis would catch
- References to prior art TM-2025-031

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] At least one Tampering finding addressing certificate storage integrity (mutable FW writing to shared SRAM that DICE also uses)
- [ ] At least one Spoofing finding addressing TDISP presenting fraudulent attestation evidence derived from stale or replaced certificates
- [ ] Trust boundary asymmetry (ROM vs. mutable FW) explicitly identified as a cross-domain threat amplifier
- [ ] Shared certificate storage (dual-port SRAM) identified as a critical shared resource with concurrent access risks
- [ ] Prior threat model TM-2025-031 referenced in the analysis context

### Should Pass (partial credit)
- [ ] Information Disclosure finding addressing CDI or alias key exposure through the shared SRAM interface
- [ ] Repudiation finding addressing inability to distinguish DICE-written vs. TDISP-modified certificate content
- [ ] Findings tagged with both Secure Boot/DICE and TDISP/CXL technology domains
- [ ] Standards references cite specific sections from DICE 1.1, TDISP 1.0, and SPDM 1.3
- [ ] Confidence tiers correctly mix GROUNDED (for spec-derived threats) and INFERRED (for interaction-point threats)

### Bonus
- [ ] Time-of-check-to-time-of-use (TOCTOU) threat on certificate storage between DICE boot-time write and TDISP runtime read
- [ ] Cross-family reuse assessment notes that the DICE-TDISP pattern applies to any data center SoC with confidential computing
- [ ] Suggests that verification-scaffold-skill should generate assertions for the shared SRAM access protocol

## Raw Trace Log
