# Threat Model Review Checklist

## Purpose

Checklist for reviewing the completeness and quality of a threat model produced by the threat-model-skill. Used as a quality gate before findings feed into verification scaffolding or compliance pipelines.

---

## Verification Tier Reference

- **Tier 1 (mechanical):** SVA assertions for access control, FSM, register locks — HIGH confidence
- **Tier 2 (protocol):** Natural-language property descriptions for DICE, CXL, protocol — needs review
- **Tier 3 (information flow):** Spec-only descriptions, no SVA — side-channel, info flow

---

## Scoping Completeness

- [ ] Target SoC family identified (Compute / Automotive / Client / Data Center)
- [ ] Technology domains selected and justified (at least 1, typically 2-3)
- [ ] Asset inventory includes all security-critical assets (keys, registers, interfaces, firmware)
- [ ] Trust boundaries explicitly identified and diagrammed
- [ ] Data flows across trust boundaries enumerated
- [ ] External interfaces cataloged (PCIe, CXL, debug, management, OTA)
- [ ] Out-of-scope items explicitly listed with rationale

## Threat Identification

- [ ] Threats drawn from all relevant threat catalog categories (physical, firmware, interface, architectural)
- [ ] Each threat has a valid threat catalog ID (PHYS-xxx, FW-xxx, INTF-xxx, ARCH-xxx)
- [ ] STRIDE classification assigned to each threat
- [ ] No obvious threat categories omitted for the selected domains
- [ ] Domain-specific threats included (e.g., TDISP state machine bypass for CXL domain)
- [ ] Cross-domain threats identified (threats spanning multiple technology domains)

## Threat Analysis Quality

- [ ] Each threat has identified preconditions (what the attacker needs)
- [ ] Each threat has identified target assets
- [ ] Impact assessment considers confidentiality, integrity, availability
- [ ] Likelihood assessment considers attacker capability and access requirements
- [ ] Risk rating consistent with impact and likelihood
- [ ] Family-specific risk adjustments applied (e.g., physical access more likely for Client than Data Center)

## Mitigation Mapping

- [ ] Each threat has at least one mitigation identified
- [ ] Mitigations map to specific standards requirements (REQ-xxx IDs)
- [ ] Mitigations are technically feasible for the target SoC family
- [ ] Residual risk documented for threats with partial mitigations
- [ ] Defense-in-depth: critical threats have multiple independent mitigations

## Verification Traceability

- [ ] Each threat mapped to a verification tier (Tier 1 / Tier 2 / Tier 3)
- [ ] Tier 1 threats linked to specific SVA template categories
- [ ] Tier 2 threats have natural-language property descriptions
- [ ] Tier 3 threats acknowledged with gap flag (cannot be fully verified in RTL simulation)
- [ ] No Tier 3 threats incorrectly classified as Tier 1

## Standards Compliance

- [ ] Applicable standards identified for each threat/mitigation pair
- [ ] Requirement IDs from standards registry referenced (REQ-DICE-xxx, REQ-SPDM-xxx, etc.)
- [ ] Compliance gaps flagged where mitigations do not fully satisfy standard requirements
- [ ] Family-specific compliance regimes addressed (FIPS for Compute, ISO 21434 for Automotive)

## Documentation Quality

- [ ] Threat model follows consistent format across all entries
- [ ] Terminology consistent with glossary (shared-references/soc-security/glossary.md)
- [ ] Cross-references to domain ontology, standards registry, and threat catalog are valid
- [ ] [FROM TRAINING] markers applied where content is derived from training knowledge
- [ ] Last verified date present

---

## Review Outcome

| Outcome | Criteria |
|---|---|
| **Pass** | All required items checked; no critical gaps |
| **Pass with Findings** | Minor gaps documented; threat model usable with noted caveats |
| **Revise** | Significant gaps in scoping, threat identification, or mitigation mapping |
