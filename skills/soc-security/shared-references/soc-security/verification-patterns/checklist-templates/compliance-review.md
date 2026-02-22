# Compliance Review Checklist

## Purpose

Checklist for reviewing compliance evidence produced by the compliance-pipeline-skill. Ensures that the traceability matrix, compliance report, and gap analysis are complete and auditor-ready.

---

## Verification Tier Reference

- **Tier 1 (mechanical):** SVA assertions for access control, FSM, register locks — HIGH confidence
- **Tier 2 (protocol):** Natural-language property descriptions for DICE, CXL, protocol — needs review
- **Tier 3 (information flow):** Spec-only descriptions, no SVA — side-channel, info flow

---

## Traceability Matrix Completeness

- [ ] All applicable standard requirements included (REQ-xxx IDs from standards registry)
- [ ] Each requirement mapped to a security domain (from technology-domains.md)
- [ ] Each requirement mapped to target SoC family (from soc-families.md)
- [ ] RTL module column populated for requirements with known implementations
- [ ] Verification asset column populated (SVA assertion name, testbench reference, or gap flag)
- [ ] Compliance evidence column populated (simulation log, coverage report, review record, or gap)
- [ ] Status column accurately reflects current state (Verified / Gap / In Progress / N/A)
- [ ] Gap flags include description of what is missing and recommended remediation

## Standards Coverage

### DICE Requirements
- [ ] All REQ-DICE-xxx requirements from standards registry addressed
- [ ] UDS protection evidence documented
- [ ] CDI derivation correctness evidence documented
- [ ] Certificate chain evidence documented
- [ ] Anti-rollback evidence documented

### SPDM Requirements
- [ ] All REQ-SPDM-xxx requirements from standards registry addressed
- [ ] Authentication flow evidence documented
- [ ] Measurement reporting evidence documented
- [ ] Key exchange and session security evidence documented

### TDISP Requirements
- [ ] All REQ-TDISP-xxx requirements from standards registry addressed
- [ ] TDI state machine compliance evidence documented
- [ ] IDE stream binding evidence documented
- [ ] DMA isolation evidence documented

### CXL Requirements (if applicable)
- [ ] All REQ-CXL-xxx requirements from standards registry addressed
- [ ] IDE for CXL sub-protocols evidence documented
- [ ] TSP configuration and attestation evidence documented
- [ ] Multi-host isolation evidence documented

### CHERI Requirements (if applicable)
- [ ] All REQ-CHERI-xxx requirements from standards registry addressed
- [ ] Capability invariant evidence documented
- [ ] Compartmentalization evidence documented

## Compliance Overlay Standards

### FIPS 140-3 (if applicable)
- [ ] Cryptographic algorithm compliance documented (approved algorithms only)
- [ ] Key management requirements mapped
- [ ] Physical security level requirements addressed (or gap flagged)
- [ ] Self-test requirements addressed

### ISO 21434 (if Automotive family)
- [ ] Cybersecurity goals traced to threat model findings
- [ ] Work product requirements mapped to existing documentation
- [ ] Supply chain requirements addressed
- [ ] Lifecycle coverage (concept through decommissioning)

## Evidence Quality

- [ ] Evidence artifacts are reproducible (simulation commands, tool versions documented)
- [ ] Evidence dates are current (within project timeline)
- [ ] No evidence gaps masked by "N/A" without justification
- [ ] Gap severity classified (Critical / High / Medium / Low)
- [ ] Remediation plan documented for Critical and High gaps
- [ ] Evidence chain is auditor-traceable (can follow from requirement to artifact)

## Report Quality

- [ ] Executive summary present and accurate
- [ ] Compliance percentage calculated correctly
- [ ] Gap analysis section lists all gaps with severity and remediation
- [ ] Terminology consistent with glossary
- [ ] [FROM TRAINING] markers applied where content from training knowledge
- [ ] Last verified date present

---

## Compliance Summary Template

| Standard | Total Reqs | Verified | In Progress | Gap | N/A |
|---|---|---|---|---|---|
| DICE | | | | | |
| SPDM | | | | | |
| TDISP | | | | | |
| CXL | | | | | |
| CHERI | | | | | |
| FIPS 140-3 | | | | | |
| ISO 21434 | | | | | |
| **Total** | | | | | |

## Review Outcome

| Outcome | Criteria |
|---|---|
| **Audit-Ready** | All requirements addressed; no Critical gaps; evidence chain complete |
| **Needs Remediation** | Critical or High gaps exist; remediation plan required before audit |
| **Incomplete** | Major standards not addressed; traceability matrix significantly incomplete |
