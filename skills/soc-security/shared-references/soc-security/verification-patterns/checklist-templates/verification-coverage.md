# Verification Coverage Checklist

## Purpose

Checklist for assessing whether the verification scaffold produced by the verification-scaffold-skill provides adequate coverage of threat model findings. Ensures that every identified threat has a corresponding verification approach at the appropriate tier.

---

## Verification Tier Reference

- **Tier 1 (mechanical):** SVA assertions for access control, FSM, register locks — HIGH confidence
- **Tier 2 (protocol):** Natural-language property descriptions for DICE, CXL, protocol — needs review
- **Tier 3 (information flow):** Spec-only descriptions, no SVA — side-channel, info flow

---

## Tier 1 Coverage (SVA Assertions)

### Access Control Assertions
- [ ] Register lock assertions generated for all security-critical registers
- [ ] Bus firewall assertions cover all protected address ranges
- [ ] Privilege-gated write assertions for security configuration registers
- [ ] IOMMU/DMA filtering assertions for all DMA-capable interfaces
- [ ] TDISP TDI access control assertions (state-dependent, owner-checked)
- [ ] CHERI capability bounds check assertions (if CHERI domain selected)

### FSM Transition Assertions
- [ ] TDISP state machine: all legal transitions asserted, illegal transitions blocked
- [ ] Debug authentication FSM: auth required before debug enable
- [ ] Boot stage transitions: measure-derive-lock-execute ordering enforced
- [ ] Error state handling: security violations trigger error state

### Register Lock Assertions
- [ ] Write-once lock bits: sticky behavior verified (no clear after set)
- [ ] Security configuration freeze: locked registers are read-only
- [ ] Monotonic counters: increment-only, no decrement, no wrap
- [ ] OTP fuse protection: no reprogramming after blow, lifecycle gating
- [ ] DICE secret locking: UDS/CDI inaccessible after layer transition

### Tier 1 Completeness
- [ ] Every Tier 1 threat in the threat model has at least one SVA assertion
- [ ] SVA assertions have INTENT and DOES NOT CHECK comments
- [ ] All assertions marked [TEMPLATE] or [READY]
- [ ] Signal bindings documented for [TEMPLATE] assertions

## Tier 2 Coverage (Protocol Properties)

- [ ] SPDM authentication flow properties described
- [ ] SPDM measurement reporting completeness properties described
- [ ] DICE CDI derivation correctness properties described
- [ ] DICE certificate chain well-formedness properties described
- [ ] CXL TSP configuration authentication properties described
- [ ] CXL IDE key rotation coordination properties described
- [ ] TDISP-to-SPDM session binding properties described
- [ ] Each Tier 2 property has a natural-language description
- [ ] Each Tier 2 property notes what directed testbench stimulus is needed
- [ ] Tier 2 properties cross-referenced to standards requirements (REQ-xxx)

## Tier 3 Coverage (Information Flow / Spec-Level)

- [ ] Cross-domain information flow threats acknowledged
- [ ] Microarchitectural side-channel threats flagged with gap marker
- [ ] Physical side-channel resistance noted as requiring lab measurement
- [ ] Covert channel analysis scope described
- [ ] Each Tier 3 item has a clear gap flag indicating it cannot be verified in RTL simulation
- [ ] Recommended external analysis methods noted (TVLA, formal info-flow, red team)

## Traceability

- [ ] Threat-to-verification mapping table complete (every threat has a verification entry)
- [ ] Standards requirement-to-assertion mapping table complete
- [ ] Coverage gaps explicitly documented with severity
- [ ] No assertion exists without a corresponding threat or requirement justification

## Quality Checks

- [ ] SVA templates compile without syntax errors (if signal-bound)
- [ ] Assertion naming convention consistent (assert_*, cover_*)
- [ ] Parameterized signals use descriptive placeholder names
- [ ] No overly constrained assertions that prevent useful coverage
- [ ] No vacuously true assertions (check antecedent reachability)

---

## Coverage Summary Template

| Category | Total Threats | Tier 1 Covered | Tier 2 Covered | Tier 3 (Gap) | Uncovered |
|---|---|---|---|---|---|
| Physical | | | | | |
| Firmware | | | | | |
| Interface | | | | | |
| Architectural | | | | | |
| **Total** | | | | | |

## Review Outcome

| Outcome | Criteria |
|---|---|
| **Adequate** | All Tier 1 threats covered; Tier 2 properties described; Tier 3 gaps documented |
| **Gaps Identified** | Some Tier 1 assertions missing or Tier 2 properties incomplete; remediation plan needed |
| **Insufficient** | Major coverage gaps; verification scaffold needs significant revision |
