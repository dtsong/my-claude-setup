# Abstraction Methodology — Worked Examples & Quality Checks

## Purpose

Worked examples across all five technology domains and per-layer quality checks for the 4-layer abstraction process.

**Primary consumer:** executive-brief-skill (output quality validation)

---

## Worked Examples

### Example 1: TDISP / CXL Domain

**Layer 0:** TF-2026-001: TDISP responder FSM transitions without validating all TLP fields. Malformed TLP could bypass DMA isolation. Source: TDISP-1.0 Section 4.3.2. Confidence: INFERRED.

**Layer 1:** An attacker with physical or logical PCIe bus access can exploit a validation gap in the device authentication protocol to bypass memory isolation between security domains.

**Layer 2:** Customer data in confidential AI inference pipelines on multi-tenant deployments may be exposed. Regulatory exposure under GDPR, CCPA, SOC 2, CSA STAR.

**Layer 3:** Prioritize device authentication protocol fix in Q2 silicon respin. Cost: ~2-3 engineer-weeks [ESTIMATED]. Risk if deferred: customer data exposure, cloud security certification blockers.

### Example 2: Secure Boot / DICE Domain

**Layer 0:** TF-2026-015: DICE Layer 1 CDI derivation does not incorporate Layer 1 firmware hash. Source: DICE-v1.2 Section 6.1. Confidence: GROUNDED.

**Layer 1:** The platform identity system does not incorporate actual firmware. Compromised firmware produces the same identity certificates as clean firmware.

**Layer 2:** Remote attestation evidence is meaningless for all families using this boot implementation. Attestation audit failures expected.

**Layer 3:** Fix CDI derivation to include firmware hash in next firmware release. Cost: ~1 EW derivation + 1 EW cert chain regression. Risk if deferred: attestation audit failures, confidential computing customer trust loss.

### Example 3: CXL Security Domain

**Layer 0:** CR-2026-012: CXL 3.1 TSP partition table not re-validated after hot-add. Source: CXL-3.1 Section 11.4. Confidence: INFERRED.

**Layer 1:** In multi-host deployments, a newly connected host can access memory regions isolated to other hosts.

**Layer 2:** Tenant data isolation failure in CXL memory pooling. Cloud SLA guarantees may be violated.

**Layer 3:** Implement TSP partition re-validation on hot-add before CXL pooling launch. Cost: ~4-6 EW [ESTIMATED]. Risk if deferred: cannot launch with credible security guarantees.

### Example 4: CHERI ISA Domain

**Layer 0:** TF-2026-022: CHERI capability tag bit settable by firmware in machine mode. Source: CHERI-v9 Section 3.2. Confidence: INFERRED.

**Layer 1:** Firmware at highest privilege level can forge hardware memory access permissions, bypassing CHERI memory safety guarantees.

**Layer 2:** Hardware memory safety value proposition invalidated if firmware compromise allows forgery. Security-critical adoption blocked.

**Layer 3:** Restrict tag-override CSR to hardware-only path. Cost: ~1-2 EW RTL + regression. Risk if deferred: CHERI security claims not defensible.

### Example 5: Supply Chain / SPDM Domain

**Layer 0:** TF-2026-030: SPDM GET_MEASUREMENTS omits secondary firmware images. Source: SPDM-v1.4 Section 10.5. Confidence: GROUNDED.

**Layer 1:** Remote attestation is incomplete. Compromised runtime firmware undetected by attestation.

**Layer 2:** Supply chain verification is incomplete for post-boot firmware. Fleet health monitoring misses runtime compromise.

**Layer 3:** Extend SPDM measurement to all firmware images. Cost: ~2-3 EW [ESTIMATED]. Risk if deferred: attestation gaps persist.

---

## Quality Checks

### Per-Layer Quality Checks

**Layer 0:** [ ] Faithful reproduction of upstream finding; [ ] Entity ID included; [ ] Confidence tier included; [ ] Source document referenced.

**Layer 1:** [ ] No hardware-specific terms remain; [ ] Attacker profile specified; [ ] Security property named; [ ] Scope bounded; [ ] Accurate translation from Layer 0.

**Layer 2:** [ ] Business assets named specifically; [ ] Regulatory frameworks referenced; [ ] Exposure quantified where possible; [ ] No catastrophizing; [ ] Consistent with Layer 1.

**Layer 3:** [ ] Imperative action; [ ] Timeline to milestone (or TBD); [ ] Cost estimated (or TBD/ESTIMATED); [ ] Deferral consequence in business terms; [ ] Achievable action; [ ] No fabricated cost/timeline.

### End-to-End Quality

- [ ] All four layers traceable (Layer 3 -> 2 -> 1 -> 0)
- [ ] No information added in later layers not derivable from earlier
- [ ] Severity consistent across all layers
- [ ] Audience vocabulary appropriate
- [ ] Verification status carries through unchanged
- [ ] Confidence tier carries through unchanged

---

## Common Translation Errors

**Error 1: Severity Inflation** — "Medium, requires physical access" translated as "Critical business risk." Correct: "Limited risk for remote deployments; elevated for physically accessible installations."

**Error 2: Loss of Scope** — "Affects TDISP in data center SoC" becomes "All products at risk." Correct: "Data center products using PCIe device assignment affected; automotive/client not impacted."

**Error 3: Fabricated Cost** — "Cost: $2.5M" with no basis. Correct: "Cost: ~4-6 EW [ESTIMATED — verify with engineering]."

**Error 4: Lost Traceability** — "Several security issues identified." Correct: "Three findings identified (TF-001 Critical, TF-005 High, TF-012 Medium)."

**Error 5: Audience Mismatch** — Board-level: "The TDISP responder FSM has an invalid state transition." Correct: "A device authentication weakness could allow unauthorized access to customer data."
