# Physical Side-Channel Assessment Checklist

## Purpose

Checklist for reviewing the physical side-channel resistance of cryptographic implementations and security-sensitive logic in an SoC design. Covers power analysis, electromagnetic analysis, fault injection, and statistical leakage assessment (TVLA). Used as a quality gate for cryptographic engines, key management modules, and security-critical datapaths.

---

## Verification Tier Reference

- **Tier 1 (mechanical):** SVA assertions for constant-time datapath selection, countermeasure presence — HIGH confidence but LIMITED scope
- **Tier 2 (design review):** Natural-language property descriptions for countermeasure requirements — needs expert review
- **Tier 3 (lab measurement):** Physical measurement required (TVLA, CPA, fault injection) — cannot be verified in simulation alone

---

## Cryptographic Asset Inventory

- [ ] **All cryptographic engines enumerated:** Verify that every cryptographic engine in the SoC is identified (AES, SHA, RSA/ECC, HMAC, TRNG, PUF).
  - *Verification:* Tier 2 — design review of block diagram and RTL hierarchy.
  - *Confidence:* HIGH — enumeration is straightforward from design documentation.

- [ ] **Key material storage locations identified:** Verify that all locations where key material resides are documented (registers, SRAM, fuses, PUF output, key cache).
  - *Verification:* Tier 2 — design review of key management architecture.
  - *Confidence:* HIGH.

- [ ] **Key transport paths mapped:** Verify that all buses, muxes, and interconnects that carry key material are identified and the exposure window is documented.
  - *Verification:* Tier 2 — datapath analysis from key source to crypto engine input.
  - *Confidence:* MEDIUM — transport paths may cross multiple design hierarchies.

- [ ] **Sensitive intermediate values identified:** Verify that security-sensitive intermediate values (S-box outputs, round keys, partial products) are identified for leakage assessment.
  - *Verification:* Tier 2 — algorithm-level analysis of leakage points.
  - *Confidence:* MEDIUM — depends on algorithm and implementation architecture.

- [ ] **Protection level requirements assigned:** Verify that each cryptographic asset has a target protection level (e.g., FIPS 140-3 Level 2/3/4, Common Criteria AVA_VAN.3/4/5).
  - *Verification:* Tier 2 — requirements review against product security target.
  - *Confidence:* HIGH — derived from compliance requirements.

---

## Power Analysis Resistance

- [ ] **SPA resistance (simple power analysis):** Verify that key-dependent control flow differences (e.g., square-and-multiply branching in RSA) are eliminated or masked.
  - *Verification:* Tier 1 — SVA assertion for constant-time operation selection (limited); Tier 3 — power trace inspection.
  - *Confidence:* MEDIUM for SVA checks; HIGH with lab measurement.

- [ ] **DPA resistance (differential power analysis):** Verify that masking or hiding countermeasures are applied to all operations processing key-dependent intermediate values.
  - *Verification:* Tier 2 — property for masking scheme presence and order; Tier 3 — CPA/DPA attack testing.
  - *Confidence:* LOW without lab measurement; HIGH with TVLA pass at target trace count.

- [ ] **Masking order verified:** Verify that the masking scheme order (1st-order, 2nd-order, etc.) matches the target protection level and is consistently applied across all sensitive operations.
  - *Verification:* Tier 2 — design review of masking implementation; Tier 3 — higher-order leakage testing.
  - *Confidence:* MEDIUM — masking correctness is subtle; glitches can reduce effective order.

- [ ] **Mask generation quality:** Verify that random masks are generated from a TRNG or PRNG with sufficient entropy and that mask refresh rate is adequate.
  - *Verification:* Tier 1 — SVA assertion for TRNG health checks; Tier 2 — entropy source review.
  - *Confidence:* HIGH for health check presence; MEDIUM for entropy quality.

- [ ] **Power supply filtering and regulation:** Verify that on-chip voltage regulators or power filtering is present to reduce power side-channel signal-to-noise ratio.
  - *Verification:* Tier 2 — design review of power delivery network; Tier 3 — power measurement SNR assessment.
  - *Confidence:* LOW without lab measurement.

---

## EM Analysis Resistance

- [ ] **EM emanation assessment scope:** Verify that electromagnetic emanation assessment covers both near-field (probe on die/package) and far-field (antenna at distance) scenarios as required by the target protection level.
  - *Verification:* Tier 3 — EM probe measurement campaign.
  - *Confidence:* LOW without lab measurement.

- [ ] **Spatial locality of leakage:** Verify that sensitive operations are not spatially isolated on the die in a way that makes localized EM probing trivial.
  - *Verification:* Tier 2 — floorplan review of crypto engine placement; Tier 3 — EM scanning.
  - *Confidence:* LOW — requires physical layout analysis.

- [ ] **Shield/guard ring presence:** If required by protection level, verify that active or passive EM shielding (shield layers, guard rings) is present over security-critical logic.
  - *Verification:* Tier 2 — layout review for shield layers; Tier 3 — EM measurement with/without shield.
  - *Confidence:* MEDIUM for presence verification; LOW for effectiveness.

- [ ] **DEMA resistance (differential EM analysis):** Verify that countermeasures effective against DPA (masking, hiding) also provide resistance against differential EM analysis.
  - *Verification:* Tier 3 — EM-based CPA/DEMA attack testing.
  - *Confidence:* LOW without lab measurement; masking generally provides EM resistance.

---

## Fault Injection Resistance

- [ ] **Voltage glitch detection:** Verify that voltage glitch detectors are present and that detection triggers an appropriate response (zeroize keys, reset, alarm).
  - *Verification:* Tier 1 — SVA assertion for glitch detector output connected to security response logic; Tier 3 — glitch injection testing.
  - *Confidence:* HIGH for detector presence; LOW for detector sensitivity.

- [ ] **Clock glitch detection:** Verify that clock frequency monitors or glitch detectors are present and trigger security responses on anomalous clock behavior.
  - *Verification:* Tier 1 — SVA assertion for clock monitor output; Tier 3 — clock glitch injection testing.
  - *Confidence:* HIGH for monitor presence; LOW for sensitivity.

- [ ] **Computational redundancy:** Verify that critical cryptographic computations use redundancy (dual computation, inverse check, parity) to detect fault-induced errors.
  - *Verification:* Tier 1 — SVA assertion for redundancy check logic; Tier 2 — property for coverage of critical operations.
  - *Confidence:* HIGH for check presence; MEDIUM for completeness.

- [ ] **Infection countermeasure:** Verify that fault detection in cryptographic operations triggers infection (corrupting the output) rather than just halting, to prevent differential fault analysis (DFA).
  - *Verification:* Tier 2 — design review of error response in crypto engine; Tier 1 — SVA assertion for infection logic.
  - *Confidence:* MEDIUM — infection completeness requires careful analysis.

- [ ] **Laser fault injection resistance:** If required by protection level, verify that light sensors or active shields detect laser/optical fault injection attempts.
  - *Verification:* Tier 2 — design review for light sensors; Tier 3 — laser fault injection testing.
  - *Confidence:* LOW without lab measurement.

- [ ] **Multi-fault resistance:** Verify that countermeasures are effective against multiple simultaneous or sequential fault injections, not just single faults.
  - *Verification:* Tier 3 — multi-glitch injection testing.
  - *Confidence:* LOW — multi-fault resistance is significantly harder to verify.

---

## Leakage Assessment (TVLA)

- [ ] **Fixed vs. random test vectors defined:** Verify that TVLA test vector sets are defined per ISO 17825 methodology (fixed class and random class) for each cryptographic engine.
  - *Verification:* Tier 2 — test plan review for TVLA vector generation; Tier 3 — TVLA execution.
  - *Confidence:* HIGH for test plan; assessment requires lab execution.

- [ ] **First-order t-test pass threshold:** Verify that first-order TVLA t-test results are below the threshold (|t| < 4.5) at the target trace count for all cryptographic operations.
  - *Verification:* Tier 3 — TVLA measurement with power/EM traces.
  - *Confidence:* HIGH when measured; cannot be verified in simulation.

- [ ] **Higher-order leakage assessment:** If masking is employed, verify that higher-order (2nd, 3rd) TVLA testing is performed commensurate with the masking order.
  - *Verification:* Tier 3 — higher-order TVLA measurement.
  - *Confidence:* LOW — higher-order testing requires significantly more traces.

- [ ] **All operation modes covered:** Verify that TVLA assessment covers all operational modes of each crypto engine (ECB, CBC, CTR, GCM for AES; sign/verify for ECC; etc.).
  - *Verification:* Tier 2 — test plan review for mode coverage; Tier 3 — per-mode TVLA.
  - *Confidence:* MEDIUM — mode coverage depends on test plan completeness.

- [ ] **Trace count sufficiency:** Verify that the number of traces collected is sufficient for the target detection sensitivity (typically 10K-1M traces for first-order, more for higher-order).
  - *Verification:* Tier 3 — statistical power analysis of TVLA results.
  - *Confidence:* HIGH when trace count is documented and justified.

---

## Countermeasure Verification

- [ ] **Countermeasure bypass paths:** Verify that no bypass path exists that allows cryptographic operations to execute without countermeasures (e.g., test mode, debug mode, performance mode).
  - *Verification:* Tier 1 — SVA assertion that countermeasure enable signals are active during crypto operations; Tier 2 — design review for bypass modes.
  - *Confidence:* HIGH for assertion; MEDIUM for bypass path enumeration completeness.

- [ ] **Random number generator health:** Verify that the TRNG used for countermeasures (masking, shuffling, random delays) passes health tests (repetition count, adaptive proportion per NIST SP 800-90B).
  - *Verification:* Tier 1 — SVA assertion for TRNG health test output; Tier 2 — entropy source design review.
  - *Confidence:* HIGH for health test presence; MEDIUM for entropy quality.

- [ ] **Shuffling implementation:** If operation shuffling is used as a hiding countermeasure, verify that the shuffle permutation is generated from the TRNG and covers all sensitive operations.
  - *Verification:* Tier 2 — design review of shuffle logic; Tier 1 — SVA for shuffle index randomness source.
  - *Confidence:* MEDIUM.

- [ ] **Constant-time guarantees:** Verify that all cryptographic operations execute in constant time regardless of input data values (no early termination, no data-dependent branching).
  - *Verification:* Tier 1 — SVA assertion for constant iteration count and constant mux selection; Tier 3 — timing measurement.
  - *Confidence:* HIGH for basic checks; MEDIUM for comprehensive constant-time verification.

- [ ] **Key zeroization on tamper detection:** Verify that key material is zeroized immediately upon tamper detection (glitch, temperature, voltage anomaly) and that zeroization is complete and irreversible.
  - *Verification:* Tier 1 — SVA assertion for zeroization trigger and completion; Tier 2 — property for zeroization completeness.
  - *Confidence:* HIGH for trigger verification; MEDIUM for completeness.

---

## Review Outcome

| Outcome | Criteria |
|---|---|
| **Pass** | All Tier 1/2 items checked; Tier 3 items assessed with TVLA pass at target trace count |
| **Pass with Findings** | Tier 1/2 items pass; Tier 3 items assessed with documented residual risk |
| **Revise** | Tier 1 failures, missing countermeasures for target protection level, or TVLA failures |
