# ISO 17825 — Test Methods for Side-Channel Leakage Assessment (TVLA)

## Specification Overview

| Field | Value |
|---|---|
| **Full Name** | ISO/IEC 17825: Information Technology — Security Techniques — Testing Methods for the Mitigation of Non-Invasive Attack Classes Against Cryptographic Modules |
| **Version** | 2nd Edition (2024) [FROM TRAINING] |
| **Organization** | ISO/IEC JTC 1/SC 27 |
| **Scope** | Standardized test methodology for detecting side-channel leakage in cryptographic implementations using statistical analysis (TVLA) |
| **Security Properties Addressed** | Leakage Resistance, Confidentiality, Implementation Security |
| **Related Standards** | ISO 19790 (cryptographic module security), FIPS 140-3 (physical security), Common Criteria AVA_VAN (vulnerability analysis) |

---

## Concept Summary

ISO 17825 provides a standardized framework for evaluating whether cryptographic implementations leak exploitable information through side channels such as power consumption and electromagnetic emanations. The primary methodology is Test Vector Leakage Assessment (TVLA), which uses Welch's t-test to determine whether the statistical distribution of physical measurements (traces) differs between operations on fixed versus random data. A t-test statistic exceeding the threshold of 4.5 (in absolute value) indicates detectable leakage. The standard defines trace collection procedures, statistical test parameters, equipment requirements, and criteria for both first-order and higher-order leakage assessment.

**Key architectural principle:** Leakage detection is a necessary but not sufficient condition — a device that fails TVLA has confirmed exploitable leakage, while a device that passes TVLA at a given order has no detectable leakage at that order with the given number of traces, but may still be vulnerable to more sophisticated attacks.

---

## Key Security Requirements

### Test Methodology Fundamentals

**REQ-ISO17825-001: Fixed vs. Random Test Vector Strategy**
The leakage assessment must use a non-specific fixed-versus-random test strategy. The fixed set uses a constant known plaintext for all encryptions, while the random set uses independently generated random plaintexts. Traces from both sets must be collected under identical environmental conditions and interleaved or randomized to prevent ordering bias.

- **Security properties:** Leakage Resistance
- **Verification tier:** Tier 3 — lab measurement and statistical analysis
- **Cross-references:** REQ-ISO17825-003 (t-test threshold), FIPS 140-3 Level 3+ (non-invasive security)

**REQ-ISO17825-002: Trace Collection Parameters**
Each trace must capture the complete cryptographic operation with sufficient temporal resolution to observe intermediate value processing. The sampling rate must be at least 5x the device clock frequency (Nyquist + margin). The number of traces collected must be documented, with a minimum of 10,000 traces per set (fixed and random) for first-order assessment, and justification provided if fewer traces are used.

- **Security properties:** Leakage Resistance, Measurement Completeness
- **Verification tier:** Tier 3 — lab measurement configuration validation
- **Cross-references:** REQ-ISO17825-005 (first-order assessment), REQ-ISO17825-008 (equipment requirements)

**REQ-ISO17825-003: T-Test Threshold Criterion**
The leakage detection criterion is based on Welch's t-test. If the absolute value of the t-statistic exceeds 4.5 at any sample point during the cryptographic operation, the device is considered to exhibit detectable leakage. This threshold corresponds to a confidence level exceeding 99.999% that the distributions differ. The t-test must be computed independently for each sample point in the trace.

- **Security properties:** Leakage Resistance
- **Verification tier:** Tier 3 — statistical analysis of collected trace data
- **Cross-references:** REQ-ISO17825-001 (test vector strategy), REQ-ISO17825-004 (leakage detection criteria)

**REQ-ISO17825-004: Leakage Detection Pass/Fail Criteria**
A device passes the leakage assessment if no sample point in the t-test result exceeds the threshold of 4.5 in absolute value across all mandatory test configurations. A device fails if any sample point exceeds the threshold. The evaluator must report the maximum observed t-statistic, the sample point at which it occurs, and the number of traces used.

- **Security properties:** Leakage Resistance, Confidentiality
- **Verification tier:** Tier 3 — statistical verdict based on collected data
- **Cross-references:** REQ-ISO17825-003 (threshold criterion), Common Criteria AVA_VAN.4/5

### Assessment Orders

**REQ-ISO17825-005: First-Order Leakage Assessment**
First-order assessment must be performed on raw (unprocessed) traces. The t-test is applied directly to the amplitude values at each sample point. This detects leakage that is exploitable without combining information from multiple trace points. First-order assessment is mandatory for all evaluation levels.

- **Security properties:** Leakage Resistance
- **Verification tier:** Tier 3 — first-order t-test on raw traces
- **Cross-references:** REQ-ISO17825-006 (higher-order assessment), REQ-ISO17825-003 (threshold)

**REQ-ISO17825-006: Higher-Order Leakage Assessment**
For devices claiming protection against first-order attacks (e.g., masking countermeasures), higher-order assessment must be performed. Second-order assessment applies the t-test to pre-processed traces where pairs of sample points are combined (e.g., using centered product). The evaluator must document the combination function, the window of sample points considered, and the computational methodology. The same threshold of 4.5 applies to higher-order tests.

- **Security properties:** Leakage Resistance
- **Verification tier:** Tier 3 — higher-order statistical analysis
- **Cross-references:** REQ-ISO17825-005 (first-order), REQ-ISO17825-012 (countermeasure evaluation)

**REQ-ISO17825-007: Multivariate Leakage Assessment**
When univariate tests (first-order and higher-order) do not capture the full leakage behavior, multivariate analysis methods may be applied. If multivariate assessment is performed, the evaluator must document the dimensionality reduction technique, the number of interesting points selected, and the statistical test employed. The pass/fail threshold must be adjusted for multiple comparisons.

- **Security properties:** Leakage Resistance
- **Verification tier:** Tier 3 — multivariate statistical analysis
- **Cross-references:** REQ-ISO17825-006 (higher-order), REQ-ISO17825-005 (first-order)

### Equipment and Environment

**REQ-ISO17825-008: Measurement Equipment Requirements**
The measurement setup must include: (a) a digital oscilloscope or equivalent acquisition device with sufficient bandwidth and resolution (minimum 8-bit vertical resolution), (b) an appropriate probe (EM probe for electromagnetic measurements, current probe or shunt resistor for power measurements), (c) a stable power supply with controlled noise characteristics, and (d) a trigger mechanism synchronized to the cryptographic operation. Equipment specifications must be documented in the evaluation report.

- **Security properties:** Measurement Integrity
- **Verification tier:** Tier 3 — equipment calibration and specification verification
- **Cross-references:** REQ-ISO17825-002 (trace collection parameters)

**REQ-ISO17825-009: Environmental Control Requirements**
Measurements must be conducted under controlled environmental conditions. Temperature must be stable within ±2°C during trace collection. Electromagnetic interference from external sources must be minimized. The evaluator must document ambient conditions and any environmental factors that could affect measurement quality. If measurements are taken at multiple temperatures, each temperature point constitutes a separate assessment.

- **Security properties:** Measurement Integrity, Reproducibility
- **Verification tier:** Tier 3 — environmental monitoring during measurement
- **Cross-references:** REQ-ISO17825-008 (equipment requirements)

### Cryptographic Operation Coverage

**REQ-ISO17825-010: Algorithm Coverage Requirements**
The leakage assessment must cover all cryptographic algorithms implemented in the device under test. For block ciphers, both encryption and decryption operations must be tested. For public-key operations, both key generation and signature/decapsulation operations must be assessed. The evaluator must justify any exclusions from the test scope.

- **Security properties:** Leakage Resistance, Confidentiality
- **Verification tier:** Tier 3 — test coverage review
- **Cross-references:** FIPS 140-3 (approved algorithms), REQ-ISO17825-001 (test vector strategy)

**REQ-ISO17825-011: Key-Dependent Leakage Testing**
In addition to data-dependent leakage (fixed vs. random plaintext), the assessment should evaluate key-dependent leakage by testing with fixed-versus-random keys where applicable. This detects leakage of key material that is independent of the plaintext. The evaluator must document which key-dependent tests were performed.

- **Security properties:** Leakage Resistance, Confidentiality
- **Verification tier:** Tier 3 — key-dependent t-test analysis
- **Cross-references:** REQ-ISO17825-001 (test vector strategy), REQ-ISO17825-003 (threshold)

### Countermeasure Evaluation

**REQ-ISO17825-012: Countermeasure Effectiveness Assessment**
For devices implementing side-channel countermeasures (masking, shuffling, noise injection, amplitude/temporal randomization), the assessment must evaluate effectiveness at the appropriate order. Masked implementations must be tested at the masking order plus one (e.g., a first-order masked implementation must be assessed with second-order analysis). The countermeasure type and claimed protection order must be documented.

- **Security properties:** Leakage Resistance
- **Verification tier:** Tier 3 — appropriate-order statistical testing
- **Cross-references:** REQ-ISO17825-006 (higher-order assessment), REQ-ISO17825-005 (first-order)

**REQ-ISO17825-013: Trace Count Scaling for Countermeasure Assessment**
When evaluating countermeasure effectiveness at higher orders, the number of traces must be scaled appropriately. Higher-order attacks typically require significantly more traces to detect leakage. The evaluator must justify the trace count used, considering that insufficient traces may lead to false negatives (missing real leakage). A minimum of 100,000 traces per set is recommended for second-order assessment.

- **Security properties:** Leakage Resistance, Assessment Completeness
- **Verification tier:** Tier 3 — trace count justification and sensitivity analysis
- **Cross-references:** REQ-ISO17825-002 (trace collection parameters), REQ-ISO17825-012 (countermeasure evaluation)

### Reporting

**REQ-ISO17825-014: Evaluation Report Completeness**
The evaluation report must include: (a) device identification and configuration, (b) measurement setup description and equipment specifications, (c) environmental conditions, (d) test vector generation methodology, (e) number of traces collected, (f) statistical test results including maximum t-statistic values, (g) pass/fail verdict for each tested operation, and (h) any deviations from the standard methodology with justification.

- **Security properties:** Transparency, Reproducibility
- **Verification tier:** Tier 3 — report review and completeness check
- **Cross-references:** Common Criteria evaluation methodology, FIPS 140-3 test reporting

**REQ-ISO17825-015: Reproducibility Requirements**
The evaluation methodology and parameters must be documented with sufficient detail that an independent evaluator could reproduce the assessment. This includes exact equipment models, probe placement locations, trigger configuration, trace alignment methodology, and all statistical processing steps. Any proprietary tools or techniques must be described at an algorithmic level.

- **Security properties:** Reproducibility, Transparency
- **Verification tier:** Tier 3 — independent reproduction feasibility review
- **Cross-references:** REQ-ISO17825-014 (report completeness), ISO 19790 (testing reproducibility)

---

## Verification Considerations

| Requirement | Tier | Verification Approach |
|---|---|---|
| REQ-ISO17825-001 | Tier 3 | Lab: fixed vs. random test vectors correctly generated and interleaved |
| REQ-ISO17825-002 | Tier 3 | Lab: trace collection setup meets sampling rate and count requirements |
| REQ-ISO17825-003 | Tier 3 | Analysis: t-test computed correctly; threshold of 4.5 applied per sample point |
| REQ-ISO17825-004 | Tier 3 | Analysis: pass/fail verdict consistent with t-test results across all configurations |
| REQ-ISO17825-005 | Tier 3 | Analysis: first-order t-test on raw traces completed for all operations |
| REQ-ISO17825-006 | Tier 3 | Analysis: higher-order pre-processing and t-test applied for masked implementations |
| REQ-ISO17825-007 | Tier 3 | Analysis: multivariate methods documented with adjusted significance thresholds |
| REQ-ISO17825-008 | Tier 3 | Lab: equipment specifications documented, bandwidth and resolution verified |
| REQ-ISO17825-009 | Tier 3 | Lab: environmental conditions monitored and within tolerance during collection |
| REQ-ISO17825-010 | Tier 3 | Review: all implemented cryptographic algorithms covered in test scope |
| REQ-ISO17825-011 | Tier 3 | Analysis: key-dependent leakage tests performed and documented |
| REQ-ISO17825-012 | Tier 3 | Analysis: countermeasures tested at appropriate order (masking order + 1) |
| REQ-ISO17825-013 | Tier 3 | Review: trace counts justified and sufficient for claimed assessment order |
| REQ-ISO17825-014 | Tier 3 | Review: evaluation report contains all required elements |
| REQ-ISO17825-015 | Tier 3 | Review: methodology documentation sufficient for independent reproduction |

---

*[FROM TRAINING] Requirements are derived summaries, not verbatim specification text. Verify requirement details against ISO/IEC 17825 2nd Edition and related ISO/IEC 19790 standards. Last verified: 2026-02-13.*
