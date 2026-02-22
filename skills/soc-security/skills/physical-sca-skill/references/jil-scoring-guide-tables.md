# JIL Attack Potential Scoring — Rating Thresholds & Worked Examples

## Contents

- [3. Rating Thresholds](#3-rating-thresholds)
- [4. Mapping to Common Criteria AVA_VAN Levels](#4-mapping-to-common-criteria-ava_van-levels)
- [5. Scoring Examples for SCA Attacks](#5-scoring-examples-for-sca-attacks)
  - [Example 1: First-Order CPA on Unprotected AES-128](#example-1-first-order-cpa-on-unprotected-aes-128)
  - [Example 2: Second-Order CPA on First-Order Masked AES-256](#example-2-second-order-cpa-on-first-order-masked-aes-256)
  - [Example 3: DFA via Voltage Glitch on AES-256 (No FI Countermeasures)](#example-3-dfa-via-voltage-glitch-on-aes-256-no-fi-countermeasures)
  - [Example 4: DFA via Voltage Glitch on AES-256 (With Glitch Sensor + Redundancy)](#example-4-dfa-via-voltage-glitch-on-aes-256-with-glitch-sensor--redundancy)
  - [Example 5: Laser Fault Injection on ECDSA Nonce Generation](#example-5-laser-fault-injection-on-ecdsa-nonce-generation)
  - [Example 6: Template Attack on Masked AES (Profiling on Clone Device)](#example-6-template-attack-on-masked-aes-profiling-on-clone-device)

---

## 3. Rating Thresholds

| Rating | Total Score Range | Resistance Level | Practical Meaning |
|--------|------------------|------------------|-------------------|
| **Basic** | < 10 | No claimed resistance | Attack feasible by proficient attacker with standard tools in days |
| **Enhanced-Basic** | 10-13 | Basic resistance | Attack requires some specialized capability but achievable |
| **Moderate** | 14-19 | Moderate resistance | Attack requires significant expertise, time, or equipment |
| **High** | 20-24 | High resistance | Attack requires expert-level resources and extended effort |
| **Beyond-High** | > 24 | Beyond high resistance | Attack requires multiple experts, advanced equipment, and months of effort |

---

## 4. Mapping to Common Criteria AVA_VAN Levels

| JIL Rating | CC AVA_VAN Level | CC Requirement | Evaluator Action |
|-----------|------------------|----------------|-----------------|
| Basic | AVA_VAN.1 | No resistance claimed | Evaluator confirms public vulnerability analysis |
| Enhanced-Basic | AVA_VAN.2 | Resistance to basic attack potential | Evaluator performs vulnerability analysis with enhanced-basic attack potential |
| Moderate | AVA_VAN.3 | Resistance to moderate attack potential | Evaluator performs vulnerability analysis with moderate attack potential |
| High | AVA_VAN.4 | Resistance to high attack potential | Evaluator performs vulnerability analysis with high attack potential |
| Beyond-High | AVA_VAN.5 | Resistance to beyond-high attack potential | Evaluator performs vulnerability analysis with beyond-high attack potential; strongest CC assurance level |

**Typical CC target levels for SCA:**
- Smartcards and secure elements: AVA_VAN.5 (Beyond-High) — must resist all known SCA
- Payment terminals: AVA_VAN.4 (High)
- IoT secure enclaves: AVA_VAN.3 (Moderate) typical minimum
- General-purpose SoC crypto engines: AVA_VAN.2-3 depending on threat model

---

## 5. Scoring Examples for SCA Attacks

### Example 1: First-Order CPA on Unprotected AES-128

| Category | Score | Rationale |
|----------|-------|-----------|
| Elapsed Time | 2 | < 2 weeks: well-documented attack, standard tools |
| Expertise | 3 | Proficient: requires SCA knowledge but widely taught |
| Knowledge of TOE | 0 | Public: AES algorithm is public; no implementation-specific knowledge needed |
| Access | 0 | Unlimited: attacker has the device in their lab |
| Equipment | 2 | Specialized: ChipWhisperer or similar SCA board |
| **TOTAL** | **7** | |
| **RATING** | **Basic** | Attack is straightforward with standard SCA tools |

**Verdict:** Unprotected AES is trivially attackable. No CC resistance claim possible.

---

### Example 2: Second-Order CPA on First-Order Masked AES-256

| Category | Score | Rationale |
|----------|-------|-----------|
| Elapsed Time | 10 | < 3 months: trace collection, point-of-interest identification, higher-order analysis development |
| Expertise | 6 | Expert: must understand masking theory, combination functions, and signal processing for higher-order analysis |
| Knowledge of TOE | 3 | Restricted: need to know masking scheme (Boolean vs. arithmetic) and share representation to choose combination function |
| Access | 0 | Unlimited: lab evaluation with purchased device |
| Equipment | 4 | Bespoke: high-end oscilloscope (> 2 GS/s, 12-bit) for sufficient SNR at higher orders |
| **TOTAL** | **23** | |
| **RATING** | **High** | Requires expert with significant time and equipment |

**Verdict:** First-order masking provides substantial resistance. Meets AVA_VAN.4 (High).

---

### Example 3: DFA via Voltage Glitch on AES-256 (No FI Countermeasures)

| Category | Score | Rationale |
|----------|-------|-----------|
| Elapsed Time | 4 | < 1 month: glitch parameter characterization, targeting the correct round |
| Expertise | 3 | Proficient: voltage glitching is well-documented; DFA is a standard technique |
| Knowledge of TOE | 3 | Restricted: need knowledge of clock frequency, voltage rail access, computation timing |
| Access | 1 | Large: device can be taken to lab; needs voltage rail access (may need PCB modification) |
| Equipment | 2 | Specialized: ChipWhisperer with glitch module or equivalent |
| **TOTAL** | **13** | |
| **RATING** | **Enhanced-Basic** | Achievable with moderate effort |

**Verdict:** Without fault injection countermeasures, DFA is practical. Meets only AVA_VAN.2.

---

### Example 4: DFA via Voltage Glitch on AES-256 (With Glitch Sensor + Redundancy)

| Category | Score | Rationale |
|----------|-------|-----------|
| Elapsed Time | 10 | < 3 months: must characterize and bypass glitch sensor, find redundancy gaps |
| Expertise | 6 | Expert: must understand sensor behavior, develop bypass technique |
| Knowledge of TOE | 7 | Sensitive: need knowledge of sensor thresholds, redundancy implementation |
| Access | 1 | Large: lab access with PCB modification |
| Equipment | 4 | Bespoke: precision glitch generator with sub-ns timing control |
| **TOTAL** | **28** | |
| **RATING** | **Beyond-High** | Sensor + redundancy significantly increases difficulty |

**Verdict:** Glitch sensor combined with computation redundancy provides strong FI resistance. Meets AVA_VAN.5.

---

### Example 5: Laser Fault Injection on ECDSA Nonce Generation

| Category | Score | Rationale |
|----------|-------|-----------|
| Elapsed Time | 15 | < 5 months: decapping, IC reverse engineering, target identification, laser characterization |
| Expertise | 8 | Multiple experts: requires IC reverse engineering specialist + SCA/FI expert + cryptanalyst for lattice attack on biased nonces |
| Knowledge of TOE | 7 | Sensitive: need layout information to target TRNG or nonce computation |
| Access | 4 | Moderate: device must be decapped (destructive); need multiple samples |
| Equipment | 6 | Advanced bespoke: laser FI station, IC decapping, microscopy |
| **TOTAL** | **40** | |
| **RATING** | **Beyond-High** | Extremely resource-intensive attack |

**Verdict:** Laser FI on nonce generation is at the extreme end of attack potential.

---

### Example 6: Template Attack on Masked AES (Profiling on Clone Device)

| Category | Score | Rationale |
|----------|-------|-----------|
| Elapsed Time | 7 | < 2 months: profiling phase on clone device, template construction, attack execution |
| Expertise | 6 | Expert: template attack requires statistical modeling, POI selection, portability analysis |
| Knowledge of TOE | 3 | Restricted: need a clone device with identical implementation |
| Access | 1 | Large: clone device in lab; target device accessible for limited traces |
| Equipment | 4 | Bespoke: high-end oscilloscope, possibly custom measurement setup for profiling |
| **TOTAL** | **21** | |
| **RATING** | **High** | Template attacks are powerful but require profiling infrastructure |
