# Physical Attacks — Threat Catalog

## Overview

Physical attacks require the attacker to have physical access to the SoC, its package, or its immediate environment (board, DRAM, interconnect). These attacks target hardware-level secrets, cryptographic operations, and data at rest in physical media.

---

## PHYS-001: Voltage Fault Injection

| Field | Value |
|---|---|
| **STRIDE** | Tampering (T), Elevation of Privilege (E) |
| **Description** | Attacker induces transient voltage glitches on the power supply rail to corrupt cryptographic computations, skip security checks (e.g., signature verification), or force incorrect branch decisions. Precise timing targets specific instruction executions. |
| **Target Assets** | Crypto engine operations, boot verification logic, security FSM transitions |
| **Affected Domains** | Secure Boot / DICE, Supply Chain Security, Confidential AI / TEE |
| **Affected SoC Families** | All — but Automotive and Client most exposed due to physical accessibility |
| **Preconditions** | Physical access to power pins or decoupling capacitors; knowledge of target operation timing |
| **Key Mitigations** | Voltage glitch detectors, redundant computation (dual-rail logic), instruction flow integrity checks, sensor-triggered zeroization |
| **Verification Approach** | Tier 3 — physical testing required; Tier 1 can verify glitch detector response logic |
| **Related Requirements** | REQ-DICE-010 (error handling), REQ-DICE-002 (immutable ROM) |

---

## PHYS-002: Clock Fault Injection

| Field | Value |
|---|---|
| **STRIDE** | Tampering (T), Elevation of Privilege (E) |
| **Description** | Attacker manipulates the clock signal (glitching, stretching, or injecting extra edges) to cause setup/hold violations that corrupt register values or skip instructions. Targets the same assets as voltage glitching but through a different physical vector. |
| **Target Assets** | Crypto engine FSMs, boot sequence logic, security check comparisons |
| **Affected Domains** | Secure Boot / DICE, Supply Chain Security |
| **Affected SoC Families** | All — external clock inputs most vulnerable; internal PLLs more resistant |
| **Preconditions** | Physical access to clock input pins or ability to influence PLL behavior |
| **Key Mitigations** | Clock monitors (frequency/duty-cycle detectors), internal clock generation (PLL with lock detection), redundant computation, temporal redundancy (execute critical operations multiple times) |
| **Verification Approach** | Tier 3 — physical testing; Tier 1 can verify clock monitor response logic |
| **Related Requirements** | REQ-DICE-010 (error handling) |

---

## PHYS-003: Laser Fault Injection

| Field | Value |
|---|---|
| **STRIDE** | Tampering (T), Elevation of Privilege (E) |
| **Description** | Attacker uses focused laser pulses on the die surface (after depackaging) to induce bit flips in specific registers or SRAM cells. Extremely precise targeting enables selective corruption of security-critical values (e.g., flipping a lock bit, corrupting a hash comparison result). |
| **Target Assets** | Security configuration registers, hash comparison registers, capability tag bits (CHERI), OTP fuse sense circuits |
| **Affected Domains** | All — particularly Secure Boot / DICE (lock bits), RISC-V CHERI (tag bits) |
| **Affected SoC Families** | All — requires depackaging, so IoT/consumer more exposed than automotive (conformal coating) |
| **Preconditions** | Depackaged die, laser fault injection equipment, detailed knowledge of die layout |
| **Key Mitigations** | Active mesh/shield layers, light sensors, redundant storage of security-critical bits, error detection codes on registers, anti-tamper enclosures |
| **Verification Approach** | Tier 3 — physical testing only; Tier 1 can verify redundancy/ECC logic on critical registers |
| **Related Requirements** | REQ-CHERI-001 (tag integrity), REQ-DICE-001 (UDS protection) |

---

## PHYS-004: Electromagnetic Fault Injection

| Field | Value |
|---|---|
| **STRIDE** | Tampering (T) |
| **Description** | Attacker uses an EM probe near the die or package to induce localized faults through electromagnetic coupling. Similar effect to voltage glitching but can target specific die regions without direct electrical contact. Does not require depackaging. |
| **Target Assets** | Crypto computations, SRAM contents, bus transactions |
| **Affected Domains** | Secure Boot / DICE, Supply Chain Security |
| **Affected SoC Families** | All — no depackaging required makes this broadly applicable |
| **Preconditions** | Physical proximity to SoC package, EM injection probe, timing synchronization |
| **Key Mitigations** | EM shielding, randomized timing (jitter insertion), redundant computation, EM sensors |
| **Verification Approach** | Tier 3 — physical EM testing; Tier 1 can verify sensor response logic |
| **Related Requirements** | REQ-DICE-010 (error handling) |

---

## PHYS-005: Power Side-Channel Analysis (SPA/DPA)

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I) |
| **Description** | Attacker monitors power consumption traces during cryptographic operations to extract secret keys. Simple Power Analysis (SPA) uses single traces; Differential Power Analysis (DPA) uses statistical analysis across many traces. Correlation Power Analysis (CPA) is a refined DPA variant. |
| **Target Assets** | AES, RSA, ECC, SHA keys and intermediate values in crypto engines |
| **Affected Domains** | All domains using cryptographic operations |
| **Affected SoC Families** | All — particularly constrained devices (Automotive, Client) where shielding is limited |
| **Preconditions** | Physical access to power measurement point (shunt resistor, current probe); ability to trigger repeated crypto operations with known/chosen inputs |
| **Key Mitigations** | Masking (Boolean, arithmetic), shuffling (randomized operation order), constant-power circuits, noise injection, key refresh/rotation, TVLA-based validation |
| **Verification Approach** | Tier 3 — lab measurement (TVLA, CPA) required; Tier 1 limited to verifying constant-time mux selection |
| **Related Requirements** | FIPS 140-3 Level 3+ (physical security) |

---

## PHYS-006: Timing Side-Channel Analysis

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I) |
| **Description** | Attacker measures execution time variations in cryptographic or security-critical operations to infer secret values. Non-constant-time implementations leak information through data-dependent branches, cache misses, and variable-time arithmetic (e.g., modular exponentiation). |
| **Target Assets** | Crypto engine operations, key comparison logic, authentication decision paths |
| **Affected Domains** | All domains with timing-sensitive security operations |
| **Affected SoC Families** | All |
| **Preconditions** | Ability to measure operation timing with sufficient precision (network-based for remote; local for high-precision) |
| **Key Mitigations** | Constant-time implementations, balanced branches, cache partitioning/flushing, timing noise injection |
| **Verification Approach** | Tier 1 — SVA can verify constant-time mux selection in datapath; Tier 3 for full timing analysis |
| **Related Requirements** | FIPS 140-3 (implementation security) |

---

## PHYS-007: Physical Probing and Bus Sniffing

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I) |
| **Description** | Attacker places physical probes on exposed buses (PCIe, CXL, DDR, SPI flash) to capture data in transit. For unencrypted buses, this directly exposes data. For encrypted buses, captured ciphertext may be used in conjunction with other attacks. |
| **Target Assets** | DRAM contents (plaintext if no memory encryption), SPI flash contents (firmware images), PCIe/CXL TLPs (plaintext if no IDE) |
| **Affected Domains** | TDISP / CXL (link interposer), Confidential AI / TEE (memory probing), Secure Boot / DICE (firmware extraction) |
| **Affected SoC Families** | Compute and Data Center (interposer on CXL/PCIe); Client (DDR probing); Automotive (CAN/SPI probing) |
| **Preconditions** | Physical access to board-level buses; probing equipment (logic analyzer, protocol analyzer) |
| **Key Mitigations** | Memory encryption (AES-XTS), link encryption (PCIe IDE, CXL IDE), SPI flash encryption, BGA packages (harder to probe), conformal coating |
| **Verification Approach** | Tier 1 — SVA that encrypted bus does not expose cleartext; Tier 3 for physical probe resistance |
| **Related Requirements** | REQ-CXL-001/002/003 (CXL IDE), REQ-TDISP-007 (IDE before assignment) |

---

## PHYS-008: Cold Boot / Memory Remanence

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I) |
| **Description** | Attacker exploits DRAM data remanence after power loss to extract encryption keys or sensitive data. Cooling DRAM modules extends remanence time. Attacker power-cycles the system and boots from attacker-controlled media to read DRAM contents before they decay. |
| **Target Assets** | Encryption keys in DRAM (full-disk encryption keys, TEE secrets), runtime secrets, capability tables (CHERI) |
| **Affected Domains** | Confidential AI / TEE, RISC-V CHERI (capability tables), Secure Boot / DICE (if keys linger in DRAM) |
| **Affected SoC Families** | Client (laptop theft scenario); Compute/Data Center (decommissioning); Automotive (vehicle theft) |
| **Preconditions** | Physical access to DRAM modules; ability to power-cycle and boot from external media; optional: cooling to extend remanence |
| **Key Mitigations** | Memory encryption (AES-XTS with per-boot keys), key zeroization on tamper detect or power-loss, DRAM scrambling, soldered DRAM (harder to transfer), volatile key storage in SRAM (faster decay) |
| **Verification Approach** | Tier 1 — SVA for key zeroization trigger on tamper/power-loss; Tier 3 for remanence testing |
| **Related Requirements** | REQ-DICE-004 (CDI secrecy — relevant to key-in-DRAM scenarios) |

---

*[FROM TRAINING] Threat descriptions are based on publicly known attack classes from academic literature and industry reports. Verify against current threat landscape assessments. Last verified: 2026-02-13.*
