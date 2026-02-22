# SoC Family Profiles — Cross-Cutting Reference

## Purpose

This reference details what reuses across SoC families (70-80%), what varies (20-30%), and provides a traceability matrix template for family-specific annotations. It bridges the domain ontology (which defines families abstractly) with practical engineering guidance for per-family customization.

**Primary consumers:** compliance-pipeline-skill (traceability matrix generation), threat-model-skill (family-specific threat weighting)
**Secondary consumers:** verification-scaffold-skill (family-aware assertion selection), executive-brief-skill (family context)

---

## Shared Architecture Components (70-80% Reuse)

These components are architecturally identical or near-identical across families. Verification assets targeting these components can be reused with minimal modification.

### High Reuse (>90% shared)

| Component | What Reuses | What Varies |
|---|---|---|
| **Crypto engines** (AES, SHA, ECC, RSA) | Algorithm implementation, interface protocol, key loading sequence | Algorithm selection (SM4 for China), performance targets, side-channel protection level |
| **Boot ROM / immutable first stage** | Security model, measurement flow, CDI derivation logic | ROM size, bus interface width, error handling behavior |
| **DICE layered identity** | CDI derivation algorithm, certificate generation, secret locking | Number of DICE layers, certificate extensions, alias key algorithm preference |
| **Fuse controller (OTP)** | Access control model, blow sequencing, read-back verification | Fuse count, field layout, programming voltage, efuse vs. antifuse technology |
| **Debug authentication FSM** | Authentication protocol (challenge-response), state machine | Debug features exposed per state, authentication key source, debug levels supported |
| **SPDM responder/requester** | Protocol stack, message encoding, algorithm negotiation | Certificate provisioning, measurement scope, transport binding (MCTP vs. DOE) |

### Medium Reuse (60-80% shared)

| Component | What Reuses | What Varies |
|---|---|---|
| **TDISP state machine** | State definitions, transition rules, SPDM session binding | Present only in PCIe-equipped families; TDI count, IDE stream count |
| **CHERI capability rules** | ISA-defined capability encoding, bounds check, tag management | Present only in CHERI-enabled designs; integration with privilege levels, TLB/cache capability storage |
| **Bus firewalls** | Address-range filtering, master ID checking, lock-after-boot | Bus protocol (AXI vs. PCIe), number of regions, master ID encoding, filtering granularity |
| **Key management unit** | Key hierarchy, key slot access control, key derivation | Key count, derivation algorithm, hardware entropy source |

---

## Per-Family Variation Matrix

### Interconnect and Bus Architecture

| Aspect | Compute | Automotive | Client | Data Center |
|---|---|---|---|---|
| **Primary on-chip bus** | AXI/ACE, proprietary NoC | AXI/AHB | Proprietary NoC | AXI/ACE, proprietary NoC |
| **Primary off-chip** | PCIe Gen5/6, CXL 3.x | CAN-FD, Automotive Ethernet | PCIe, USB4/Thunderbolt | CXL fabric, PCIe, 100/400GbE |
| **Management bus** | BMC (I3C/SPI/LPC), MCTP | SPI, I2C/I3C | EC (eSPI/LPC) | BMC, MCTP, I3C |
| **Impact on security** | CXL fabric security, multi-host IDE | CAN authentication (SecOC), gateway firewalls | Thunderbolt DMA protection, USB security | CXL TSP, switch port isolation |

### Power Domain Topology

| Aspect | Compute | Automotive | Client | Data Center |
|---|---|---|---|---|
| **Power model** | Always-on, high budget (200-500W) | Constrained, multi-domain (5-50W) | Battery-optimized (15-45W) | Medium-high (50-200W) |
| **Security implication** | Crypto always available; no power-state security gaps | Crypto may be power-gated; must preserve security state across power transitions | Balance crypto power with battery life; suspend/resume security | Always-on crypto; redundant power for security subsystem |
| **Threat surface** | Minimal power-related security gaps | Power-state transitions may create TOCTOU windows | Suspend/resume may leak keys if not properly handled | Power redundancy reduces DoS risk |

### Clock Domain Crossings

| Aspect | Compute | Automotive | Client | Data Center |
|---|---|---|---|---|
| **Clock domains** | Many (core, uncore, PCIe, CXL, memory) | Many (safety-critical, non-safety, gated) | Many (core, GPU, NPU, IO) | Many (core, CXL, network, management) |
| **Security implication** | CDC bugs can cause security state corruption | Safety-critical clock domains must be independent of security domains | Clock gating for power must not affect security timing | CXL clock domain synchronization for IDE |
| **Verification need** | CDC checks on security signals crossing domains | Safety-security clock domain independence verification | Security state preservation across clock gating | IDE timing synchronization across CXL clock domains |

### Compliance Regime

| Regime | Compute | Automotive | Client | Data Center |
|---|---|---|---|---|
| **FIPS 140-3** | Level 2+ required | Emerging | Level 1-2 | Level 2+ required |
| **ISO 21434** | N/A | Mandatory | N/A | N/A |
| **ISO 26262** | N/A | ASIL-B to ASIL-D | N/A | N/A |
| **TCG TPM 2.0** | Common | Rare | Required (Win11) | Common |
| **Common Criteria** | Optional (EAL4+) | Optional | Optional | Optional |
| **SOC 2 Type II** | Required (cloud) | N/A | N/A | Required (cloud) |

### Interrupt Routing

| Aspect | Compute | Automotive | Client | Data Center |
|---|---|---|---|---|
| **Interrupt controller** | APIC/x2APIC | GIC (ARM), PLIC (RISC-V) | APIC/GIC | APIC/x2APIC |
| **Security implication** | MSI/MSI-X injection from PCIe devices | Interrupt priority inversion affecting safety-critical handlers | Interrupt across TEE boundary | MSI injection, interrupt isolation across hosts |
| **Mitigation** | Interrupt remapping (IOMMU) | Priority ceiling, interrupt partitioning | Interrupt remapping | Interrupt remapping, per-host isolation |

---

## Family-Specific Annotation Format

When generating traceability matrices, per-family annotations use the following format:

```
[FAMILY:{family_name}] {annotation_text}
```

Examples:
```
[FAMILY:Automotive] ISO 21434 clause 8.3 requires supply chain cybersecurity management
[FAMILY:Compute] FIPS 140-3 Level 2 requires tamper-evidence for physical security
[FAMILY:Client] TPM 2.0 PCR values must be consistent with DICE measurements
[FAMILY:Data Center] CXL TSP partition configuration must survive host reboot
```

---

## Traceability Matrix Template

| Spec Req ID | Req Text (Summary) | Security Domain | SoC Family | RTL Module | Verification Asset | Compliance Evidence | Status | Gap Flag |
|---|---|---|---|---|---|---|---|---|
| REQ-DICE-001 | UDS must be hardware-protected and locked after first CDI derivation | Secure Boot / DICE | All | `dice_uds_ctrl.sv` | `sva_dice_secret_lock` | Sim log + formal report | Verified | None |
| REQ-DICE-001 | UDS must be hardware-protected and locked after first CDI derivation | Secure Boot / DICE | Automotive | `dice_uds_ctrl.sv` | `sva_dice_secret_lock` | Sim log + formal report | Verified | [FAMILY:Automotive] Verify HSM integration path |
| REQ-TDISP-003 | TDI state machine must follow legal transitions only | TDISP / CXL | Compute | `tdisp_fsm.sv` | `sva_tdisp_state_machine` | Sim log + coverage | Verified | None |
| REQ-TDISP-003 | TDI state machine must follow legal transitions only | TDISP / CXL | Automotive | N/A | N/A | N/A | N/A | [FAMILY:Automotive] TDISP not applicable (no PCIe device passthrough) |
| REQ-CXL-007 | Memory partition isolation for multi-host | TDISP / CXL | Data Center | `cxl_tsp_partition.sv` | `sva_cxl_partition` | Sim log + formal | In Progress | Multi-host test infrastructure needed |
| REQ-CHERI-002 | Capability bounds check on every memory access | RISC-V CHERI | Compute | `cheri_bounds_check.sv` | `sva_cheri_bounds_check` | Formal proof | Verified | None |

---

*[FROM TRAINING] All content in this file is derived from general hardware security engineering knowledge. Specific implementation details should be verified against target SoC documentation. Last verified: 2026-02-13.*
