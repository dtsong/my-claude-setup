# Interface Attacks — Threat Catalog

## Overview

Interface attacks target the communication interfaces of the SoC — PCIe, CXL, debug ports, mailboxes, and interrupt controllers. These attacks exploit protocol weaknesses, misconfigured access controls, or missing authentication on hardware interfaces.

---

## INTF-001: PCIe TLP Injection

| Field | Value |
|---|---|
| **STRIDE** | Tampering (T), Elevation of Privilege (E) |
| **Description** | Attacker injects malicious Transaction Layer Packets (TLPs) onto the PCIe bus via a compromised device, physical interposer, or rogue endpoint. Injected TLPs can perform unauthorized memory reads/writes (DMA), configuration space manipulation, or message injection. Without IDE, TLPs are unencrypted and unauthenticated. |
| **Target Assets** | Host memory (via DMA), device configuration space, MMIO regions of other devices |
| **Affected Domains** | TDISP / CXL, Confidential AI / TEE |
| **Affected SoC Families** | Compute, Data Center, Client (Thunderbolt/USB4) |
| **Preconditions** | Compromised PCIe endpoint or physical interposer on PCIe link; IDE not enabled |
| **Key Mitigations** | PCIe IDE (encrypt/authenticate TLPs), IOMMU enforcement, PCIe ACS (Access Control Services), TDISP device assignment, ARI (Alternative Routing-ID Interpretation) |
| **Verification Approach** | Tier 1 — SVA for IOMMU enforcement on all DMA; SVA for IDE active before data transfer |
| **Related Requirements** | REQ-TDISP-007, REQ-TDISP-011, REQ-CXL-001 |

---

## INTF-002: CXL Protocol Manipulation

| Field | Value |
|---|---|
| **STRIDE** | Tampering (T), Information Disclosure (I) |
| **Description** | Attacker manipulates CXL protocol messages (CXL.io, CXL.cache, CXL.mem) to access memory belonging to another host, corrupt cache coherence state, or extract data from shared memory devices. In multi-host CXL configurations, a compromised host or switch port can attempt cross-partition access. |
| **Target Assets** | Shared CXL memory partitions, cache coherence directory, other hosts' data |
| **Affected Domains** | TDISP / CXL |
| **Affected SoC Families** | Data Center (primary), Compute |
| **Preconditions** | Compromised host connected to CXL fabric, or compromised CXL switch firmware |
| **Key Mitigations** | CXL IDE (encrypt/authenticate all CXL traffic), TSP partition isolation (REQ-CXL-007), per-host encryption keys (REQ-CXL-008), switch port isolation (REQ-CXL-009) |
| **Verification Approach** | Tier 1 — SVA for partition boundary enforcement; Tier 2 — protocol check for TSP configuration |
| **Related Requirements** | REQ-CXL-007, REQ-CXL-008, REQ-CXL-009, REQ-CXL-010 |

---

## INTF-003: TDISP Handshake Bypass

| Field | Value |
|---|---|
| **STRIDE** | Spoofing (S), Elevation of Privilege (E) |
| **Description** | Attacker attempts to use a device without completing the TDISP handshake (authentication, measurement, IDE setup). If the platform does not enforce the TDI state machine, a device could be accessed in CONFIG or LOCK state before security properties are established. |
| **Target Assets** | TDI state machine, SPDM session binding, IDE stream |
| **Affected Domains** | TDISP / CXL, Confidential AI / TEE |
| **Affected SoC Families** | Compute, Data Center |
| **Preconditions** | Platform firmware vulnerability that allows TDI access without state machine completion; or race condition in state transitions |
| **Key Mitigations** | Hardware-enforced TDI state machine (REQ-TDISP-003), SVA assertions for legal transitions only, platform firmware verification of TDI state before granting access |
| **Verification Approach** | Tier 1 — SVA for state machine transition rules; SVA that data access blocked unless TDI in RUN state |
| **Related Requirements** | REQ-TDISP-001, REQ-TDISP-003, REQ-TDISP-005 |

---

## INTF-004: DMA Attacks

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I), Tampering (T), Elevation of Privilege (E) |
| **Description** | Attacker uses a DMA-capable device (legitimate or rogue) to read or write host memory without CPU involvement. Classic examples include FireWire/Thunderbolt DMA attacks and compromised PCIe devices. DMA bypasses CPU-level access controls (MMU, CHERI capabilities) because the access originates from the device, not the CPU. |
| **Target Assets** | Host DRAM (encryption keys, page tables, kernel code), TEE memory (if IOMMU misconfigured) |
| **Affected Domains** | TDISP / CXL, Confidential AI / TEE, RISC-V CHERI (DMA bypasses capability checks) |
| **Affected SoC Families** | All — Client (Thunderbolt hot-plug), Compute (device passthrough), Data Center (DPU DMA) |
| **Preconditions** | DMA-capable device accessible to attacker; IOMMU not enforced or misconfigured; pre-boot DMA window (before IOMMU initialized) |
| **Key Mitigations** | IOMMU enforcement from earliest boot (DMA protection boot policy), TDISP device assignment (REQ-TDISP-011), PCIe ACS to prevent peer-to-peer DMA, pre-boot DMA protection, Thunderbolt security levels |
| **Verification Approach** | Tier 1 — SVA for IOMMU active before first DMA transaction; SVA for TDISP DMA isolation |
| **Related Requirements** | REQ-TDISP-011, REQ-TDISP-005, PCIe ACS |

---

## INTF-005: Debug Port Exploitation (JTAG/SWD)

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I), Elevation of Privilege (E) |
| **Description** | Attacker connects to an exposed debug port (JTAG, SWD, DCI) to halt the CPU, read/write memory and registers, set breakpoints, and extract secrets. Debug interfaces typically operate at the highest privilege level. If debug authentication is weak or absent, full compromise is possible. |
| **Target Assets** | All CPU-accessible memory and registers, key material, firmware execution state, security configuration |
| **Affected Domains** | All — debug is cross-cutting |
| **Affected SoC Families** | All — Automotive (OBD-II path to JTAG), Client (exposed pads), Compute (RMA debug headers) |
| **Preconditions** | Debug port physically accessible; debug not permanently disabled; debug authentication bypassable |
| **Key Mitigations** | Debug authentication FSM, permanent debug disable fuse for production, secret zeroization on debug unlock, debug access levels (manufacturing/field/locked), test pin multiplexing (hide debug behind non-obvious pins) |
| **Verification Approach** | Tier 1 — SVA for debug auth FSM (challenge-response required); SVA for secret zeroization on debug enable |
| **Related Requirements** | Verification patterns `sva-templates/fsm-transitions.sv` |

---

## INTF-006: Mailbox and Register Abuse

| Field | Value |
|---|---|
| **STRIDE** | Tampering (T), Elevation of Privilege (E) |
| **Description** | Attacker exploits misconfigured or insufficiently protected hardware mailboxes and control registers to modify security configuration, inject commands into security controllers, or read sensitive state. Mailboxes between CPU and security subsystem, BMC and host, or between firmware layers are common targets. |
| **Target Assets** | Security configuration registers, inter-processor mailboxes, command queues for crypto engines, firmware update registers |
| **Affected Domains** | Secure Boot / DICE, TDISP / CXL, Confidential AI / TEE |
| **Affected SoC Families** | Compute and Data Center (BMC-host mailbox), All (inter-subsystem mailboxes) |
| **Preconditions** | Software access to register/mailbox address space; access control not enforced or bypassable |
| **Key Mitigations** | Register access control (per-field write masks, privilege-level gating), sticky lock bits for security configuration, bus firewall filtering by master ID, mailbox authentication (signed commands) |
| **Verification Approach** | Tier 1 — SVA for register lock enforcement, write-mask behavior, privilege-gated access |
| **Related Requirements** | REQ-TDISP-004 (LOCK state enforcement), Verification patterns `sva-templates/register-locks.sv` |

---

## INTF-007: Interrupt Injection

| Field | Value |
|---|---|
| **STRIDE** | Denial of Service (D), Elevation of Privilege (E) |
| **Description** | Attacker injects spurious interrupts via a compromised device or by manipulating interrupt controller configuration. Interrupt flooding can cause denial of service by starving legitimate interrupt handlers. Targeted interrupt injection can redirect execution to attacker-controlled handlers or trigger race conditions in security-critical interrupt handlers. |
| **Target Assets** | Interrupt controller (APIC, GIC, PLIC), interrupt handler execution, interrupt-driven security state machines |
| **Affected Domains** | Confidential AI / TEE (interrupt across trust boundary), TDISP / CXL |
| **Affected SoC Families** | All — Compute and Data Center (MSI/MSI-X injection from PCIe devices) |
| **Preconditions** | Compromised device or control of interrupt configuration registers; MSI/MSI-X target address writable |
| **Key Mitigations** | Interrupt remapping (via IOMMU), interrupt rate limiting, MSI/MSI-X address filtering, interrupt isolation for TEE VMs, Posted Interrupts for virtualized interrupt delivery |
| **Verification Approach** | Tier 1 — SVA for interrupt rate limiting, MSI address filtering; Tier 2 — protocol check for interrupt remapping configuration |
| **Related Requirements** | REQ-TDISP-005 (access control in RUN state) |

---

*[FROM TRAINING] Threat descriptions are based on publicly known attack classes from academic literature and industry reports. Verify against current threat landscape assessments. Last verified: 2026-02-13.*
