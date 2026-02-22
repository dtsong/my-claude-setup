# Architectural Attacks — Threat Catalog

## Overview

Architectural attacks exploit design-level weaknesses in security boundaries, privilege models, and state management. These attacks do not require physical access — they are carried out through software running on the SoC, exploiting logical flaws in the security architecture.

---

## ARCH-001: Privilege Escalation Across Security Boundaries

| Field | Value |
|---|---|
| **STRIDE** | Elevation of Privilege (E) |
| **Description** | Attacker in a lower-privilege domain (user mode, non-secure world, guest VM) exploits a vulnerability to execute code or access resources in a higher-privilege domain (kernel, secure world, hypervisor). Common vectors include system call vulnerabilities, SMC (Secure Monitor Call) handler bugs, and hypercall interface flaws. |
| **Target Assets** | Privilege level boundaries (EL0/EL1/EL2/EL3 on ARM, M/S/U on RISC-V), secure/non-secure boundary, hypervisor interface |
| **Affected Domains** | Confidential AI / TEE, Secure Boot / DICE, RISC-V CHERI |
| **Affected SoC Families** | All |
| **Preconditions** | Code execution at lower privilege level; vulnerability in privilege transition handler |
| **Key Mitigations** | Minimal attack surface on privilege boundaries, formal verification of privilege transition logic, CHERI compartmentalization to limit blast radius, hardware privilege enforcement (PMP, MPU, MMU) |
| **Verification Approach** | Tier 1 — SVA for privilege-level checks on every privileged operation; Tier 3 — formal analysis of privilege transition completeness |
| **Related Requirements** | REQ-CHERI-011 (PMP/capability interaction), REQ-CHERI-003 (permission enforcement) |

---

## ARCH-002: VM Escape / TEE Breakout

| Field | Value |
|---|---|
| **STRIDE** | Elevation of Privilege (E), Information Disclosure (I) |
| **Description** | Attacker in a guest VM or TEE workload escapes the isolation boundary to access the hypervisor, other VMs, or the host. Vectors include vulnerabilities in virtual device emulation, shared memory handling, interrupt delivery, or hardware isolation mechanisms. In confidential computing contexts, the threat model assumes the hypervisor is untrusted, so the escape vector is from the untrusted hypervisor into the TEE. |
| **Target Assets** | VM isolation boundary, TEE memory encryption, GPT/EPT (Granule/Extended Page Tables), shared device state |
| **Affected Domains** | Confidential AI / TEE, TDISP / CXL (device in VM context) |
| **Affected SoC Families** | Compute (primary — multi-tenant VMs), Data Center (DPU-hosted VMs) |
| **Preconditions** | Code execution in guest VM; vulnerability in isolation mechanism or shared resource handling |
| **Key Mitigations** | Hardware memory encryption per VM, hardware page table isolation (GPT, EPT with encryption), minimal shared state between VMs, TDISP for device isolation, side-channel mitigations for shared microarchitectural state |
| **Verification Approach** | Tier 1 — SVA for page table isolation enforcement; Tier 3 — information flow analysis across VM boundaries |
| **Related Requirements** | REQ-TDISP-005 (RUN state access control), REQ-CXL-007 (memory partition isolation) |

---

## ARCH-003: Memory Isolation Bypass

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I), Elevation of Privilege (E) |
| **Description** | Attacker bypasses memory isolation mechanisms (MMU, MPU, bus firewall, IOMMU) to access memory belonging to another security domain. Bypass vectors include: address translation manipulation, firewall misconfiguration, race conditions during reconfiguration, or hardware bugs in the isolation logic. |
| **Target Assets** | Bus firewalls (AXI/AHB protection units), IOMMU translation tables, MPU/MMU configuration, memory encryption key domains |
| **Affected Domains** | All |
| **Affected SoC Families** | All |
| **Preconditions** | Knowledge of memory layout; ability to trigger firewall reconfiguration or exploit race condition; or hardware bug in isolation logic |
| **Key Mitigations** | Lock firewall configuration after boot, hardware-enforced isolation (not firmware-configurable at runtime), defense-in-depth (firewall + encryption), CHERI capability bounds as additional layer, formal verification of firewall logic |
| **Verification Approach** | Tier 1 — SVA for firewall configuration lock, address-range enforcement; Tier 3 — formal verification of firewall completeness |
| **Related Requirements** | REQ-CXL-007, REQ-TDISP-011, REQ-CHERI-002 (bounds checking) |

---

## ARCH-004: Capability Forgery (CHERI)

| Field | Value |
|---|---|
| **STRIDE** | Elevation of Privilege (E), Tampering (T) |
| **Description** | Attacker attempts to create a capability with more authority than legitimately held. If the tag bit mechanism or monotonicity invariant is broken (due to hardware bug, fault injection, or design flaw), an attacker could forge capabilities granting arbitrary memory access or permission escalation. |
| **Target Assets** | CHERI tag bits, capability register file, capability cache/TLB, monotonicity invariant |
| **Affected Domains** | RISC-V CHERI |
| **Affected SoC Families** | Any family with CHERI-enabled processors |
| **Preconditions** | Hardware bug in tag management, fault injection targeting tag bits, or ISA implementation error that violates monotonicity |
| **Key Mitigations** | Formal verification of tag bit management across all datapaths, ECC/redundancy on tag storage, physical side-channel mitigations for tag bits (PHYS-003), comprehensive ISA compliance testing |
| **Verification Approach** | Tier 1 — SVA for tag clearing on non-capability writes, monotonicity on all capability operations; Tier 3 — formal verification of complete tag propagation |
| **Related Requirements** | REQ-CHERI-001, REQ-CHERI-004, REQ-CHERI-009 |

---

## ARCH-005: Cross-Domain Information Flow

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I) |
| **Description** | Information leaks between security domains through shared microarchitectural resources — caches, branch predictors, TLBs, interconnect buffers, power management state. Unlike physical side channels (PHYS-005/006), these attacks are executed entirely in software by observing timing or contention on shared hardware. Spectre, Meltdown, and their variants are canonical examples. |
| **Target Assets** | Shared caches (L1/L2/LLC), branch predictor state, TLB entries, memory bus bandwidth, power management state |
| **Affected Domains** | Confidential AI / TEE, TDISP / CXL, RISC-V CHERI |
| **Affected SoC Families** | Compute (primary — multi-tenant), Data Center, Client |
| **Preconditions** | Code execution on the same physical core or sharing microarchitectural resources with the victim; knowledge of victim's access patterns |
| **Key Mitigations** | Cache partitioning (way/set partitioning), branch predictor flushing on context switch, TLB tagging/flushing, speculative execution barriers (fence instructions), CHERI compartmentalization to reduce shared state |
| **Verification Approach** | Tier 3 — information flow analysis and microarchitectural simulation; cannot be fully verified with SVA |
| **Related Requirements** | REQ-CXL-011 (coherence protocol isolation), REQ-CHERI-007 (compartment isolation) |

---

## ARCH-006: Confused Deputy

| Field | Value |
|---|---|
| **STRIDE** | Elevation of Privilege (E) |
| **Description** | Attacker tricks a higher-privileged component (deputy) into performing an action on the attacker's behalf that the attacker is not authorized to perform directly. In SoC contexts, a confused deputy might be a firmware component that accepts parameters from untrusted sources and uses its own elevated privileges to execute operations using those parameters. |
| **Target Assets** | Security firmware interfaces, BMC management APIs, SPDM responder (if it can be tricked into reporting false measurements), mailbox command handlers |
| **Affected Domains** | Secure Boot / DICE, Supply Chain Security, Confidential AI / TEE |
| **Affected SoC Families** | All — particularly Compute and Data Center (BMC as deputy) |
| **Preconditions** | Ability to send crafted requests to the higher-privileged component; the component does not validate that the requested operation is authorized for the requester |
| **Key Mitigations** | Input validation on all privilege-boundary interfaces, capability-based access control (CHERI), least-privilege design (deputies hold only necessary authority), parameter sanitization, request origin authentication |
| **Verification Approach** | Tier 2 — protocol review of privilege-boundary interfaces; Tier 1 — SVA for input validation on command interfaces |
| **Related Requirements** | REQ-CHERI-003 (permission enforcement), REQ-SPDM-005 (measurement integrity) |

---

## ARCH-007: TOCTOU on Security State Transitions

| Field | Value |
|---|---|
| **STRIDE** | Tampering (T), Elevation of Privilege (E) |
| **Description** | Time-of-check-to-time-of-use (TOCTOU) race condition where security state is checked at one point but the actual operation occurs later, and the state changes between check and use. In SoC contexts: (1) TDISP state checked as RUN but transitions to CONFIG between check and access; (2) firewall configuration verified but modified before the protected access occurs; (3) measurement taken but firmware modified before the measurement is reported. |
| **Target Assets** | TDISP TDI state machine, bus firewall configuration, measurement registers, security mode registers |
| **Affected Domains** | TDISP / CXL, Secure Boot / DICE, Confidential AI / TEE |
| **Affected SoC Families** | All |
| **Preconditions** | Ability to trigger state changes concurrently with security checks; non-atomic check-and-use operations |
| **Key Mitigations** | Atomic check-and-use operations in hardware, lock state during critical operations, hardware-enforced state machine (no software override during transition), register locks that prevent modification after check |
| **Verification Approach** | Tier 1 — SVA for atomic state transitions, lock-before-use patterns; Tier 2 — protocol review for TOCTOU windows |
| **Related Requirements** | REQ-TDISP-003, REQ-TDISP-004, REQ-DICE-009 (layer transition atomicity) |

---

## ARCH-008: Attestation Evidence Manipulation

| Field | Value |
|---|---|
| **STRIDE** | Spoofing (S), Repudiation (R) |
| **Description** | Attacker manipulates attestation evidence (DICE certificates, SPDM measurement responses, TSP attestation) to present a false platform state to a verifier. If the attacker can modify measurement registers after boot, forge signatures, or replay previous attestation responses, the verifier receives incorrect information about the platform's security state. |
| **Target Assets** | Measurement registers (PCRs, DICE measurements), attestation signing keys, SPDM GET_MEASUREMENTS response, DICE alias certificates |
| **Affected Domains** | Secure Boot / DICE, Supply Chain Security, Confidential AI / TEE |
| **Affected SoC Families** | All — Compute and Data Center where remote attestation is critical |
| **Preconditions** | Write access to measurement registers (misconfigured lock), access to attestation signing key, ability to replay responses (missing nonce freshness) |
| **Key Mitigations** | Hardware-locked measurement registers (REQ-SPDM-005), attestation key protection in hardware, nonce-based freshness (REQ-SPDM-010), transcript hashing (REQ-SPDM-012), DICE CDI binding (attestation identity changes if firmware changes) |
| **Verification Approach** | Tier 1 — SVA for measurement register lock; Tier 2 — protocol check for nonce inclusion and transcript binding |
| **Related Requirements** | REQ-SPDM-004, REQ-SPDM-005, REQ-SPDM-010, REQ-SPDM-012, REQ-DICE-003 |

---

*[FROM TRAINING] Threat descriptions are based on publicly known attack classes from academic literature and industry reports. Verify against current threat landscape assessments. Last verified: 2026-02-13.*
