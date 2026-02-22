# PCIe TDISP 1.0 — Security Requirements Extract

## Specification Overview

| Field | Value |
|---|---|
| **Full Name** | TEE Device Interface Security Protocol (TDISP) |
| **Version** | 1.0 (2023) [FROM TRAINING] |
| **Organization** | PCI-SIG |
| **Scope** | Secure assignment of PCIe device interfaces to TEE trust domains |
| **Security Properties Addressed** | Isolation, Authenticity, Integrity, Confidentiality, Freshness |
| **Related Standards** | DMTF SPDM v1.4 (authentication), PCIe IDE (link encryption), CXL 3.1 (CXL device assignment) |

---

## Concept Summary

TDISP defines the protocol and state machine for securely assigning a PCIe device interface (called a TDI — Trust Domain Interface) to a specific trust domain (e.g., a confidential VM). Before a device can be used by a trust domain, the platform must authenticate the device (via SPDM), establish an IDE-encrypted link, and transition the TDI through a defined state machine that ensures the device is in a known-good security state. Once assigned, only the owning trust domain can access the TDI's MMIO and DMA resources.

**Key architectural principle:** Device assignment is a stateful protocol — security properties depend on the TDI being in the correct state. A TDI in CONFIG state is being set up; in RUN state it is actively assigned; in ERROR state it must not be accessible. The state machine is the enforcement mechanism.

---

## Key Security Requirements

### Device Authentication

**REQ-TDISP-001: SPDM-Based Device Authentication**
Before TDI assignment, the platform must authenticate the device using SPDM. The device must prove its identity via certificate chain and challenge-response. Authentication must complete successfully before the TDI state machine can advance beyond CONFIG state.

- **Security properties:** Authenticity
- **Verification tier:** Tier 1 — SVA assertion that TDI state cannot advance to RUN without authentication complete signal
- **Cross-references:** REQ-SPDM-001, REQ-SPDM-003 (SPDM authentication)

**REQ-TDISP-002: Device Measurement Verification**
The platform must verify device firmware measurements (via SPDM GET_MEASUREMENTS) before completing TDI assignment. Measurements must match expected values for the device type and firmware version. Assignment must fail if measurements do not match policy.

- **Security properties:** Integrity, Attestation
- **Verification tier:** Tier 2 — protocol check for measurement verification before state advance
- **Cross-references:** REQ-SPDM-004, REQ-SPDM-006 (measurement reporting)

### TDI State Machine

**REQ-TDISP-003: TDI State Machine Integrity**
The TDI must implement the defined state machine with states including (at minimum): CONFIG, RUN, ERROR, and LOCK. State transitions must follow the defined rules — no illegal transitions are permitted. The current state must be readable by the platform.

- **Security properties:** Integrity, Isolation
- **Verification tier:** Tier 1 — SVA assertions for legal state transitions only; no undefined transitions
- **Cross-references:** Verification patterns `sva-templates/fsm-transitions.sv`

**REQ-TDISP-004: LOCK State Enforcement**
When a TDI is in LOCK state, the device's security configuration must be frozen — no changes to security-relevant registers, MMIO mappings, or DMA configuration. The LOCK state prevents the device from being reconfigured between authentication and actual use by the trust domain.

- **Security properties:** Integrity, Isolation
- **Verification tier:** Tier 1 — SVA assertions that security registers are read-only in LOCK state
- **Cross-references:** Verification patterns `sva-templates/register-locks.sv`

**REQ-TDISP-005: RUN State Access Control**
When a TDI is in RUN state, only the owning trust domain may access the TDI's MMIO and DMA resources. The platform must enforce this access control at the hardware level (e.g., via IOMMU/ATS configuration). Any access from a non-owning entity must be blocked and optionally reported.

- **Security properties:** Isolation, Access Control
- **Verification tier:** Tier 1 — SVA assertions for access control enforcement based on TDI state and owner
- **Cross-references:** REQ-TDISP-003 (state machine), PCIe ACS

**REQ-TDISP-006: ERROR State Handling**
If a security violation is detected (authentication failure, measurement mismatch, protocol error, IDE key failure), the TDI must transition to ERROR state. In ERROR state, the TDI must not be accessible by any trust domain. Recovery from ERROR state must require re-authentication.

- **Security properties:** Availability (safe degradation), Isolation
- **Verification tier:** Tier 1 — SVA assertions for error-state transition on security violations; access blocked in ERROR
- **Cross-references:** REQ-DICE-010 (error handling in derivation)

### IDE Stream Binding

**REQ-TDISP-007: IDE Stream Setup Before Assignment**
An IDE (Integrity and Data Encryption) stream must be established for the link between the host and the TDI's device before the TDI can transition to RUN state. This ensures that all data between the trust domain and the device is encrypted and integrity-protected.

- **Security properties:** Confidentiality, Integrity
- **Verification tier:** Tier 1 — SVA assertion that RUN state requires IDE stream active signal
- **Cross-references:** PCIe IDE ECN, REQ-TDISP-003 (state transitions)

**REQ-TDISP-008: SPDM Session Binding to IDE**
The IDE stream keys must be derived from or bound to the SPDM session established during device authentication. This binding ensures that the encryption keys are tied to the authenticated device identity. Replacing the device or performing a man-in-the-middle attack breaks the binding.

- **Security properties:** Authenticity, Confidentiality, Integrity
- **Verification tier:** Tier 2 — protocol check for key binding between SPDM session and IDE stream
- **Cross-references:** REQ-SPDM-007 (key exchange), PCIe IDE

**REQ-TDISP-009: IDE Key Rotation**
IDE stream keys must support rotation without disrupting active data transfers. Key rotation must be initiated by the platform and acknowledged by the device. During rotation, both old and new keys may be temporarily active to avoid dropping in-flight TLPs.

- **Security properties:** Freshness, Confidentiality
- **Verification tier:** Tier 2 — protocol check for key rotation handshake and transition window
- **Cross-references:** PCIe IDE (key rotation mechanism)

### Security Configuration

**REQ-TDISP-010: TDI Interface Report**
The device must report the security capabilities and configuration of each TDI via a structured interface report. This report must include: supported SPDM versions, supported algorithms, IDE capabilities, number of TDIs, and security state. The platform uses this report to determine if the device meets assignment requirements.

- **Security properties:** Authenticity, Integrity
- **Verification tier:** Tier 2 — protocol check for interface report completeness and consistency
- **Cross-references:** REQ-SPDM-011 (algorithm negotiation)

**REQ-TDISP-011: DMA Isolation**
When a TDI is assigned to a trust domain, the device's DMA must be restricted to the memory regions owned by that trust domain. The platform must configure IOMMU/ATS to enforce this restriction. The device must not be able to DMA to memory outside its assigned trust domain.

- **Security properties:** Isolation, Access Control
- **Verification tier:** Tier 1 — SVA assertions for IOMMU configuration enforcement
- **Cross-references:** PCIe ACS, REQ-TDISP-005 (RUN state access control)

---

## TDI State Machine Summary

```
             ┌──────────────┐
             │   CONFIG     │ ← Initial state
             │  (setup)     │
             └──────┬───────┘
                    │ auth + measurement OK
             ┌──────▼───────┐
             │    LOCK      │ ← Config frozen
             │  (verified)  │
             └──────┬───────┘
                    │ IDE stream established
             ┌──────▼───────┐
             │     RUN      │ ← Active assignment
             │  (assigned)  │
             └──────┬───────┘
                    │ tear-down or violation
             ┌──────▼───────┐
             │   CONFIG     │ ← Re-enter setup
             └──────────────┘

    Any state ──(security violation)──► ERROR
                                         │
                                         │ recovery (re-auth)
                                         ▼
                                       CONFIG
```

---

## Verification Considerations

| Requirement | Tier | Verification Approach |
|---|---|---|
| REQ-TDISP-001 | Tier 1 | SVA: state cannot advance past CONFIG without auth_complete |
| REQ-TDISP-002 | Tier 2 | Protocol: measurement verification before LOCK transition |
| REQ-TDISP-003 | Tier 1 | SVA: only legal state transitions; no undefined paths |
| REQ-TDISP-004 | Tier 1 | SVA: security registers read-only in LOCK state |
| REQ-TDISP-005 | Tier 1 | SVA: access blocked for non-owning entities in RUN state |
| REQ-TDISP-006 | Tier 1 | SVA: error state on violations; access blocked in ERROR |
| REQ-TDISP-007 | Tier 1 | SVA: RUN state requires IDE_active signal |
| REQ-TDISP-008 | Tier 2 | Protocol: IDE key derivation tied to SPDM session |
| REQ-TDISP-009 | Tier 2 | Protocol: key rotation handshake without data loss |
| REQ-TDISP-010 | Tier 2 | Protocol: interface report complete and consistent |
| REQ-TDISP-011 | Tier 1 | SVA: IOMMU/ATS restricts DMA to assigned trust domain |

---

*[FROM TRAINING] Requirements are derived summaries, not verbatim specification text. Verify requirement details against PCI-SIG TDISP 1.0 and related PCIe specifications. Last verified: 2026-02-13.*
