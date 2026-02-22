# CXL 3.1 Security — Requirements Extract

## Specification Overview

| Field | Value |
|---|---|
| **Full Name** | Compute Express Link (CXL) Specification — Security Chapter |
| **Version** | 3.1 (2024) [FROM TRAINING] |
| **Organization** | CXL Consortium |
| **Scope** | Link security (IDE for CXL), Type-3 Security Protocol (TSP), multi-host memory isolation |
| **Security Properties Addressed** | Confidentiality, Integrity, Isolation, Attestation, Freshness |
| **Related Standards** | PCIe IDE (underlying encryption), DMTF SPDM v1.4 (authentication), TDISP 1.0 (device assignment) |

---

## Concept Summary

CXL 3.1 extends PCIe security mechanisms to cover three protocol types: CXL.io (PCIe-like I/O), CXL.cache (device-to-host coherence), and CXL.mem (host-to-device memory). Security features include IDE (Integrity and Data Encryption) for all three protocol types, TSP (Type-3 Security Protocol) for managing security on shared memory devices, and multi-host isolation mechanisms for CXL switches and pooled memory.

**Key architectural principle:** CXL security must protect data across chip-to-chip links that may traverse physical interposers, while also isolating multiple hosts sharing the same memory device. The combination of link encryption (IDE) and logical partitioning (TSP) provides defense in depth.

---

## Key Security Requirements

### IDE for CXL

**REQ-CXL-001: CXL.io IDE**
CXL.io transactions must support IDE encryption and integrity protection equivalent to PCIe IDE. AES-GCM must be used for AEAD. IDE streams must be established before security-sensitive data traverses the link.

- **Security properties:** Confidentiality, Integrity
- **Verification tier:** Tier 1 — SVA assertion that CXL.io data is encrypted when IDE stream is active
- **Cross-references:** PCIe IDE ECN, REQ-TDISP-007 (IDE before assignment)

**REQ-CXL-002: CXL.cache IDE**
CXL.cache coherence transactions (snoop, data, response) must support IDE encryption. Cache coherence traffic can leak information about memory access patterns; encryption mitigates interposer-based snooping attacks.

- **Security properties:** Confidentiality, Integrity
- **Verification tier:** Tier 2 — protocol check that cache coherence transactions are encrypted
- **Cross-references:** C2C CHI (coherence interface)

**REQ-CXL-003: CXL.mem IDE**
CXL.mem transactions (memory read, write, writeback) must support IDE encryption. This is critical for Type-3 (memory expander) devices where DRAM contents traverse the CXL link.

- **Security properties:** Confidentiality, Integrity
- **Verification tier:** Tier 2 — protocol check that memory transactions are encrypted on CXL.mem
- **Cross-references:** REQ-CXL-007 (TSP memory isolation)

**REQ-CXL-004: IDE Key Management**
IDE keys for CXL streams must be established via SPDM key exchange. Key rotation must be supported without disrupting active memory or coherence transactions. Key epoch transitions must be coordinated across CXL.io, CXL.cache, and CXL.mem sub-protocols.

- **Security properties:** Freshness, Confidentiality
- **Verification tier:** Tier 2 — protocol check for key rotation coordination across sub-protocols
- **Cross-references:** REQ-SPDM-007 (key exchange), REQ-TDISP-009 (IDE key rotation)

### Type-3 Security Protocol (TSP)

**REQ-CXL-005: TSP Configuration**
Type-3 memory devices must implement TSP to manage security configuration. TSP allows the host to query device security capabilities, configure memory partitions, and manage per-partition security policies. TSP configuration must be authenticated (only authorized hosts can configure security).

- **Security properties:** Access Control, Integrity
- **Verification tier:** Tier 2 — protocol check for authenticated TSP configuration
- **Cross-references:** REQ-SPDM-001 (device authentication)

**REQ-CXL-006: TSP Attestation**
Type-3 devices must support attestation via TSP, allowing a host to verify the device's firmware state and security configuration. Attestation responses must be signed and must include measurement data. TSP attestation may leverage SPDM measurement infrastructure.

- **Security properties:** Attestation, Integrity
- **Verification tier:** Tier 2 — protocol check for signed attestation responses
- **Cross-references:** REQ-SPDM-004 (measurement reporting)

### Multi-Host Isolation

**REQ-CXL-007: Memory Partition Isolation**
In multi-host configurations, a Type-3 memory device must enforce memory partition isolation. Each host must be able to access only its assigned memory range. Cross-host access must be blocked by the device hardware. Partition configuration must be locked before hosts can access memory.

- **Security properties:** Isolation, Access Control
- **Verification tier:** Tier 1 — SVA assertions for partition boundary enforcement
- **Cross-references:** REQ-TDISP-005 (TDI access control)

**REQ-CXL-008: Per-Host Encryption Keys**
In multi-host configurations, IDE keys must be per-host. Traffic from Host A must be encrypted with keys not accessible to Host B. The device must maintain separate key contexts for each host's IDE streams.

- **Security properties:** Confidentiality, Isolation
- **Verification tier:** Tier 1 — SVA assertion that key contexts are separate per host
- **Cross-references:** REQ-CXL-004 (IDE key management)

**REQ-CXL-009: Switch Port Isolation**
CXL switches must enforce port isolation. Traffic from one downstream port must not be observable on another downstream port unless explicitly routed. Switch configuration must prevent cross-port snooping.

- **Security properties:** Isolation, Confidentiality
- **Verification tier:** Tier 1 — SVA assertions for port isolation in switch fabric
- **Cross-references:** PCIe ACS (Access Control Services)

### Cache Coherence Security

**REQ-CXL-010: Snoop Filter Integrity**
The snoop filter (directory) in CXL cache-coherent configurations must be protected against manipulation. A compromised snoop filter could redirect cache lines to unauthorized hosts or leak information about access patterns.

- **Security properties:** Integrity, Isolation
- **Verification tier:** Tier 2 — protocol check for snoop filter access control
- **Cross-references:** C2C CHI security considerations

**REQ-CXL-011: Coherence Protocol Isolation**
Cache coherence transactions (snoops, data transfers, invalidations) must be scoped to the originating host's coherence domain. Cross-domain coherence must be explicitly authorized and mediated by the device or switch.

- **Security properties:** Isolation, Integrity
- **Verification tier:** Tier 2 — protocol check for coherence domain scoping
- **Cross-references:** REQ-CXL-007 (memory partition isolation)

---

## Verification Considerations

| Requirement | Tier | Verification Approach |
|---|---|---|
| REQ-CXL-001 | Tier 1 | SVA: CXL.io data encrypted when IDE active |
| REQ-CXL-002 | Tier 2 | Protocol: cache coherence transactions encrypted |
| REQ-CXL-003 | Tier 2 | Protocol: memory transactions encrypted on CXL.mem |
| REQ-CXL-004 | Tier 2 | Protocol: key rotation coordinated across sub-protocols |
| REQ-CXL-005 | Tier 2 | Protocol: TSP configuration authenticated |
| REQ-CXL-006 | Tier 2 | Protocol: attestation responses signed with measurements |
| REQ-CXL-007 | Tier 1 | SVA: partition boundaries enforced in hardware |
| REQ-CXL-008 | Tier 1 | SVA: per-host key contexts are separate |
| REQ-CXL-009 | Tier 1 | SVA: port isolation in switch fabric |
| REQ-CXL-010 | Tier 2 | Protocol: snoop filter access control |
| REQ-CXL-011 | Tier 2 | Protocol: coherence domain scoping |

---

*[FROM TRAINING] Requirements are derived summaries, not verbatim specification text. Verify requirement details against CXL 3.1 specification and related CXL Consortium publications. Last verified: 2026-02-13.*
