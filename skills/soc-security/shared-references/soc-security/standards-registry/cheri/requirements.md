# CHERI ISA — Security Properties Extract

## Specification Overview

| Field | Value |
|---|---|
| **Full Name** | Capability Hardware Enhanced RISC Instructions (CHERI) |
| **Version** | v9 (2023) [FROM TRAINING] |
| **Organization** | University of Cambridge / SRI International |
| **Scope** | Capability-based addressing, hardware memory safety, compartmentalization |
| **Security Properties Addressed** | Access Control, Isolation, Integrity, Side-Channel Resistance (partial) |
| **Related Standards** | RISC-V Privileged Specification (PMP integration), CHERI C/C++ specification (software model) |

---

## Concept Summary

CHERI extends a base ISA (RISC-V or ARM) with capability-based addressing. Every pointer becomes a hardware capability — a fat pointer that includes bounds (base, length), permissions (read, write, execute, seal), an object type, and a tag bit. The hardware enforces that no operation can exceed the authority encoded in the capability: bounds are checked on every memory access, permissions are checked on every operation, and the tag bit prevents forgery. Compartmentalization is achieved through sealed capabilities (domain transitions) and sentries (controlled entry points).

**Key architectural principle:** Capabilities are unforgeable — the tag bit, maintained by hardware on every store, ensures that software cannot manufacture a capability from an integer. Authority can only be derived by restricting (narrowing) an existing capability, never by amplifying one.

---

## Key Security Properties

### Capability Model

**REQ-CHERI-001: Capability Encoding Integrity**
Every capability must include: base address, bounds (length or top), permissions, object type, and a tag bit. The tag bit must be maintained by hardware — any non-capability store to a capability-width register or memory location must clear the tag, rendering the value a non-capability integer.

- **Security properties:** Integrity, Access Control
- **Verification tier:** Tier 1 — SVA assertions for tag clearing on non-capability stores
- **Cross-references:** RISC-V base ISA (register file extension)

**REQ-CHERI-002: Bounds Checking**
Every memory access through a capability must be checked against the capability's bounds. An access outside the bounds must raise a hardware exception (capability bounds fault). The bounds check must occur before the memory access is issued to the memory subsystem.

- **Security properties:** Access Control, Isolation
- **Verification tier:** Tier 1 — SVA assertions for bounds check before memory access commit
- **Cross-references:** REQ-CHERI-001 (encoding integrity)

**REQ-CHERI-003: Permission Enforcement**
Every operation must be checked against the capability's permission bits. A read through a capability without read permission must fault. A write through a capability without write permission must fault. An instruction fetch through a capability without execute permission must fault. Permission checks must be enforced by hardware before the operation commits.

- **Security properties:** Access Control
- **Verification tier:** Tier 1 — SVA assertions for permission check before operation commit
- **Cross-references:** REQ-CHERI-002 (bounds checking)

**REQ-CHERI-004: Monotonicity (No Amplification)**
Capability operations must be monotonic — a derived capability can only have the same or fewer permissions and the same or narrower bounds than the source capability. No instruction sequence may produce a capability with more authority than any capability in the derivation chain.

- **Security properties:** Access Control, Integrity
- **Verification tier:** Tier 1 — SVA assertions for monotonicity on all capability-modifying instructions
- **Cross-references:** REQ-CHERI-001 (tag bit prevents forgery from integers)

### Compartmentalization

**REQ-CHERI-005: Sealed Capabilities**
Capabilities must support sealing — a sealed capability cannot be dereferenced or modified until it is unsealed by a matching unseal capability (with the correct object type). Sealing enables secure cross-compartment object references: a compartment can hold a sealed capability to another compartment's data without being able to access that data.

- **Security properties:** Isolation, Access Control
- **Verification tier:** Tier 1 — SVA assertions that sealed capabilities cannot be dereferenced
- **Cross-references:** REQ-CHERI-006 (sentries)

**REQ-CHERI-006: Sentry Capabilities**
Sentries are sealed capabilities that represent controlled entry points into compartments. When a sentry is invoked (called), the hardware performs a domain transition: the sentry is unsealed, execution jumps to the sentry's address, and the calling compartment's authority is restricted to what the sentry grants. This enables controlled inter-compartment communication.

- **Security properties:** Isolation, Access Control
- **Verification tier:** Tier 1 — SVA assertions for domain transition behavior on sentry invocation
- **Cross-references:** REQ-CHERI-005 (sealed capabilities)

**REQ-CHERI-007: Compartment Isolation**
Compartments must be isolated by default — a compartment's capabilities are not accessible to other compartments unless explicitly shared (e.g., passed as a function argument through a sentry). The hardware must not provide any mechanism for a compartment to discover or forge capabilities belonging to another compartment.

- **Security properties:** Isolation
- **Verification tier:** Tier 2 — architectural review that no ISA instruction violates compartment isolation
- **Cross-references:** REQ-CHERI-004 (monotonicity), REQ-CHERI-005 (sealing)

### Memory Safety Invariants

**REQ-CHERI-008: Spatial Safety**
CHERI must enforce spatial memory safety — every memory access is bounded by the capability's base and length. Buffer overflows, out-of-bounds reads, and wild pointer dereferences must be caught by the hardware bounds check.

- **Security properties:** Integrity, Access Control
- **Verification tier:** Tier 1 — SVA assertions for bounds fault on out-of-bounds access
- **Cross-references:** REQ-CHERI-002 (bounds checking)

**REQ-CHERI-009: Referential Safety (Tag Bit)**
CHERI must enforce referential safety — software cannot forge a capability from an arbitrary integer. The tag bit distinguishes valid capabilities from data. Only capability-producing instructions (derivation, load from tagged memory) can produce tagged values. Any attempt to set a tag through data manipulation must fail.

- **Security properties:** Integrity, Access Control
- **Verification tier:** Tier 1 — SVA assertions that only defined instructions can produce tagged values
- **Cross-references:** REQ-CHERI-001 (tag clearing), REQ-CHERI-004 (monotonicity)

### Revocation

**REQ-CHERI-010: Capability Revocation Support**
CHERI should support mechanisms for revoking previously granted capabilities (temporal safety). This may include hardware-assisted revocation (sweeping memory to clear capabilities pointing to freed objects) or software-managed revocation with hardware support for tag scanning. The specific mechanism varies by implementation.

- **Security properties:** Access Control, Integrity
- **Verification tier:** Tier 2 — architectural review of revocation mechanism completeness
- **Cross-references:** CheriBSD revocation, Cornucopia (research)

### Integration with Privilege Levels

**REQ-CHERI-011: PMP/Capability Interaction**
On RISC-V CHERI implementations, CHERI capability checks and PMP (Physical Memory Protection) checks must both be enforced. The most restrictive of the two must prevail — a PMP violation must fault even if the capability permits the access, and a capability bounds violation must fault even if PMP permits the access.

- **Security properties:** Access Control, Isolation
- **Verification tier:** Tier 1 — SVA assertions for dual enforcement (CHERI AND PMP)
- **Cross-references:** RISC-V Privileged Specification (PMP)

---

## Verification Considerations

| Requirement | Tier | Verification Approach |
|---|---|---|
| REQ-CHERI-001 | Tier 1 | SVA: tag cleared on non-capability store |
| REQ-CHERI-002 | Tier 1 | SVA: bounds check before memory access commit |
| REQ-CHERI-003 | Tier 1 | SVA: permission check before operation commit |
| REQ-CHERI-004 | Tier 1 | SVA: derived capability authority <= source authority |
| REQ-CHERI-005 | Tier 1 | SVA: sealed capability dereference faults |
| REQ-CHERI-006 | Tier 1 | SVA: domain transition on sentry invocation |
| REQ-CHERI-007 | Tier 2 | Architectural review: no capability leakage across compartments |
| REQ-CHERI-008 | Tier 1 | SVA: bounds fault on out-of-bounds access |
| REQ-CHERI-009 | Tier 1 | SVA: only defined instructions produce tagged values |
| REQ-CHERI-010 | Tier 2 | Architectural review: revocation completeness |
| REQ-CHERI-011 | Tier 1 | SVA: both CHERI and PMP enforced; most restrictive wins |

---

## Notes on CHERI vs. Protocol-Based Standards

Unlike DICE, SPDM, TDISP, and CXL, CHERI is an ISA extension rather than a protocol. Its "requirements" are architectural invariants that must hold for every instruction execution, not protocol messages that must be exchanged correctly. This means:

- **Verification is predominantly Tier 1** — most CHERI properties can be expressed as SVA assertions on the processor pipeline
- **No protocol-level interactions** — CHERI does not have a request-response protocol like SPDM
- **Integration testing** focuses on interaction with privilege levels (PMP, hypervisor extensions) and memory subsystem (caches, TLBs)

---

*[FROM TRAINING] Properties are derived from publicly available CHERI ISA technical reports and Morello architecture documentation. Verify against the CHERI ISA specification v9 and CHERI C/C++ specification. Last verified: 2026-02-13.*
