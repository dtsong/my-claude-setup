# TCG DICE v1.2 — Security Requirements Extract

## Specification Overview

| Field | Value |
|---|---|
| **Full Name** | TCG Device Identifier Composition Engine (DICE) |
| **Version** | 1.2 (2024) [FROM TRAINING] |
| **Organization** | Trusted Computing Group (TCG) |
| **Scope** | Layered device identity, measurement, and attestation for hardware platforms |
| **Security Properties Addressed** | Integrity, Authenticity, Attestation, Freshness, Non-Repudiation |
| **Related Standards** | SPDM v1.4 (attestation transport), TDISP 1.0 (device identity), X.509 v3 (certificate format) |

---

## Concept Summary

DICE defines a hardware-rooted mechanism for deriving per-layer device identity from measurements of firmware and configuration. Starting from a Unique Device Secret (UDS) embedded in hardware, each firmware layer derives a Compound Device Identifier (CDI) that combines the secret from the layer below with a measurement (hash) of the current layer's code and configuration. This CDI is used to generate an asymmetric key pair and certificate for the layer, creating a chain of identity certificates that reflects the exact firmware composition of the device.

**Key architectural principle:** Identity is compositional — if any firmware layer changes, the CDI and all derived identities change, making the change cryptographically detectable by any verifier holding the expected certificate chain.

---

## Key Security Requirements

### Hardware Root

**REQ-DICE-001: Unique Device Secret (UDS) Protection**
The UDS must be stored in hardware (fuses, PUF, or equivalent) and must be accessible only to the DICE engine during the first boot stage. After the first CDI derivation, the UDS must be hardware-locked (inaccessible to any software, including the firmware that was just measured). The UDS must have sufficient entropy (minimum 256 bits) and must be unique per device.

- **Security properties:** Integrity, Confidentiality (of root secret), Authenticity
- **Verification tier:** Tier 1 — SVA assertions for UDS register lock after first access
- **Cross-references:** REQ-SPDM-001 (device identity root), FIPS 140-3 (key storage)

**REQ-DICE-002: Immutable First-Stage Code**
The code that performs the initial CDI derivation (DICE engine or equivalent) must be immutable — stored in ROM or one-time-programmable memory. It must not be modifiable by any software after manufacturing. Any attempt to modify this code must be detectable.

- **Security properties:** Integrity, Authenticity
- **Verification tier:** Tier 1 — SVA assertions that ROM address range is read-only
- **Cross-references:** NIST SP 800-193 (platform firmware resiliency)

### CDI Derivation

**REQ-DICE-003: CDI Derivation Correctness**
The CDI for each layer must be derived as a cryptographic function of: (a) the secret from the previous layer (UDS for the first layer), and (b) the measurement (hash) of the current layer's firmware code and security-relevant configuration. The derivation function must be a NIST-approved KDF or HMAC construction.

- **Security properties:** Integrity, Authenticity, Freshness
- **Verification tier:** Tier 2 — protocol-level check that CDI derivation follows specified algorithm
- **Cross-references:** FIPS 140-3 (approved algorithms), NIST SP 800-108 (KDF)

**REQ-DICE-004: CDI Secrecy**
Each layer's CDI must be accessible only to that layer. Once a layer derives the CDI for the next layer and transfers control, the previous layer's CDI must be erased or hardware-locked. No layer may access the CDI of a layer below it.

- **Security properties:** Confidentiality, Isolation
- **Verification tier:** Tier 1 — SVA assertions for CDI register lock/erase after layer transition
- **Cross-references:** REQ-DICE-001 (UDS locking is a special case of CDI secrecy)

**REQ-DICE-005: Measurement Completeness**
The measurement input to CDI derivation must include all security-relevant code and configuration for the layer being measured. Omitting security-relevant inputs (e.g., measuring code but not configuration) weakens the binding between identity and actual platform state.

- **Security properties:** Integrity, Attestation
- **Verification tier:** Tier 2 — review that measurement scope covers all security-relevant inputs
- **Cross-references:** REQ-SPDM-008 (measurement completeness for attestation)

### Identity and Certificates

**REQ-DICE-006: DeviceID Certificate Generation**
The first DICE layer must generate a DeviceID key pair and self-signed certificate (or certificate signed by the manufacturer CA). The DeviceID represents the long-term identity of the device and is stable across boot cycles (assuming no firmware change at the first layer).

- **Security properties:** Authenticity, Non-Repudiation
- **Verification tier:** Tier 2 — protocol check for certificate well-formedness and key binding
- **Cross-references:** X.509 v3 (certificate format), REQ-SPDM-002 (certificate chain)

**REQ-DICE-007: Alias Certificate Chain**
Each subsequent DICE layer must generate an Alias key pair and certificate signed by the layer below. The Alias certificate chain, rooted at the DeviceID, constitutes the attestation evidence for the platform's firmware composition. The chain must be well-formed X.509 and must include the measurement of each layer as a certificate extension.

- **Security properties:** Authenticity, Attestation, Non-Repudiation
- **Verification tier:** Tier 2 — protocol check for chain well-formedness, signature validity
- **Cross-references:** REQ-SPDM-003 (certificate delivery), TCG Platform Certificate Profile

**REQ-DICE-008: Key Pair Freshness**
Alias key pairs must be regenerated on every boot cycle. The key derivation must include the CDI (which incorporates the firmware measurement), ensuring that any firmware change produces different keys. DeviceID keys may be stable across boots if the first-layer firmware is unchanged.

- **Security properties:** Freshness, Integrity
- **Verification tier:** Tier 2 — protocol check that key derivation includes boot-cycle-specific input
- **Cross-references:** REQ-SPDM-010 (session freshness)

### Security State Transitions

**REQ-DICE-009: Layer Transition Atomicity**
The transition from one DICE layer to the next must be atomic with respect to secret access: the current layer's secrets must be locked before the next layer's code begins executing. There must be no window where both layers' secrets are simultaneously accessible.

- **Security properties:** Isolation, Integrity
- **Verification tier:** Tier 1 — SVA assertions for lock-before-execute sequencing
- **Cross-references:** REQ-DICE-004 (CDI secrecy)

**REQ-DICE-010: Error Handling in Derivation**
If CDI derivation fails (hash engine error, KDF failure, certificate generation failure), the DICE layer must not proceed to execute the next layer. The device must enter a safe error state that does not expose the UDS or any CDI material.

- **Security properties:** Availability (safe degradation), Confidentiality
- **Verification tier:** Tier 1 — SVA assertions for error-state transitions, secret zeroization on error
- **Cross-references:** FIPS 140-3 (error handling, key zeroization)

### Anti-Rollback

**REQ-DICE-011: Firmware Version Binding**
The measurement used in CDI derivation should include a firmware version indicator (e.g., Security Version Number — SVN). When combined with anti-rollback counters in OTP, this ensures that a rollback to a vulnerable firmware version produces a CDI that cannot access keys sealed to the current version.

- **Security properties:** Freshness, Integrity
- **Verification tier:** Tier 1 — SVA assertions for monotonic counter enforcement (increment-only, no decrement)
- **Cross-references:** REQ-SPDM-009 (measurement versioning)

---

## Verification Considerations

| Requirement | Tier | Verification Approach |
|---|---|---|
| REQ-DICE-001 | Tier 1 | SVA: UDS register inaccessible after first CDI derivation complete |
| REQ-DICE-002 | Tier 1 | SVA: ROM address range write-protection asserted at all times |
| REQ-DICE-003 | Tier 2 | Protocol: CDI output matches expected value for given inputs |
| REQ-DICE-004 | Tier 1 | SVA: CDI registers locked/erased before next layer executes |
| REQ-DICE-005 | Tier 2 | Review: measurement scope documentation covers all security inputs |
| REQ-DICE-006 | Tier 2 | Protocol: DeviceID certificate valid X.509, correct key usage |
| REQ-DICE-007 | Tier 2 | Protocol: Alias chain validates to DeviceID root, measurements in extensions |
| REQ-DICE-008 | Tier 2 | Protocol: Alias keys differ across boot cycles with same firmware |
| REQ-DICE-009 | Tier 1 | SVA: Lock signal asserts before execute signal for next layer |
| REQ-DICE-010 | Tier 1 | SVA: Error state entered on derivation failure; secrets zeroized |
| REQ-DICE-011 | Tier 1 | SVA: Anti-rollback counter is monotonic (never decrements) |

---

*[FROM TRAINING] Requirements are derived summaries, not verbatim specification text. Verify requirement details against TCG DICE Attestation Architecture v1.2 and related TCG specifications. Last verified: 2026-02-13.*
