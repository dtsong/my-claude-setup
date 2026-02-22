# DMTF SPDM v1.4 — Security Requirements Extract

## Specification Overview

| Field | Value |
|---|---|
| **Full Name** | Security Protocol and Data Model (SPDM) |
| **Version** | 1.4 (2024) [FROM TRAINING] |
| **Organization** | DMTF (Distributed Management Task Force) |
| **Scope** | Device authentication, firmware measurement reporting, key exchange, and secure session establishment |
| **Security Properties Addressed** | Authenticity, Integrity, Attestation, Freshness, Confidentiality (session) |
| **Related Standards** | TCG DICE v1.2 (identity source), TDISP 1.0 (device assignment), CXL 3.1 TSP (attestation), MCTP (transport) |

---

## Concept Summary

SPDM is a request-response protocol enabling a Requester (typically a host or platform manager) to authenticate a Responder (a device such as a GPU, NIC, or storage controller), retrieve firmware measurements, exchange keys, and establish encrypted sessions. SPDM is transport-agnostic — it operates over MCTP, PCIe DOE, or other transports. It serves as the authentication and attestation backbone for TDISP device assignment and CXL TSP interactions.

**Key architectural principle:** SPDM separates authentication (who are you?) from measurement (what firmware are you running?) and session establishment (let's communicate securely). Each capability can be used independently, but the full security value comes from combining all three.

---

## Key Security Requirements

### Authentication

**REQ-SPDM-001: Device Identity Root**
A Responder must possess a device identity key pair rooted in hardware (DICE DeviceID, manufacturer-provisioned key, or equivalent). The private key must be protected against extraction. The public key must be bound to a certificate chain that a Requester can validate.

- **Security properties:** Authenticity, Integrity
- **Verification tier:** Tier 2 — protocol check for certificate chain validation
- **Cross-references:** REQ-DICE-006 (DeviceID generation), FIPS 140-3 (key protection)

**REQ-SPDM-002: Certificate Chain Delivery**
A Responder must be able to deliver its certificate chain to a Requester via the GET_CERTIFICATE request. The chain must include all intermediate certificates needed for validation up to a trust anchor known to the Requester. The chain must be well-formed X.509 v3.

- **Security properties:** Authenticity
- **Verification tier:** Tier 2 — protocol check for GET_CERTIFICATE response completeness
- **Cross-references:** REQ-DICE-007 (alias certificate chain), X.509 v3

**REQ-SPDM-003: Challenge-Response Authentication**
A Requester must be able to challenge a Responder to prove possession of its identity private key via the CHALLENGE request. The Responder signs a hash of the challenge nonce and transcript with its identity key. The signature must be verified by the Requester before proceeding.

- **Security properties:** Authenticity, Freshness
- **Verification tier:** Tier 2 — protocol check for nonce inclusion, signature verification
- **Cross-references:** REQ-SPDM-010 (nonce freshness)

### Measurement

**REQ-SPDM-004: Measurement Reporting**
A Responder must be able to report its firmware measurements via GET_MEASUREMENTS. Measurements must reflect the actual firmware and configuration state of the device. The measurement response must be signed by the Responder's identity key or a measurement-specific signing key.

- **Security properties:** Attestation, Integrity
- **Verification tier:** Tier 2 — protocol check for measurement response completeness and signature validity
- **Cross-references:** REQ-DICE-005 (measurement completeness)

**REQ-SPDM-005: Measurement Integrity**
Measurement values must be computed using approved hash algorithms. Measurements must be computed at boot time (before the measured firmware executes) and must not be modifiable by the firmware after boot. Runtime re-measurement is permitted only through a defined re-measurement protocol.

- **Security properties:** Integrity, Freshness
- **Verification tier:** Tier 1 — SVA assertions for measurement register lock after boot
- **Cross-references:** REQ-DICE-003 (CDI derivation incorporates measurements)

**REQ-SPDM-006: Measurement Index Completeness**
All measurement indices advertised by the Responder in GET_MEASUREMENTS must return valid measurement data. No measurement index may be silently omitted. The Requester should verify that all expected indices are present and accounted for.

- **Security properties:** Attestation, Integrity
- **Verification tier:** Tier 2 — protocol check for index completeness
- **Cross-references:** REQ-DICE-005 (measurement completeness)

### Key Exchange and Session

**REQ-SPDM-007: Key Exchange Protocol**
SPDM key exchange must use Diffie-Hellman (DHE) or equivalent to establish a shared session key. Both Requester and Responder must contribute entropy. The key exchange must be authenticated (both parties verify identity before trusting the session key).

- **Security properties:** Confidentiality, Authenticity, Freshness
- **Verification tier:** Tier 2 — protocol check for mutual authentication during key exchange
- **Cross-references:** FIPS 140-3 (approved key exchange algorithms)

**REQ-SPDM-008: Secure Session Encryption**
Once a session is established, all SPDM messages within the session must be encrypted and integrity-protected using the derived session keys. The encryption must use AEAD (Authenticated Encryption with Associated Data) — AES-GCM or equivalent.

- **Security properties:** Confidentiality, Integrity
- **Verification tier:** Tier 2 — protocol check for session encryption activation
- **Cross-references:** FIPS 140-3 (approved AEAD algorithms)

**REQ-SPDM-009: Session Sequence Numbers**
Each message within an SPDM session must carry a monotonically increasing sequence number. The Responder and Requester must reject messages with out-of-order or replayed sequence numbers. Sequence number overflow must terminate the session.

- **Security properties:** Freshness, Integrity
- **Verification tier:** Tier 1 — SVA assertions for sequence number monotonicity
- **Cross-references:** REQ-TDISP-006 (session binding)

### Protocol Integrity

**REQ-SPDM-010: Nonce Freshness**
All challenge-response and key exchange operations must include nonces contributed by both parties. Nonces must be generated from a cryptographically secure random number generator. Nonce reuse within a session must be prevented.

- **Security properties:** Freshness
- **Verification tier:** Tier 2 — protocol check for nonce uniqueness and entropy source
- **Cross-references:** FIPS 140-3 (RNG requirements), NIST SP 800-90B

**REQ-SPDM-011: Algorithm Negotiation**
The Requester and Responder must negotiate cryptographic algorithms (hash, signature, DHE group, AEAD) at the start of the SPDM exchange via GET_ALGORITHMS. The negotiated algorithms must be from the set of mutually supported algorithms. Neither party may downgrade to an algorithm not advertised by the other.

- **Security properties:** Integrity (protocol), Authenticity
- **Verification tier:** Tier 2 — protocol check for algorithm negotiation correctness
- **Cross-references:** FIPS 140-3 (approved algorithms)

**REQ-SPDM-012: Transcript Hashing**
SPDM maintains a running hash (transcript) of all messages exchanged. Signatures and key derivations incorporate the transcript hash to bind them to the specific message sequence. Any message tampering or reordering invalidates subsequent transcript-dependent operations.

- **Security properties:** Integrity, Non-Repudiation
- **Verification tier:** Tier 2 — protocol check for transcript inclusion in signatures
- **Cross-references:** TLS 1.3 (similar transcript mechanism)

---

## Verification Considerations

| Requirement | Tier | Verification Approach |
|---|---|---|
| REQ-SPDM-001 | Tier 2 | Protocol: identity key protected in hardware; certificate chain validates |
| REQ-SPDM-002 | Tier 2 | Protocol: GET_CERTIFICATE returns complete chain |
| REQ-SPDM-003 | Tier 2 | Protocol: challenge signature valid; nonce present |
| REQ-SPDM-004 | Tier 2 | Protocol: GET_MEASUREMENTS signed response complete |
| REQ-SPDM-005 | Tier 1 | SVA: measurement registers locked after boot-time computation |
| REQ-SPDM-006 | Tier 2 | Protocol: all advertised indices return valid data |
| REQ-SPDM-007 | Tier 2 | Protocol: mutual authentication during key exchange |
| REQ-SPDM-008 | Tier 2 | Protocol: session traffic encrypted with AEAD |
| REQ-SPDM-009 | Tier 1 | SVA: session sequence numbers monotonically increase |
| REQ-SPDM-010 | Tier 2 | Protocol: nonces present and unique; entropy source qualified |
| REQ-SPDM-011 | Tier 2 | Protocol: negotiated algorithms within mutual set |
| REQ-SPDM-012 | Tier 2 | Protocol: transcript hash included in all signatures |

---

*[FROM TRAINING] Requirements are derived summaries, not verbatim specification text. Verify requirement details against DMTF DSP0274 (SPDM) v1.4 and related DMTF specifications. Last verified: 2026-02-13.*
