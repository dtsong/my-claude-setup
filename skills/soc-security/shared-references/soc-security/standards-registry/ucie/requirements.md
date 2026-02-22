# UCIe 1.1 — Universal Chiplet Interconnect Express Security Requirements

## Specification Overview

| Field | Value |
|---|---|
| **Full Name** | Universal Chiplet Interconnect Express (UCIe) Specification |
| **Version** | 1.1 (2023) [FROM TRAINING] |
| **Organization** | UCIe Consortium |
| **Scope** | Die-to-die interconnect standard for chiplet-based architectures, covering physical layer, protocol layer, and security requirements for multi-die packages |
| **Security Properties Addressed** | Die-to-Die Integrity, Confidentiality, Authenticity, Supply Chain Trust, Isolation |
| **Related Standards** | PCIe/CXL (protocol layer), DMTF SPDM (authentication), TCG DICE (chiplet identity), NIST SP 800-193 (platform firmware resiliency) |

---

## Concept Summary

UCIe defines a standardized die-to-die interconnect for chiplet-based system-in-package (SiP) architectures, enabling heterogeneous integration of chiplets from different vendors within a single package. The security requirements address a fundamentally different threat model from board-level interconnects: while die-to-die links within a package were historically considered trusted, chiplet disaggregation introduces supply chain risks (untrusted chiplets from third-party vendors), integrity risks (interposer-level probing or fault injection), and confidentiality risks (sensitive data traversing shared interconnect fabric). UCIe 1.1 defines security capabilities including link-level authentication, encryption, and integrity protection, building on established protocols (SPDM, IDE) adapted for the die-to-die context.

**Key architectural principle:** In a chiplet architecture, the package boundary is not a trust boundary — each chiplet must be independently authenticated and the die-to-die links must be protected as if they were exposed interfaces, because the supply chain for individual chiplets may be independently compromised.

---

## Key Security Requirements

### Die-to-Die Link Authentication

**REQ-UCIE-001: Chiplet Mutual Authentication**
Before exchanging application data, communicating chiplets must perform mutual authentication to verify each other's identity. Authentication must use DMTF SPDM-based protocols (or equivalent) adapted for the die-to-die link. Each chiplet must present a verifiable identity credential (certificate chain rooted at a trusted CA or device manufacturer). Authentication must complete before any protected data traverses the link.

- **Security properties:** Authenticity, Die-to-Die Integrity
- **Verification tier:** Tier 2 — protocol-level check for SPDM authentication handshake over UCIe link
- **Cross-references:** REQ-SPDM-001 (device identity), REQ-UCIE-004 (chiplet identity and attestation)

**REQ-UCIE-002: Authentication Freshness**
The authentication protocol must include freshness guarantees (nonces or timestamps) to prevent replay of previously captured authentication exchanges. An attacker who records a valid authentication session must not be able to replay it to authenticate a rogue chiplet. Session keys derived during authentication must be unique per session.

- **Security properties:** Freshness, Authenticity
- **Verification tier:** Tier 2 — protocol-level check for nonce inclusion and session key uniqueness
- **Cross-references:** REQ-SPDM-010 (session freshness), REQ-UCIE-001 (mutual authentication)

### Link Integrity and Encryption

**REQ-UCIE-003: Link Integrity Protection (IDE)**
Die-to-die links carrying security-sensitive data must support Integrity and Data Encryption (IDE) as defined in the UCIe security specification. Link integrity uses a MAC (message authentication code) computed over each flit or group of flits to detect tampering or bit-flip attacks on the interposer. The MAC algorithm must be AES-GCM or equivalent approved construction. Integrity check failures must be reported and must halt the affected data transfer.

- **Security properties:** Die-to-Die Integrity
- **Verification tier:** Tier 1 — SVA assertions for MAC computation and verification on every protected flit; Tier 2 — protocol check for error handling on integrity failure
- **Cross-references:** PCIe IDE specification, REQ-UCIE-005 (link encryption)

**REQ-UCIE-004: Chiplet Identity and Attestation**
Each chiplet must have a hardware-rooted identity that can be attested to other chiplets and to the package-level platform management. The identity must be bound to the chiplet's hardware (via fuses, PUF, or DICE-derived identity) and must reflect the chiplet's firmware/configuration state. A chiplet that has been tampered with or is running unauthorized firmware must produce a different attestation result that can be detected by the verifying chiplet or platform manager.

- **Security properties:** Authenticity, Attestation, Supply Chain Trust
- **Verification tier:** Tier 1 — SVA assertions for identity register protection; Tier 2 — protocol check for attestation evidence correctness
- **Cross-references:** REQ-DICE-001 (UDS protection), REQ-DICE-007 (alias certificate chain), REQ-SPDM-008 (measurement)

**REQ-UCIE-005: Link Encryption**
Die-to-die links must support encryption to protect data confidentiality against physical interposer probing attacks. Encryption must use AES-256-GCM (or equivalent approved algorithm) with keys derived during the authenticated key exchange. Encryption must cover the flit payload and must not leak plaintext through protocol headers or side channels. Key refresh must occur periodically or after a configurable number of flits to limit the exposure from a single compromised key.

- **Security properties:** Confidentiality, Die-to-Die Integrity
- **Verification tier:** Tier 1 — SVA assertions for encryption of all protected flit payloads; Tier 2 — protocol check for key derivation and refresh
- **Cross-references:** REQ-UCIE-003 (link integrity), FIPS 140-3 (approved algorithms)

### Supply Chain and Multi-Die Trust

**REQ-UCIE-006: Supply Chain Trust for Individual Chiplets**
Each chiplet in a multi-die package must carry provenance information that can be verified during platform initialization. This includes: (a) manufacturer identity and signing key, (b) chiplet model and revision, (c) firmware version and measurement, and (d) a certificate chain linking the chiplet's identity to the manufacturer's root CA. The platform must be able to verify that each chiplet is genuine and authorized before allowing it to participate in security-sensitive operations.

- **Security properties:** Supply Chain Trust, Authenticity
- **Verification tier:** Tier 2 — protocol check for certificate chain validation during platform boot
- **Cross-references:** REQ-UCIE-004 (chiplet identity), REQ-DICE-006 (DeviceID certificate)

**REQ-UCIE-007: Multi-Die Package Security Boundary Definition**
The platform security policy must define which chiplets constitute a trust domain and the security boundaries between domains. Chiplets from the same trusted vendor may share a security domain with relaxed inter-chiplet protection, while chiplets from different vendors or with different trust levels must be in separate security domains with full link protection. The security domain assignment must be configurable and must be enforced by hardware access control on the UCIe interconnect fabric.

- **Security properties:** Isolation, Die-to-Die Integrity
- **Verification tier:** Tier 1 — SVA assertions for security domain enforcement on interconnect fabric; Tier 2 — policy review
- **Cross-references:** REQ-UCIE-003 (link integrity), REQ-UCIE-005 (link encryption)

**REQ-UCIE-008: Chiplet Isolation on Authentication Failure**
If a chiplet fails authentication or attestation during platform initialization, the platform must isolate the failed chiplet from security-sensitive resources. Isolation options include: disabling the chiplet's UCIe link, restricting the chiplet to a non-secure domain, or halting platform boot with an error. The isolation policy must be configurable and must not allow a failed chiplet to access data from other chiplets' security domains.

- **Security properties:** Isolation, Availability (safe degradation)
- **Verification tier:** Tier 1 — SVA assertions for link disable or domain restriction on authentication failure
- **Cross-references:** REQ-UCIE-001 (mutual authentication), REQ-UCIE-007 (security boundaries)

### UCIe Retimer and Physical Layer Security

**REQ-UCIE-009: UCIe Retimer Security**
If the UCIe link path includes retimers (signal conditioning devices on the interposer), the retimers must not compromise link security. Retimers must either: (a) operate transparently below the security layer (forwarding encrypted/integrity-protected flits without decryption), or (b) participate in the security protocol as authenticated entities with their own identity and key material. A retimer must not be able to silently inspect or modify protected flit payloads.

- **Security properties:** Confidentiality, Die-to-Die Integrity
- **Verification tier:** Tier 2 — protocol check for retimer transparency or authenticated participation
- **Cross-references:** REQ-UCIE-003 (link integrity), REQ-UCIE-005 (link encryption)

**REQ-UCIE-010: Physical Layer Tamper Detection**
The UCIe physical layer should support mechanisms to detect physical tampering with the die-to-die link (e.g., interposer probing, wire bonding to exposed traces). Detection mechanisms may include: link error rate monitoring (anomalous bit error rates may indicate probing), electromagnetic shielding verification, or active tamper detection circuits on the interposer. Detected physical tampering must trigger a security alert and may trigger link shutdown.

- **Security properties:** Die-to-Die Integrity, Tamper Resistance
- **Verification tier:** Tier 1 — SVA assertions for error rate threshold monitoring; Tier 3 — physical tamper testing
- **Cross-references:** REQ-UCIE-003 (link integrity), FIPS 140-3 Level 3+ (physical security)

### Key Management and Lifecycle

**REQ-UCIE-011: Die-to-Die Session Key Management**
Session keys used for link encryption and integrity must be derived using an approved key derivation function (KDF) from the authenticated key exchange. Keys must be stored in hardware registers accessible only to the link security engine. Session keys must be zeroized on link reset, chiplet power-down, or security domain reconfiguration. Key rotation must be supported and must not cause data loss or link interruption (hitless key update).

- **Security properties:** Confidentiality, Die-to-Die Integrity
- **Verification tier:** Tier 1 — SVA assertions for key register access control, zeroization on reset, hitless key rotation
- **Cross-references:** REQ-UCIE-005 (link encryption), FIPS 140-3 (key management)

**REQ-UCIE-012: Security State Recovery After Link Reset**
After a UCIe link reset (due to error recovery, power management event, or reconfiguration), the security state must be re-established before protected data transfer resumes. This requires re-authentication and re-keying of the link. The implementation must not fall back to unprotected data transfer during the re-establishment window. If re-authentication fails after reset, the link must remain in a non-operational state for protected traffic.

- **Security properties:** Integrity, Confidentiality, Availability
- **Verification tier:** Tier 1 — SVA assertions for security state machine re-initialization on link reset; Tier 2 — protocol check for re-authentication sequence
- **Cross-references:** REQ-UCIE-001 (mutual authentication), REQ-UCIE-011 (session key management)

---

## Verification Considerations

| Requirement | Tier | Verification Approach |
|---|---|---|
| REQ-UCIE-001 | Tier 2 | Protocol: SPDM-based mutual authentication completes before data transfer |
| REQ-UCIE-002 | Tier 2 | Protocol: nonces present in authentication; session keys unique per session |
| REQ-UCIE-003 | Tier 1/2 | SVA: MAC computed on every protected flit; Protocol: integrity failure halts transfer |
| REQ-UCIE-004 | Tier 1/2 | SVA: identity registers protected; Protocol: attestation evidence matches expected |
| REQ-UCIE-005 | Tier 1/2 | SVA: all protected payloads encrypted; Protocol: key derivation and refresh correct |
| REQ-UCIE-006 | Tier 2 | Protocol: certificate chain validates to manufacturer root during boot |
| REQ-UCIE-007 | Tier 1/2 | SVA: security domain isolation enforced on fabric; Policy: domain assignments reviewed |
| REQ-UCIE-008 | Tier 1 | SVA: link disabled or domain restricted on authentication failure |
| REQ-UCIE-009 | Tier 2 | Protocol: retimer operates transparently or authenticates as participant |
| REQ-UCIE-010 | Tier 1/3 | SVA: error rate monitoring active; Lab: physical tamper detection testing |
| REQ-UCIE-011 | Tier 1 | SVA: key register access control, zeroization, and hitless rotation verified |
| REQ-UCIE-012 | Tier 1/2 | SVA: security FSM resets to unauthenticated on link reset; Protocol: re-auth before data |

---

*[FROM TRAINING] Requirements are derived summaries, not verbatim specification text. Verify requirement details against UCIe Specification 1.1 and related DMTF SPDM, PCIe IDE, and TCG DICE specifications. Last verified: 2026-02-13.*
