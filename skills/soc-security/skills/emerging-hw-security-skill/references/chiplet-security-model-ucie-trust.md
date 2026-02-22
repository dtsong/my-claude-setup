# Chiplet Security Model — UCIe, D2D Trust & Supply Chain

Covers UCIe 1.1 security features, die-to-die trust hierarchy, attestation, and multi-vendor supply chain provenance.

**Primary consumer:** emerging-hw-security-skill (Phase 2-3 chiplet/UCIe analysis)

---

## UCIe 1.1 Security Features

Universal Chiplet Interconnect Express (UCIe) defines the die-to-die interconnect for chiplet-based SoCs. UCIe 1.1 includes security features for link protection.

### Link Authentication

**UCIe Authentication Model:**
- UCIe leverages SPDM (Security Protocol and Data Model) for mutual authentication between chiplets
- Each die has a unique identity (device certificate chain rooted in a manufacturer CA)
- Authentication occurs during link initialization before any data transfer
- SPDM 1.2+ message flow: GET_DIGESTS -> GET_CERTIFICATE -> CHALLENGE -> CHALLENGE_AUTH

**Security Properties:**
- Mutual authentication: both dies verify each other's identity
- Fresh challenge: replay protection via nonce exchange
- Certificate chain validation: trust anchored to known root CA

**Threats to UCIe Authentication:**

| Threat | Description | Impact |
|--------|-------------|--------|
| Spoofed die identity | Counterfeit chiplet presents valid-looking but forged certificate | Unauthorized chiplet joins package |
| Replay attack | Attacker replays a previous authentication session | Stale authentication accepted |
| Man-in-the-middle on D2D | Interposer-level attack intercepts authentication messages | Session hijack |
| Root CA compromise | Manufacturer CA key compromised | All chiplet identities untrustworthy |
| Certificate revocation | No efficient CRL/OCSP for in-package chiplets | Revoked chiplet remains trusted |

### Link Integrity

**UCIe Integrity Protection:**
- Per-flit integrity check using CRC or MAC
- Integrity covers the flit header and payload
- Protects against bit flips (accidental or adversarial) on the D2D link
- MAC-based integrity (when encryption is enabled) provides authenticity in addition to integrity

**Integrity Modes:**

| Mode | Mechanism | Protection Level | Performance Impact |
|------|-----------|-----------------|-------------------|
| CRC only | CRC-32 per flit | Detects random errors, not adversarial tampering | Minimal |
| MAC per flit | GMAC or similar per flit | Detects both random errors and adversarial tampering | Moderate (MAC computation latency) |
| MAC + replay counter | MAC with monotonic counter | Detects tampering and replay | Moderate (counter management) |

### Link Encryption

**UCIe Encryption:**
- AES-GCM-256 encryption for data confidentiality on D2D links
- Key establishment via SPDM secured session (DHE-based)
- Encryption is optional and negotiated during link setup
- Provides confidentiality for data traversing exposed D2D interconnects (e.g., on an organic substrate or silicon interposer)

**When Encryption Is Needed:**
- Multi-vendor packages where dies from different vendors share a substrate
- Packages where the D2D link traverses an interposer that is manufactured by a third party
- Threat model includes substrate-level probing or interposer tampering
- When encryption is NOT needed: dies from the same vendor in a tightly integrated package with no substrate-level probing threat

---

## Die-to-Die Trust Model

### Which Chiplets Trust Which

In a multi-chiplet package, not all chiplets are equally trusted. The trust model must define trust relationships.

**Trust Hierarchy:**

```
Trust Level 0 (Root of Trust):
  - Security chiplet / root die
  - Contains: RoT, key storage, attestation engine
  - Trusts: only itself and verified firmware

Trust Level 1 (Authenticated Compute):
  - CPU die(s), authenticated via SPDM at boot
  - Trusts: Trust Level 0 for key provisioning
  - Trusted by: Trust Level 2 after mutual auth

Trust Level 2 (Authenticated I/O):
  - I/O chiplets (PCIe, CXL, Ethernet)
  - Trusts: Trust Level 1 for configuration
  - Trusted by: Trust Level 3 conditionally

Trust Level 3 (Untrusted / Third-Party):
  - Third-party accelerator chiplets
  - Must be authenticated before any data exchange
  - Minimal trust: isolated memory domain, restricted D2D access
```

### Attestation Between Dies

**Boot-Time Attestation:**
1. Security die (Trust Level 0) boots first, establishes root of trust
2. Security die initiates SPDM authentication with each connected die
3. Each die presents its firmware measurement (hash chain) during attestation
4. Security die verifies measurements against expected values (golden measurements)
5. Dies that fail attestation are isolated (D2D link disabled or restricted to error-only traffic)

**Runtime Attestation:**
- Periodic re-attestation to detect runtime firmware tampering
- Event-triggered re-attestation on firmware update or configuration change
- Attestation failure at runtime triggers alert and optional die isolation

**Attestation Threats:**

| Threat | Description | Countermeasure |
|--------|-------------|---------------|
| TOCTOU between measurement and execution | Firmware modified after measurement but before execution | Hardware-enforced measurement: measure from immutable boot ROM, lock firmware memory after measurement |
| Measurement forgery | Compromised die reports false measurements | Hardware measurement engine (TPM-like) per die with protected measurement registers |
| Attestation replay | Die replays a previous valid attestation | Fresh nonce per attestation session (provided by verifier die) |
| Golden measurement management | Incorrect expected measurements lead to false accept/reject | Secure provisioning of golden measurements during manufacturing |

---

## Chiplet Supply Chain Security

### Multi-Vendor Chiplet Packages

Chiplet architectures enable mixing dies from multiple vendors in a single package. This expands the supply chain attack surface.

**Supply Chain Trust Model:**

```
Die Manufacturing:
  Vendor A (CPU die)    -> Wafer fab A -> Die sort A -> Known Good Die (KGD) A
  Vendor B (I/O chiplet) -> Wafer fab B -> Die sort B -> KGD B
  Vendor C (Accelerator) -> Wafer fab C -> Die sort C -> KGD C

Package Assembly:
  OSAT (Outsourced Assembly and Test) ->
    Receives KGDs from A, B, C ->
    Substrate / interposer from Vendor D ->
    Assembly and packaging ->
    Final test

Deployment:
  System integrator -> Board assembly -> System test -> Deployment
```

### Provenance Per Die

**Per-Die Provenance Requirements:**

| Provenance Element | Description | Verification Method |
|-------------------|-------------|-------------------|
| Die identity | Unique per-die identifier (e.g., PUF-based) | Challenge-response during attestation |
| Manufacturer certificate | X.509 certificate chain rooted in vendor CA | Certificate validation during SPDM auth |
| Firmware version | Measured firmware hash | Attestation measurement comparison |
| Wafer lot / date code | Manufacturing provenance metadata | Out-of-band verification (supply chain management system) |
| Test results | Die sort and package test records | Out-of-band verification |

**Supply Chain Threats:**

| Threat | Description | Impact | Countermeasure |
|--------|-------------|--------|---------------|
| Counterfeit die | Non-genuine die inserted during assembly | Unknown behavior, potential backdoor | PUF-based identity + certificate chain |
| Die substitution | Genuine die replaced with different (lower capability or compromised) die | Reduced security or backdoor | Attestation with firmware measurement |
| Interposer tampering | Interposer modified to add probing points or signal manipulation | Data interception, signal manipulation | Encrypted D2D links, interposer integrity checks |
| OSAT compromise | Assembly facility inserts additional components or modifies package | Backdoor, interception | Trusted OSAT, package X-ray inspection, PUF verification post-assembly |
| Firmware supply chain | Compromised firmware delivered for chiplet update | Chiplet runs malicious firmware | Signed firmware with secure boot per die |
