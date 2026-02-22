# Root of Trust Chain — Cross-Cutting Reference

## Purpose

This reference describes the unified Root of Trust (RoT) concept across all five technology domains. It shows how hardware trust anchors connect through DICE layering, platform attestation, device identity, and capability roots to form a coherent chain of trust. Understanding this chain is essential for identifying where trust is established, how it propagates, and where it can break.

**Primary consumers:** threat-model-skill (trust boundary identification), verification-scaffold-skill (trust chain assertions)
**Secondary consumers:** compliance-pipeline-skill (trust chain compliance), executive-brief-skill (trust chain explanation)

---

## Trust Chain Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                    HARDWARE ROOT OF TRUST                           │
│  ┌──────────┐  ┌──────────┐  ┌──────────────┐  ┌───────────────┐  │
│  │ OTP Fuses│  │   PUF    │  │ Immutable ROM│  │ Entropy Source │  │
│  │ (UDS,    │  │ (device  │  │ (DICE engine │  │ (TRNG for key │  │
│  │  keys)   │  │  unique) │  │  code)       │  │  generation)  │  │
│  └────┬─────┘  └────┬─────┘  └──────┬───────┘  └───────┬───────┘  │
│       │              │               │                  │          │
│       └──────────────┴───────────────┴──────────────────┘          │
│                              │                                     │
└──────────────────────────────┼─────────────────────────────────────┘
                               │
                    ┌──────────▼──────────┐
                    │   DICE LAYERING     │
                    │  UDS → CDI₀ → CDI₁  │
                    │  → CDI₂ → ...       │
                    │  (Alias cert chain) │
                    └──────────┬──────────┘
                               │
              ┌────────────────┼────────────────┐
              │                │                │
    ┌─────────▼──────┐  ┌─────▼──────┐  ┌──────▼──────────┐
    │ PLATFORM       │  │ DEVICE     │  │ CAPABILITY      │
    │ ATTESTATION    │  │ IDENTITY   │  │ ROOTS           │
    │ (SPDM meas.)  │  │ (TDISP     │  │ (CHERI root     │
    │                │  │  auth)     │  │  capability)    │
    └────────┬───────┘  └─────┬──────┘  └──────┬──────────┘
             │                │                │
    ┌────────▼───────┐  ┌─────▼──────┐  ┌──────▼──────────┐
    │ REMOTE         │  │ TRUST      │  │ COMPARTMENT     │
    │ VERIFIER       │  │ DOMAIN     │  │ BOUNDARIES      │
    │ (cloud, owner) │  │ ASSIGNMENT │  │ (runtime)       │
    └────────────────┘  └────────────┘  └─────────────────┘
```

---

## Layer 1: Hardware Root of Trust

### Definition

The Hardware Root of Trust (HRoT) is the minimal set of hardware components that must be unconditionally trusted. If any HRoT component is compromised, the entire trust chain collapses. The HRoT cannot be verified by the system itself — it is trusted by virtue of its physical properties.

### Components

| Component | Function | Trust Basis | Threat if Compromised |
|---|---|---|---|
| **OTP Fuses** | Store UDS, root key hashes, anti-rollback counters, lifecycle state | Physical irreversibility of fuse programming | Attacker can forge device identity, bypass rollback protection |
| **PUF (Physical Unclonable Function)** | Generate device-unique secrets from manufacturing variation | Physical uniqueness, unclonable | Attacker can clone device identity (requires modeling PUF) |
| **Immutable ROM** | Execute first DICE layer (measure, derive CDI, lock UDS) | Physical immutability (mask ROM, fused ROM) | Attacker controls first boot stage; entire chain untrusted |
| **Entropy Source (TRNG)** | Generate random values for key generation, nonces | Physical randomness from hardware noise source | Predictable keys, replayable nonces, broken crypto |

### Verification Approach

- HRoT components are assumed correct in simulation (they are the trust anchor)
- Physical verification: fuse programming validation, PUF characterization, ROM read-back, entropy testing (NIST SP 800-90B)
- SVA assertions verify that HRoT outputs are consumed correctly by the first DICE layer

### Cross-Domain Relevance

| Domain | HRoT Dependency |
|---|---|
| Secure Boot / DICE | UDS in fuses, DICE engine in ROM |
| Supply Chain Security | Root key hashes in fuses for firmware signing verification |
| Confidential AI / TEE | HRoT establishes TEE firmware identity |
| TDISP / CXL | Device identity key rooted in HRoT (via DICE) |
| RISC-V CHERI | Root capability derived from boot-time initialization |

---

## Layer 2: DICE Layered Identity

### Definition

DICE creates a chain of derived identities from the HRoT through each firmware layer. Each layer measures the next, derives a CDI, generates keys and certificates, and locks its secrets before passing control. The resulting certificate chain is the cryptographic evidence of the platform's firmware composition.

### Trust Propagation

```
HRoT (UDS) ──measure(FW₀)──► CDI₀ ──measure(FW₁)──► CDI₁ ──measure(FW₂)──► CDI₂
     │                         │                       │                      │
  DeviceID key           Alias key₀              Alias key₁             Alias key₂
  (long-term)            (per-boot)              (per-boot)             (per-boot)
```

### Trust Properties

| Property | How DICE Provides It |
|---|---|
| **Identity binding** | CDI incorporates firmware measurement; different firmware = different identity |
| **Freshness** | Alias keys regenerated each boot; previous-boot keys not reusable |
| **Layer isolation** | Each layer's secrets locked before next layer executes |
| **Attestation evidence** | Certificate chain proves firmware composition to remote verifier |
| **Non-repudiation** | Certificate chain provides evidence of booted firmware versions |

### Trust Chain Break Points

| Break Point | Effect | Detection |
|---|---|---|
| UDS extraction | Attacker can forge any DICE identity for this device | Undetectable by the device itself; detected by verifier policy change |
| ROM compromise | Attacker controls measurement; can produce arbitrary CDIs | Undetectable — ROM is the trust root |
| Measurement bypass | Firmware modification does not change CDI | Verifier sees valid but incorrect identity; gap in measurement scope |
| Lock failure | Previous-layer secrets accessible to current layer | Privilege escalation; CDI for previous layer extractable |

---

## Layer 3: Platform Attestation (SPDM)

### Definition

SPDM carries DICE-derived identity and firmware measurements to remote verifiers. The platform (or device) proves its firmware state through signed measurement reports. The verifier compares reported measurements against expected values to decide whether to trust the platform.

### Trust Flow

```
Device (SPDM Responder)          Requester / Verifier
         │                              │
         │←── GET_CERTIFICATE ──────────│
         │─── CERTIFICATE (chain) ─────►│  ← Verifier validates chain to trust anchor
         │                              │
         │←── CHALLENGE (nonce) ────────│
         │─── CHALLENGE_AUTH (sig) ────►│  ← Proves possession of identity key
         │                              │
         │←── GET_MEASUREMENTS ─────────│
         │─── MEASUREMENTS (signed) ───►│  ← Reports firmware state
         │                              │
         │←── KEY_EXCHANGE ─────────────│
         │─── KEY_EXCHANGE_RSP ────────►│  ← Establishes encrypted session
```

### Trust Dependencies

| SPDM Trust Depends On | If Missing |
|---|---|
| DICE identity chain (Layer 2) | No cryptographic identity to authenticate with |
| Measurement register integrity | Measurements can be forged; verifier receives false state |
| Nonce freshness | Responses can be replayed from previous sessions |
| Certificate chain validity | Verifier cannot validate device identity |

---

## Layer 4: Device Identity and Assignment (TDISP)

### Definition

TDISP uses SPDM-established identity and trust to securely assign a device interface to a trust domain (e.g., a confidential VM). The TDI state machine ensures that the device is authenticated and its security configuration is locked before it becomes accessible to the trust domain.

### Trust Flow

```
SPDM Authentication ──► TDISP CONFIG ──► TDISP LOCK ──► IDE Setup ──► TDISP RUN
     (identity)           (setup)        (freeze config)  (encrypt link) (active)
```

### Trust Dependencies

| TDISP Trust Depends On | If Missing |
|---|---|
| SPDM authentication (Layer 3) | Device identity unverified; rogue device possible |
| SPDM measurement (Layer 3) | Device firmware state unknown; compromised firmware possible |
| IDE encryption | Link data exposed to physical interposer |
| State machine integrity | State bypass allows access without security properties |

---

## Layer 5: Capability Roots (CHERI)

### Definition

In CHERI-enabled designs, the root capability is the initial capability with full authority (all addresses, all permissions). It is established at boot time by the firmware and narrowed (restricted) as capabilities are distributed to software components. The root capability is analogous to the UDS — it is the starting point from which all authority derives, and it must be protected from unauthorized access.

### Trust Propagation

```
Boot firmware (root capability: full authority)
    │
    ├── Kernel capability (narrowed: kernel memory only)
    │   ├── Process A capability (narrowed: process A memory)
    │   └── Process B capability (narrowed: process B memory)
    │
    └── Security monitor capability (narrowed: security subsystem)
        └── Compartment capabilities (sealed, per-compartment)
```

### Trust Properties

| Property | How CHERI Provides It |
|---|---|
| **Monotonicity** | Authority can only decrease through derivation; never amplified |
| **Unforgeability** | Tag bit prevents manufacturing capabilities from data |
| **Compartmentalization** | Sealed capabilities and sentries enforce compartment boundaries |
| **Revocation** | Capabilities can be revoked to remove previously granted authority |

### Trust Dependencies

| CHERI Trust Depends On | If Missing |
|---|---|
| Tag bit integrity | Capabilities can be forged from arbitrary data |
| Monotonicity enforcement | Authority can be escalated through derivation |
| Boot firmware correctness | Root capability may be distributed too broadly |
| Hardware bounds checking | Out-of-bounds access not caught |

---

## Cross-Domain Trust Relationships

### Trust Chain Integration Points

| Integration | Layers Involved | What Happens |
|---|---|---|
| TEE firmware attestation | HRoT → DICE → SPDM | TEE firmware identity verified by remote owner before deploying workload |
| Device assignment to VM | HRoT → DICE → SPDM → TDISP | Device authenticated and assigned to confidential VM via TDISP |
| Supply chain verification | HRoT → DICE → SPDM | Component firmware state verified against expected measurements |
| Capability-based boot | HRoT → DICE → CHERI | Boot firmware establishes capability root; distributes narrowed capabilities |
| CXL fabric attestation | HRoT → DICE → SPDM → CXL TSP | Memory device firmware attested before multi-host sharing |

### End-to-End Trust Scenarios

**Scenario 1: Confidential VM on CXL-Attached Accelerator**
```
GPU HRoT → GPU DICE chain → GPU SPDM attestation → Platform verifies GPU firmware
→ TDISP assigns GPU TDI to VM trust domain → IDE encrypts PCIe link
→ VM owner verifies GPU attestation evidence → Workload deployed
```
Trust chain length: 6 links. Break at any link compromises confidential workload.

**Scenario 2: Automotive Secure Boot with OTA Update**
```
SoC HRoT → DICE boot chain → Measured boot to HSM → HSM verifies OTA package signature
→ Anti-rollback counter checked → New firmware measured → DICE identity updated
→ SPDM reports new measurements to fleet manager
```
Trust chain length: 7 links. Anti-rollback counter is critical — rollback bypasses all update security.

---

## Trust Chain Verification Strategy

| Layer | Verification Approach | Confidence |
|---|---|---|
| HRoT | Physical validation (assumed correct in simulation) | Axiom |
| DICE | Tier 1 SVA (secret locking, measurement ordering) + Tier 2 (CDI correctness) | High |
| SPDM | Tier 2 (protocol correctness) + Tier 1 (measurement register locks) | High |
| TDISP | Tier 1 SVA (state machine) + Tier 2 (SPDM binding) | High |
| CXL TSP | Tier 1 SVA (partition isolation) + Tier 2 (TSP configuration) | High |
| CHERI | Tier 1 SVA (bounds, tags, monotonicity) — most properties directly assertable | High |
| Cross-layer | Tier 3 (information flow between trust layers) | Requires expert review |

---

*[FROM TRAINING] All content in this file is derived from general hardware security engineering knowledge and publicly available specification summaries. Verify trust chain details against target SoC documentation. Last verified: 2026-02-13.*
