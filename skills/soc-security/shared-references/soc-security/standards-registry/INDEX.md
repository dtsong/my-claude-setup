# Standards Registry — Index

## Purpose

Master index of security standards and specifications relevant to SoC hardware security. Each entry links to a detailed requirements extract in its subdirectory. Requirements are derived and summarized — never verbatim copied — to maintain IP-clean status.

**Primary consumers:** compliance-pipeline-skill (requirement traceability), threat-model-skill (standard-aware threat analysis)
**Secondary consumers:** verification-scaffold-skill (verification considerations per standard), executive-brief-skill (standard context)

---

## Priority Order

Standards are ordered by priority for the SoC Security Suite:

1. **TCG DICE v1.2 + DMTF SPDM v1.4 / TDISP 1.0** — Foundation for platform identity, attestation, and device assignment
2. **CXL 3.1 Security** — Fabric-level security for next-generation data center interconnects
3. **CHERI ISA** — Capability-based hardware memory safety
4. **PCIe IDE** — Link encryption and integrity (covered within TDISP and CXL registries)

---

## Master Specification List

| Standard | Version | Org | Scope | Last Verified | Registry Path |
|---|---|---|---|---|---|
| TCG DICE | v1.2 (2024) | TCG | Layered device identity, CDI derivation, attestation | 2026-02-13 [FROM TRAINING] | `dice/requirements.md` |
| DMTF SPDM | v1.4 (2024) | DMTF | Device authentication, measurement, key exchange | 2026-02-13 [FROM TRAINING] | `spdm/requirements.md` |
| PCIe TDISP | 1.0 (2023) | PCI-SIG | TEE device interface security, TDI lifecycle | 2026-02-13 [FROM TRAINING] | `tdisp/requirements.md` |
| CXL Security | 3.1 (2024) | CXL Consortium | Link security, TSP, multi-host isolation | 2026-02-13 [FROM TRAINING] | `cxl/requirements.md` |
| CHERI ISA | v9 (2023) | Cambridge/SRI | Capability encoding, bounds, compartmentalization | 2026-02-13 [FROM TRAINING] | `cheri/requirements.md` |
| ISO 17825 | (2016) | ISO | Side-channel leakage assessment (TVLA) | 2026-02-13 [FROM TRAINING] | `iso17825/requirements.md` |
| NIST PQC (FIPS 203/204/205) | (2024) | NIST | Post-quantum cryptography standards | 2026-02-13 [FROM TRAINING] | `nist-pqc/requirements.md` |
| UCIe | 1.1 (2023) | UCIe Consortium | Universal Chiplet Interconnect Express security | 2026-02-13 [FROM TRAINING] | `ucie/requirements.md` |

---

## Compliance Overlay Standards

These standards are not hardware specifications but impose security requirements on SoC designs. They are referenced in per-standard requirement files where applicable.

| Standard | Version | Org | Scope | Applicability |
|---|---|---|---|---|
| FIPS 140-3 | (2019, active) | NIST | Cryptographic module validation | Compute, Data Center, Client |
| ISO 21434 | (2021) | ISO/SAE | Automotive cybersecurity engineering | Automotive |
| ISO 26262 | (2018, Ed.2) | ISO | Functional safety (security intersection) | Automotive |
| NIST SP 800-53 | Rev. 5 | NIST | Security and privacy controls | Government deployments |
| Common Criteria | CC:2022 | CCRA | Security evaluation (EAL levels) | Cross-family, procurement |

---

## Cross-Standard Relationships

```
                    ┌─────────────┐
                    │  TCG DICE   │
                    │   v1.2      │
                    └──────┬──────┘
                           │ identity feeds into
                    ┌──────▼──────┐
                    │  DMTF SPDM  │
                    │   v1.4      │
                    └──┬───────┬──┘
          auth for     │       │    auth for
        ┌──────────────▼┐    ┌▼──────────────┐
        │  PCIe TDISP   │    │  CXL 3.1 TSP  │
        │    1.0        │    │  (Security)    │
        └───────────────┘    └───────────────┘

        ┌─────────────┐
        │  CHERI ISA  │  (orthogonal — memory safety layer)
        │    v9       │
        └─────────────┘

        ┌─────────────┐          ┌───────────────┐
        │  ISO 17825  │─────────▶│  FIPS 140-3   │
        │   (TVLA)    │ leakage  │  Level 3+     │
        └─────────────┘ testing  └───────────────┘

        ┌─────────────┐          ┌───────────────┐
        │  NIST PQC   │─────────▶│  DICE / SPDM  │
        │ FIPS 203-205│ future   │  (PQ migration)│
        └─────────────┘ migration└───────────────┘

        ┌─────────────┐
        │    UCIe     │  (chiplet interconnect — extends IDE/SPDM to chiplet links)
        │    1.1      │
        └─────────────┘
```

**Key relationships:**
- DICE provides the identity foundation that SPDM carries to verifiers
- SPDM is the transport protocol for both TDISP authentication and CXL TSP attestation
- TDISP and CXL security share PCIe IDE as the link encryption mechanism
- CHERI is architecturally orthogonal — it operates at the ISA level rather than the protocol level, but capability-based access control complements protocol-level isolation
- ISO 17825 defines TVLA methodology used for FIPS 140-3 Level 3+ physical security validation
- NIST PQC (FIPS 203/204/205) provides post-quantum algorithms that will migrate into DICE certificate chains and SPDM authentication
- UCIe extends PCIe IDE and SPDM security mechanisms to chiplet-to-chiplet interconnects

---

## Requirement ID Convention

All extracted requirements use the following ID format:

```
REQ-{STANDARD}-{NUMBER}
```

Examples:
- `REQ-DICE-001` — First extracted requirement from DICE
- `REQ-SPDM-012` — Twelfth extracted requirement from SPDM
- `REQ-TDISP-005` — Fifth extracted requirement from TDISP

IDs are stable within a version of this registry. Cross-references between standards use these IDs.

---

*[FROM TRAINING] Version numbers and dates are based on training knowledge. Verify against authoritative sources for current versions. Last verified: 2026-02-13.*
