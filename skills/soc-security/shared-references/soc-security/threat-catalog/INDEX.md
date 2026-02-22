# Threat Catalog — Index

## Purpose

Comprehensive catalog of hardware security threats relevant to SoC designs. Organized by attack surface category. Each threat entry includes structured metadata enabling the threat-model-skill to generate targeted, domain-aware threat models.

**Primary consumers:** threat-model-skill (threat identification and scoring), verification-scaffold-skill (mapping threats to verification approaches)
**Secondary consumers:** compliance-pipeline-skill (threat-to-requirement tracing), executive-brief-skill (risk context)

---

## Attack Surface Taxonomy

```
SoC Attack Surfaces
├── Physical Attacks (PHYS-xxx)
│   ├── Fault injection (voltage, clock, laser, EM)
│   ├── Side-channel analysis (power, timing, EM)
│   ├── Physical probing and bus sniffing
│   └── Cold boot and memory remanence
├── Firmware Attacks (FW-xxx)
│   ├── Boot chain subversion
│   ├── Firmware rollback
│   ├── Supply chain implant
│   ├── Debug-based code injection
│   └── OTA update hijacking
├── Interface Attacks (INTF-xxx)
│   ├── PCIe/CXL protocol manipulation
│   ├── DMA attacks
│   ├── Debug port exploitation
│   ├── Mailbox/register abuse
│   └── Interrupt injection
├── Architectural Attacks (ARCH-xxx)
│   ├── Privilege escalation
│   ├── VM/TEE escape
│   ├── Memory isolation bypass
│   ├── Capability forgery (CHERI)
│   ├── Cross-domain information flow
│   └── TOCTOU on security state
├── Microarchitectural Attacks (UARCH-xxx)
│   ├── Transient execution (Spectre, Meltdown, MDS)
│   ├── Cache side-channels (Prime+Probe, Flush+Reload)
│   ├── Branch predictor attacks
│   └── Shared resource contention
└── Kernel Attacks (KERN-xxx)
    ├── Privilege escalation
    ├── Container/VM escape
    ├── IOMMU/DMA bypass
    └── Kernel integrity bypass
```

---

## STRIDE Category Reference

| Category | Definition | Typical SoC Manifestation |
|---|---|---|
| **S** — Spoofing | Pretending to be a different entity | Forged device identity, debug auth bypass |
| **T** — Tampering | Modifying data or code without authorization | Firmware modification, TLP injection, register tampering |
| **R** — Repudiation | Denying having performed an action | Unsigned firmware updates, no audit trail |
| **I** — Information Disclosure | Exposing data to unauthorized entities | Side-channel leakage, memory disclosure, covert channels |
| **D** — Denial of Service | Making a resource unavailable | Interrupt flooding, bus lockup, watchdog starvation |
| **E** — Elevation of Privilege | Gaining unauthorized access level | VM escape, capability forgery, privilege escalation |

---

## Cross-Reference: Threats by Domain

| Threat Category | Confidential AI/TEE | TDISP/CXL | Supply Chain | Secure Boot/DICE | RISC-V CHERI |
|---|---|---|---|---|---|
| Physical | Memory probing | Link interposer | Component substitution | Fuse extraction | N/A (ISA-level) |
| Firmware | TEE firmware tampering | Device firmware rollback | Firmware implant | Boot chain subversion | Firmware compartment bypass |
| Interface | VM-host interface | PCIe TLP injection | SPDM protocol manipulation | Debug port attack | Capability via debug |
| Architectural | VM escape | TDISP state bypass | Attestation forgery | CDI chain compromise | Capability forgery |

---

## Threat Entry Format

Each threat in the sub-files follows this structure:

| Field | Description |
|---|---|
| **ID** | Unique identifier (e.g., PHYS-001) |
| **Name** | Short descriptive name |
| **STRIDE** | STRIDE category (S/T/R/I/D/E) |
| **Description** | What the attack does and how |
| **Target Assets** | What the attacker targets |
| **Affected Domains** | Technology domains from domain-ontology |
| **Affected SoC Families** | SoC families from soc-families.md |
| **Preconditions** | What the attacker needs |
| **Key Mitigations** | Hardware/protocol countermeasures |
| **Verification Approach** | Which tier and what to verify |
| **Related Requirements** | REQ-xxx IDs from standards registry |

---

## Catalog Files

| File | Threats | ID Range |
|---|---|---|
| `physical-attacks.md` | Fault injection, side-channel, probing, cold boot | PHYS-001 to PHYS-008 |
| `firmware-attacks.md` | Boot subversion, rollback, implant, debug injection, OTA | FW-001 to FW-006 |
| `interface-attacks.md` | TLP injection, DMA, debug port, mailbox, interrupt | INTF-001 to INTF-007 |
| `architectural-attacks.md` | Privilege escalation, VM escape, isolation bypass, TOCTOU | ARCH-001 to ARCH-008 |
| `microarchitectural-attacks.md` | Spectre, Meltdown, MDS, cache side-channels, branch predictor attacks | UARCH-001 to UARCH-020 |
| `kernel-attacks.md` | Privilege escalation, container escape, IOMMU bypass, kernel integrity | KERN-001 to KERN-015 |

---

*[FROM TRAINING] Threat descriptions are based on publicly known attack classes and general security domain knowledge. Specific attack details should be verified against published research. Last verified: 2026-02-13.*
