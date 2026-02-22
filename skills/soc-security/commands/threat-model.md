---
name: threat-model
description: Start structured threat modeling for a SoC hardware security component or subsystem
---

# /soc-security:threat-model

Start the threat modeling process. This command activates the threat-model-skill to systematically identify, categorize, and document hardware security threats using STRIDE and attack-tree methodology.

## Usage

```
/soc-security:threat-model
/soc-security:threat-model "Analyze the TDISP device assignment flow for data-center SoCs"
/soc-security:threat-model --domain tdisp-cxl --family data-center
```

## What Happens

1. **Context gathering:** Claude asks for the component description, relevant spec sections, and security boundary definition. If a component description is provided inline, proceeds directly.
2. **Knowledge base check:** Checks the findings ledger for prior findings on the same domain and SoC family.
3. **Requirements extraction:** Extracts SecurityRequirement entities from provided spec sections and embedded references, with full source traceability.
4. **STRIDE analysis:** Systematically walks through each STRIDE category against the component's security boundaries:
   - **S**poofing — Identity and authentication threats
   - **T**ampering — Data and firmware integrity threats
   - **R**epudiation — Audit and attestation threats
   - **I**nformation Disclosure — Confidentiality and side-channel threats
   - **D**enial of Service — Availability and resource exhaustion threats
   - **E**levation of Privilege — Authorization and isolation bypass threats
5. **Attack surface checklist:** Marks each standard attack area as ANALYZED or NOT ANALYZED (side-channel, fault injection, debug interface, key management, boot chain, firmware update, bus access control).
6. **Confidence assessment:** Every finding tagged with GROUNDED/INFERRED/SPECULATIVE/ABSENT tier.
7. **Output generation:** Produces a threat model document with SecurityRequirement and ThreatFinding entities in DocumentEnvelope format.

## Technology Domains

| Domain | Scope |
|--------|-------|
| `confidential-ai` | TEE-based inference/training, model isolation |
| `tdisp-cxl` | Device isolation, memory expansion security, CXL.cache/mem/io |
| `supply-chain` | Firmware provenance, SBOM, counterfeit detection |
| `secure-boot-dice` | Hardware root of trust, DICE layering, attestation |
| `cheri` | Capability-based memory safety, compartmentalization |

## SoC Families

| Family | Key Constraints |
|--------|-----------------|
| `compute` | Server/HPC, high-bandwidth interconnects, multi-tenant |
| `automotive` | ISO 21434, functional safety overlay, real-time constraints |
| `client` | Mobile/laptop, power-constrained, consumer privacy |
| `data-center` | Multi-tenant, PCIe/CXL fabric, compliance-heavy |

## Output

The threat model is saved to your working folder as `threat-model.md` with YAML frontmatter (DocumentEnvelope format).

## Next Step

After threat modeling, use `/soc-security:verify` to generate verification checklists and SVA assertion templates from the findings.

## Skill Reference

This command invokes the [threat-model-skill](../threat-model-skill/SKILL.md). See also:
- [threat-modeling-methodology.md](../threat-model-skill/references/threat-modeling-methodology.md) — STRIDE workflow and attack tree construction
- [output-templates.md](../threat-model-skill/references/output-templates.md) — document envelope and entity format templates
- [threat-catalog/](../shared-references/soc-security/threat-catalog/) — known attack surface taxonomy
- [standards-registry/](../shared-references/soc-security/standards-registry/) — spec requirement extracts
