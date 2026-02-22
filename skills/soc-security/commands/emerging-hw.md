---
name: emerging-hw
description: Run emerging hardware security assessment (PQC, chiplets, heterogeneous compute, AI accelerators)
---

# /soc-security:emerging-hw

Assess security implications of emerging hardware paradigms. This command activates the emerging-hw-security-skill to evaluate post-quantum crypto implementations, chiplet/UCIe architectures, heterogeneous compute security, and AI accelerator security.

## Usage

```
/soc-security:emerging-hw
/soc-security:emerging-hw "Assess PQC readiness of our crypto engine for FIPS 203 migration"
/soc-security:emerging-hw --paradigm chiplet-ucie --family data-center
```

## What Happens

1. **Paradigm context loading:** Claude identifies which emerging paradigm(s) apply and loads relevant standards and threat patterns.
2. **Threat landscape assessment:** Evaluates paradigm-specific threats (PQC implementation SCA, chiplet supply chain, NPU model extraction).
3. **Architecture security review:** Reviews the specific architecture against identified threats.
4. **Migration & readiness assessment:** Assesses migration risk and readiness for the paradigm transition.
5. **Output generation:** Produces an emerging HW assessment with EmergingHWFinding entities and migration risk analysis.

## Paradigms Covered

| Paradigm | Scope |
|----------|-------|
| Post-quantum crypto | ML-KEM (FIPS 203), ML-DSA (FIPS 204), SLH-DSA (FIPS 205), HW implementation security |
| Chiplet/UCIe | Die-to-die auth, chiplet supply chain, UCIe 1.1 link security |
| Heterogeneous compute | CPU+GPU+NPU trust boundaries, shared memory, driver isolation |
| AI accelerator | Model confidentiality, inference integrity, weight protection |

## Output

The assessment is saved as an `emerging-hw-assessment` DocumentEnvelope with EmergingHWFinding entities, maturity assessment, and migration risk analysis.

## Next Step

After emerging HW assessment, findings can feed into:
- `/soc-security:threat-model` — incorporate findings into comprehensive threat models
- `/soc-security:comply` — map to FIPS 203/204/205 or UCIe 1.1 requirements
- `/soc-security:formalize` — formalize security properties for novel architectures

## Skill Reference

This command invokes the [emerging-hw-security-skill](../emerging-hw-security-skill/SKILL.md). See also:
- [pqc-implementation-guide.md](../emerging-hw-security-skill/references/pqc-implementation-guide.md) — PQC HW security guide
- [chiplet-security-model.md](../emerging-hw-security-skill/references/chiplet-security-model.md) — chiplet and heterogeneous compute security
- [nist-pqc/requirements.md](../shared-references/soc-security/standards-registry/nist-pqc/requirements.md) — FIPS 203/204/205 requirements
- [ucie/requirements.md](../shared-references/soc-security/standards-registry/ucie/requirements.md) — UCIe 1.1 security requirements
