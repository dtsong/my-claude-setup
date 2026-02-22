---
name: physical-sca
description: Run physical side-channel assessment on a SoC cryptographic component
---

# /soc-security:physical-sca

Assess physical side-channel attack resistance. This command activates the physical-sca-skill to systematically evaluate power analysis, EM analysis, and fault injection resistance of cryptographic implementations, with JIL attack potential scoring and ISO 17825 leakage assessment.

## Usage

```
/soc-security:physical-sca
/soc-security:physical-sca "Assess the AES-256 crypto engine for DPA resistance"
/soc-security:physical-sca --target "HSM crypto module" --standard iso17825
```

## What Happens

1. **Cryptographic asset inventory:** Claude asks for the cryptographic operations, algorithms, key material, and implementation details of the target component.
2. **Leakage surface analysis:** Maps potential leakage points — power, EM, timing — for each cryptographic operation.
3. **Attack potential scoring:** Applies JIL methodology to score attack potential (elapsed time, expertise, knowledge, access, equipment).
4. **Countermeasure assessment:** Evaluates masking, hiding, and detection countermeasures for effectiveness and residual risk.
5. **Output generation:** Produces a physical SCA assessment with PhysicalSCAFinding entities, JIL scores, and ISO 17825 status.

## Attack Classes Covered

| Class | Techniques |
|-------|-----------|
| Power analysis | SPA, DPA, CPA, higher-order DPA |
| EM analysis | EMA, DEMA, near-field probing |
| Fault injection | Voltage glitch, clock glitch, laser FI, EM FI |
| Combined | Fault + side-channel, multi-modal attacks |
| Leakage assessment | TVLA (fixed vs random), specific t-test |

## Output

The assessment is saved as a `physical-sca-assessment` DocumentEnvelope with PhysicalSCAFinding entities, JIL score summaries, ISO 17825 status, and countermeasure effectiveness table.

## Next Step

After physical SCA assessment, findings can feed into:
- `/soc-security:verify` — generate verification properties for countermeasure correctness
- `/soc-security:comply` — map findings to FIPS 140-3 Level 3+ and ISO 17825 requirements
- `/soc-security:brief` — translate SCA findings for executive audiences

## Skill Reference

This command invokes the [physical-sca-skill](../physical-sca-skill/SKILL.md). See also:
- [sca-assessment-methodology.md](../physical-sca-skill/references/sca-assessment-methodology.md) — SCA analysis methodology
- [jil-scoring-guide.md](../physical-sca-skill/references/jil-scoring-guide.md) — JIL attack potential scoring
- [physical-sca-review.md](../shared-references/soc-security/verification-patterns/checklist-templates/physical-sca-review.md) — SCA assessment checklist
