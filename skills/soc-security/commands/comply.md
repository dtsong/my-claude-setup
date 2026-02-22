---
name: comply
description: Run compliance mapping and gap analysis against security standards (FIPS, ISO 21434, DICE, TDISP)
---

# /soc-security:comply

Run the compliance pipeline. This command activates the compliance-pipeline-skill to map security requirements to compliance evidence, identify gaps, and produce traceability matrices.

## Usage

```
/soc-security:comply
/soc-security:comply "Map TDISP requirements to FIPS 140-3"
/soc-security:comply --standard fips-140-3
/soc-security:comply --standard iso-21434 --family automotive
/soc-security:comply --cross-family          # Compare compliance across SoC families
```

## What Happens

### Stage 1: Requirements Extraction

1. Claude reads upstream SecurityRequirement entities from the threat model. If none exist, extracts requirements directly from provided spec text.
2. Each requirement is structured with: source spec, clause reference, domain, SoC family, security property, implementation layer.
3. Requirements tagged with confidence tier based on extraction source.

### Stage 2: Evidence Mapping

4. Each requirement is mapped to available compliance evidence:
   - SVA results from verification-scaffold-skill output
   - Simulation logs, test reports, design documents
   - Review records and manual attestations
5. Coverage status assigned: `covered`, `partial`, `gap`, `not-applicable`.
6. Critical distinction maintained: "no evidence found" vs. "requirement not met".

### Stage 3: Gap Analysis

7. Gaps identified and categorized by severity and remediation effort.
8. Cross-family analysis shows which gaps are family-specific vs. shared.
9. Traceability matrix links: Spec Requirement -> Security Requirement -> Threat Finding -> Verification Item -> Evidence -> Compliance Result.

## Compliance Standards

| Standard | Domain | Typical Use |
|----------|--------|-------------|
| FIPS 140-3 | Cryptographic module security | Data-center, government SoCs |
| ISO 21434 | Automotive cybersecurity | Automotive SoCs |
| TCG DICE v1.2 | Hardware root of trust | All SoC families |
| TDISP 1.0 | Device isolation | Data-center, compute SoCs |
| CXL 3.1 Security | Memory expansion security | Data-center SoCs |
| SPDM v1.4 | Secure protocol messaging | All SoC families |

## Output

The compliance matrix is saved to your working folder as `compliance-matrix.md` with full traceability in DocumentEnvelope format.

## Next Step

After compliance mapping, use `/soc-security:brief` to translate findings into audience-calibrated executive communication.

## Skill Reference

This command invokes the [compliance-pipeline-skill](../compliance-pipeline-skill/SKILL.md). See also:
- [compliance-methodology.md](../compliance-pipeline-skill/references/compliance-methodology.md) — 3-stage pipeline methodology
- [cross-family-analysis.md](../compliance-pipeline-skill/references/cross-family-analysis.md) — cross-family traceability patterns
- [standards-registry/](../shared-references/soc-security/standards-registry/) — spec requirement extracts
