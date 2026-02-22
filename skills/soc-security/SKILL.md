---
name: soc-security-skills
description: >
  Use this skill when performing hardware security analysis for System-on-Chip
  components — threat modeling, verification scaffolding, compliance mapping,
  executive briefing, microarchitectural attack analysis, physical side-channel
  assessment, kernel security analysis, emerging hardware security, or TLA+
  formal specification. Routes to the appropriate specialist. Trigger phrases
  include "threat model my SoC", "run STRIDE analysis", "generate SVA
  assertions", "compliance check against FIPS", "executive summary of
  findings", "Spectre analysis for cache", "DPA attack assessment", "kernel
  hardening review", "PQC hardware review", "TLA+ spec for access control".
  Do NOT use for software-only security, network security, or web application
  security.
model:
  preferred: sonnet
  acceptable: [sonnet, opus]
  minimum: sonnet
  allow_downgrade: true
  reasoning_demand: low
---

# SoC Security Skills

## Purpose

Routes SoC hardware security analysis requests to the appropriate specialist skill.

## Classification

- If threat modeling, STRIDE, attack trees, or standards-derived threat extraction → load `skills/threat-model-skill/SKILL.md`
- If verification planning, SVA assertions, or security checklists → load `skills/verification-scaffold-skill/SKILL.md`
- If compliance mapping, gap analysis, FIPS 140-3, or ISO 21434 → load `skills/compliance-pipeline-skill/SKILL.md`
- If executive briefing, risk register, or board/CISO updates → load `skills/executive-brief-skill/SKILL.md`
- If Spectre, Meltdown, MDS, cache side-channels, or branch predictor attacks → load `skills/microarch-attack-skill/SKILL.md`
- If DPA, SPA, fault injection, JIL scoring, or ISO 17825 → load `skills/physical-sca-skill/SKILL.md`
- If kernel security, KASLR, IOMMU, seccomp, or privilege escalation → load `skills/kernel-security-skill/SKILL.md`
- If PQC, chiplets, UCIe, heterogeneous compute, or AI accelerator security → load `skills/emerging-hw-security-skill/SKILL.md`
- If TLA+, formal verification, or safety/liveness properties → load `skills/tlaplus-security-skill/SKILL.md`
- Default: If request involves threat identification → threat-model-skill. Otherwise ask to clarify.

## Skill Registry

| Skill | Path | Purpose | Model |
|-------|------|---------|-------|
| threat-model | `skills/threat-model-skill/SKILL.md` | STRIDE + attack tree threat identification | sonnet |
| verification-scaffold | `skills/verification-scaffold-skill/SKILL.md` | Tiered verification checklists + SVA templates | sonnet |
| compliance-pipeline | `skills/compliance-pipeline-skill/SKILL.md` | Standards compliance mapping + gap analysis | sonnet |
| executive-brief | `skills/executive-brief-skill/SKILL.md` | 4-layer abstraction executive communication | sonnet |
| microarch-attack | `skills/microarch-attack-skill/SKILL.md` | Transient execution + cache side-channel analysis | opus |
| physical-sca | `skills/physical-sca-skill/SKILL.md` | JIL scoring + ISO 17825 side-channel assessment | opus |
| kernel-security | `skills/kernel-security-skill/SKILL.md` | Kernel hardening + isolation boundary analysis | sonnet |
| emerging-hw-security | `skills/emerging-hw-security-skill/SKILL.md` | PQC + chiplet + heterogeneous compute security | sonnet |
| tlaplus-security | `skills/tlaplus-security-skill/SKILL.md` | TLA+ formal security property specification | opus |

## Load Directive

Read ONLY the relevant specialist SKILL.md based on classification above. Do not pre-load multiple specialists. If the request spans multiple specialists, complete one specialist's full procedure before loading the next.

## Handoff Protocol

Pass between skills as structured data:
```json
{
  "source_skill": "skill-name",
  "entity_type": "ThreatFindings|VerificationChecklist|ComplianceState|BriefSections|...",
  "findings": [],
  "confidence_summary": {"CONFIRMED": 0, "INFERRED": 0, "SPECULATIVE": 0}
}
```
Downstream skills consume upstream entity types. See `shared-references/soc-security/entity-schema.md` for type definitions.
