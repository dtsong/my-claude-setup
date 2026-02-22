---
name: advanced-pipeline
description: Run the advanced analysis pipeline (microarch + physical SCA + kernel + emerging HW + formal verification)
---

# /soc-security:advanced-pipeline

Run the advanced analysis pipeline across all new skill domains, optionally feeding results into formal verification. This orchestrates the A0-A3 skills (microarch, physical SCA, kernel, emerging HW) and F0 (TLA+ formalization) in a structured sequence with review checkpoints.

## Usage

```
/soc-security:advanced-pipeline
/soc-security:advanced-pipeline "Full advanced analysis of our data-center SoC security subsystem"
/soc-security:advanced-pipeline --skills microarch,physical-sca,formalize
```

## What Happens

The advanced pipeline runs in stages with review checkpoints:

```
Stage 1: Advanced Analysis (parallel)
  ├── A0: microarch-attack-skill   → MicroarchAttackFindings
  ├── A1: physical-sca-skill       → PhysicalSCAFindings
  ├── A2: kernel-security-skill    → KernelSecFindings
  └── A3: emerging-hw-security-skill → EmergingHWFindings
      │
      ├── [REVIEW CHECKPOINT — engineer reviews findings]
      │
Stage 2: Formal Verification
  └── F0: tlaplus-security-skill   → FormalSecSpec
      │
      ├── [REVIEW CHECKPOINT — engineer reviews specs]
      │
Stage 3: Cross-Feed (optional)
  └── Feed A0-A3 findings into existing pipeline:
      → P1: verification-scaffold-skill
      → P2: compliance-pipeline-skill
      → P3: executive-brief-skill
```

### Stage 1: Advanced Analysis

Each skill runs on the same component description. Skills that are not applicable to the component are skipped with a rationale.

- **Microarch (A0):** Runs if the component has speculative execution or shared caches
- **Physical SCA (A1):** Runs if the component has cryptographic operations
- **Kernel Security (A2):** Runs if the component interacts with an OS kernel
- **Emerging HW (A3):** Runs if the component uses PQC, chiplets, heterogeneous compute, or AI accelerators

After Stage 1, Claude presents a consolidated findings summary for engineer review.

### Stage 2: Formal Verification

The tlaplus-security-skill selects the most critical findings from Stage 1 and formalizes their security properties. The engineer can request specific properties to formalize.

### Stage 3: Cross-Feed

Optionally, Stage 1 findings feed into the existing pipeline (P1-P3) for verification scaffolding, compliance mapping, and executive briefing.

## Skill Selection

Use `--skills` to run only specific skills:

| Flag | Skills |
|------|--------|
| `microarch` | A0 only |
| `physical-sca` | A1 only |
| `kernel` | A2 only |
| `emerging-hw` | A3 only |
| `formalize` | F0 only (requires upstream findings) |
| (default) | All applicable skills |

## Output

Each skill produces its own DocumentEnvelope. The pipeline also produces a consolidated summary document linking all outputs.

## Estimated Duration

- Single skill: 20-40 minutes
- Full pipeline (A0-A3 + F0): 90-150 minutes
- Full pipeline + cross-feed: 150-240 minutes

## Skill Reference

This command orchestrates:
- [microarch-attack-skill](../microarch-attack-skill/SKILL.md) (A0)
- [physical-sca-skill](../physical-sca-skill/SKILL.md) (A1)
- [kernel-security-skill](../kernel-security-skill/SKILL.md) (A2)
- [emerging-hw-security-skill](../emerging-hw-security-skill/SKILL.md) (A3)
- [tlaplus-security-skill](../tlaplus-security-skill/SKILL.md) (F0)
