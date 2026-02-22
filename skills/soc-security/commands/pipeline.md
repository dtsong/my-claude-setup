---
name: pipeline
description: Run the full SoC security analysis pipeline — threat model through executive brief in one session
---

# /soc-security:pipeline

Run the complete security analysis pipeline from threat modeling through executive communication. This command orchestrates all 4 skills in sequence, checking in with you at each transition point.

## Usage

```
/soc-security:pipeline
/soc-security:pipeline "Analyze the TDISP device assignment flow for data-center SoCs"
```

## Pipeline Stages

```
Stage 1: THREAT MODEL      Stage 2: VERIFY           Stage 3: COMPLY          Stage 4: BRIEF
   |                          |                          |                        |
   v                          v                          v                        v
Identify threats          Generate verification      Map requirements         Translate findings
with STRIDE analysis      checklists and SVA         to compliance evidence   for executive audience
and spec grounding        assertion templates        with gap analysis

   |                          |                          |                        |
   v                          v                          v                        v
SecurityRequirements     VerificationChecklist       ComplianceState          ExecutiveBrief
 + ThreatFindings        (Tier 1/2/3 items)        (gaps + evidence)        (4-layer abstraction)
   |                          |                          |                        |
   v                          v                          v                        v
[You review]             [You review]               [You review]             [You review]
```

## What Happens

### Stage 1: Threat Model (30-60 min)
- Describe the component, provide spec sections and security boundary
- Claude performs STRIDE analysis with spec-grounded requirements extraction
- Produces threat model with SecurityRequirement and ThreatFinding entities
- Attack surface checklist: each area marked ANALYZED or NOT ANALYZED
- **Checkpoint:** Review findings, adjust scope if needed

### Stage 2: Verification Scaffold (20-30 min)
- Claude maps each threat to tiered verification items
- Generates SVA assertion templates (Tier 1/2) and natural-language specs (Tier 3)
- Every assertion annotated with INTENT and DOES NOT CHECK
- **Checkpoint:** Review verification items, confirm coverage

### Stage 3: Compliance Mapping (20-30 min)
- Claude maps requirements to compliance evidence
- Gap analysis distinguishes "no evidence" from "not met"
- Cross-family traceability if multiple SoC families involved
- **Checkpoint:** Review compliance gaps, prioritize remediation

### Stage 4: Executive Brief (15-20 min)
- Claude translates findings through 4-layer abstraction
- Audience-calibrated output (board, CISO, or program level)
- BLUF-first format with risk summary table
- **Checkpoint:** Review brief, request alternative audience renderings

### Total: ~90-140 min for a complete security analysis package

## Output

All artifacts are saved to your working folder:
- `threat-model.md`
- `verification-checklist.md`
- `compliance-matrix.md`
- `executive-brief.md`

## Stopping and Resuming

You can stop the pipeline at any checkpoint and resume later. Each stage's output is saved independently, so you can:
- Run threat modeling today, verification tomorrow
- Stop after compliance mapping if you need engineering input
- Re-run executive brief with different audience targets
- Skip stages if you already have upstream artifacts

## When to Use /soc-security:pipeline vs. Individual Commands

| Situation | Use |
|-----------|-----|
| Full analysis, threat model to executive brief | `/soc-security:pipeline` |
| Just need to identify threats for a component | `/soc-security:threat-model` |
| Already have threats, need verification scaffolding | `/soc-security:verify` |
| Map existing verification to compliance standards | `/soc-security:comply` |
| Translate existing findings for executives | `/soc-security:brief` |
