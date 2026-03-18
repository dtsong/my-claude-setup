---
name: SUITE_NAME
description: >
  TRIGGER_DESCRIPTION. Use when USER_CONTEXT. Routes to specialists for CAPABILITIES.
---

# SUITE_NAME

## Purpose
One-sentence description of what this skill suite does.

## Classification
- If REQUEST_TYPE_A → load `skills/specialist-a/SKILL.md`
- If REQUEST_TYPE_B → load `skills/specialist-b/SKILL.md`
- Default → load `skills/specialist-a/SKILL.md`

## Skill Registry
| Skill | Path | Purpose | Model Tier |
|-------|------|---------|------------|
| specialist-a | `skills/specialist-a/SKILL.md` | Does X | analytical |
| specialist-b | `skills/specialist-b/SKILL.md` | Does Y | reasoning |

## Load Directive
Read ONLY the relevant specialist SKILL.md based on classification above. Do not pre-load multiple specialists.

## Handoff Protocol
Pass between skills as structured JSON:
```json
{
  "source_skill": "specialist-a",
  "findings": [],
  "confidence": "high|medium|low"
}
```
