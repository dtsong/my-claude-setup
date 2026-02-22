---
name: verify
description: Generate tiered verification checklists and SVA assertion templates from threat findings
---

# /soc-security:verify

Generate verification scaffolding from threat model findings. This command activates the verification-scaffold-skill to produce tiered verification items — SVA assertion templates, protocol checks, and information-flow specifications.

## Usage

```
/soc-security:verify
/soc-security:verify "Generate verification checklist for the TDISP threat model"
/soc-security:verify --tier 1              # Mechanical checks only (access control, FSM, registers)
/soc-security:verify --tier 2              # Protocol checks (DICE, CXL, SPDM handshakes)
/soc-security:verify --tier 3              # Information flow specs (side-channel, timing)
```

## What Happens

1. **Input loading:** Claude reads the threat model output (ThreatFinding entities). If no threat model exists, prompts you to run `/soc-security:threat-model` first or provide threat findings inline.
2. **Threat-to-verification mapping:** Each ThreatFinding is mapped to one or more VerificationItem entities, inheriting confidence tiers from the upstream threat analysis.
3. **Tier assignment:** Each verification item is classified into one of three tiers:

| Tier | Name | Scope | Output |
|------|------|-------|--------|
| 1 | Mechanical | Access control, FSM state coverage, register lock-down | SVA assertion templates (high confidence) |
| 2 | Protocol | DICE handshake, CXL.cache coherence, SPDM session state | SVA assertion templates (needs review) |
| 3 | Information Flow | Side-channel, data-dependent timing, covert channels | Natural language specification only |

4. **SVA generation (Tier 1 & 2):** Generates assertion templates with mandatory annotations:
   - `// INTENT:` — What the assertion is checking
   - `// DOES NOT CHECK:` — What is explicitly out of scope
   - Status: `[TEMPLATE]` (needs signal customization) or `[READY]` (uses provided RTL signals)
5. **Coverage boundary:** Documents what the checklist covers and does NOT cover.
6. **Output generation:** Produces a verification checklist in DocumentEnvelope format.

## Output

The verification checklist is saved to your working folder as `verification-checklist.md`.

## Important: Scaffolds, Not Solutions

Every artifact this command produces is a starting point. SVA assertion templates require signal-level customization by the verification engineer. Never treat generated assertions as production-ready verification IP.

## Next Step

After verification scaffolding, use `/soc-security:comply` to map verification results to compliance requirements.

## Skill Reference

This command invokes the [verification-scaffold-skill](../verification-scaffold-skill/SKILL.md). See also:
- [verification-methodology.md](../verification-scaffold-skill/references/verification-methodology.md) — tier definitions and mapping rules
- [sva-authoring-guide.md](../verification-scaffold-skill/references/sva-authoring-guide.md) — SVA template conventions and annotation format
- [verification-patterns/](../shared-references/soc-security/verification-patterns/) — SVA templates and checklist templates
