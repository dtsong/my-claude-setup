---
name: brief
description: Generate audience-adapted executive briefs from security findings (board, CISO, program level)
---

# /soc-security:brief

Generate executive communication. This command activates the executive-brief-skill to translate technical security findings through a 4-layer abstraction into audience-calibrated briefs.

## Usage

```
/soc-security:brief
/soc-security:brief "CISO brief on the TDISP compliance gaps"
/soc-security:brief --audience board
/soc-security:brief --audience ciso
/soc-security:brief --audience program
```

## What Happens

1. **Input loading:** Claude reads upstream findings — ThreatFindings, ComplianceResults, VerificationItems. If none exist, prompts for findings input.
2. **4-layer translation:** Each significant finding is translated through four layers of increasing abstraction:

```
Layer 0: Raw technical finding
    "DMA bypass via malformed TLP in TDISP handshake"
Layer 1: Security impact statement
    "Attacker with physical access can bypass memory isolation"
Layer 2: Business risk statement
    "Customer data in confidential AI pipelines may be exposed"
Layer 3: Executive action item
    "Prioritize fix in Q2 silicon respin. Cost: ~2-3 weeks. Risk if deferred: [consequence]"
```

3. **Audience calibration:** Output vocabulary, depth, and framing adapt to the target audience:

| Audience | Focus | Depth | Vocabulary |
|----------|-------|-------|------------|
| **Board** | Investment decisions, strategic risk | Highest abstraction, 1-2 pages | Business terms, no acronyms |
| **CISO** | Security posture, compliance exposure | Moderate detail, risk-focused | Security domain terms, limited acronyms |
| **Program** | Engineering priorities, timeline, resources | Most detail, action-oriented | Technical terms acceptable |

4. **BLUF (Bottom Line Up Front):** Every brief starts with the most critical risk, recommended action, and timeline.
5. **Risk summary table:** Aggregated findings with severity, trend, and confidence.
6. **Traceability appendix:** Maps every executive finding back to specific technical entities.

## Output

The executive brief is saved to your working folder as `executive-brief.md` (or `ciso-brief.md`, `board-brief.md`, `program-brief.md` depending on audience).

## Confidence Handling

Findings marked SPECULATIVE require explicit acknowledgment before appearing in executive briefs. ABSENT items appear as coverage gaps, not as risks.

## Skill Reference

This command invokes the [executive-brief-skill](../executive-brief-skill/SKILL.md). See also:
- [abstraction-methodology.md](../executive-brief-skill/references/abstraction-methodology.md) — 4-layer translation methodology
- [executive-templates.md](../executive-brief-skill/references/executive-templates.md) — brief structure templates per audience
- [executive-communication.md](../shared-references/soc-security/cross-cutting/executive-communication.md) — audience calibration guide
