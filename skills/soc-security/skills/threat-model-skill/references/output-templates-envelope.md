# Output Templates — DocumentEnvelope and Frontmatter

## Table of Contents

- [Quick Reference](#quick-reference)
- [DocumentEnvelope Template](#2-documentenvelope-template)
- [Envelope Rules](#envelope-rules)

---

## Quick Reference

| Template | Use When | Required Fields |
|----------|----------|----------------|
| ThreatFinding Entity | Every individual threat identified | id, title, threatStatement, confidenceTier, severity, attackVector, sourceGrounding |
| DocumentEnvelope | Wrapping the complete threat model output | type, id, title, dates, confidenceSummary, caveats |
| Attack Surface Checklist | Every threat model output (mandatory) | All 7 standard surfaces with ANALYZED/NOT ANALYZED |
| Coverage Boundary | Every threat model output (mandatory) | analyzed, notAnalyzed lists |
| Confidence Summary | Every threat model output (mandatory) | Counts of all 4 tiers |
| Findings Ledger Entry | Significant findings (CRITICAL/HIGH) | date, domain, family, finding, reusability |
| Attack Tree | When attack tree framework is used | root goal, paths, leaf annotations, cut sets |

---

## 2. DocumentEnvelope Template

Every persisted threat model uses this envelope format.

```yaml
---
type: threat-model
id: "TM-[YYYY]-[NNN]"
title: "[Component Name] Threat Model — [Technology Domain(s)]"
created: "[YYYY-MM-DD]"
updated: "[YYYY-MM-DD]"
soc-family:
  - "[family 1]"
  - "[family 2]"
technology-domain:
  - "[domain 1]"
  - "[domain 2]"
standards:
  - "[Standard Name] [Version]"
  - "[Standard Name] [Version]"
related-documents:
  - "[TM-YYYY-NNN]"      # Prior threat models
  - "[VC-YYYY-NNN]"      # Related verification checklists
  - "[CM-YYYY-NNN]"      # Related compliance matrices
status: "draft"           # draft | reviewed | approved
confidence-summary:
  grounded: "[count]"
  inferred: "[count]"
  speculative: "[count]"
  absent: "[count]"
caveats: |
  LLM-generated draft. All findings are candidates for expert review.
  Items marked INFERRED or SPECULATIVE require human verification before
  use in security decisions. Items marked ABSENT represent known attack
  surfaces that were NOT analyzed in this engagement.
  NOT ANALYZED: [comma-separated list of surfaces not covered]
---
```

### Envelope Rules

1. **`id` format:** Always `TM-YYYY-NNN` where YYYY is the year and NNN is sequential
2. **`title` format:** Always `[Component] Threat Model — [Domain(s)]`
3. **`status`:** New outputs are always `draft`. Only the engineer can promote to `reviewed` or `approved`
4. **`confidence-summary`:** Must match the actual counts in the findings. Validated at output time.
5. **`caveats`:** Must be specific to this analysis, not generic boilerplate. List specific surfaces not covered.
6. **`related-documents`:** Include all known related document IDs. Cross-reference is mandatory.
