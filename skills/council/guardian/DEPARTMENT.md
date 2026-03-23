---
name: "Guardian Department"
executive: "Guardian"
color: "Silver"
description: "Compliance review, data classification, audit trail design"
---

# Guardian Department — Silver Lens

The Guardian's department of focused skills for ensuring regulatory compliance, classifying data, and designing audit systems.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [compliance-review](compliance-review/SKILL.md) | GDPR/privacy compliance review with gap analysis | default | `GDPR`, `privacy`, `PII`, `compliance`, `consent`, `regulation` |
| [data-classification](data-classification/SKILL.md) | Data sensitivity classification and handling requirements | default | `data classification`, `PII`, `sensitive`, `confidential`, `public`, `internal` |
| [audit-trail-design](audit-trail-design/SKILL.md) | Audit logging design with event catalogs and retention | default | `audit`, `logging`, `trail`, `accountability`, `traceability` |

## Classification Logic

| Input Signal | Route To | Confidence |
|---|---|---|
| GDPR, CCPA, privacy regulation, consent flows, lawful basis, right to erasure | compliance-review | High |
| Data sensitivity tiers, PII inventory, encryption requirements, data handling policies | data-classification | High |
| Audit logging, event catalogs, immutable logs, forensic traceability, compliance reporting | audit-trail-design | High |
| New data model or external integration handling user data | data-classification | Medium |
| Feature requiring accountability or regulatory evidence without specifying audit design | audit-trail-design | Medium |

## Shared Directives

Load Directive, Handoff Protocol, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
