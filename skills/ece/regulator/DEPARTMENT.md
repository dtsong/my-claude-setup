---
name: "Regulator Department"
executive: "Regulator"
color: "Silver"
description: "IEC-60601, FDA 510(k)/PMA, ISO 13485, ISO 14971 risk management"
---

# Regulator Department — Silver Lens

The Regulator's department of focused skills for regulatory strategy, risk management, and standards compliance planning.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [regulatory-strategy](regulatory-strategy/SKILL.md) | Determine optimal regulatory pathway and submission strategy for a medical device | default | `regulatory`, `pathway`, `510(k)`, `PMA`, `De Novo`, `classification`, `predicate`, `submission` |
| [risk-management](risk-management/SKILL.md) | Develop ISO 14971-compliant risk management file for a medical device design | default | `risk`, `hazard`, `ISO 14971`, `FMEA`, `risk analysis`, `severity`, `probability`, `risk control` |
| [iec60601-review](iec60601-review/SKILL.md) | Conduct IEC 60601-1 compliance gap analysis for a medical device design | default | `IEC 60601`, `compliance`, `gap analysis`, `general requirements`, `particular standard`, `collateral` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Request involves FDA pathway selection, device classification, predicate analysis, or submission strategy | regulatory-strategy | High |
| Request involves ISO 14971 risk analysis, hazard identification, FMEA, or risk control measures | risk-management | High |
| Request involves IEC 60601-1 compliance, gap analysis, or particular/collateral standard applicability | iec60601-review | High |
| Request mentions 510(k), PMA, De Novo, product code, or device class | regulatory-strategy | Medium |
| Request mentions risk acceptability, severity ratings, or benefit-risk analysis | risk-management | Medium |
| Request mentions EMC per -1-2, usability per -1-6, alarms per -1-8, or applied part classification | iec60601-review | Medium |
| Request mentions design controls, DHF, or design history file organization | regulatory-strategy | Medium |
| Request mentions essential performance identification or basic safety | iec60601-review | Medium |

## Shared Directives

Load Directive, Handoff Protocol, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
