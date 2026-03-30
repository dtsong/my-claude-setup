---
name: "Accountant Department"
executive: "Accountant"
color: "Emerald"
description: "Accounting domain expertise, professional standards, practitioner workflows"
---

# Accountant Department — Emerald Lens

The Accountant's department of focused skills for financial reporting, tax compliance, audit methodology, and accounting workflow automation.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [core/reconciliation](core/reconciliation/SKILL.md) | Bank and GL reconciliation workflows | default | `reconciliation`, `bank rec`, `GL`, `balance`, `clearing` |
| [core/journal-engine](core/journal-engine/SKILL.md) | Double-entry journal creation and validation | default | `journal entry`, `debit`, `credit`, `double-entry`, `posting` |
| [tax/tax-research](tax/tax-research/SKILL.md) | IRC and regulation lookup methodology | default | `tax`, `IRC`, `deduction`, `tax code`, `compliance`, `1099`, `W-2` |
| [audit/risk-assessment](audit/risk-assessment/SKILL.md) | Audit risk assessment and sampling design | default | `audit`, `risk`, `sampling`, `materiality`, `assertion`, `SOX` |
| [reporting/financial-statements](reporting/financial-statements/SKILL.md) | Financial statement preparation and disclosure | default | `financial statements`, `balance sheet`, `income statement`, `cash flow`, `disclosure`, `footnote` |
| [advisory/variance-analysis](advisory/variance-analysis/SKILL.md) | Budget vs actual variance analysis | default | `variance`, `budget`, `actual`, `forecast`, `KPI`, `trend` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Request involves bank reconciliation, GL account clearing, or balance verification | core/reconciliation | High |
| Request involves creating, validating, or reversing journal entries | core/journal-engine | High |
| Request involves tax code research, IRC sections, deductions, or compliance | tax/tax-research | High |
| Request involves audit planning, risk assessment, sampling, or SOX testing | audit/risk-assessment | High |
| Request involves financial statement preparation, GAAP disclosure, or reporting | reporting/financial-statements | High |
| Request involves budget vs actual analysis, variance explanation, or forecasting | advisory/variance-analysis | High |
| Request mentions general accounting workflow or chart of accounts setup | core/journal-engine | Medium |
| Request mentions regulatory compliance without specifying tax or audit | tax/tax-research | Medium |

## Shared Directives

Load Directive, Handoff Protocol, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
