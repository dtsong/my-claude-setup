---
name: "Operator Department"
executive: "Operator"
color: "Orange"
description: "DevOps, deployment, infrastructure, monitoring"
---

# Operator Department — Orange Lens

The Operator's department of focused skills for deployment pipelines, observability, and infrastructure cost management.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [deployment-plan](deployment-plan/SKILL.md) | Deployment strategy, rollback, and release planning | default | `deploy`, `rollback`, `release`, `staging`, `production` |
| [observability-design](observability-design/SKILL.md) | Monitoring, alerting, and logging strategy | default | `monitoring`, `alerting`, `logging`, `observability`, `Sentry` |
| [cost-analysis](cost-analysis/SKILL.md) | Infrastructure cost modeling and optimization | default | `cost`, `pricing`, `budget`, `compute`, `scaling` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Deploy, rollback, release, CI/CD, pipeline, blue-green, canary, staging, production | deployment-plan | High |
| Monitoring, alerting, logging, observability, Sentry, metrics, tracing, dashboard, SLO | observability-design | High |
| Cost, pricing, budget, compute, scaling, infrastructure cost, reserved instances, optimization | cost-analysis | High |
| Environment configuration, feature flags, zero-downtime | deployment-plan | Medium |
| Error budgets, burn rate, SLI definitions | observability-design | Medium |

## Load Directive

Load one specialist skill at a time using the Skill tool. Read the classification logic table to select the appropriate specialist, then invoke the skill. Do not pre-load multiple specialists simultaneously.

## Handoff Protocol

When the specialist skill output reveals issues in another department's domain:
1. Complete the current skill's output format.
2. Note the cross-domain findings in the output.
3. Recommend loading the appropriate department and skill (e.g., "Hand off performance-impacting infrastructure findings to tuner/performance-audit for optimization analysis").
