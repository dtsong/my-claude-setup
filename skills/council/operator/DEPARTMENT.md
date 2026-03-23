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

## Shared Directives

Load Directive, Handoff Protocol, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
