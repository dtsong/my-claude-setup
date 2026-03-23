---
name: "Strategist Department"
executive: "Strategist"
color: "Gold"
description: "Business value, scope, MVP, prioritization"
---

# Strategist Department — Gold Lens

The Strategist's department of focused skills for maximizing business impact through disciplined scoping, prioritization, and measurement.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [mvp-scoping](mvp-scoping/SKILL.md) | MoSCoW prioritization and value-effort matrix | default | `MVP`, `scope`, `priority`, `phase`, `launch`, `v1` |
| [impact-estimation](impact-estimation/SKILL.md) | RICE scoring for feature prioritization | default | `impact`, `effort`, `ROI`, `value`, `metric`, `KPI` |
| [analytics-design](analytics-design/SKILL.md) | Telemetry events, A/B test instrumentation, success metrics | default | `analytics`, `telemetry`, `tracking`, `A/B test`, `funnel`, `metric` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| MVP, scope, priority, phase, launch, v1, minimum viable, cut scope, roadmap | mvp-scoping | High |
| Impact, effort, ROI, RICE, scoring, prioritize features, compare initiatives | impact-estimation | High |
| Analytics, telemetry, tracking, A/B test, funnel, experiment, instrumentation | analytics-design | High |
| KPI, success metric, measurement strategy without experimentation context | impact-estimation | Medium |
| Feature evaluation with both scoping and measurement needs | mvp-scoping then analytics-design | Medium |

## Shared Directives

Load Directive, Handoff Protocol, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
