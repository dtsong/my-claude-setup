---
name: "Tuner Department"
executive: "Tuner"
color: "Amber"
description: "Performance, scalability, optimization, capacity planning"
---

# Tuner Department — Amber Lens

The Tuner's department of focused skills for performance optimization, caching architecture, and capacity planning.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [performance-audit](performance-audit/SKILL.md) | Bottleneck identification and optimization roadmap | default | `performance`, `slow`, `bottleneck`, `Core Web Vitals`, `lighthouse`, `profiling` |
| [caching-strategy](caching-strategy/SKILL.md) | Cache hierarchy design with TTL and invalidation | default | `cache`, `caching`, `CDN`, `stale`, `invalidation`, `TTL` |
| [load-modeling](load-modeling/SKILL.md) | Capacity planning and scaling projections | default | `load`, `scale`, `capacity`, `throughput`, `concurrent`, `benchmark` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Mentions slow page loads, LCP, CLS, INP, Lighthouse scores, or profiling | performance-audit | High |
| Requests cache design, TTL policies, CDN configuration, or invalidation flows | caching-strategy | High |
| Asks about capacity planning, scaling triggers, load testing, or cost projections | load-modeling | High |
| Reports high latency without specifying whether it is rendering, caching, or infrastructure | performance-audit | Medium |
| Mentions scaling concerns that could involve both caching and capacity planning | load-modeling | Medium |

## Shared Directives

Load Directive, Handoff Protocol, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
