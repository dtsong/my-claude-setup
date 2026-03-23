---
name: "Skeptic Department"
executive: "Skeptic"
color: "Red"
description: "Risk assessment, security analysis, failure mode discovery"
---

# Skeptic Department — Red Lens

The Skeptic's department of focused skills for stress-testing proposals, finding risks, and hardening designs.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [threat-model](threat-model/SKILL.md) | STRIDE-based security threat analysis | default | `security`, `auth`, `threat`, `attack`, `vulnerability` |
| [failure-mode-analysis](failure-mode-analysis/SKILL.md) | Systematic failure scenario discovery and mitigations | default | `failure`, `error`, `crash`, `downtime`, `resilience` |
| [edge-case-enumeration](edge-case-enumeration/SKILL.md) | Exhaustive edge case discovery for features | default | `edge case`, `boundary`, `empty state`, `concurrent`, `race condition` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Security, authentication, authorization, threat, attack, vulnerability, XSS, injection, CSRF, token, encryption | threat-model | High |
| Failure, error, crash, downtime, resilience, availability, recovery, rollback, degradation, timeout, retry | failure-mode-analysis | High |
| Edge case, boundary, empty state, concurrent, race condition, validation, malformed, overflow, unicode, null | edge-case-enumeration | High |
| Permission model, role-based access, data sensitivity classification | threat-model | Medium |
| Infrastructure change with reliability SLA/SLO concerns | failure-mode-analysis | Medium |

## Shared Directives

Load Directive, Handoff Protocol, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
