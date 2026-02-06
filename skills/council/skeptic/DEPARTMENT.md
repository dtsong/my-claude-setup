---
name: "Skeptic Department"
executive: "Skeptic"
color: "Red"
description: "Risk assessment, security analysis, failure mode discovery"
---

# Skeptic Department — Red Lens

The Skeptic's department of focused skills for stress-testing proposals, finding risks, and hardening designs.

## Skills

| Skill | Purpose | Triggers |
|-------|---------|----------|
| [threat-model](threat-model/SKILL.md) | STRIDE-based security threat analysis | `security`, `auth`, `threat`, `attack`, `vulnerability` |
| [failure-mode-analysis](failure-mode-analysis/SKILL.md) | Systematic failure scenario discovery and mitigations | `failure`, `error`, `crash`, `downtime`, `resilience` |
| [edge-case-enumeration](edge-case-enumeration/SKILL.md) | Exhaustive edge case discovery for features | `edge case`, `boundary`, `empty state`, `concurrent`, `race condition` |

## When This Department Activates

The Skeptic gets +2 bonus for any auth/security-related work. Threat modeling is loaded for any feature touching authentication, authorization, or sensitive data. Failure mode analysis is loaded for infrastructure changes. Edge case enumeration is loaded for complex user-facing features.

## Department Philosophy

If it can fail, it will fail. Design for the failure case first. Every risk comes with a mitigation — constructive, not destructive. Calibrate severity: distinguish "will break in production" from "theoretical concern."
