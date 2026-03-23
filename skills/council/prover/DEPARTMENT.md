---
name: "Prover Department"
executive: "Prover"
color: "Pearl"
description: "Formal methods, mathematical verification, security invariants, property specification"
---

# Prover Department — Pearl Lens

The Prover's department of focused skills for writing formal specifications, identifying security invariants, and assessing verification feasibility.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [formal-spec](formal-spec/SKILL.md) | Formal specification writing with TLA+ and model checking | default | `formal`, `TLA+`, `specification`, `model checking`, `temporal logic`, `state machine` |
| [invariant-analysis](invariant-analysis/SKILL.md) | Security invariant identification and verification assessment | default | `invariant`, `property`, `safety`, `liveness`, `correctness`, `proof` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Formal, TLA+, PlusCal, specification, model checking, temporal logic, refinement | formal-spec | High |
| Invariant, property, safety, liveness, correctness, proof, assumption, security claim | invariant-analysis | High |
| State machine design needing formal verification | formal-spec | Medium |
| Security claims needing enumeration before specification | invariant-analysis then formal-spec | Medium |

## Shared Directives

Load Directive, Handoff Protocol, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
