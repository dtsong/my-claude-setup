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

## Load Directive

Load one specialist skill at a time using the Skill tool. Read the classification logic table to select the appropriate specialist, then invoke the skill. Do not pre-load multiple specialists simultaneously.

## Handoff Protocol

When the specialist skill output reveals issues in another department's domain:
1. Complete the current skill's output format.
2. Note the cross-domain findings in the output.
3. Recommend loading the appropriate department and skill (e.g., "Hand off protocol verification needs to cipher/protocol-analysis for state machine security analysis").
