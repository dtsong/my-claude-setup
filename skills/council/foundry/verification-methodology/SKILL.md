---
name: verification-methodology
department: "foundry"
description: "Use when designing verification environments, planning coverage-driven closure, or architecting UVM testbenches. Covers constrained-random stimulus, functional coverage models, assertion-based verification, formal property checking, and coverage closure planning. Do not use for RTL design flow (use chip-design-flow) or SoC integration (use soc-integration)."
version: 1
triggers:
  - "UVM"
  - "verification"
  - "coverage"
  - "constrained random"
  - "assertions"
  - "formal"
  - "testbench"
  - "functional coverage"
  - "coverage closure"
---

# Verification Methodology

## Purpose

Design verification environments and coverage-driven closure plans that prove functional correctness of RTL designs through structured stimulus generation, coverage modeling, and assertion-based checking.

## Scope Constraints

Reviews RTL specifications and existing verification infrastructure. Does not execute simulations or formal tools. Does not modify RTL or testbench code.

## Inputs

- RTL design specification or block description
- Verification requirements (features to verify, corner cases)
- Target coverage metrics (functional, code, assertion)
- Existing testbench infrastructure, if any
- Formal verification scope, if applicable

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Define verification plan
- [ ] Step 2: Architect UVM testbench
- [ ] Step 3: Design coverage model
- [ ] Step 4: Plan constrained-random stimulus
- [ ] Step 5: Define assertion strategy
- [ ] Step 6: Plan coverage closure

### Step 1: Define Verification Plan

- Extract features from specification and enumerate verification items.
- Classify each item by complexity and risk (high/medium/low).
- Map features to verification methods: directed test, constrained-random, formal.
- Define pass/fail criteria for each verification item.
- Set coverage targets per feature group.

### Step 2: Architect UVM Testbench

- Define testbench hierarchy: test, env, agent, driver, monitor, scoreboard.
- Specify interface connections and virtual interface binding.
- Design sequence library with base sequences and derived scenarios.
- Plan scoreboard architecture: reference model, comparison strategy.
- Define configuration objects for testbench parameterization.

### Step 3: Design Coverage Model

- Define functional coverage groups aligned with verification plan features.
- Specify coverpoints for key design parameters and state variables.
- Define cross-coverage for critical parameter combinations.
- Set per-bin and per-covergroup targets (default 100% for critical, 95% for standard).
- Plan coverage exclusions with documented justification.

### Step 4: Plan Constrained-Random Stimulus

- Define transaction-level stimulus classes with randomizable fields.
- Specify constraints that target coverage holes and corner cases.
- Plan constraint layering: base constraints, scenario-specific, directed.
- Design weighted distributions to bias toward interesting scenarios.
- Identify fields requiring special constraint attention (boundary values, illegal combinations).

### Step 5: Define Assertion Strategy

- Write interface protocol assertions (bus handshake, flow control).
- Define internal design assertions (FSM transitions, data path integrity).
- Specify liveness properties (eventually responds, eventually completes).
- Plan assertion coverage tracking (how many assertions fired/covered).
- Identify candidates for formal proof vs simulation-based checking.

### Step 6: Plan Coverage Closure

- Define regression suite structure: sanity, nightly, weekly.
- Plan seed management for reproducibility.
- Set coverage merge strategy across regression runs.
- Define coverage closure criteria for sign-off.
- Plan for hole analysis: identify uncovered bins and write targeted tests.

> **Compaction resilience**: If context was lost, re-read the Inputs section for the design under verification, check the Progress Checklist, then resume from the earliest incomplete step.

## Output Format

### Verification Plan Summary

| Feature | Method | Coverage Target | Priority | Status |
|---------|--------|----------------|----------|--------|
| Bus protocol | UVM + formal | 100% | P0 | ... |
| Data path | Constrained-random | 95% | P0 | ... |
| Error handling | Directed + random | 100% | P1 | ... |

### Coverage Model

| Coverage Group | Coverpoints | Cross-Coverage | Target |
|---------------|-------------|----------------|--------|
| `cg_bus_txn` | addr, size, burst | addr x size | 100% |
| ... | ... | ... | ... |

## Handoff

- Hand off to chip-design-flow for RTL coding style or synthesis guidance.
- Hand off to soc-integration for SoC-level verification planning.
- Hand off to prover/formal-spec for complex formal property specification.

## Quality Checks

- [ ] All specification features mapped to verification items
- [ ] UVM testbench hierarchy defined with component responsibilities
- [ ] Functional coverage model aligned with verification plan
- [ ] Constrained-random strategy targets coverage holes
- [ ] Interface and internal assertions specified
- [ ] Regression suite structure and coverage merge planned
- [ ] Coverage closure criteria defined for sign-off

## Evolution Notes
<!-- Observations appended after each use -->
