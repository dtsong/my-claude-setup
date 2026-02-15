---
name: invariant-analysis
department: "prover"
description: "Use when enumerating security claims from a design, formalizing them as invariants, checking for hidden assumptions, and assessing verification feasibility. Covers safety invariants, temporal properties, and verification tool recommendations. Do not use for writing TLA+ specifications directly (use formal-spec) or implementation-level security review."
version: 1
triggers:
  - "invariant"
  - "property"
  - "safety"
  - "liveness"
  - "correctness"
  - "proof"
  - "assumption"
  - "verification"
  - "security claim"
  - "guarantee"
---

# Invariant Analysis

## Purpose
Enumerate security claims made by a design, formalize them as invariants, check for hidden assumptions, assess verification feasibility, and propose a specification approach for proving or disproving the claims.

## Scope Constraints

Reads system designs, security documentation, and existing formal specifications. Does not modify implementation code or execute verification tools. Does not access production systems for testing.

## Inputs
- System design with stated or implied security claims
- Threat model defining attacker capabilities
- Architecture documentation describing components and interactions
- Existing tests or verification results
- Constraints on verification effort (time, tools, expertise)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Step 1: Enumerate Security Claims
Extract all security claims from the design, whether explicit or implicit:
- **Explicit claims**: Stated in documentation ("the system ensures mutual exclusion")
- **Implicit claims**: Assumed but not stated ("processes always terminate")
- **Derived claims**: Inferred from the design ("if A holds and B holds, then C should hold")
- For each claim, identify who makes it, what components it depends on, and what could violate it

### Step 2: Formalize as Invariants
For each security claim, produce a formal invariant:
- Express the claim as a precise predicate over system state
- Classify as safety invariant (must hold in every reachable state) or temporal property
- Identify the state variables the invariant references
- Determine if the invariant is inductive (preserved by every action) or requires auxiliary lemmas
- Note invariants that cannot be expressed as simple state predicates (information flow, probabilistic)

### Step 3: Check for Hidden Assumptions
For each invariant, enumerate the assumptions required for it to hold:
- **Environmental**: "The network eventually delivers messages" — is this guaranteed?
- **Implementation**: "The RNG produces uniform random output" — has this been verified?
- **Threat model**: "The attacker cannot read kernel memory" — what if they can (Meltdown)?
- **Timing**: "Operations complete within T milliseconds" — is this a hard guarantee?
- Classify assumptions by verifiability: axiom (accepted), verifiable (can be checked), unverified (risk)

### Step 4: Assess Verification Feasibility
For each invariant, evaluate whether formal verification is practical:
- **State space**: How many states does the system have? Is bounded model checking feasible?
- **Decidability**: Is the property decidable for the system class? (Finite state? Parameterized? Infinite?)
- **Tool support**: Do existing tools (TLC, Spin, CBMC, Dafny) support this verification?
- **Abstraction**: Can the system be abstracted to make verification tractable without losing the property?
- **Effort**: How much effort (person-days) would verification require?

### Step 5: Propose Specification Approach
Recommend a verification strategy for the highest-priority invariants:
- **Full formal verification**: TLA+/TLC for protocol properties, Dafny/Coq for implementation
- **Bounded model checking**: TLC or CBMC for bounded instances
- **Property-based testing**: QuickCheck/Hypothesis as a lightweight alternative
- **Runtime monitoring**: Instrument invariants as runtime assertions for production
- For each approach, state what it guarantees and what it does not

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what system is being analyzed, then resume from the earliest incomplete step.

## Output Format

### Security Claims Inventory

| ID | Claim | Type | Source | Formalized | Assumptions |
|----|-------|------|--------|------------|-------------|
| I1 | "No unauthorized memory access" | Safety | Design doc 3.2 | `\A p: access[p] => authorized[p]` | MMU enabled, no HW bugs |
| I2 | "All requests eventually complete" | Liveness | Implicit | `\A r: []<>(status[r] = "done")` | Fair scheduling, no deadlock |
| ... | ... | ... | ... | ... | ... |

### Hidden Assumption Analysis

| Invariant | Assumption | Category | Verifiable? | Risk if Violated |
|-----------|-----------|----------|-------------|------------------|
| I1 | MMU correctly configured | Implementation | Yes — audit kernel config | Critical — full bypass |
| I2 | No circular wait | Design | Yes — deadlock analysis | High — livelock |
| ... | ... | ... | ... | ... |

### Verification Feasibility Matrix

| Invariant | State Space | Tool | Approach | Effort | Confidence |
|-----------|------------|------|----------|--------|------------|
| I1 | ~10^6 (bounded) | TLC | Model checking, N<=4 | 3 days | High (bounded) |
| I2 | Infinite | — | Runtime monitoring | 1 day | Medium |
| ... | ... | ... | ... | ... | ... |

### Recommended Verification Strategy
1. [Highest priority invariant]: [Approach] — [Justification]
2. [Next priority]: [Approach] — [Justification]
3. ...

## Handoff

- Hand off to formal-spec if high-priority invariants should be formally specified in TLA+.
- Hand off to the requesting department for implementation of the recommended verification approach.

## Quality Checks
- [ ] All explicit and implicit security claims enumerated
- [ ] Each claim formalized as a precise predicate
- [ ] Hidden assumptions identified and classified by verifiability
- [ ] Verification feasibility assessed with state space estimates
- [ ] Tool recommendations match the invariant class (safety/liveness/information flow)
- [ ] Verification effort estimated realistically
- [ ] Approach recommendations include both guarantees and limitations

## Evolution Notes
<!-- Observations appended after each use -->
