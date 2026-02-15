---
name: formal-spec
department: "prover"
description: "Use when writing formal specifications in TLA+ to verify system properties, defining state variables, configuring TLC model checker, and documenting assumptions and limitations. Covers safety and liveness properties for protocols and concurrent systems. Do not use for security claim enumeration without specification intent (use invariant-analysis)."
version: 1
triggers:
  - "formal"
  - "TLA+"
  - "PlusCal"
  - "specification"
  - "model checking"
  - "temporal logic"
  - "state machine"
  - "safety property"
  - "liveness"
  - "refinement"
---

# Formal Spec

## Purpose
Extract properties from a system design, define state variables, write TLA+ specifications, identify invariants, configure the TLC model checker, and document assumptions and limitations.

## Scope Constraints

Reads system designs, protocol descriptions, and existing specifications. Produces TLA+ specification files as output. Does not execute model checkers or modify implementation code.

## Inputs
- System design or protocol description to formalize
- Security properties that should hold (informally stated)
- Concurrency model (number of processes, shared state, communication mechanism)
- Scope constraints (bounded checking parameters)
- Existing informal specification or documentation

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Extract properties from design
- [ ] Step 2: Define state variables
- [ ] Step 3: Write TLA+ specification
- [ ] Step 4: Identify invariants
- [ ] Step 5: Configure model checker
- [ ] Step 6: Document assumptions and limitations

### Step 1: Extract Properties from Design
Translate informal requirements into candidate formal properties:
- **Safety properties**: "Bad thing never happens" — e.g., "No two processes hold the lock simultaneously"
- **Liveness properties**: "Good thing eventually happens" — e.g., "Every request eventually gets a response"
- **Security properties**: "Unauthorized access never occurs" — e.g., "A process at EL0 never reads EL1 memory"
- Classify each property as safety (invariant) or liveness (temporal)
- Identify the state variables each property depends on

### Step 2: Define State Variables
Define the formal state space:
- Enumerate all state variables (process states, shared variables, message channels)
- Define the type/domain of each variable
- Specify the initial state (Init predicate)
- Identify which variables are shared vs. local to each process
- Define the granularity of state transitions (atomic actions)

### Step 3: Write TLA+ Specification
Produce a TLA+ module:
- **Module declaration** with EXTENDS (Integers, Sequences, FiniteSets, TLC)
- **Constants** for parameterizable bounds (NUM_PROCESSES, MAX_VALUE, etc.)
- **Variables** with type invariant
- **Init** predicate defining initial state
- **Next** predicate as disjunction of all possible actions
- **Actions** as individual state transitions with enabling conditions and effects
- **Fairness** conditions if liveness properties require them

### Step 4: Identify Invariants
Define the key invariants to check:
- Type invariant (state variables stay within their domains)
- Safety invariants (extracted from Step 1)
- Security invariants (access control, information flow, integrity)
- Structural invariants (data structure consistency)
- Express each invariant as a TLA+ state predicate

### Step 5: Configure Model Checker
Set up TLC model checking configuration:
- Define model constants (specific values for CONSTANTS)
- Set state constraint (bound the state space for feasibility)
- Select invariants and temporal properties to check
- Configure symmetry sets to reduce state space
- Estimate state space size and checking time
- Document what the bounded check covers and what it does not

### Step 6: Document Assumptions and Limitations
Explicitly state:
- Environmental assumptions (fair scheduling, reliable channels, bounded processes)
- Abstraction choices (what was simplified or omitted from the model)
- Bounded verification limits (the check covers N=3 processes, not N=arbitrary)
- What a successful check guarantees and what it does not
- Recommendations for increasing confidence (larger bounds, different abstractions, proof)

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what system is being analyzed, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Output Format

### Property Table

| ID | Property | Type | TLA+ Expression | Status |
|----|----------|------|-----------------|--------|
| S1 | Mutual exclusion | Safety | `MutualExclusion == \A p1, p2 \in Procs: ...` | Verified (N<=5) |
| L1 | Starvation freedom | Liveness | `\A p \in Procs: []<>(state[p] = "done")` | Requires fairness |
| ... | ... | ... | ... | ... |

### TLA+ Specification
```tla
---- MODULE [Name] ----
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS NUM_PROCS

VARIABLES state, shared

vars == <<state, shared>>

TypeInvariant == ...

Init == ...

Action1(p) == ...

Next == \E p \in 1..NUM_PROCS: Action1(p) \/ ...

Spec == Init /\ [][Next]_vars /\ Fairness

====
```

### Model Checking Configuration
- Constants: NUM_PROCS = 3
- State constraint: [Bound description]
- Invariants checked: [List]
- Estimated states: [N]
- Estimated time: [T]

### Assumptions and Limitations
- [Assumption 1]: [Justification]
- [Limitation 1]: [What is not covered]

## Handoff

- Hand off to invariant-analysis if additional security claims need enumeration before specification.
- Hand off to the requesting department for implementation of verified properties.

## Quality Checks
- [ ] All informal security properties formalized as TLA+ predicates
- [ ] State variables fully defined with types and initial values
- [ ] Actions cover all possible state transitions
- [ ] Invariants include both type invariant and security invariants
- [ ] Model checker configured with reasonable bounds
- [ ] State space is feasible to check (or bounds are documented)
- [ ] Assumptions and limitations are explicitly documented
- [ ] Fairness conditions specified if liveness properties are checked

## Evolution Notes
<!-- Observations appended after each use -->
