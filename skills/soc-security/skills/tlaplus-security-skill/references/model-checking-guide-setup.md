# TLC Model Checking Guide — Configuration and Basic Setup

## TLC Overview

TLC is an explicit-state model checker for TLA+ specifications. It works by:

1. **Enumerating all initial states** satisfying the `Init` predicate
2. **Computing all successor states** by applying the `Next` relation
3. **Checking invariants** in every reachable state
4. **Checking temporal properties** across all behaviors (execution paths)
5. **Reporting violations** as counterexample traces from initial state to violation

TLC is **exhaustive within the finite state space** — if a property holds for all states TLC explores, no finite counterexample exists within that configuration. However, TLC cannot prove properties for unbounded systems; it only confirms them for the specific constant instantiation.

### What TLC Can and Cannot Do

| TLC Can | TLC Cannot |
|---------|------------|
| Exhaustively check finite state spaces | Prove properties for infinite-state systems |
| Find counterexamples (violation traces) | Handle real-time or continuous-time properties |
| Check safety invariants | Model probabilistic behaviors |
| Check temporal (liveness) properties with fairness | Handle unbounded data structures without constraints |
| Detect deadlocks | Scale to arbitrarily large state spaces |
| Apply symmetry reduction | Verify timing or performance properties |

---

## Configuration

### CONSTANTS

Constants define the finite instantiation of the specification. Choose the smallest values that exercise the property meaningfully.

```
CONSTANTS
    \* Enumerate finite sets by listing elements
    Domains = {d1, d2, d3}
    Resources = {r1, r2}
    MaxEpoch = 5

    \* Model values (opaque identifiers — TLC optimized)
    d1 = d1    \* Use "model value" type in TLC, not ordinary assignment
    d2 = d2
    d3 = d3
```

**Guidance for choosing constant sizes:**

| Property Type | Minimum Constants | Why |
|---------------|------------------|-----|
| Mutual exclusion / isolation | 2-3 domains, 2 resources | Need at least 2 contending entities |
| Authentication protocol | 2 identities, 2-3 nonces | Need requester + responder, multiple attempts |
| Key lifecycle | MaxEpoch = 3-5 | Need generation + rotation + destruction |
| Noninterference | 2 high vals, 2 low vals | Need variation in both domains |
| Boot chain | 3-4 layers | Need enough layers to test chain properties |
| Anti-rollback | MaxVersion = 4-5 | Need room for forward and backward attempts |

### SYMMETRY

Symmetry sets tell TLC that certain constant values are interchangeable, reducing the state space by the factorial of the set size.

```
SYMMETRY
    Permutations(Domains)     \* If d1, d2, d3 are interchangeable
    Permutations(Resources)   \* If r1, r2 are interchangeable
```

**When symmetry is valid:**
- All entities in the set play identical roles in the specification
- No constant is referenced individually in any property or action guard
- The initial state treats all entities identically

**When symmetry is NOT valid:**
- One entity has a special role (e.g., `TSM` is distinguished from `Domains`)
- The initial state assigns different values to different entities
- A property references a specific entity by name

**Warning:** Invalid symmetry declarations produce incorrect results silently — TLC will not warn you. Verify symmetry validity carefully.

### CONSTRAINT (State Constraints)

State constraints bound the state space by excluding states where variables exceed limits.

```
CONSTRAINT
    counter <= 10
    Len(messageQueue) <= 5
    Cardinality(activeSet) <= 8
```

**When to use constraints:**
- Unbounded variables (counters, sequences) that would create infinite state spaces
- Reducing state space for feasibility when exhaustive checking is too expensive
- Bounding attacker capabilities (maximum number of attack attempts)

**When NOT to use constraints:**
- Constraining the variable would exclude states where the security property could be violated
- The bound is so tight that no interesting behavior is explored

**Always document:** What behaviors are excluded by the constraint and whether any security-relevant scenarios are lost.

### PROPERTY and INVARIANT

TLC checks two kinds of properties:

```
\* INVARIANT: must hold in every reachable state
INVARIANT
    TypeInvariant
    SafetyInvariant
    AccessControlCheck

\* PROPERTY: temporal formula that must hold for all behaviors
PROPERTY
    [][NoRegression]_vars          \* Safety temporal
    EventualAuthentication          \* Liveness
    EpochMonotonic                  \* Safety temporal
```

**Key distinction:**
- `INVARIANT P` checks `P` in every reachable state — equivalent to `[]P` but more efficient
- `PROPERTY P` checks temporal formula `P` over all behaviors — required for `[]`, `<>`, `~>`, `[][...]_vars`

**Performance tip:** Use `INVARIANT` for state predicates whenever possible — TLC checks invariants more efficiently than equivalent temporal properties.

---

## Quick Reference: TLC Configuration Template

```
---- CONFIG [ModuleName] ----

CONSTANTS
    Const1 = {val1, val2, val3}
    Const2 = {val4, val5}
    MaxBound = 5

SYMMETRY
    Permutations(Const1)

CONSTRAINT
    StateConstraint

INIT
    Init

NEXT
    Next

INVARIANTS
    TypeInvariant
    SecurityInvariant1
    SecurityInvariant2

PROPERTIES
    TemporalProperty1
    TemporalProperty2

CHECK_DEADLOCK
    TRUE    \* or FALSE to disable
```
