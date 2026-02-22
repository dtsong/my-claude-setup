# TLC Model Checking Guide — State Space Management and Abstraction Techniques

## Understanding State Space Size

The raw state space is the product of all variable domain sizes:

```
Example: TDISP Access Control
  tdiState: 4 states per TDI, 2 TDIs = 4^2 = 16
  tdiOwner: 4 values per TDI (3 domains + unassigned), 2 TDIs = 4^2 = 16
  dmaEnabled: 2 per TDI, 2 TDIs = 2^2 = 4
  accessAttempt: 3 values = 3

  Raw state space: 16 * 16 * 4 * 3 = 3,072
  Reachable states: typically much smaller (many states are unreachable)
```

## State Space Explosion Indicators

| Symptom | Cause | Remedy |
|---------|-------|--------|
| TLC runs for hours with no termination | State space too large | Add constraints, reduce constants |
| Memory exhaustion (OutOfMemoryError) | Too many distinct states | Increase heap, add symmetry, reduce constants |
| Billions of states with small constants | Combinatorial explosion from set/sequence variables | Bound set cardinalities, limit sequence lengths |
| State space grows exponentially with one constant | That constant is in an exponent position | Identify and reduce it first |

## Abstraction Techniques

When the state space is too large, apply these abstractions in order:

### 1. Reduce Constant Cardinalities

Start with the smallest values that exercise the property. Increase only if needed.

```
Instead of:   Domains = {d1, d2, d3, d4, d5}
Try:          Domains = {d1, d2}       \* 2 is enough for mutual exclusion
```

### 2. Apply Symmetry Reduction

If constants represent interchangeable entities, symmetry reduces state space by up to N! for a set of size N.

```
3 symmetric domains: 6x reduction
4 symmetric domains: 24x reduction
5 symmetric domains: 120x reduction
```

### 3. Add State Constraints

Bound counters, sequence lengths, and set cardinalities:

```
CONSTRAINT
    counter <= 5                      \* Bound counters
    Len(messageBuffer) <= 3           \* Bound sequences
    Cardinality(activeConns) <= 4     \* Bound sets
```

### 4. Merge Equivalent States

If two variable values are indistinguishable for the property being checked, merge them:

```
\* Instead of tracking exact nonce values:
nonce \in {n1, n2, n3, n4, n5}

\* Track only "fresh" vs "used":
nonceStatus \in {"fresh", "used"}
```

### 5. Abstract Away Irrelevant Details

Remove variables that do not affect the property under check:

```
\* If checking access control, timer details may be irrelevant:
\* Remove: implTimer \in 0..MaxTimer
\* This eliminates MaxTimer+1 multiplier on state space
```

## State Space Estimation Worksheet

```
State Space Estimation
======================
Variable          Domain Size    Notes
-------------------------------------------
var1              |D1|           [description]
var2              |D2|           [description]
var3              |D3|           [description]
...

Raw product:      |D1| * |D2| * |D3| * ...
Symmetry factor:  / N!          (if applicable)
Constraint factor: * reduction   (estimated)
-------------------------------------------
Estimated states: [number]

Feasibility:
  < 10^6:    Feasible (minutes)
  10^6-10^8: Feasible (hours, use multiple workers)
  10^8-10^10: Borderline (may require overnight run, add constraints)
  > 10^10:   Infeasible (must abstract further)
```

---

## Security-Specific Modeling Tips

### Modeling the Attacker as Environment

In security specifications, the attacker is part of the system's environment. Model the attacker as nondeterministic actions that represent all possible attacker behaviors within their capability:

```tla
\* Attacker can propose any version (including old ones)
AttackerProposeUpdate ==
    \E v \in 0..MaxVersion :
        ProposeUpdate(v)

\* Attacker can send any message in the protocol
AttackerSendMessage ==
    \E m \in AttackerMessages :
        ReceiveMessage(m)

\* Attacker can attempt access from any domain
AttackerAccessAttempt ==
    \E d \in Domains, r \in Resources :
        AttemptAccess(d, r)
```

**Key principle:** The attacker is modeled as a maximally nondeterministic agent bounded only by their stated capabilities. TLC explores all possible attacker behaviors within these bounds.

### Bounding Attacker Capabilities

The attacker model must be bounded for finite model checking. Document the bounds explicitly as assumptions:

```tla
\* Attacker capabilities (bounded for model checking)
CONSTANTS
    MaxAttackerAttempts,    \* Maximum number of attack attempts
    AttackerMessages,       \* Set of messages attacker can construct
    AttackerDomains         \* Domains attacker controls

\* Assumption: attacker cannot:
\*   - Forge cryptographic signatures (ideal crypto)
\*   - Corrupt hardware state directly (no fault injection)
\*   - Observe internal state (only external interfaces)
```

**Warning:** Bounding attacker capabilities is the most security-critical modeling decision. Over-bounding (giving the attacker too little power) may miss real attacks. Under-bounding (giving too much power) may make the state space infeasible.

### Modeling Nondeterministic Interleavings

Concurrent security protocols must consider all possible interleavings of concurrent actions. TLC naturally explores all interleavings:

```tla
\* Two concurrent processes — TLC explores all interleavings
Next ==
    \/ Process1Action
    \/ Process2Action
    \/ AttackerAction
```

For security, this means TLC will find race conditions and TOCTOU vulnerabilities — any interleaving of legitimate and attacker actions that violates the security property.

### Modeling Crash and Reset

Security properties often need to hold across crashes and resets:

```tla
\* Model crash as nondeterministic loss of volatile state
Crash ==
    /\ volatileState' = initialVolatileState
    /\ UNCHANGED nonVolatileState  \* NVM survives crash

\* Security property: NVM-backed state survives crash
StateSurvivedCrash ==
    [][Crash => nonVolatileState' = nonVolatileState]_vars
```

### Modeling Timeout and Retry

```tla
\* Model timeout as nondeterministic action (can occur at any time)
Timeout ==
    /\ state \in {"waiting_response", "challenge_sent"}
    /\ state' = "timed_out"
    /\ retryCount' = retryCount + 1
    /\ UNCHANGED otherVars

\* Bound retries for feasibility
CONSTRAINT retryCount <= MaxRetries
```
