# TLC Model Checking Guide — Common Pitfalls, Debugging Traces, and Performance

## Common Pitfalls

### 1. State Space Explosion from Unbounded Variables

**Problem:** Variables like counters, sequences, or sets without explicit bounds create infinite or practically infinite state spaces.

**Symptom:** TLC runs indefinitely or crashes with memory errors.

**Fix:** Add state constraints or restructure variables:

```tla
\* BAD: unbounded counter
VARIABLES counter
counter' = counter + 1

\* GOOD: bounded counter
CONSTRAINT counter <= MaxCount
```

### 2. Infinite Sequences

**Problem:** Using `Seq(S)` as a variable type creates an infinite domain.

**Symptom:** TLC reports "Attempted to enumerate infinite set."

**Fix:** Use `BoundedSeq` or constrain sequence length:

```tla
\* BAD:
messages \in Seq(Messages)

\* GOOD:
CONSTRAINT Len(messages) <= MaxMsgLen
```

### 3. Missing UNCHANGED Clauses

**Problem:** Forgetting `UNCHANGED` for variables not modified by an action causes TLC to explore all possible next values for those variables.

**Symptom:** Unexpected state space explosion; invariant violations in states that should not be reachable.

**Fix:** Every action must specify the new value for every variable, either through assignment or `UNCHANGED`:

```tla
\* BAD: what happens to counter?
Action ==
    /\ state' = "next"
    \* counter is unconstrained!

\* GOOD:
Action ==
    /\ state' = "next"
    /\ UNCHANGED counter
```

### 4. Deadlock False Positives

**Problem:** TLC reports deadlock when no action in `Next` is enabled, but this may be intentional (e.g., a terminal "locked" state).

**Symptom:** "Deadlock reached" error for states that are intentionally absorbing.

**Fix:** Either disable deadlock checking or add a stuttering step:

```tla
\* Option 1: Disable in TLC configuration
Deadlock: disabled

\* Option 2: Add explicit stuttering for terminal states
Stutter ==
    /\ state = "locked"
    /\ UNCHANGED vars

Next == RealActions \/ Stutter
```

### 5. Liveness Properties Without Fairness

**Problem:** Liveness properties (`<>P`, `P ~> Q`) fail because TLC finds a behavior that stutters forever without taking the enabling action.

**Symptom:** Liveness violation with a counterexample showing infinite stuttering.

**Fix:** Add fairness conditions to the specification:

```tla
\* Weak fairness: if Action is continuously enabled, it eventually occurs
Fairness == WF_vars(Action)

Spec == Init /\ [][Next]_vars /\ Fairness
```

### 6. Symmetry Applied to Non-Symmetric Constants

**Problem:** Declaring symmetry for constants that are not truly interchangeable produces incorrect results.

**Symptom:** No error message — TLC silently produces wrong results (may miss real violations or report spurious ones).

**Fix:** Verify symmetry validity before declaring. If in doubt, do not use symmetry — correctness is more important than speed.

---

## Interpreting TLC Results

### Successful Verification

```
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 1.2E-15

State space:
  12,847 states generated, 3,412 distinct states found, 0 states left on queue.
  The depth of the complete state graph search is 23.
```

**What this means:**
- All reachable states (3,412) were checked against all invariants
- All behaviors were checked against all temporal properties
- No violation was found within this finite instantiation
- The property holds for constants of these sizes, but NOT proven for larger instantiations

**Fingerprint collision:** The probability that two distinct states were mapped to the same fingerprint (hash collision). If this is below 10^-10, the result is reliable.

### Invariant Violation

```
Error: Invariant SafetyInvariant is violated.

Error: The following behavior constitutes a counter-example:

State 1: <Initial predicate>
/\ state = "IDLE"
/\ authenticated = FALSE

State 2: <Action line 47, col 5 to line 52, col 30>
/\ state = "RUN"
/\ authenticated = FALSE
```

**What this means:**
- TLC found a reachable state where the invariant does not hold
- The trace shows the exact sequence of states from Init to the violation
- This is a real counterexample — the specification has a bug (or the system has a vulnerability)

**Action:** Analyze the trace. Either:
1. The specification has a bug (missing guard in a transition) — fix the spec
2. The system has a real security vulnerability — the trace shows the attack path
3. The invariant is too strong — the property needs to be weakened

### Temporal Property Violation

```
Error: Temporal properties were violated.

Error: The following behavior constitutes a counter-example:

State 1: ...
State 2: ...
...
State N: Back to state 3.   <--- cycle detected
```

**What this means:**
- TLC found a behavior (infinite execution path) that violates the temporal property
- For liveness violations, the trace typically shows a cycle where the desired state is never reached
- The "Back to state N" indicates where the cycle starts

**Action:**
1. Check if fairness assumptions are missing (most common cause of liveness violations)
2. Check if the cycle represents a real deadlock or livelock in the system
3. Verify that the temporal property is correctly specified

### Deadlock Detection

```
Error: Deadlock reached.

Error: The following behavior constitutes a counter-example:

State 1: ...
...
State N: <deadlock>
/\ state = "locked"
/\ waiting = {"req1", "req2"}
```

**What this means:**
- TLC reached a state where no action in `Next` is enabled
- This may be intentional (terminal state) or a bug (stuck state)

**Action:**
1. If the deadlock state is intentional, disable deadlock checking or add stuttering
2. If the deadlock state is unintentional, add a transition out of it or fix the guards

### State Space Exceeded

```
Error: TLC has run out of memory.
State space: 2,147,483,647 states generated (still running)
```

**Action:**
1. Reduce constant sizes
2. Apply symmetry reduction
3. Add state constraints
4. Abstract away irrelevant variables
5. Consider using TLC in disk-based mode (slower but uses disk for state storage)

---

## TLC Limitations for Security Verification

### Finite State Only

TLC checks properties within the finite state space defined by the constant instantiation. It does not prove properties for unbounded systems. For infinite-state properties, use the TLA+ proof system (TLAPS) or Isabelle/TLA+.

### No Real-Time

TLA+ and TLC have no notion of real time. Properties like "authentication must complete within 100ms" cannot be expressed or checked. Time-bounded properties require timed automata (UPPAAL) or real-time extensions.

### No Probabilistic Properties

TLC cannot check probabilistic properties like "attack succeeds with probability < 2^-128." Probabilistic security requires PRISM or similar probabilistic model checkers.

### No Side-Channel Analysis

TLC operates on the logical state machine level. Side channels through timing, power consumption, electromagnetic emissions, or cache state cannot be modeled or detected. Side-channel analysis requires specialized tools and physical measurement.

### Abstraction Gap

The TLA+ specification is an abstraction of the real system. The gap between the specification and the implementation is not checked by TLC. Bridging this gap requires:
- Refinement checking between abstraction levels
- Manual code review against the specification
- Property-based testing that checks implementation behaviors against spec-derived properties
