# Formal Methods — TLA+ Patterns for Security Properties

## Purpose

This reference provides TLA+ specification patterns for common hardware security properties. These patterns serve as starting templates for the tlaplus-security-skill when formalizing security claims from threat models, verification scaffolds, and compliance requirements. Each pattern captures a canonical security property shape that recurs across SoC security domains.

**Primary consumers:** tlaplus-security-skill (specification generation, refinement checking)
**Secondary consumers:** verification-scaffold-skill (formal tier mapping), threat-model-skill (verifiability assessment)

---

## Quick Reference

| Pattern | Security Property | Applicability |
|---|---|---|
| Exclusive Access Invariant | Isolation, Access Control | Bus firewalls, TEE memory, TDI state |
| One-Way State Progression | Integrity, Freshness | Fuse locks, monotonic counters, lifecycle FSMs |
| Noninterference | Confidentiality, Isolation | Cross-domain information flow |
| Authentication State Machine | Authenticity | SPDM, DICE, debug unlock |
| Key Lifecycle | Freshness, Confidentiality | Key generation, rotation, destruction |
| State Machine Refinement | Formal Verifiability | Protocol FSM vs. implementation FSM |
| Measurement Chain Integrity | Integrity, Attestation | DICE CDI chain, boot measurement |
| Mutual Exclusion with Priority | Availability, Isolation | Shared resource arbitration |
| Anti-Rollback Counter | Freshness, Integrity | Firmware rollback prevention |
| Speculation Boundary Safety | Speculation Safety | Speculative access domain checks |

---

## Pattern Definitions

### 1. Exclusive Access Invariant

**Security Property:** Isolation, Access Control

**Description:** Ensures that at most one security domain can access a protected resource at any time, and only when authorized. This pattern models bus firewalls, TEE memory isolation, and TDI device assignment.

**TLA+ Template:**

```tla
---- MODULE ExclusiveAccess ----
EXTENDS Naturals, FiniteSets

CONSTANTS Domains, Resources, AuthorizedPairs
\* AuthorizedPairs \subseteq Domains \times Resources

VARIABLES owner, accessState

TypeInvariant ==
    /\ owner \in [Resources -> Domains \union {\"none\"}]
    /\ accessState \in [Resources -> {\"free\", \"locked\"}]

ExclusiveAccessInvariant ==
    \A r \in Resources :
        accessState[r] = \"locked\" =>
            /\ owner[r] /= \"none\"
            /\ <<owner[r], r>> \in AuthorizedPairs

NoSimultaneousAccess ==
    \A r \in Resources :
        Cardinality({d \in Domains : owner[r] = d}) <= 1

SafetyProperty == ExclusiveAccessInvariant /\ NoSimultaneousAccess
====
```

**Assumptions:**
- Authorization relation (AuthorizedPairs) is static during the checked epoch
- Domain identifiers are trustworthy (no spoofing at this abstraction level)

**Limitations:**
- Does not model timing-based contention or priority inversion
- Does not capture side-channel leakage through shared microarchitectural state

**When to Use:** Verifying bus firewall configurations, TEE memory partition isolation, TDISP TDI device assignment exclusivity.

---

### 2. One-Way State Progression

**Security Property:** Integrity, Freshness

**Description:** Models state that can only advance forward and never regress. Captures fuse-blow irreversibility, monotonic counters, and security lifecycle FSMs where backward transitions constitute security violations.

**TLA+ Template:**

```tla
---- MODULE OneWayProgression ----
EXTENDS Naturals

CONSTANTS MaxState
ASSUME MaxState \in Nat

VARIABLES state

TypeInvariant == state \in 0..MaxState

Init == state = 0

Advance == state < MaxState /\ state' = state + 1

NoRegression == [][state' >= state]_state

Next == Advance \/ UNCHANGED state

Spec == Init /\ [][Next]_state

THEOREM Spec => NoRegression
====
```

**Assumptions:**
- State transitions are atomic at this abstraction level
- The hardware mechanism enforcing one-way progression is trusted (e.g., OTP fuses, hardware counter)

**Limitations:**
- Does not model fault injection that might bypass the one-way mechanism
- Abstraction does not distinguish between different physical implementations (fuse vs. counter)

**When to Use:** Verifying monotonic anti-rollback counters, OTP fuse state progression, security lifecycle FSMs (e.g., manufacturing to deployment to locked).

---

### 3. Noninterference

**Security Property:** Confidentiality, Isolation

**Description:** Formalizes the property that actions by a high-security domain produce no observable effect on the low-security domain's view of the system. This is the canonical information-flow security property.

**TLA+ Template:**

```tla
---- MODULE Noninterference ----
EXTENDS Naturals

CONSTANTS HighVals, LowVals, Actions
VARIABLES highState, lowState

TypeInvariant ==
    /\ highState \in HighVals
    /\ lowState \in LowVals

LowProjection(s) == s.lowState

HighAction(a) == a \in {\"high_write\", \"high_compute\"}
LowAction(a) == a \in {\"low_read\", \"low_write\"}

\* Noninterference: for any two states s1, s2 that agree on lowState,
\* executing a high action from s1 and s2 yields states that still
\* agree on lowState.
\*
\* Checked by verifying:
\*   LowProjection(Step(s1, highAction)) = LowProjection(Step(s2, highAction))
\*   whenever LowProjection(s1) = LowProjection(s2)

NoninterferenceInvariant ==
    \* In practice, instantiate with concrete Step operator
    \* and check via refinement or symmetry reduction.
    TRUE \* placeholder — instantiate per design

\* Downgrading exception: explicit declassification must be
\* modeled as an authorized channel with its own invariants.
====
```

**Assumptions:**
- Security domains are well-defined and static during the checked epoch
- The low-observation function (LowProjection) accurately captures what the attacker can observe
- No covert channels through timing or resource contention (these require separate analysis)

**Limitations:**
- Noninterference is undecidable in general; TLC checks only finite instantiations
- Does not capture probabilistic or timing-based information flow
- Declassification (intentional information release) requires explicit modeling

**When to Use:** Verifying cross-domain isolation in TEEs, CXL multi-host memory partitioning, bus firewall information flow properties.

---

### 4. Authentication State Machine

**Security Property:** Authenticity

**Description:** Models a challenge-response authentication protocol as a state machine. Verifies that the authenticated state is reachable only through the correct protocol sequence and that no shortcut or bypass path exists.

**TLA+ Template:**

```tla
---- MODULE AuthStateMachine ----
EXTENDS Naturals, Sequences

CONSTANTS Identities, Nonces, Keys

VARIABLES
    authState,    \* \in {\"idle\", \"challenged\", \"responded\", \"authenticated\", \"failed\"}
    challenger,   \* identity of the verifier
    responder,    \* identity of the prover
    nonce,        \* current challenge nonce
    attempts      \* failed attempt counter

TypeInvariant ==
    /\ authState \in {\"idle\", \"challenged\", \"responded\", \"authenticated\", \"failed\"}
    /\ attempts \in Nat

Init ==
    /\ authState = \"idle\"
    /\ attempts = 0

Challenge(id, n) ==
    /\ authState = \"idle\"
    /\ challenger' = id
    /\ nonce' = n
    /\ authState' = \"challenged\"
    /\ UNCHANGED <<responder, attempts>>

Respond(id, proof) ==
    /\ authState = \"challenged\"
    /\ responder' = id
    /\ authState' = \"responded\"
    /\ UNCHANGED <<challenger, nonce, attempts>>

Verify(valid) ==
    /\ authState = \"responded\"
    /\ IF valid
       THEN authState' = \"authenticated\"
       ELSE /\ authState' = \"idle\"
            /\ attempts' = attempts + 1
    /\ UNCHANGED <<challenger, responder, nonce>>

\* Safety: authenticated state requires valid protocol traversal
NoAuthBypass ==
    authState = \"authenticated\" =>
        \* The state machine must have passed through challenged -> responded -> authenticated
        TRUE \* enforced by transition structure

\* Liveness: a valid prover eventually authenticates (under fairness)
EventualAuth == <>(authState = \"authenticated\")
====
```

**Assumptions:**
- Cryptographic primitives are ideal (signatures/MACs cannot be forged)
- Nonces are unique and unpredictable
- Communication channel integrity is assumed (or separately verified)

**Limitations:**
- Does not model computational cryptographic security
- Liveness depends on fairness assumptions about the environment
- Does not capture timing attacks on the authentication protocol

**When to Use:** Verifying SPDM authentication handshake, DICE identity verification, debug unlock challenge-response, TDISP TDI authentication.

---

### 5. Key Lifecycle

**Security Property:** Freshness, Confidentiality

**Description:** Models the complete lifecycle of a cryptographic key from generation through active use, rotation, and destruction. Verifies that keys are never used outside their valid epoch and that destruction is irreversible.

**TLA+ Template:**

```tla
---- MODULE KeyLifecycle ----
EXTENDS Naturals

CONSTANTS MaxEpoch
VARIABLES keyState, epoch, keyMaterial

States == {\"uninitialized\", \"generating\", \"active\", \"rotating\", \"deprecated\", \"destroyed\"}

TypeInvariant ==
    /\ keyState \in States
    /\ epoch \in 0..MaxEpoch

Init ==
    /\ keyState = \"uninitialized\"
    /\ epoch = 0

Generate ==
    /\ keyState = \"uninitialized\"
    /\ keyState' = \"active\"
    /\ epoch' = 1
    /\ UNCHANGED keyMaterial

Rotate ==
    /\ keyState = \"active\"
    /\ epoch < MaxEpoch
    /\ keyState' = \"active\"
    /\ epoch' = epoch + 1

Deprecate ==
    /\ keyState = \"active\"
    /\ keyState' = \"deprecated\"
    /\ UNCHANGED epoch

Destroy ==
    /\ keyState \in {\"active\", \"deprecated\"}
    /\ keyState' = \"destroyed\"
    /\ UNCHANGED epoch

\* Safety: destroyed keys are never reactivated
NoResurrection == [][keyState = \"destroyed\" => keyState' = \"destroyed\"]_keyState

\* Safety: key used only when active
UseOnlyWhenActive ==
    \* Operations referencing key material must check keyState = \"active\"
    TRUE \* enforced by gating operations on keyState

\* Epoch monotonicity
EpochMonotonic == [][epoch' >= epoch]_epoch
====
```

**Assumptions:**
- Key material zeroization is effective (hardware guarantees)
- Epoch transitions are atomic
- Key generation uses a trusted entropy source

**Limitations:**
- Does not model key compromise or side-channel extraction
- Does not capture key escrow or backup scenarios
- Hardware zeroization effectiveness is assumed, not verified

**When to Use:** Verifying PCIe IDE key rotation, DICE CDI epoch management, TEE sealing key lifecycle, SPDM session key management.

---

### 6. State Machine Refinement

**Security Property:** Formal Verifiability

**Description:** Establishes a refinement mapping between a high-level protocol specification and a lower-level implementation state machine. Verifies that the implementation correctly implements the protocol by showing every implementation behavior is permitted by the specification.

**TLA+ Template:**

```tla
---- MODULE Refinement ----
EXTENDS Naturals

\* ---- High-Level Spec ----
CONSTANTS SpecStates, SpecInit, SpecTransitions
VARIABLES specState

SpecTypeInv == specState \in SpecStates
SpecInitPred == specState = SpecInit
SpecNext == \E t \in SpecTransitions : specState' = t[2] /\ specState = t[1]

\* ---- Implementation ----
CONSTANTS ImplStates, ImplInit
VARIABLES implState, implDetail

ImplTypeInv == implState \in ImplStates

\* Refinement mapping: maps implementation state to spec state
RefMap(is) ==
    \* Define per-design: maps each implState to the corresponding specState
    CASE is = ImplInit -> SpecInit
    [] OTHER -> specState \* placeholder

\* Refinement invariant: the mapped implementation state is always
\* a valid spec state, and the mapped behavior satisfies SpecNext.
RefinementInvariant ==
    RefMap(implState) \in SpecStates

\* Checked via:
\*   ImplSpec => SpecSpec  (refinement check in TLC)
\*   where ImplSpec substitutes RefMap(implState) for specState
====
```

**Assumptions:**
- The specification is correct and complete for the security property of interest
- The refinement mapping is total (every implementation state maps to a spec state)
- Stuttering steps in the implementation correspond to unchanged spec state

**Limitations:**
- Refinement checking is computationally expensive for large state spaces
- The mapping must be manually defined — errors in the mapping undermine the proof
- Does not verify properties not captured in the specification

**When to Use:** Verifying that an RTL-level FSM correctly implements the TDISP state machine spec, that a DICE implementation follows the CDI derivation protocol, or that an SPDM responder correctly implements the message exchange specification.

---

### 7. Measurement Chain Integrity

**Security Property:** Integrity, Attestation

**Description:** Models a layered measurement chain where each layer measures the next before transferring control. Verifies that the chain is unbroken and that any modification to a layer produces a detectably different measurement at the root.

**TLA+ Template:**

```tla
---- MODULE MeasurementChain ----
EXTENDS Naturals, Sequences

CONSTANTS NumLayers, HashFunc
VARIABLES measurements, bootProgress, compromised

TypeInvariant ==
    /\ measurements \in [1..NumLayers -> Nat]
    /\ bootProgress \in 0..NumLayers
    /\ compromised \in SUBSET (1..NumLayers)

Init ==
    /\ bootProgress = 0
    /\ compromised = {}

MeasureAndBoot(layer) ==
    /\ bootProgress = layer - 1
    /\ layer \in 1..NumLayers
    /\ measurements' = [measurements EXCEPT ![layer] = HashFunc(layer)]
    /\ bootProgress' = layer
    /\ UNCHANGED compromised

\* Safety: if any layer is compromised, the measurement chain
\* produces a different value from the golden reference
TamperDetection ==
    compromised /= {} =>
        \E l \in compromised : measurements[l] /= HashFunc(l)

\* Safety: measurements are write-once per boot cycle
MeasurementImmutability ==
    \A l \in 1..NumLayers :
        bootProgress >= l =>
            [][measurements[l]' = measurements[l]]_measurements[l]

\* Chain completeness: all layers measured before attestation
ChainComplete ==
    bootProgress = NumLayers =>
        \A l \in 1..NumLayers : measurements[l] = HashFunc(l) \/ l \in compromised
====
```

**Assumptions:**
- Hash function is collision-resistant (modeled as injective)
- Root of trust (layer 0) is immutable hardware
- Measurement registers are hardware-protected against firmware modification

**Limitations:**
- Does not model TOCTOU attacks between measurement and execution
- Hash collision resistance is assumed, not proven
- Does not capture measurement of dynamic/runtime state

**When to Use:** Verifying DICE CDI derivation chains, secure boot measurement sequences, SPDM measurement reporting completeness.

---

### 8. Mutual Exclusion with Priority

**Security Property:** Availability, Isolation

**Description:** Models shared resource arbitration where security-critical requestors have priority. Verifies that high-priority security operations are not starved by lower-priority traffic, while ensuring eventual service for all requestors.

**TLA+ Template:**

```tla
---- MODULE PriorityMutex ----
EXTENDS Naturals

CONSTANTS Requestors, Priority
\* Priority \in [Requestors -> Nat], higher = more critical

VARIABLES holder, waiting

TypeInvariant ==
    /\ holder \in Requestors \union {\"none\"}
    /\ waiting \subseteq Requestors

Init ==
    /\ holder = \"none\"
    /\ waiting = {}

Request(r) ==
    /\ holder /= r
    /\ waiting' = waiting \union {r}
    /\ UNCHANGED holder

Grant ==
    /\ holder = \"none\"
    /\ waiting /= {}
    /\ LET best == CHOOSE r \in waiting :
            \A s \in waiting : Priority[r] >= Priority[s]
       IN /\ holder' = best
          /\ waiting' = waiting \ {best}

Release ==
    /\ holder /= \"none\"
    /\ holder' = \"none\"
    /\ UNCHANGED waiting

\* Safety: mutual exclusion
MutualExclusion ==
    holder /= \"none\" => Cardinality({holder}) = 1

\* Liveness: no starvation (under weak fairness)
NoStarvation ==
    \A r \in Requestors : r \in waiting ~> holder = r
====
```

**Assumptions:**
- Priority assignments are static and trusted
- Request/grant/release are atomic at this abstraction level
- The arbiter hardware is correct and cannot be bypassed

**Limitations:**
- Does not model timing-based denial of service within a single grant
- Priority inversion through transitive dependencies is not captured
- Real hardware arbitration may have additional latency constraints

**When to Use:** Verifying crypto engine arbitration, bus bandwidth partitioning for security-critical traffic, shared cache partitioning fairness.

---

### 9. Anti-Rollback Counter

**Security Property:** Freshness, Integrity

**Description:** Models a monotonic counter used to prevent firmware rollback. Verifies that the counter value only increases, that firmware versions below the counter are rejected, and that the counter survives reset.

**TLA+ Template:**

```tla
---- MODULE AntiRollback ----
EXTENDS Naturals

CONSTANTS MaxVersion
VARIABLES counter, proposedVersion, decision

TypeInvariant ==
    /\ counter \in 0..MaxVersion
    /\ proposedVersion \in 0..MaxVersion
    /\ decision \in {\"pending\", \"accepted\", \"rejected\"}

Init ==
    /\ counter = 0
    /\ decision = \"pending\"

ProposeUpdate(v) ==
    /\ proposedVersion' = v
    /\ decision' = \"pending\"
    /\ UNCHANGED counter

EvaluateProposal ==
    /\ decision = \"pending\"
    /\ IF proposedVersion >= counter
       THEN /\ decision' = \"accepted\"
            /\ counter' = proposedVersion
       ELSE /\ decision' = \"rejected\"
            /\ UNCHANGED counter
    /\ UNCHANGED proposedVersion

\* Safety: counter never decreases
CounterMonotonic == [][counter' >= counter]_counter

\* Safety: rejected proposals never advance the counter
RejectionSafe ==
    decision = \"rejected\" => counter' = counter

\* Safety: old firmware is always rejected
RollbackPrevention ==
    proposedVersion < counter => decision /= \"accepted\"
====
```

**Assumptions:**
- Counter is stored in non-volatile, tamper-resistant storage (OTP or secure NVM)
- Counter update is atomic with firmware acceptance decision
- Counter survives power loss and reset

**Limitations:**
- Does not model physical attacks on the counter storage
- Does not capture the gap between counter check and firmware execution (TOCTOU)
- Maximum counter value creates a theoretical end-of-life scenario

**When to Use:** Verifying firmware anti-rollback mechanisms, DICE layer version enforcement, secure boot version policy.

---

### 10. Speculation Boundary Safety

**Security Property:** Speculation Safety

**Description:** Models the property that speculative execution does not access memory or resources outside the architecturally permitted domain. Captures the essence of Spectre-class boundary checks at an abstract level.

**TLA+ Template:**

```tla
---- MODULE SpeculationBoundary ----
EXTENDS Naturals

CONSTANTS Domains, MemoryRegions, DomainRegionMap
\* DomainRegionMap \in [Domains -> SUBSET MemoryRegions]

VARIABLES
    currentDomain,
    archAccess,       \* architecturally resolved access
    specAccess,       \* speculatively attempted access
    specResolved      \* whether speculation has resolved

TypeInvariant ==
    /\ currentDomain \in Domains
    /\ archAccess \in MemoryRegions \union {\"none\"}
    /\ specAccess \in MemoryRegions \union {\"none\"}
    /\ specResolved \in BOOLEAN

\* Safety: speculative access must not touch regions outside
\* the current domain's authorized set
SpeculationSafety ==
    specAccess /= \"none\" =>
        specAccess \in DomainRegionMap[currentDomain]

\* Safety: when speculation resolves, the result matches
\* architectural permission
ResolutionConsistency ==
    specResolved =>
        (archAccess /= \"none\" => archAccess \in DomainRegionMap[currentDomain])

\* Observable state invariant: speculative side-effects on
\* shared microarchitectural state do not leak cross-domain data
\* (abstracted as: specAccess domain = archAccess domain)
NoSpeculativeLeakage ==
    /\ specAccess /= \"none\"
    /\ archAccess /= \"none\"
    => specAccess \in DomainRegionMap[currentDomain]
====
```

**Assumptions:**
- Domain boundaries are correctly configured in architectural state
- The speculation model is an abstraction — real microarchitectural speculation is more complex
- Cache and branch predictor state are not explicitly modeled (they are the leakage channel, not the property)

**Limitations:**
- This is a high-level abstraction; real Spectre variants exploit specific microarchitectural structures
- Cannot capture timing-based leakage through cache state
- Meltdown-class attacks (where architectural checks are delayed) require a different model
- TLC state space may not capture all speculative execution paths in a real processor

**When to Use:** Reasoning about speculation barrier placement, domain transition speculation safety, understanding the abstract property that Spectre mitigations must enforce.

---

## Pattern Selection Guide

| Security Concern | Recommended Pattern(s) |
|---|---|
| TEE / VM memory isolation | Exclusive Access Invariant, Noninterference |
| Secure boot chain | Measurement Chain Integrity, One-Way State Progression |
| SPDM / DICE authentication | Authentication State Machine, State Machine Refinement |
| Key rotation (IDE, TEE) | Key Lifecycle, Anti-Rollback Counter |
| Bus firewall correctness | Exclusive Access Invariant, Noninterference |
| Firmware rollback prevention | Anti-Rollback Counter, One-Way State Progression |
| Shared resource fairness | Mutual Exclusion with Priority |
| Spectre-class mitigations | Speculation Boundary Safety, Noninterference |
| Protocol implementation correctness | State Machine Refinement |
| TDISP state machine | State Machine Refinement, Exclusive Access Invariant |

---

## Usage Notes for tlaplus-security-skill

1. **Start from a pattern, then specialize.** These patterns are templates — the skill should instantiate constants, refine variables, and add domain-specific transitions for the target design.

2. **State explicitly what is NOT modeled.** Every TLA+ specification has an abstraction boundary. Document what the model does not capture (timing, physical effects, implementation bugs below the abstraction level).

3. **Use TLC for finite model checking first.** Start with small constant values to validate the specification, then increase bounds. Infinite-state properties require manual proof or Isabelle/TLA+ proof integration.

4. **Compose patterns for complex properties.** Real security properties often combine patterns — e.g., an authenticated key lifecycle combines Authentication State Machine with Key Lifecycle.

5. **Trace to security properties.** Every specification should reference one or more properties from `security-properties.md` and one or more threats from the threat catalog.

---

*[FROM TRAINING] All TLA+ patterns in this file are derived from general formal methods knowledge and publicly available specification techniques. Specific protocol details should be verified against authoritative spec documents. Last verified: 2026-02-13.*
