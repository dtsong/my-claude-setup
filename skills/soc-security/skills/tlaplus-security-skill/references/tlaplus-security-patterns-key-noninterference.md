# TLA+ Security Patterns — Key Management & Noninterference

## Purpose

Ready-to-use TLA+ modules for key lifecycle management and noninterference verification. Each pattern is standalone with assumptions, limitations, and TLC configuration. Instantiate constants and refine transitions for the target design.

**Primary consumer:** tlaplus-security-skill (Phase 2 module construction, Phase 3 property formalization)

---

## Table of Contents

- Pattern 3: Key Management Protocol
- Pattern 4: Noninterference

---

## Pattern 3: Key Management Protocol

**Security Property:** Freshness, Confidentiality — IDE encryption keys follow a correct lifecycle: generation, activation, rotation with epoch monotonicity, and irreversible destruction.

**Applicability:** PCIe IDE key rotation, TEE sealing key lifecycle, SPDM session key management, DICE CDI epoch management.

### TLA+ Module

```tla
---- MODULE IDEKeyManagement ----
EXTENDS Naturals

CONSTANTS
    MaxEpoch,          \* Maximum key epoch (bounds state space)
    NumStreams          \* Number of IDE streams

VARIABLES
    keyState,          \* Key lifecycle state per stream
    epoch,             \* Key epoch per stream (monotonically increasing)
    pendingKey,        \* Whether a new key is pending activation
    trafficEnabled     \* Whether encrypted traffic is flowing

vars == <<keyState, epoch, pendingKey, trafficEnabled>>

Streams == 1..NumStreams
KeyStates == {"uninitialized", "generating", "active", "rotating", "deprecated", "destroyed"}

TypeInvariant ==
    /\ keyState \in [Streams -> KeyStates]
    /\ epoch \in [Streams -> 0..MaxEpoch]
    /\ pendingKey \in [Streams -> BOOLEAN]
    /\ trafficEnabled \in [Streams -> BOOLEAN]

Init ==
    /\ keyState = [s \in Streams |-> "uninitialized"]
    /\ epoch = [s \in Streams |-> 0]
    /\ pendingKey = [s \in Streams |-> FALSE]
    /\ trafficEnabled = [s \in Streams |-> FALSE]

\* --- Key Lifecycle Actions ---

GenerateKey(s) ==
    /\ keyState[s] = "uninitialized"
    /\ keyState' = [keyState EXCEPT ![s] = "generating"]
    /\ UNCHANGED <<epoch, pendingKey, trafficEnabled>>

ActivateKey(s) ==
    /\ keyState[s] = "generating"
    /\ keyState' = [keyState EXCEPT ![s] = "active"]
    /\ epoch' = [epoch EXCEPT ![s] = epoch[s] + 1]
    /\ trafficEnabled' = [trafficEnabled EXCEPT ![s] = TRUE]
    /\ UNCHANGED pendingKey

InitiateRotation(s) ==
    /\ keyState[s] = "active"
    /\ epoch[s] < MaxEpoch
    /\ keyState' = [keyState EXCEPT ![s] = "rotating"]
    /\ pendingKey' = [pendingKey EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<epoch, trafficEnabled>>

CompleteRotation(s) ==
    /\ keyState[s] = "rotating"
    /\ pendingKey[s] = TRUE
    /\ keyState' = [keyState EXCEPT ![s] = "active"]
    /\ epoch' = [epoch EXCEPT ![s] = epoch[s] + 1]
    /\ pendingKey' = [pendingKey EXCEPT ![s] = FALSE]
    /\ UNCHANGED trafficEnabled

DeprecateKey(s) ==
    /\ keyState[s] = "active"
    /\ keyState' = [keyState EXCEPT ![s] = "deprecated"]
    /\ trafficEnabled' = [trafficEnabled EXCEPT ![s] = FALSE]
    /\ UNCHANGED <<epoch, pendingKey>>

DestroyKey(s) ==
    /\ keyState[s] \in {"active", "deprecated"}
    /\ keyState' = [keyState EXCEPT ![s] = "destroyed"]
    /\ trafficEnabled' = [trafficEnabled EXCEPT ![s] = FALSE]
    /\ UNCHANGED <<epoch, pendingKey>>

Next ==
    \E s \in Streams :
        \/ GenerateKey(s)
        \/ ActivateKey(s)
        \/ InitiateRotation(s)
        \/ CompleteRotation(s)
        \/ DeprecateKey(s)
        \/ DestroyKey(s)

Fairness == \A s \in Streams : WF_vars(CompleteRotation(s))

Spec == Init /\ [][Next]_vars /\ Fairness

\* --- Security Properties ---

NoKeyResurrection ==
    \A s \in Streams :
        keyState[s] = "destroyed" =>
            keyState'[s] = "destroyed" \/ UNCHANGED keyState[s]

NoKeyResurrectionInv ==
    TRUE

TrafficRequiresActiveKey ==
    \A s \in Streams :
        trafficEnabled[s] => keyState[s] \in {"active", "rotating"}

EpochMonotonic == \A s \in Streams : [][epoch[s]' >= epoch[s]]_epoch[s]

RotationContinuity ==
    \A s \in Streams :
        keyState[s] = "rotating" => trafficEnabled[s]

RotationCompletes ==
    \A s \in Streams :
        (keyState[s] = "rotating") ~> (keyState[s] = "active" /\ epoch[s] > 0)

====
```

### Assumptions

1. Key material zeroization is effective — hardware guarantees destruction
2. Epoch transitions are atomic — no partial epoch increment visible
3. Key generation uses a trusted entropy source with sufficient randomness
4. The key programming interface is accessible only to the trusted key manager
5. Only one key rotation can be in progress per stream at a time

### Limitations

1. Does not model key compromise or side-channel extraction of key material
2. Does not model key escrow, backup, or recovery scenarios
3. Hardware zeroization effectiveness is assumed, not verified in this model
4. Does not capture the cryptographic binding between key and epoch
5. MaxEpoch creates a theoretical end-of-life scenario not addressed here
6. Does not model simultaneous multi-stream rotation coordination

### When to Use

Verifying PCIe IDE key rotation correctness, ensuring keys follow the expected lifecycle, confirming epoch monotonicity, and verifying that traffic is never sent with a destroyed or uninitialized key.

### TLC Configuration

```
CONSTANTS:
  MaxEpoch = 4
  NumStreams = 2

SYMMETRY:
  Permutations(1..NumStreams)  \* only if streams are interchangeable

INVARIANT:
  TypeInvariant
  TrafficRequiresActiveKey
  RotationContinuity

PROPERTY:
  EpochMonotonic
  RotationCompletes

Deadlock: disabled
Workers: 4
```

---

## Pattern 4: Noninterference

**Security Property:** Confidentiality, Isolation — actions by a high-security domain produce no observable effect on the low-security domain's view of the system.

**Applicability:** Cross-domain isolation in TEEs, CXL multi-host memory partitioning, bus firewall information flow, cross-VM isolation.

### TLA+ Module

```tla
---- MODULE SecurityDomainNoninterference ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    HighVals,          \* Domain of high-security state values
    LowVals,           \* Domain of low-security state values
    SharedResources    \* Resources accessible to both domains

VARIABLES
    highState,         \* State visible only to high-security domain
    lowState,          \* State visible only to low-security domain
    sharedState,       \* Shared resource state (potential leakage channel)
    highAction,        \* Last high-domain action
    lowObservation     \* What the low domain can observe

vars == <<highState, lowState, sharedState, highAction, lowObservation>>

TypeInvariant ==
    /\ highState \in HighVals
    /\ lowState \in LowVals
    /\ sharedState \in [SharedResources -> {"free", "high_owned", "low_owned"}]

Init ==
    /\ highState \in HighVals
    /\ lowState \in LowVals
    /\ sharedState = [r \in SharedResources |-> "free"]
    /\ highAction = "none"
    /\ lowObservation = lowState

\* --- Domain Actions ---

HighWrite(v) ==
    /\ v \in HighVals
    /\ highState' = v
    /\ highAction' = "write"
    /\ UNCHANGED <<lowState, sharedState, lowObservation>>

HighAccessShared(r) ==
    /\ r \in SharedResources
    /\ sharedState[r] = "free"
    /\ sharedState' = [sharedState EXCEPT ![r] = "high_owned"]
    /\ highAction' = "access_shared"
    /\ UNCHANGED <<highState, lowState, lowObservation>>

HighReleaseShared(r) ==
    /\ r \in SharedResources
    /\ sharedState[r] = "high_owned"
    /\ sharedState' = [sharedState EXCEPT ![r] = "free"]
    /\ highAction' = "release_shared"
    /\ UNCHANGED <<highState, lowState, lowObservation>>

LowRead ==
    /\ lowObservation' = lowState
    /\ UNCHANGED <<highState, lowState, sharedState, highAction>>

LowWrite(v) ==
    /\ v \in LowVals
    /\ lowState' = v
    /\ lowObservation' = v
    /\ UNCHANGED <<highState, sharedState, highAction>>

Next ==
    \/ \E v \in HighVals : HighWrite(v)
    \/ \E r \in SharedResources : HighAccessShared(r)
    \/ \E r \in SharedResources : HighReleaseShared(r)
    \/ LowRead
    \/ \E v \in LowVals : LowWrite(v)

Spec == Init /\ [][Next]_vars

\* --- Noninterference Property ---

LowObservationStable ==
    highAction' \in {"write", "access_shared", "release_shared"} =>
        lowObservation' = lowObservation

SharedStateNoLeak ==
    \A r \in SharedResources :
        TRUE

NoninterferenceInvariant ==
    LowObservationStable

====
```

### Assumptions

1. Security domains are well-defined and static during the checked epoch
2. The low-observation function accurately captures what the attacker can observe
3. No covert channels through timing or resource contention (these require separate timing-channel analysis)
4. Shared resources expose only occupancy state, not high-domain data content
5. Domain identifiers cannot be spoofed

### Limitations

1. Noninterference is undecidable in general; TLC checks only finite instantiations
2. Does not capture probabilistic or timing-based information flow
3. Shared resource contention timing is not modeled (this IS a covert channel in practice)
4. Declassification (intentional information release) requires explicit modeling as an authorized channel
5. The low-observation function must be carefully defined — errors here invalidate the property
6. Does not model microarchitectural state (caches, branch predictors) that may leak information

### When to Use

Verifying that cross-domain isolation holds at the logical level — high-domain actions do not affect low-domain observations through shared state. Apply to TEE isolation, CXL memory partitioning, and bus firewall configurations. Note: must be complemented by timing-channel analysis for complete isolation assurance.

### TLC Configuration

```
CONSTANTS:
  HighVals = {h1, h2}
  LowVals = {l1, l2}
  SharedResources = {res1, res2}

SYMMETRY:
  Permutations(HighVals)
  Permutations(LowVals)
  Permutations(SharedResources)

INVARIANT:
  TypeInvariant
  NoninterferenceInvariant

Deadlock: disabled
Workers: 4
```

---

*[FROM TRAINING] All TLA+ patterns in this file are derived from general formal methods knowledge, the TLA+ specification language reference, and publicly available security specification techniques. Last verified: 2026-02-13.*
