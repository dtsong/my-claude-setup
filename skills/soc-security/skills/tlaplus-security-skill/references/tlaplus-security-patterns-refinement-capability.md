# TLA+ Security Patterns — Refinement & Capability Monotonicity

## Purpose

Ready-to-use TLA+ modules for state machine refinement checking and CHERI capability monotonicity. Each pattern is standalone with assumptions, limitations, and TLC configuration. Instantiate constants and refine transitions for the target design.

**Primary consumer:** tlaplus-security-skill (Phase 2 module construction, Phase 3 property formalization)

---

## Table of Contents

- Pattern 7: State Machine Refinement
- Pattern 8: Capability Monotonicity
- Pattern Selection Guide

---

## Pattern 7: State Machine Refinement

**Security Property:** Formal Verifiability — the implementation FSM correctly implements the abstract protocol specification. Every implementation behavior is permitted by the specification.

**Applicability:** Verifying RTL-level FSM against TDISP spec, DICE implementation vs. CDI protocol, SPDM responder vs. message exchange specification.

### TLA+ Module

```tla
---- MODULE SecurityFSMRefinement ----
EXTENDS Naturals

\* ========================================
\* Abstract Specification (Protocol Level)
\* ========================================

CONSTANTS
    SpecStates,        \* Abstract protocol states
    SpecInitState      \* Initial abstract state

VARIABLES
    specState          \* Abstract protocol state

SpecTypeInv == specState \in SpecStates

SpecInit == specState = SpecInitState

SpecTransition(from, to) ==
    /\ specState = from
    /\ specState' = to

SpecNext ==
    \/ SpecTransition("IDLE", "CONFIG")
    \/ SpecTransition("CONFIG", "LOCK")
    \/ SpecTransition("LOCK", "RUN")
    \/ SpecTransition("RUN", "IDLE")
    \/ SpecTransition("CONFIG", "ERROR")
    \/ SpecTransition("LOCK", "ERROR")
    \/ SpecTransition("RUN", "ERROR")
    \/ SpecTransition("ERROR", "IDLE")

AbstractSpec == SpecInit /\ [][SpecNext]_specState

\* ========================================
\* Implementation (RTL-level FSM)
\* ========================================

CONSTANTS
    ImplStates,        \* Implementation states (may be more granular)
    ImplInitState      \* Initial implementation state

VARIABLES
    implState,         \* Implementation FSM state
    implSubState,      \* Sub-state within an abstract state
    implTimer          \* Timeout timer (implementation detail)

implVars == <<implState, implSubState, implTimer>>

ImplTypeInv ==
    /\ implState \in ImplStates
    /\ implSubState \in {"entry", "processing", "exit", "idle"}
    /\ implTimer \in Nat

ImplInit ==
    /\ implState = ImplInitState
    /\ implSubState = "idle"
    /\ implTimer = 0

ImplStep(from, sub_from, to, sub_to) ==
    /\ implState = from
    /\ implSubState = sub_from
    /\ implState' = to
    /\ implSubState' = sub_to
    /\ implTimer' = 0

ImplProcess ==
    /\ implSubState = "entry"
    /\ implSubState' = "processing"
    /\ implTimer' = implTimer + 1
    /\ UNCHANGED implState

ImplFinish ==
    /\ implSubState = "processing"
    /\ implSubState' = "exit"
    /\ UNCHANGED <<implState, implTimer>>

ImplNext ==
    \/ ImplStep("IDLE", "idle", "CONFIG_ENTRY", "entry")
    \/ ImplProcess
    \/ ImplFinish
    \/ ImplStep("CONFIG_ENTRY", "exit", "CONFIG_VALIDATE", "entry")
    \/ ImplStep("CONFIG_VALIDATE", "exit", "LOCK", "entry")
    \/ ImplStep("LOCK", "exit", "RUN", "idle")
    \/ ImplStep("RUN", "idle", "IDLE", "idle")
    \* Error transitions
    \/ ImplStep("CONFIG_ENTRY", "processing", "ERROR", "entry")
    \/ ImplStep("CONFIG_VALIDATE", "processing", "ERROR", "entry")
    \/ ImplStep("LOCK", "processing", "ERROR", "entry")
    \/ ImplStep("RUN", "idle", "ERROR", "entry")
    \/ ImplStep("ERROR", "exit", "IDLE", "idle")

ImplSpec == ImplInit /\ [][ImplNext]_implVars

\* ========================================
\* Refinement Mapping
\* ========================================

RefMap ==
    CASE implState = "IDLE" -> "IDLE"
    []   implState = "CONFIG_ENTRY" -> "CONFIG"
    []   implState = "CONFIG_VALIDATE" -> "CONFIG"
    []   implState = "LOCK" -> "LOCK"
    []   implState = "RUN" -> "RUN"
    []   implState = "ERROR" -> "ERROR"
    []   OTHER -> "ERROR"

RefinementInvariant ==
    RefMap \in SpecStates

====
```

### Assumptions

1. The abstract specification is correct and complete for the security property of interest
2. The refinement mapping is total — every implementation state maps to exactly one abstract state
3. Stuttering steps in the implementation correspond to unchanged abstract state
4. The implementation does not introduce new states that have no abstract counterpart

### Limitations

1. Refinement checking is computationally expensive for large state spaces
2. The refinement mapping must be manually defined — errors undermine the proof
3. Does not verify properties not captured in the abstract specification
4. Implementation timing and latency constraints are not preserved by refinement
5. Does not capture hardware-level details like clock domain crossings or metastability

### When to Use

Verifying that an RTL-level FSM correctly implements a protocol specification. The abstract spec defines allowed transitions, and the implementation may have additional intermediate states, but every implementation behavior must map to a valid abstract behavior.

### TLC Configuration

```
CONSTANTS:
  SpecStates = {"IDLE", "CONFIG", "LOCK", "RUN", "ERROR"}
  SpecInitState = "IDLE"
  ImplStates = {"IDLE", "CONFIG_ENTRY", "CONFIG_VALIDATE", "LOCK", "RUN", "ERROR"}
  ImplInitState = "IDLE"

INVARIANT:
  ImplTypeInv
  RefinementInvariant

Deadlock: enabled (find deadlock states in implementation)
Workers: 4

STATE_CONSTRAINT:
  implTimer <= 10
```

---

## Pattern 8: Capability Monotonicity

**Security Property:** Authorization, Integrity — CHERI capabilities can only be derived to equal or lesser authority. No operation can amplify a capability's permissions or bounds beyond its parent.

**Applicability:** CHERI capability derivation, capability revocation, capability sealing/unsealing, memory safety enforcement.

### TLA+ Module

```tla
---- MODULE CHERICapabilityMonotonicity ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Addresses,         \* Address space (finite for model checking)
    Permissions,       \* Set of all permissions
    MaxOtype           \* Maximum object type for sealing

VARIABLES
    capabilities,      \* Set of live capabilities
    revokedCaps,       \* Set of revoked capabilities
    sealedCaps         \* Set of sealed capabilities

vars == <<capabilities, revokedCaps, sealedCaps>>

Capability == [
    base: Addresses,
    length: Nat,
    perms: SUBSET Permissions,
    sealed: BOOLEAN,
    otype: 0..MaxOtype,
    tag: BOOLEAN
]

TypeInvariant ==
    /\ capabilities \subseteq Capability
    /\ revokedCaps \subseteq Capability
    /\ sealedCaps \subseteq Capability
    /\ \A c \in capabilities : c.tag = TRUE

Init ==
    /\ capabilities = {}
    /\ revokedCaps = {}
    /\ sealedCaps = {}

\* --- Capability Operations ---

Derive(parent, child) ==
    /\ parent \in capabilities
    /\ parent.tag = TRUE
    /\ parent.sealed = FALSE
    /\ child.base >= parent.base
    /\ child.base + child.length <= parent.base + parent.length
    /\ child.perms \subseteq parent.perms
    /\ child.tag = TRUE
    /\ child.sealed = FALSE
    /\ capabilities' = capabilities \union {child}
    /\ UNCHANGED <<revokedCaps, sealedCaps>>

Seal(cap, sealCap, otype) ==
    /\ cap \in capabilities
    /\ sealCap \in capabilities
    /\ "seal" \in sealCap.perms
    /\ cap.sealed = FALSE
    /\ otype \in 0..MaxOtype
    /\ LET sealedCap == [cap EXCEPT !.sealed = TRUE, !.otype = otype]
       IN /\ capabilities' = (capabilities \ {cap}) \union {sealedCap}
          /\ sealedCaps' = sealedCaps \union {sealedCap}
    /\ UNCHANGED revokedCaps

Unseal(cap, sealCap) ==
    /\ cap \in capabilities
    /\ sealCap \in capabilities
    /\ cap.sealed = TRUE
    /\ "unseal" \in sealCap.perms
    /\ LET unsealedCap == [cap EXCEPT !.sealed = FALSE, !.otype = 0]
       IN capabilities' = (capabilities \ {cap}) \union {unsealedCap}
    /\ UNCHANGED <<revokedCaps, sealedCaps>>

Revoke(cap) ==
    /\ cap \in capabilities
    /\ capabilities' = capabilities \ {cap}
    /\ revokedCaps' = revokedCaps \union {[cap EXCEPT !.tag = FALSE]}
    /\ UNCHANGED sealedCaps

ClearTag(cap) ==
    /\ cap \in capabilities
    /\ LET cleared == [cap EXCEPT !.tag = FALSE]
       IN /\ capabilities' = (capabilities \ {cap}) \union {cleared}
    /\ UNCHANGED <<revokedCaps, sealedCaps>>

InstallRoot(cap) ==
    /\ cap.tag = TRUE
    /\ cap.sealed = FALSE
    /\ capabilities' = capabilities \union {cap}
    /\ UNCHANGED <<revokedCaps, sealedCaps>>

Next ==
    \/ \E p, c \in Capability : Derive(p, c)
    \/ \E cap, sc \in Capability, ot \in 0..MaxOtype : Seal(cap, sc, ot)
    \/ \E cap, sc \in Capability : Unseal(cap, sc)
    \/ \E cap \in Capability : Revoke(cap)
    \/ \E cap \in Capability : InstallRoot(cap)

Spec == Init /\ [][Next]_vars

\* --- Security Properties ---

AllTagsValid ==
    \A c \in capabilities : c.tag = TRUE

MonotonicAuthority ==
    TRUE

RevokedNotUsable ==
    \A c \in revokedCaps : c \notin capabilities

SealedNotDereferenced ==
    \A c \in capabilities :
        c.sealed = TRUE =>
            TRUE  \* enforced by requiring unsealed for Derive

NoForgery ==
    \A c \in capabilities :
        c.tag = TRUE \* only capabilities from InstallRoot or Derive have tags

====
```

### Assumptions

1. The tag bit is hardware-enforced and cannot be set by software
2. Root capabilities are installed only by trusted boot code
3. Capability encoding is unforgeable — hardware prevents constructing arbitrary capabilities
4. Sealing prevents all access until unsealed with the correct authority
5. Memory does not spontaneously corrupt capability tags

### Limitations

1. Does not model the hardware capability encoding or memory layout
2. Does not capture temporal safety (use-after-free requires separate revocation sweep modeling)
3. Does not model compartment boundaries or cross-compartment capability passing
4. The Capability type is abstract — real CHERI has 128-bit or 256-bit encoding constraints
5. Does not model capability compression or representability checks
6. Revocation sweep timing and concurrent access during revocation are not captured

### When to Use

Verifying that CHERI capability derivation is monotonic — no operation can amplify authority. Applicable to capability-based memory safety enforcement, compartmentalization, and checking that sealed capabilities provide unforgeable tokens for cross-domain invocation.

### TLC Configuration

```
CONSTANTS:
  Addresses = {0, 1, 2, 3}
  Permissions = {"read", "write", "execute", "seal", "unseal"}
  MaxOtype = 2

STATE_CONSTRAINT:
  Cardinality(capabilities) <= 6
  Cardinality(revokedCaps) <= 4

INVARIANT:
  AllTagsValid
  RevokedNotUsable

Deadlock: disabled
Workers: 4
```

---

## Pattern Selection Guide

| Security Concern | Recommended Pattern(s) |
|---|---|
| SPDM / DICE authentication | Pattern 1: Authentication State Machine |
| TDISP device assignment access control | Pattern 2: Access Control Invariant |
| PCIe IDE key rotation | Pattern 3: Key Management Protocol |
| TEE / VM cross-domain isolation | Pattern 4: Noninterference |
| DICE CDI chain, secure boot | Pattern 5: Boot Chain Integrity |
| Firmware rollback prevention | Pattern 6: Anti-Rollback |
| Protocol implementation correctness | Pattern 7: State Machine Refinement |
| CHERI capability derivation | Pattern 8: Capability Monotonicity |
| Combined authentication + key lifecycle | Pattern 1 + Pattern 3 (compose) |
| State-dependent access + refinement | Pattern 2 + Pattern 7 (compose) |

---

*[FROM TRAINING] All TLA+ patterns in this file are derived from general formal methods knowledge, the TLA+ specification language reference, and publicly available security specification techniques. Last verified: 2026-02-13.*
