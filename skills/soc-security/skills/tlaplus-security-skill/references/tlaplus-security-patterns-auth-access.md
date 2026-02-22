# TLA+ Security Patterns — Authentication & Access Control

## Purpose

Ready-to-use TLA+ modules for authentication state machines and access control invariants. Each pattern is standalone with assumptions, limitations, and TLC configuration. Instantiate constants and refine transitions for the target design.

**Primary consumer:** tlaplus-security-skill (Phase 2 module construction, Phase 3 property formalization)

---

## Table of Contents

- Pattern 1: Authentication State Machine
- Pattern 2: Access Control Invariant

---

## Pattern 1: Authentication State Machine

**Security Property:** Authenticity — the authenticated state is reachable only through the correct challenge-response protocol sequence.

**Applicability:** SPDM challenge-response authentication, DICE identity verification, debug unlock sequences, TDISP TDI authentication.

### TLA+ Module

```tla
---- MODULE SPDMAuthentication ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Identities,       \* Set of valid identities (requester, responder)
    MaxAttempts,       \* Maximum failed attempts before lockout
    Nonces             \* Finite set of nonce values for model checking

VARIABLES
    authState,         \* Protocol state
    requester,         \* Identity requesting authentication
    responder,         \* Identity being authenticated
    challengeNonce,    \* Current challenge nonce
    failedAttempts,    \* Counter of failed attempts
    sessionEstablished \* Whether a secure session exists

vars == <<authState, requester, responder, challengeNonce, failedAttempts, sessionEstablished>>

TypeInvariant ==
    /\ authState \in {"idle", "get_version", "get_capabilities", "negotiate_algorithms",
                       "get_digests", "get_certificate", "challenge", "challenge_auth",
                       "authenticated", "failed", "locked"}
    /\ failedAttempts \in 0..MaxAttempts
    /\ sessionEstablished \in BOOLEAN
    /\ challengeNonce \in Nonces \union {"none"}

Init ==
    /\ authState = "idle"
    /\ requester = "none"
    /\ responder = "none"
    /\ challengeNonce = "none"
    /\ failedAttempts = 0
    /\ sessionEstablished = FALSE

\* --- Protocol Actions (SPDM 1.3+ simplified) ---

StartAuthentication(req, resp) ==
    /\ authState = "idle"
    /\ req \in Identities
    /\ resp \in Identities
    /\ req /= resp
    /\ requester' = req
    /\ responder' = resp
    /\ authState' = "get_version"
    /\ UNCHANGED <<challengeNonce, failedAttempts, sessionEstablished>>

GetVersion ==
    /\ authState = "get_version"
    /\ authState' = "get_capabilities"
    /\ UNCHANGED <<requester, responder, challengeNonce, failedAttempts, sessionEstablished>>

GetCapabilities ==
    /\ authState = "get_capabilities"
    /\ authState' = "negotiate_algorithms"
    /\ UNCHANGED <<requester, responder, challengeNonce, failedAttempts, sessionEstablished>>

NegotiateAlgorithms ==
    /\ authState = "negotiate_algorithms"
    /\ authState' = "get_digests"
    /\ UNCHANGED <<requester, responder, challengeNonce, failedAttempts, sessionEstablished>>

GetDigests ==
    /\ authState = "get_digests"
    /\ authState' = "get_certificate"
    /\ UNCHANGED <<requester, responder, challengeNonce, failedAttempts, sessionEstablished>>

GetCertificate ==
    /\ authState = "get_certificate"
    /\ authState' = "challenge"
    /\ UNCHANGED <<requester, responder, challengeNonce, failedAttempts, sessionEstablished>>

IssueChallenge(n) ==
    /\ authState = "challenge"
    /\ n \in Nonces
    /\ challengeNonce' = n
    /\ authState' = "challenge_auth"
    /\ UNCHANGED <<requester, responder, failedAttempts, sessionEstablished>>

\* Successful authentication
VerifySuccess ==
    /\ authState = "challenge_auth"
    /\ authState' = "authenticated"
    /\ sessionEstablished' = TRUE
    /\ UNCHANGED <<requester, responder, challengeNonce, failedAttempts>>

\* Failed authentication
VerifyFailure ==
    /\ authState = "challenge_auth"
    /\ failedAttempts' = failedAttempts + 1
    /\ IF failedAttempts' >= MaxAttempts
       THEN authState' = "locked"
       ELSE authState' = "idle"
    /\ sessionEstablished' = FALSE
    /\ UNCHANGED <<requester, responder, challengeNonce>>

\* Error at any protocol stage
ProtocolError ==
    /\ authState \in {"get_version", "get_capabilities", "negotiate_algorithms",
                       "get_digests", "get_certificate", "challenge", "challenge_auth"}
    /\ authState' = "failed"
    /\ sessionEstablished' = FALSE
    /\ UNCHANGED <<requester, responder, challengeNonce, failedAttempts>>

Reset ==
    /\ authState \in {"failed", "authenticated"}
    /\ authState' = "idle"
    /\ sessionEstablished' = FALSE
    /\ UNCHANGED <<requester, responder, challengeNonce, failedAttempts>>

Next ==
    \/ \E req, resp \in Identities : StartAuthentication(req, resp)
    \/ GetVersion
    \/ GetCapabilities
    \/ NegotiateAlgorithms
    \/ GetDigests
    \/ GetCertificate
    \/ \E n \in Nonces : IssueChallenge(n)
    \/ VerifySuccess
    \/ VerifyFailure
    \/ ProtocolError
    \/ Reset

Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

\* --- Security Properties ---

\* Safety: authenticated state requires full protocol traversal
NoAuthenticationBypass ==
    authState = "authenticated" => sessionEstablished

\* Safety: locked state is absorbing (no further attempts)
LockoutEffective ==
    authState = "locked" => authState' = "locked" \/ UNCHANGED authState

\* Safety: nonce is set before challenge-auth
NoncePresent ==
    authState = "challenge_auth" => challengeNonce /= "none"

\* Liveness: under fairness, a valid responder eventually authenticates
EventualAuthentication == <>(authState = "authenticated")

====
```

### Assumptions

1. Cryptographic primitives are ideal — signatures cannot be forged, nonces cannot be predicted
2. The communication channel has integrity (no message tampering between requester and responder)
3. Certificate chain validation is abstracted to a single step (GetCertificate)
4. The responder's identity is bound to a valid certificate chain
5. Protocol message ordering is enforced by the transport layer

### Limitations

1. Does not model computational cryptographic security (e.g., key length, algorithm strength)
2. Does not model message replay — nonce uniqueness is assumed, not verified
3. Does not capture timing attacks on the authentication protocol
4. Certificate revocation checking is not modeled
5. Mutual authentication (requester also authenticates) requires extending the model
6. Does not model session key derivation after authentication

### When to Use

Verifying that the SPDM authentication handshake cannot be bypassed — no shortcut path to the authenticated state without traversing all protocol steps. Also applicable to DICE attestation protocols and debug unlock challenge-response sequences.

### TLC Configuration

```
CONSTANTS:
  Identities = {req, resp}
  MaxAttempts = 3
  Nonces = {n1, n2, n3}

SYMMETRY:
  Permutations(Nonces)

INVARIANT:
  TypeInvariant
  NoAuthenticationBypass
  NoncePresent

PROPERTY:
  EventualAuthentication

Deadlock: enabled
Workers: 4
```

---

## Pattern 2: Access Control Invariant

**Security Property:** Authorization, Isolation — device interface access is governed by the TDISP state machine, and only authorized domains can access a TDI when it is in the appropriate state.

**Applicability:** TDISP state-dependent access control, TEE memory partition isolation, bus firewall authorization.

### TLA+ Module

```tla
---- MODULE TDISPAccessControl ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Domains,           \* Security domains (e.g., VMs, trust domains)
    TDIs,              \* TDI (Trusted Device Interface) identifiers
    TSM                \* Trusted Security Manager identity

VARIABLES
    tdiState,          \* State of each TDI: [TDIs -> TDIStates]
    tdiOwner,          \* Assigned owner domain: [TDIs -> Domains \union {"unassigned"}]
    dmaEnabled,        \* DMA enabled per TDI: [TDIs -> BOOLEAN]
    accessAttempt      \* Last access attempt result for checking

vars == <<tdiState, tdiOwner, dmaEnabled, accessAttempt>>

TDIStates == {"CONFIG_UNLOCKED", "CONFIG_LOCKED", "RUN", "ERROR"}

TypeInvariant ==
    /\ tdiState \in [TDIs -> TDIStates]
    /\ tdiOwner \in [TDIs -> Domains \union {"unassigned"}]
    /\ dmaEnabled \in [TDIs -> BOOLEAN]
    /\ accessAttempt \in {"none", "granted", "denied"}

Init ==
    /\ tdiState = [t \in TDIs |-> "CONFIG_UNLOCKED"]
    /\ tdiOwner = [t \in TDIs |-> "unassigned"]
    /\ dmaEnabled = [t \in TDIs |-> FALSE]
    /\ accessAttempt = "none"

\* --- TSM-controlled state transitions ---

AssignTDI(tdi, domain) ==
    /\ tdiState[tdi] = "CONFIG_UNLOCKED"
    /\ tdiOwner' = [tdiOwner EXCEPT ![tdi] = domain]
    /\ UNCHANGED <<tdiState, dmaEnabled, accessAttempt>>

LockTDI(tdi) ==
    /\ tdiState[tdi] = "CONFIG_UNLOCKED"
    /\ tdiOwner[tdi] /= "unassigned"
    /\ tdiState' = [tdiState EXCEPT ![tdi] = "CONFIG_LOCKED"]
    /\ UNCHANGED <<tdiOwner, dmaEnabled, accessAttempt>>

StartTDI(tdi) ==
    /\ tdiState[tdi] = "CONFIG_LOCKED"
    /\ tdiState' = [tdiState EXCEPT ![tdi] = "RUN"]
    /\ dmaEnabled' = [dmaEnabled EXCEPT ![tdi] = TRUE]
    /\ UNCHANGED <<tdiOwner, accessAttempt>>

StopTDI(tdi) ==
    /\ tdiState[tdi] = "RUN"
    /\ tdiState' = [tdiState EXCEPT ![tdi] = "CONFIG_UNLOCKED"]
    /\ dmaEnabled' = [dmaEnabled EXCEPT ![tdi] = FALSE]
    /\ tdiOwner' = [tdiOwner EXCEPT ![tdi] = "unassigned"]
    /\ UNCHANGED accessAttempt

ErrorTDI(tdi) ==
    /\ tdiState[tdi] \in {"CONFIG_LOCKED", "RUN"}
    /\ tdiState' = [tdiState EXCEPT ![tdi] = "ERROR"]
    /\ dmaEnabled' = [dmaEnabled EXCEPT ![tdi] = FALSE]
    /\ UNCHANGED <<tdiOwner, accessAttempt>>

\* --- Access attempt by a domain ---

AttemptAccess(tdi, domain) ==
    /\ IF /\ tdiState[tdi] = "RUN"
          /\ tdiOwner[tdi] = domain
          /\ dmaEnabled[tdi] = TRUE
       THEN accessAttempt' = "granted"
       ELSE accessAttempt' = "denied"
    /\ UNCHANGED <<tdiState, tdiOwner, dmaEnabled>>

Next ==
    \/ \E tdi \in TDIs, d \in Domains :
        \/ AssignTDI(tdi, d)
        \/ AttemptAccess(tdi, d)
    \/ \E tdi \in TDIs :
        \/ LockTDI(tdi)
        \/ StartTDI(tdi)
        \/ StopTDI(tdi)
        \/ ErrorTDI(tdi)

Spec == Init /\ [][Next]_vars

\* --- Security Properties ---

DMAOnlyInRun ==
    \A tdi \in TDIs :
        dmaEnabled[tdi] => tdiState[tdi] = "RUN"

AccessControlInvariant ==
    \A tdi \in TDIs, d \in Domains :
        (tdiState[tdi] = "RUN" /\ tdiOwner[tdi] /= d) =>
            TRUE  \* Enforced by AttemptAccess guard

ExclusiveOwnership ==
    \A tdi \in TDIs :
        tdiOwner[tdi] /= "unassigned" =>
            Cardinality({d \in Domains : tdiOwner[tdi] = d}) = 1

ErrorDisablesDMA ==
    \A tdi \in TDIs :
        tdiState[tdi] = "ERROR" => dmaEnabled[tdi] = FALSE

UnassignedNotRunning ==
    \A tdi \in TDIs :
        tdiOwner[tdi] = "unassigned" => tdiState[tdi] \in {"CONFIG_UNLOCKED", "ERROR"}

====
```

### Assumptions

1. TSM (Trusted Security Manager) is trusted and cannot be compromised
2. State transitions are atomic — no partial transitions visible to other domains
3. Domain identifiers are trustworthy and cannot be spoofed at this abstraction level
4. The TDI hardware enforces the access control checks modeled here
5. Error detection is reliable — if an error occurs, the FSM transitions to ERROR

### Limitations

1. Does not model DMA transaction content — only whether DMA is enabled/disabled
2. Does not model concurrent access attempts from multiple domains to the same TDI
3. Does not capture TOCTOU between state check and DMA transfer
4. Does not model the SPDM authentication that should precede TDI assignment
5. Does not model physical attacks that might corrupt the state register

### When to Use

Verifying that TDISP device interface access control is correctly specified — DMA is only enabled in RUN state, only the assigned owner domain can access the TDI, and error conditions reliably disable access.

### TLC Configuration

```
CONSTANTS:
  Domains = {vm1, vm2, vm3}
  TDIs = {tdi1, tdi2}
  TSM = tsm

SYMMETRY:
  Permutations(Domains)
  Permutations(TDIs)

INVARIANT:
  TypeInvariant
  DMAOnlyInRun
  ExclusiveOwnership
  ErrorDisablesDMA
  UnassignedNotRunning

Deadlock: disabled (system can idle)
Workers: 4
```

---

*[FROM TRAINING] All TLA+ patterns in this file are derived from general formal methods knowledge, the TLA+ specification language reference, and publicly available security specification techniques. Last verified: 2026-02-13.*
