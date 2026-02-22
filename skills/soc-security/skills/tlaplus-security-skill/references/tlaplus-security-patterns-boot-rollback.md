# TLA+ Security Patterns — Boot Chain & Anti-Rollback

## Purpose

Ready-to-use TLA+ modules for boot chain integrity verification and anti-rollback counter safety. Each pattern is standalone with assumptions, limitations, and TLC configuration. Instantiate constants and refine transitions for the target design.

**Primary consumer:** tlaplus-security-skill (Phase 2 module construction, Phase 3 property formalization)

---

## Table of Contents

- Pattern 5: Boot Chain Integrity
- Pattern 6: Anti-Rollback

---

## Pattern 5: Boot Chain Integrity

**Security Property:** Integrity, Attestation — each boot layer measures the next before transferring control. Any modification to a layer produces a detectably different measurement.

**Applicability:** DICE CDI derivation chains, secure boot measurement sequences, SPDM measurement reporting, firmware measurement for attestation.

### TLA+ Module

```tla
---- MODULE DICEBootChain ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    NumLayers,         \* Number of boot layers (e.g., ROM, loader, OS, app)
    HashValues         \* Finite set of hash values for model checking

VARIABLES
    bootProgress,      \* Current boot layer (0 = not started)
    measurements,      \* Measurement register per layer
    goldenRef,         \* Expected (golden) measurements
    compromised,       \* Set of compromised layers
    cdi,               \* Compound Device Identifier per layer
    attestationValid   \* Whether the full chain attestation is valid

vars == <<bootProgress, measurements, goldenRef, compromised, cdi, attestationValid>>

TypeInvariant ==
    /\ bootProgress \in 0..NumLayers
    /\ measurements \in [1..NumLayers -> HashValues \union {"unmeasured"}]
    /\ goldenRef \in [1..NumLayers -> HashValues]
    /\ compromised \subseteq 1..NumLayers
    /\ attestationValid \in BOOLEAN

Init ==
    /\ bootProgress = 0
    /\ measurements = [l \in 1..NumLayers |-> "unmeasured"]
    /\ goldenRef \in [1..NumLayers -> HashValues]
    /\ compromised \in SUBSET (1..NumLayers)
    /\ cdi = [l \in 1..NumLayers |-> "unmeasured"]
    /\ attestationValid = FALSE

\* --- Boot Actions ---

MeasureAndBoot ==
    /\ bootProgress < NumLayers
    /\ LET nextLayer == bootProgress + 1
       IN
        /\ IF nextLayer \in compromised
           THEN \E h \in HashValues \ {goldenRef[nextLayer]} :
                    measurements' = [measurements EXCEPT ![nextLayer] = h]
           ELSE measurements' = [measurements EXCEPT ![nextLayer] = goldenRef[nextLayer]]
        /\ cdi' = [cdi EXCEPT ![nextLayer] = measurements'[nextLayer]]
        /\ bootProgress' = nextLayer
    /\ UNCHANGED <<goldenRef, compromised, attestationValid>>

Attest ==
    /\ bootProgress = NumLayers
    /\ attestationValid' = (\A l \in 1..NumLayers : measurements[l] = goldenRef[l])
    /\ UNCHANGED <<bootProgress, measurements, goldenRef, compromised, cdi>>

Next == MeasureAndBoot \/ Attest

Fairness == WF_vars(MeasureAndBoot) /\ WF_vars(Attest)

Spec == Init /\ [][Next]_vars /\ Fairness

\* --- Security Properties ---

MeasurementImmutability ==
    \A l \in 1..NumLayers :
        measurements[l] /= "unmeasured" =>
            [][measurements[l]' = measurements[l]]_measurements[l]

BootMonotonic == [][bootProgress' >= bootProgress]_bootProgress

TamperDetection ==
    /\ bootProgress = NumLayers
    /\ compromised /= {}
    => \E l \in compromised : measurements[l] /= goldenRef[l]

AttestationSoundness ==
    (compromised /= {} /\ bootProgress = NumLayers) => ~attestationValid

BootCompletes == <>(bootProgress = NumLayers)

AttestationRuns == <>(attestationValid \/ (~attestationValid /\ bootProgress = NumLayers))

====
```

### Assumptions

1. Hash function is collision-resistant (modeled as injective — different inputs produce different outputs)
2. Root of trust (layer 0 / ROM) is immutable hardware that cannot be compromised
3. Measurement registers are hardware-protected — firmware cannot overwrite them after the boot layer has advanced
4. The golden reference values are securely provisioned and trusted
5. Compromise of a layer changes its hash (no hash collisions)

### Limitations

1. Does not model TOCTOU attacks between measurement and execution of a layer
2. Hash collision resistance is assumed, not proven (model uses abstract hash values)
3. Does not capture measurement of dynamic/runtime state after boot
4. Does not model the CDI derivation function beyond simple hash chaining
5. Layer compromise is modeled as binary — partial compromise or subtle modifications are not captured
6. Does not model secure storage of CDI values

### When to Use

Verifying DICE CDI derivation chain integrity, secure boot measurement sequences, and SPDM measurement reporting completeness. Confirms that any tampering with a boot layer is detectable through the measurement chain.

### TLC Configuration

```
CONSTANTS:
  NumLayers = 4
  HashValues = {h1, h2, h3, h4, h_bad}

INVARIANT:
  TypeInvariant
  TamperDetection
  AttestationSoundness

PROPERTY:
  BootMonotonic
  BootCompletes

STATE_CONSTRAINT:
  bootProgress <= NumLayers

Deadlock: disabled
Workers: 4
```

---

## Pattern 6: Anti-Rollback

**Security Property:** Freshness, Integrity — a monotonic counter prevents firmware rollback. The counter only increases, firmware below the counter is rejected, and the counter survives reset.

**Applicability:** Firmware anti-rollback mechanisms, DICE layer version enforcement, secure boot version policy, OTP fuse-based versioning.

### TLA+ Module

```tla
---- MODULE AntiRollbackCounter ----
EXTENDS Naturals

CONSTANTS
    MaxVersion,        \* Maximum firmware version (bounds state space)
    AttackerVersions   \* Versions the attacker may propose (includes old versions)

VARIABLES
    counter,           \* Monotonic anti-rollback counter (non-volatile)
    proposedVersion,   \* Version being proposed for update
    decision,          \* Update decision: pending, accepted, rejected
    bootedVersion,     \* Currently booted firmware version
    resetOccurred      \* Whether a system reset has occurred

vars == <<counter, proposedVersion, decision, bootedVersion, resetOccurred>>

TypeInvariant ==
    /\ counter \in 0..MaxVersion
    /\ proposedVersion \in 0..MaxVersion
    /\ decision \in {"pending", "accepted", "rejected"}
    /\ bootedVersion \in 0..MaxVersion
    /\ resetOccurred \in BOOLEAN

Init ==
    /\ counter = 1
    /\ proposedVersion = 0
    /\ decision = "pending"
    /\ bootedVersion = 1
    /\ resetOccurred = FALSE

\* --- Actions ---

ProposeUpdate(v) ==
    /\ v \in 0..MaxVersion
    /\ proposedVersion' = v
    /\ decision' = "pending"
    /\ UNCHANGED <<counter, bootedVersion, resetOccurred>>

EvaluateProposal ==
    /\ decision = "pending"
    /\ IF proposedVersion >= counter
       THEN /\ decision' = "accepted"
            /\ counter' = proposedVersion
            /\ bootedVersion' = proposedVersion
       ELSE /\ decision' = "rejected"
            /\ UNCHANGED <<counter, bootedVersion>>
    /\ UNCHANGED <<proposedVersion, resetOccurred>>

SystemReset ==
    /\ resetOccurred' = TRUE
    /\ decision' = "pending"
    /\ proposedVersion' = 0
    \* CRITICAL: counter is NOT reset (non-volatile storage)
    /\ UNCHANGED <<counter, bootedVersion>>

RecoverAfterReset ==
    /\ resetOccurred = TRUE
    /\ resetOccurred' = FALSE
    /\ UNCHANGED <<counter, proposedVersion, decision, bootedVersion>>

Next ==
    \/ \E v \in 0..MaxVersion : ProposeUpdate(v)
    \/ EvaluateProposal
    \/ SystemReset
    \/ RecoverAfterReset

Spec == Init /\ [][Next]_vars

\* --- Security Properties ---

CounterMonotonic == [][counter' >= counter]_counter

RollbackPrevention ==
    (decision = "accepted") => (proposedVersion >= counter)

RejectionSafe ==
    [][decision = "rejected" => counter' = counter]_<<decision, counter>>

CounterSurvivesReset ==
    [][resetOccurred' = TRUE => counter' = counter]_<<resetOccurred, counter>>

BootedVersionValid ==
    bootedVersion >= counter \/ decision = "pending"

====
```

### Assumptions

1. Counter is stored in non-volatile, tamper-resistant storage (OTP fuses or secure NVM)
2. Counter update is atomic with the firmware acceptance decision
3. Counter survives power loss and reset (non-volatile)
4. The counter comparison logic is trusted and cannot be bypassed
5. Firmware version numbers are monotonically ordered integers

### Limitations

1. Does not model physical attacks on the counter storage (e.g., fault injection on OTP fuses)
2. Does not capture the TOCTOU gap between counter check and firmware execution
3. MaxVersion creates a theoretical end-of-life when the counter reaches maximum
4. Does not model branched version numbering (only linear progression)
5. Does not model the firmware image integrity check (only version comparison)
6. Does not model attacker's ability to reprogram the counter directly

### When to Use

Verifying that the anti-rollback mechanism correctly prevents firmware downgrade attacks, that the counter is monotonic and survives reset, and that old firmware versions are always rejected.

### TLC Configuration

```
CONSTANTS:
  MaxVersion = 5
  AttackerVersions = {0, 1, 2, 3, 4, 5}

INVARIANT:
  TypeInvariant
  RollbackPrevention
  BootedVersionValid

PROPERTY:
  CounterMonotonic
  CounterSurvivesReset

Deadlock: disabled
Workers: 4
```

---

*[FROM TRAINING] All TLA+ patterns in this file are derived from general formal methods knowledge, the TLA+ specification language reference, and publicly available security specification techniques. Last verified: 2026-02-13.*
