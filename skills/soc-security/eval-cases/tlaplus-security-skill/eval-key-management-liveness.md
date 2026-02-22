# Eval Case: Key Management Liveness Property Specification

## Metadata
- **Case ID:** TS-003
- **Tier:** 2 (medium)
- **Skill Route:** tlaplus-security-skill
- **Estimated Complexity:** medium

## Input
```json
{
  "user_prompt": "Write a TLA+ specification for our SoC key management subsystem with both safety and liveness properties.\n\nSystem description:\n- Key slots: 4 hardware key slots (SLOT_0 through SLOT_3)\n- Key states per slot: {EMPTY, PROVISIONING, ACTIVE, SUSPENDED, DESTROYED}\n- Key lifecycle transitions:\n  - EMPTY -> PROVISIONING (key generation initiated)\n  - PROVISIONING -> ACTIVE (key generation complete, key usable)\n  - PROVISIONING -> DESTROYED (generation failed, cleanup)\n  - ACTIVE -> SUSPENDED (temporary revocation)\n  - SUSPENDED -> ACTIVE (reinstatement)\n  - ACTIVE -> DESTROYED (permanent revocation)\n  - SUSPENDED -> DESTROYED (permanent revocation)\n  - DESTROYED -> EMPTY (slot recycling after zeroization)\n\n- Concurrency: multiple key operations can occur simultaneously on different slots\n- Constraint: at most 1 slot in PROVISIONING state at a time (hardware RNG limitation)\n\nSecurity properties:\n1. (Safety invariant) A DESTROYED key slot cannot transition to ACTIVE without passing through EMPTY and PROVISIONING first\n2. (Safety invariant) At most 1 slot in PROVISIONING at any time\n3. (Liveness) Every key in PROVISIONING state eventually reaches either ACTIVE or DESTROYED (no stuck provisioning)\n4. (Liveness) Every DESTROYED slot is eventually recycled to EMPTY (no permanent slot exhaustion)\n\nFairness assumption: the key generation hardware is weakly fair (if continuously enabled, it eventually completes).\n\nUpstream finding: TF-2025-031 — 'Key slot exhaustion via abandoned provisioning operations'",
  "context": "Key management with lifecycle state machine. 4 concurrent key slots with a provisioning constraint. Mix of safety invariants and liveness properties. Fairness assumptions needed for liveness. Medium complexity — concurrent slots with constrained transitions."
}
```

## Expected Output
A FormalSecSpec with:
- TLA+ module modeling 4 key slots each with lifecycle state machine
- Concurrent slot operations with the provisioning exclusion constraint
- Two safety invariants and two liveness properties as TLA+ temporal formulas
- Fairness conditions (weak fairness) on key generation and slot recycling actions
- TLC configuration with state space estimate

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output contains a syntactically valid TLA+ module modeling key slot lifecycle
- [ ] 4 key slots modeled with states {EMPTY, PROVISIONING, ACTIVE, SUSPENDED, DESTROYED}
- [ ] At least one safety invariant expressed as a TLA+ INVARIANT
- [ ] At least one liveness property expressed as a TLA+ temporal PROPERTY (using <> or ~>)
- [ ] Fairness assumption explicitly stated and included in the Spec definition (WF or SF)
- [ ] TLC configuration provided
- [ ] Upstream finding ID (TF-2025-031) referenced

### Should Pass (partial credit)
- [ ] Provisioning exclusion constraint enforced: at most 1 slot in PROVISIONING at a time
- [ ] DESTROYED-to-ACTIVE bypass invariant correctly prevents skipping EMPTY and PROVISIONING
- [ ] Liveness property for provisioning completion: PROVISIONING ~> (ACTIVE \/ DESTROYED)
- [ ] Liveness property for slot recycling: DESTROYED ~> EMPTY
- [ ] Fairness documented: "This liveness property holds ONLY under weak fairness of [action]. Without fairness, [counterexample]."
- [ ] State space estimate: 5^4 = 625 base states per slot configuration (feasible for TLC)
- [ ] Concurrent operations on different slots modeled (not sequential lock-step)

### Bonus
- [ ] Notes that without fairness, a PROVISIONING slot could be starved indefinitely — the TLA+ spec without fairness admits infinite stuttering
- [ ] Models a slot exhaustion scenario: all 4 slots DESTROYED with no recycling, demonstrating why liveness property 4 matters
- [ ] Limitations note that real key zeroization time is not modeled — DESTROYED to EMPTY may take variable time in hardware

## Raw Trace Log
