# Eval Case: Noninterference Property for Trust Domain Isolation

## Metadata
- **Case ID:** TS-004
- **Tier:** 2 (medium)
- **Skill Route:** tlaplus-security-skill
- **Estimated Complexity:** medium

## Input
```json
{
  "user_prompt": "Write a TLA+ specification for a noninterference property verifying trust domain isolation in our SoC. We have two trust domains sharing a hardware resource.\n\nSystem description:\n- Trust domains: {HIGH (secure TEE), LOW (normal world OS)}\n- Shared resource: single-ported SRAM (shared crypto scratchpad, 256 entries)\n- Operations:\n  - HIGH can READ and WRITE any entry (full access)\n  - LOW can READ and WRITE entries 128-255 only (lower half restricted)\n  - Each operation is atomic (single cycle)\n- State visible to LOW: entries 128-255 values, plus a status register indicating LOW's last operation result\n- State visible to HIGH: all 256 entries, status register, LOW's operation history (for audit)\n\nNoninterference property:\n- HIGH-domain actions must not be observable by LOW-domain\n- Specifically: for any two system executions that differ only in HIGH-domain actions, the LOW-visible state (entries 128-255 and LOW status register) must be identical\n- This is a standard Goguen-Meseguer noninterference formulation\n\nAttack scenario (from upstream finding):\n- HIGH writes to entry 0-127, but a hardware bug causes a side-effect on the status register visible to LOW\n- The TLA+ spec should detect this as a noninterference violation\n\nUpstream finding: TF-2025-055 — 'Cross-domain information leakage via shared scratchpad status register'",
  "context": "Noninterference via two-copy simulation in TLA+. Two trust domains, shared SRAM, information-flow property. Medium complexity — requires the two-copy technique to formalize noninterference. State space must be abstracted (256 entries is too large for TLC)."
}
```

## Expected Output
A FormalSecSpec with:
- TLA+ module using the two-copy technique (dual system instances) to express noninterference
- HIGH and LOW domain actions modeled with appropriate access permissions
- Noninterference invariant: LOW-visible state identical across both copies when only HIGH actions differ
- Abstraction to make model checking feasible (reduce 256 entries to a small representative set)
- TLC configuration with state space estimate after abstraction

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output contains a syntactically valid TLA+ module expressing a noninterference property
- [ ] Two trust domains (HIGH, LOW) modeled with distinct access permissions
- [ ] Noninterference formalized using two-copy technique or equivalent refinement approach
- [ ] LOW-visible state projection defined explicitly
- [ ] TLC configuration provided with abstraction strategy (256 entries reduced)
- [ ] Upstream finding ID (TF-2025-055) referenced
- [ ] Property classified as information-flow type

### Should Pass (partial credit)
- [ ] Two-copy technique correctly implemented: two system instances that agree on LOW inputs but differ on HIGH inputs
- [ ] Noninterference invariant: LOW_visible(sys1) = LOW_visible(sys2) holds in every reachable state
- [ ] Abstraction documented: 256 entries reduced to N representative entries (e.g., 2-4) with justification that the property is preserved
- [ ] LOW access restriction enforced: LOW cannot read/write entries 0-127
- [ ] Assumptions explicitly listed (e.g., atomic operations, no timing channels, no cache effects)
- [ ] Limitations listed (e.g., does not capture microarchitectural side-channels, timing, or power leakage)

### Bonus
- [ ] Models the specific attack scenario: HIGH write to entry 0-127 with status register side-effect, and shows the invariant detects it
- [ ] Notes that TLA+ noninterference captures functional information flow only — not timing channels or physical side-channels
- [ ] Discusses state space after abstraction with symmetry reduction (symmetric entries within each domain's partition)

## Raw Trace Log
