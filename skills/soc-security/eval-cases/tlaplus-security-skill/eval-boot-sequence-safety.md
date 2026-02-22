# Eval Case: Boot Sequence Safety Property Specification

## Metadata
- **Case ID:** TS-002
- **Tier:** 1 (simple)
- **Skill Route:** tlaplus-security-skill
- **Estimated Complexity:** low

## Input
```json
{
  "user_prompt": "Write a TLA+ specification for the secure boot sequence of our SoC. The boot chain has 4 stages:\n\nBoot stages (in order):\n1. ROM (immutable, root of trust)\n2. BL1 (first-stage bootloader, authenticated by ROM)\n3. BL2 (second-stage bootloader, authenticated by BL1)\n4. OS_KERNEL (authenticated by BL2)\n\nBoot state machine:\n- Initial state: RESET\n- Transitions: RESET -> ROM_EXEC -> BL1_VERIFY -> BL1_EXEC -> BL2_VERIFY -> BL2_EXEC -> KERNEL_VERIFY -> KERNEL_EXEC -> RUNNING\n- On verification failure at any stage: transition to BOOT_FAILED (terminal state)\n- No rollback: once a stage advances, it cannot return to a previous stage\n\nSecurity properties to verify:\n1. (Safety) KERNEL_EXEC is reachable only through the complete chain: ROM_EXEC -> BL1_VERIFY -> BL1_EXEC -> BL2_VERIFY -> BL2_EXEC -> KERNEL_VERIFY -> KERNEL_EXEC\n2. (Safety) No state can transition backward (anti-rollback)\n3. (Safety) BOOT_FAILED is a terminal state — no recovery without full reset\n\nUpstream finding: TF-2025-018 — 'Boot stage skip allows unsigned BL2 execution'",
  "context": "Linear boot chain with verification at each stage. Finite state machine with 9 states. Three safety properties. Simple — no branching, no concurrency, deterministic transitions."
}
```

## Expected Output
A FormalSecSpec with:
- TLA+ module modeling the boot state machine with 9 states
- Verification success/failure modeled as nondeterministic choice at each verify stage
- Three safety invariants as TLA+ formulas
- Proof that no stage can be skipped in the chain
- TLC configuration for exhaustive checking

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output contains a syntactically valid TLA+ module with Init, Next, and Spec definitions
- [ ] Boot states modeled (at minimum: RESET, ROM_EXEC, verify/exec stages, RUNNING, BOOT_FAILED)
- [ ] At least one safety property expressed as a TLA+ formula checkable by TLC
- [ ] No-skip property formalized — KERNEL_EXEC requires traversal of all prior stages
- [ ] TLC configuration provided
- [ ] Upstream finding ID (TF-2025-018) referenced

### Should Pass (partial credit)
- [ ] All three safety properties formalized: chain integrity, anti-rollback, BOOT_FAILED terminal
- [ ] Anti-rollback expressed as a temporal property or invariant on state ordering
- [ ] BOOT_FAILED modeled as absorbing state (no outgoing transitions except to itself or none)
- [ ] Verification at each stage modeled as nondeterministic (can succeed or fail)
- [ ] State space estimated — 9 states, fully enumerable
- [ ] Assumptions documented (e.g., atomic transitions, ROM is trustworthy)

### Bonus
- [ ] Models an attacker action attempting to skip a boot stage and shows the invariant catches it
- [ ] Notes that the TLA+ model does not capture fault injection that could corrupt the state variable itself
- [ ] Includes a version/monotonic counter for anti-rollback of firmware images (beyond stage ordering)

## Raw Trace Log
