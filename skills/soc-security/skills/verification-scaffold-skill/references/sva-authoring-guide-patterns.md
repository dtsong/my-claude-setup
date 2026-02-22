# SVA Authoring Guide — Patterns, Examples, and Anti-Patterns

## Table of Contents

- [Common SVA Patterns for Security Properties](#7-common-sva-patterns-for-security-properties)
- [Pattern Library Overview](#pattern-library-overview)
- [Pattern 8: Sequence Ordering](#pattern-8-sequence-ordering)
- [Pattern 9: Counter Monotonicity](#pattern-9-counter-monotonicity)
- [Pattern 10: Key Zeroization](#pattern-10-key-zeroization)
- [Anti-Patterns](#8-anti-patterns)
- [Assertion Template File Structure](#9-assertion-template-file-structure)
- [Synthesis vs Simulation Considerations](#10-synthesis-vs-simulation-considerations)

---

## 7. Common SVA Patterns for Security Properties

### Pattern Library Overview

| # | Pattern | Security Use | Complexity |
|---|---------|-------------|-----------|
| 1 | Access Control Gate | Protect resources from unauthorized access | Low |
| 2 | FSM Transition Guard | Ensure correct state machine behavior | Low-Medium |
| 3 | Register Lock | Prevent modification after configuration | Low |
| 4 | Address Range Check | Enforce memory region boundaries | Low |
| 5 | One-Hot Encoding | Detect state corruption | Low |
| 6 | Mutual Exclusion | Prevent race conditions | Low |
| 7 | Handshake Timeout | Detect stalled security protocols | Medium |
| 8 | Sequence Ordering | Enforce operation ordering | Medium |
| 9 | Counter Monotonicity | Ensure counters only increment | Low |
| 10 | Key Zeroization | Verify key material is erased | Low-Medium |

### Pattern 8: Sequence Ordering

```systemverilog
// INTENT: Operations A and B must occur in order (A before B) within
//         the same security session. Prevents out-of-order execution
//         that could bypass security checks.
// DOES NOT CHECK: Whether A was successful (only that it occurred),
//                  whether there are intervening operations between A and B,
//                  ordering across different sessions.

property p_sequence_ordering;
  @(posedge <clk>) disable iff (!<rst_n>)
  // If B occurs, A must have occurred earlier in this session
  ($rose(<operation_b>) && <session_active>) |->
    <operation_a_completed>;
endproperty

// Note: <operation_a_completed> should be a sticky flag set when A occurs
// and cleared at session start. This avoids unbounded temporal lookback.
```

### Pattern 9: Counter Monotonicity

```systemverilog
// INTENT: Anti-rollback counter must never decrease. Any decrease indicates
//         a tampering attempt to roll back to a previous firmware version.
// DOES NOT CHECK: Counter overflow behavior, whether the counter value
//                  is correct (only that it doesn't decrease), counter
//                  initialization value.

property p_counter_monotonic;
  @(posedge <clk>) disable iff (!<rst_n>)
  // Counter value must be >= previous value at all times
  (<counter_valid>) |-> (<counter_value> >= $past(<counter_value>));
endproperty

// Note: $past() returns the value from the previous clock cycle.
// For counters that update infrequently, consider a sticky max-value tracker.
```

### Pattern 10: Key Zeroization

```systemverilog
// INTENT: When key_zeroize is asserted, the key register must be
//         completely zeroed within MAX_ZEROIZE_CYCLES. Ensures that
//         key material does not persist after a security context ends
//         or an error condition occurs.
// DOES NOT CHECK: Whether the memory cells physically retain the key
//                  (remanence), whether all copies of the key are zeroed
//                  (only this specific register), whether zeroization
//                  was triggered at the right time.

property p_key_zeroization;
  @(posedge <clk>) disable iff (!<rst_n>)
  $rose(<key_zeroize>) |-> ##[1:<MAX_ZEROIZE_CYCLES>] (<key_register> == '0);
endproperty
```

---

## 8. Anti-Patterns

### What NOT to Do in Security SVA

#### Anti-Pattern 1: Vacuously True Assertion

```systemverilog
// BAD: Antecedent condition is always false
property p_vacuous;
  @(posedge clk) disable iff (!rst_n)
  (1'b0) |-> (key_out != key_in);  // Never fires — provides zero coverage
endproperty
```

**Fix:** Ensure the antecedent can actually occur in simulation. Use coverage companions to detect vacuous assertions.

#### Anti-Pattern 2: Checking Information Flow with SVA

```systemverilog
// BAD: Attempting to verify information flow through signal comparison
property p_bad_info_flow;
  @(posedge clk) disable iff (!rst_n)
  $changed(secret_key) |-> $stable(public_output);
endproperty
// This does NOT verify information flow. Information can flow through
// intermediate signals, across multiple cycles, or through timing.
```

**Fix:** Classify as Tier 3. Use information flow analysis tools.

#### Anti-Pattern 3: Unbounded Temporal Property

```systemverilog
// BAD: Unbounded "eventually" — may never terminate in bounded model checking
property p_unbounded;
  @(posedge clk) disable iff (!rst_n)
  request |-> ##[1:$] acknowledge;
  // ##[1:$] means "eventually" — some formal tools cannot handle this
endproperty
```

**Fix:** Use bounded time: `##[1:MAX_CYCLES]`. Document the bound and its rationale.

#### Anti-Pattern 4: Missing Reset Handling

```systemverilog
// BAD: No disable iff — assertion fires during reset when state is undefined
property p_no_reset;
  @(posedge clk)  // Missing: disable iff (!rst_n)
  (state == LOCKED) |-> locked_output;
endproperty
```

**Fix:** Always include `disable iff (!<rst_n>)`.

#### Anti-Pattern 5: Assertion on Combinational Loop

```systemverilog
// BAD: Referencing a signal that depends on the assertion's own output
// (can occur when assertion output feeds back into design via assertion action blocks)
```

**Fix:** Assertions should be purely observational. Never use assertion action blocks (`pass`, `fail`) to drive design signals.

#### Anti-Pattern 6: Overconfident Coverage Claim

```systemverilog
// BAD annotation:
// INTENT: Completely verifies that the bus access control is secure.
// [No single assertion can "completely verify" anything]
```

**Fix:** Be specific and honest about what one assertion checks. Coverage requires a suite of assertions, not one "complete" assertion.

#### Anti-Pattern 7: Copy-Paste Annotations

```systemverilog
// BAD: Same annotation on every assertion (clearly copy-pasted)
// DOES NOT CHECK: Side-channel attacks, fault injection, multi-step attacks.
// [This may be true but it's generic — specific omissions matter more]
```

**Fix:** Each assertion's `DOES NOT CHECK` must be specific to what THAT assertion omits. Generic items can appear, but at least 1-2 items must be specific to the particular property being checked.

---

## 9. Assertion Template File Structure

### Recommended File Organization

Each verification scaffold should organize assertions by attack surface:

```
verification-scaffold/
├── sva_access_control/
│   ├── sva_key_storage_access.sv
│   ├── sva_register_write_protect.sv
│   └── sva_bus_firewall.sv
├── sva_fsm_integrity/
│   ├── sva_tdisp_transitions.sv
│   ├── sva_boot_fsm.sv
│   └── sva_state_encoding.sv
├── sva_range_checks/
│   ├── sva_dma_address_range.sv
│   └── sva_bar_decoding.sv
├── sva_key_management/
│   ├── sva_key_lock.sv
│   ├── sva_key_zeroization.sv
│   └── sva_key_rotation_timeout.sv
└── bind_file.sv  # Central bind file for all assertions
```

### Bind File Template

```systemverilog
// =============================================================================
// Bind File: Security Assertion Templates
// Source: [VC-YYYY-NNN]
// Status: [TEMPLATE] — All module paths and signal names require customization
// =============================================================================

// Access Control assertions
bind <target_module_path> sva_key_storage_access sva_key_inst (
  .clk     (<module_clk>),
  .rst_n   (<module_rst_n>),
  // ... signal connections
);

// FSM Integrity assertions
bind <target_module_path> sva_tdisp_transitions sva_tdisp_inst (
  .clk     (<module_clk>),
  .rst_n   (<module_rst_n>),
  // ... signal connections
);

// [Repeat for all assertion modules]
```

---

## 10. Synthesis vs. Simulation Considerations

### Synthesis-Friendly SVA

Some assertions may need to be synthesized (e.g., for emulation or FPGA prototyping). Synthesis-friendly SVA constraints:

| Feature | Simulation | Synthesis-Friendly |
|---------|-----------|-------------------|
| `$past()` | Yes | Yes (single cycle) |
| `$rose()`, `$fell()` | Yes | Yes |
| `$stable()` | Yes | Yes |
| `$onehot()` | Yes | Yes |
| `##[1:N]` bounded delay | Yes | Yes (small N) |
| `##[1:$]` unbounded | Yes | No |
| `[*0:$]` unbounded rep | Yes | No |
| `$sampled()` | Yes | Tool-dependent |
| `$changed()` | Yes | Yes |
| `throughout` | Yes | Yes |

### Marking Synthesis Compatibility

```systemverilog
// SYNTHESIS NOTE: This assertion uses $past() with single-cycle delay —
//                  compatible with synthesis/emulation tools.

// SYNTHESIS NOTE: This assertion uses ##[1:$] (unbounded delay) —
//                  simulation only. For synthesis, replace with bounded
//                  version: ##[1:MAX_CYCLES].
```
