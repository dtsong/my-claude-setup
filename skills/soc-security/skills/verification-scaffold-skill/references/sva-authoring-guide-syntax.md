# SVA Authoring Guide — Template Syntax and Signal Naming

## Table of Contents

- [Quick Reference](#quick-reference)
- [TEMPLATE vs READY Marking](#2-template-vs-ready-marking)
- [Signal Naming Conventions](#3-signal-naming-conventions)
- [Clock and Reset Handling](#4-clock-and-reset-handling)
- [Property and Assertion Structure](#5-property-and-assertion-structure)

---

## Quick Reference

| Topic | Section | Key Rule |
|-------|---------|----------|
| Annotation requirements | Section 1 | Every assertion MUST have `// INTENT:` and `// DOES NOT CHECK:` |
| TEMPLATE vs READY | Section 2 | `[TEMPLATE]` = placeholder signals, `[READY]` = actual signals |
| Signal naming | Section 3 | Use `<angle_brackets>` for placeholders, descriptive names |
| Clock and reset | Section 4 | Always `disable iff (!<rst_n>)`, document clock domain |
| Property vs assertion | Section 5 | Separate `property` from `assert property` for reuse |
| Coverage | Section 6 | Every assertion must have a companion `cover` property |

---

## 2. TEMPLATE vs READY Marking

### `[TEMPLATE]` — Placeholder Signals

An assertion is marked `[TEMPLATE]` when it uses placeholder signal names because the actual RTL signal names are not available.

**Placeholder conventions:**
- Use angle brackets: `<signal_name>`
- Use descriptive names that indicate what kind of signal is needed: `<access_request>`, `<fsm_state>`, `<key_register>`
- Include a comment next to each placeholder explaining what RTL signal to substitute

```systemverilog
// [TEMPLATE] — Replace placeholder signals with actual RTL signals
// Placeholders:
//   <clk>              → System clock for this module
//   <rst_n>            → Active-low synchronous reset
//   <tdisp_state>      → TDISP FSM current state register (one-hot or encoded)
//   <auth_complete>    → Signal from SPDM module indicating mutual auth passed
//   STATE_LOCKED       → Encoded value for the LOCKED state
//   STATE_DATA_XFER    → Encoded value for the DATA_TRANSFER state
```

### `[READY]` — Actual Signals

An assertion is marked `[READY]` when the engineer has provided actual RTL signal names and they have been substituted into the template.

**READY does not mean correct.** It means the signal names are from the actual design, not placeholders. The assertion still requires:
- Verification that the property logic is correct for the design
- Verification that the signal timing is correct (combinational vs. registered)
- Verification that clock and reset are correct for this module
- Syntax check (will it compile?)
- Semantic check (does it express the intended property?)

```systemverilog
// [READY] — Signal names from user-provided RTL, but assertion logic
//           must still be reviewed for correctness.
// Signals from: tdisp_assignment_ctrl.sv, lines 45-120
```

### Transition from TEMPLATE to READY

When the engineer provides signal information:

1. Replace all `<placeholder>` signals with actual signal names
2. Replace state encoding constants with actual values
3. Update the module instantiation port list
4. Change the marker from `[TEMPLATE]` to `[READY]`
5. Add a note indicating which RTL file the signals come from
6. **Do not change the INTENT or DOES NOT CHECK annotations** — these describe the property, not the signals

---

## 3. Signal Naming Conventions

### Placeholder Naming

| Signal Type | Naming Pattern | Examples |
|------------|---------------|---------|
| Clock | `<clk>`, `<module_clk>` | `<sec_engine_clk>` |
| Reset | `<rst_n>` (active low), `<rst>` (active high) | `<sec_rst_n>` |
| FSM state | `<fsm_name_state>` | `<tdisp_state>`, `<boot_fsm_state>` |
| Control signal | `<action_verb>` or `<noun_adj>` | `<auth_complete>`, `<lock_bit_set>` |
| Data signal | `<data_type>` | `<key_register>`, `<address>`, `<transaction_data>` |
| ID signal | `<entity_id>` | `<master_id>`, `<device_id>` |
| Address signal | `<addr>`, `<base_addr>`, `<limit_addr>` | `<dma_addr>`, `<bar_base>` |
| Valid/enable | `<action_valid>`, `<module_enable>` | `<read_valid>`, `<write_enable>` |

### State Encoding Constants

Use uppercase with underscores for state constants:
```systemverilog
// State encoding (replace with actual values from RTL)
localparam STATE_IDLE        = <IDLE_VALUE>;
localparam STATE_CONFIG      = <CONFIG_VALUE>;
localparam STATE_LOCKED      = <LOCKED_VALUE>;
localparam STATE_DATA_XFER   = <DATA_XFER_VALUE>;
localparam STATE_ERROR       = <ERROR_VALUE>;
```

### Module Port Naming

When wrapping assertions in a module (bind-compatible format):
```systemverilog
module sva_<component>_<property> (
  input logic <clk>,
  input logic <rst_n>,
  // Group 1: State signals
  input logic [<WIDTH-1>:0] <state_signal>,
  // Group 2: Control signals
  input logic <control_signal_1>,
  input logic <control_signal_2>,
  // Group 3: Data signals
  input logic [<WIDTH-1>:0] <data_signal>
);
```

---

## 4. Clock and Reset Handling

### Standard Clock Pattern

```systemverilog
// Always sample on posedge of the module's primary clock
@(posedge <clk>)
```

### Standard Reset Handling

```systemverilog
// Always disable assertions during reset (active-low reset assumed)
disable iff (!<rst_n>)
```

**Why disable during reset:**
- Security FSM state is undefined during reset
- Register values may be in transition
- Assertions during reset would produce false failures
- Reset behavior should be checked by dedicated reset assertions

### Multi-Clock Domain Considerations

When the property involves signals from different clock domains:

```systemverilog
// WARNING: This assertion involves signals from multiple clock domains.
// Signal <cross_domain_signal> originates in <other_clock_domain>.
// This assertion assumes the signal is properly synchronized.
// DOES NOT CHECK: Metastability or synchronization correctness.
// The synchronizer must be verified separately.
```

**Rule:** Never write an assertion that samples a signal from a different clock domain without noting the clock domain crossing. The synchronizer is a separate verification concern.

### Reset Assertion Pattern

For checking behavior immediately after reset:

```systemverilog
// INTENT: After reset deassertion, the security FSM must be in IDLE state
//         and all key registers must be zero. Ensures clean security state
//         after any reset event.
property p_reset_security_state;
  @(posedge <clk>)
  $rose(<rst_n>) |-> ##1
    (<security_fsm_state> == STATE_IDLE) &&
    (<key_register> == '0) &&
    (<lock_bits> == '0);
endproperty
```

---

## 5. Property and Assertion Structure

### Separation of Property and Assertion

Always define the property separately from the assertion. This enables:
- Reuse of the same property in multiple assertions (assert, assume, cover)
- Cleaner error messages
- Easier debugging

```systemverilog
// Property definition (reusable)
property p_<property_name>;
  @(posedge <clk>) disable iff (!<rst_n>)
  <antecedent> |-> <consequent>;
endproperty

// Assertion (triggers on property violation)
a_<property_name>: assert property (p_<property_name>)
  else $error("[<VI-ID>] <descriptive failure message>");

// Cover (tracks property activation)
c_<property_name>_trigger: cover property (
  @(posedge <clk>) <antecedent>
);
```

### Implication Operators

| Operator | Meaning | Use When |
|----------|---------|----------|
| `\|->` | Overlapping implication | Consequent starts in the same cycle as antecedent completes |
| `\|=>` | Non-overlapping implication | Consequent starts in the cycle AFTER antecedent completes |

**For security assertions, prefer `\|->` (overlapping)** unless the property explicitly requires a one-cycle delay. Overlapping implication catches more violations.

### Error Messages

Error messages should be:
- Prefixed with the verification item ID: `[VI-TM-2026-001-003]`
- Descriptive of the specific violation
- Actionable (what went wrong, not just that something went wrong)

```systemverilog
// Good error message:
else $error("[VI-001] TDISP FSM transitioned LOCKED->DATA_TRANSFER without authentication_complete");

// Bad error message:
else $error("assertion failed");
```
