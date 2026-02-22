## Contents

- [Pattern 1: Access Control Gate](#pattern-1-access-control-gate)
- [Pattern 2: FSM Transition Guard](#pattern-2-fsm-transition-guard)
- [Pattern 3: Register Lock (Write Protection After Lock)](#pattern-3-register-lock-write-protection-after-lock)
- [Pattern 4: Address Range Bounds Check](#pattern-4-address-range-bounds-check)
- [Pattern 5: One-Hot State Encoding](#pattern-5-one-hot-state-encoding)
- [Pattern 6: Mutual Exclusion](#pattern-6-mutual-exclusion)
- [Pattern 7: Handshake Timeout (Bounded Liveness)](#pattern-7-handshake-timeout-bounded-liveness)
- [Domain-Specific Tier 2 Patterns](#domain-specific-tier-2-patterns)
  - [DICE Protocol: Layer Measurement Ordering](#dice-protocol-layer-measurement-ordering)
  - [TDISP: Assignment State Machine Ordering](#tdisp-assignment-state-machine-ordering)
  - [CXL: IDE Key Rotation Compliance](#cxl-ide-key-rotation-compliance)
  - [SPDM: Mutual Authentication Freshness](#spdm-mutual-authentication-freshness)

## Pattern 1: Access Control Gate

```systemverilog
// INTENT: Only authorized master(s) can access protected resource in secured state.
// DOES NOT CHECK: Authorization mechanism itself, master identity spoofing,
//   DMA-based access bypassing this check, fault injection on gate signal.

property p_access_control_gate;
  @(posedge <clk>) disable iff (!<rst_n>)
  (<access_request> && <secured_state>) |-> <authorized_master>;
endproperty
```

## Pattern 2: FSM Transition Guard

```systemverilog
// INTENT: State transition from [state_A] to [state_B] requires [guard_condition].
// DOES NOT CHECK: Glitch-based state corruption, state encoding integrity,
//   transitions to other states, multi-cycle attack sequences.

property p_fsm_transition_guard;
  @(posedge <clk>) disable iff (!<rst_n>)
  (<state> == <STATE_A>) ##1 (<state> == <STATE_B>) |->
    $past(<guard_condition>);
endproperty
```

## Pattern 3: Register Lock (Write Protection After Lock)

```systemverilog
// INTENT: Once lock bit set, protected register cannot change.
// DOES NOT CHECK: Whether lock bit itself can be cleared,
//   reset behavior, register reads (write protection only).

property p_register_lock;
  @(posedge <clk>) disable iff (!<rst_n>)
  $rose(<lock_bit>) |-> ##1 $stable(<protected_register>)[*0:$];
endproperty

// Note: [*0:$] = "for all subsequent cycles" — strong liveness property.
// Some tools may require bounded version: [*0:MAX_CYCLES]
```

## Pattern 4: Address Range Bounds Check

```systemverilog
// INTENT: Transactions from protected device are within assigned range [base, base+size).
// DOES NOT CHECK: Whether base/size are correctly configured, address aliasing,
//   transactions by other bus masters, non-memory-mapped transactions.

property p_address_range_check;
  @(posedge <clk>) disable iff (!<rst_n>)
  (<valid_transaction> && <device_id> == <PROTECTED_DEVICE>) |->
    (<address> >= <base_addr>) && (<address> < (<base_addr> + <size>));
endproperty
```

## Pattern 5: One-Hot State Encoding

```systemverilog
// INTENT: Security FSM state register maintains valid one-hot encoding.
//   Detects state corruption from fault injection or logic errors.
// DOES NOT CHECK: Whether one-hot encoding is the correct state,
//   glitches shorter than one clock cycle, state transitions.

property p_onehot_state;
  @(posedge <clk>) disable iff (!<rst_n>)
  $onehot(<state_register>);
endproperty
```

## Pattern 6: Mutual Exclusion

```systemverilog
// INTENT: Mutually exclusive operations on key storage cannot occur simultaneously.
// DOES NOT CHECK: Temporal proximity (adjacent cycles), operations from different
//   clock domains, logically related operations using different physical signals.

property p_mutual_exclusion;
  @(posedge <clk>) disable iff (!<rst_n>)
  not (<operation_a_active> && <operation_b_active>);
endproperty
```

## Pattern 7: Handshake Timeout (Bounded Liveness)

```systemverilog
// INTENT: After security handshake request, must complete within MAX_CYCLES.
//   Prevents indefinite stall exploitable for denial of service.
// DOES NOT CHECK: Whether handshake completed correctly (only that it completed),
//   timeout recovery behavior, multi-handshake interleaving.

property p_handshake_timeout;
  @(posedge <clk>) disable iff (!<rst_n>)
  <handshake_request> |-> ##[1:<MAX_CYCLES>] <handshake_complete>;
endproperty
```

## Domain-Specific Tier 2 Patterns

### DICE Protocol: Layer Measurement Ordering

**Statement:** "Before Layer N+1 begins execution, Layer N must have: (1) measured the Layer N+1 code image, (2) derived the CDI for Layer N+1, (3) sealed Layer N CDI so it is no longer accessible."

**Checks:** Correct DICE layering — each layer's identity bound to next layer's integrity.
**Does NOT check:** Measurement algorithm collision resistance, CDI derivation cryptographic strength, sealing mechanism physical security.

### TDISP: Assignment State Machine Ordering

**Statement:** "A TDI must transition through IDLE -> CONFIG -> LOCK -> RUN with each transition gated by appropriate completion signal. No state may be skipped. RUN must not be entered without LOCK achieved and SPDM authentication completed."

**Checks:** Protocol compliance of assignment sequence.
**Does NOT check:** SPDM authentication security, device identity legitimacy, assigned memory range correctness.

### CXL: IDE Key Rotation Compliance

**Statement:** "IDE stream encryption keys must be rotated at intervals not exceeding KEY_ROTATION_MAX_INTERVAL. Key rotation must complete atomically — no traffic processed with expired key or during transition."

**Checks:** Timely key rotation and atomic transition.
**Does NOT check:** Key generation quality, key storage security, rotation interval configuration appropriateness.

### SPDM: Mutual Authentication Freshness

**Statement:** "Each SPDM authentication session must use fresh nonce from both requester and responder. No nonce reuse across sessions. Authentication result must not be cached beyond configured validity period."

**Checks:** Replay resistance in authentication protocol.
**Does NOT check:** Nonce generation quality (entropy), certificate chain validity, revocation checking.
