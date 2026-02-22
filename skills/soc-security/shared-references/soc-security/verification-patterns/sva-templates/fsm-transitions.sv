// =============================================================================
// SVA Templates: Security FSM Transition Assertions
// =============================================================================
//
// VERIFICATION TIER MODEL:
//   Tier 1 (mechanical): SVA assertions for access control, FSM, register locks
//     — HIGH confidence, directly checkable in simulation/formal
//   Tier 2 (protocol): Natural-language property descriptions for DICE, CXL, etc.
//     — needs expert review, may require directed testbench
//   Tier 3 (information flow): Spec-only descriptions, no SVA
//     — side-channel, covert channel, requires specialized analysis
//
// These templates are Tier 1 — designed for direct use in SystemVerilog
// simulation and formal verification.
//
// USAGE:
//   1. Replace [PLACEHOLDER] signal names with actual design signals
//   2. Adjust state encodings and transition rules for your design
//   3. Review DOES NOT CHECK sections for coverage gaps
//   4. Mark as [READY] after integration and signal binding
//
// =============================================================================

// -----------------------------------------------------------------------------
// Template: TDISP TDI State Machine Transitions
// [TEMPLATE]
// -----------------------------------------------------------------------------
// INTENT: Verify that the TDI state machine follows only legal transitions
//         as defined by the TDISP specification.
// DOES NOT CHECK: Whether the conditions for each transition are semantically
//                 correct (e.g., whether authentication actually completed).
//                 Only checks that the state encoding follows legal paths.

module sva_tdisp_state_machine (
  input logic       clk,
  input logic       rst_n,
  input logic [2:0] tdi_state,         // [PLACEHOLDER] current TDI state
  input logic [2:0] tdi_state_next,    // [PLACEHOLDER] next TDI state
  input logic       state_transition,  // [PLACEHOLDER] state change occurring
  input logic       auth_complete,     // [PLACEHOLDER] SPDM authentication done
  input logic       ide_active,        // [PLACEHOLDER] IDE stream established
  input logic       security_violation // [PLACEHOLDER] security violation detected
);

  // State encoding (adjust to match design)
  localparam logic [2:0] ST_CONFIG = 3'b000;
  localparam logic [2:0] ST_LOCK   = 3'b001;
  localparam logic [2:0] ST_RUN    = 3'b010;
  localparam logic [2:0] ST_ERROR  = 3'b011;

  // Only legal transitions allowed
  assert_legal_transitions: assert property (
    @(posedge clk) disable iff (!rst_n)
    state_transition |-> (
      // CONFIG -> LOCK (after auth)
      ((tdi_state == ST_CONFIG) && (tdi_state_next == ST_LOCK)) ||
      // LOCK -> RUN (after IDE setup)
      ((tdi_state == ST_LOCK) && (tdi_state_next == ST_RUN)) ||
      // RUN -> CONFIG (tear-down)
      ((tdi_state == ST_RUN) && (tdi_state_next == ST_CONFIG)) ||
      // Any -> ERROR (security violation)
      (tdi_state_next == ST_ERROR) ||
      // ERROR -> CONFIG (recovery)
      ((tdi_state == ST_ERROR) && (tdi_state_next == ST_CONFIG))
    )
  ) else $error("SVA FAIL: Illegal TDI state transition %0d -> %0d",
                 tdi_state, tdi_state_next);

  // CONFIG -> LOCK requires authentication complete
  assert_auth_before_lock: assert property (
    @(posedge clk) disable iff (!rst_n)
    (state_transition && (tdi_state == ST_CONFIG) && (tdi_state_next == ST_LOCK))
    |-> auth_complete
  ) else $error("SVA FAIL: CONFIG -> LOCK without authentication");

  // LOCK -> RUN requires IDE active
  assert_ide_before_run: assert property (
    @(posedge clk) disable iff (!rst_n)
    (state_transition && (tdi_state == ST_LOCK) && (tdi_state_next == ST_RUN))
    |-> ide_active
  ) else $error("SVA FAIL: LOCK -> RUN without IDE stream");

  // Security violation must cause transition to ERROR
  assert_violation_to_error: assert property (
    @(posedge clk) disable iff (!rst_n)
    security_violation |=> (tdi_state == ST_ERROR)
  ) else $error("SVA FAIL: Security violation did not cause ERROR state");

  // No direct CONFIG -> RUN (must go through LOCK)
  assert_no_config_to_run: assert property (
    @(posedge clk) disable iff (!rst_n)
    (state_transition && (tdi_state == ST_CONFIG))
    |-> (tdi_state_next != ST_RUN)
  ) else $error("SVA FAIL: Direct CONFIG -> RUN transition (must go through LOCK)");

endmodule


// -----------------------------------------------------------------------------
// Template: Secure Boot Stage Transition
// [TEMPLATE]
// -----------------------------------------------------------------------------
// INTENT: Verify that boot stage transitions follow the DICE layered model:
//         measure, derive CDI, lock previous secrets, then execute next stage.
// DOES NOT CHECK: Correctness of the CDI derivation algorithm itself.

module sva_boot_stage_transition (
  input logic       clk,
  input logic       rst_n,
  input logic       measurement_done,    // [PLACEHOLDER] measurement of next stage complete
  input logic       cdi_derived,         // [PLACEHOLDER] CDI for next stage derived
  input logic       prev_secret_locked,  // [PLACEHOLDER] previous stage secrets locked
  input logic       next_stage_execute,  // [PLACEHOLDER] next boot stage starts executing
  input logic       derivation_error,    // [PLACEHOLDER] CDI derivation failed
  input logic       error_state          // [PLACEHOLDER] entered error/halt state
);

  // Next stage must not execute without measurement
  assert_measure_before_execute: assert property (
    @(posedge clk) disable iff (!rst_n)
    $rose(next_stage_execute) |-> measurement_done
  ) else $error("SVA FAIL: Next boot stage executed without measurement");

  // Next stage must not execute without CDI derivation
  assert_cdi_before_execute: assert property (
    @(posedge clk) disable iff (!rst_n)
    $rose(next_stage_execute) |-> cdi_derived
  ) else $error("SVA FAIL: Next boot stage executed without CDI derivation");

  // Previous secrets must be locked before next stage executes
  assert_lock_before_execute: assert property (
    @(posedge clk) disable iff (!rst_n)
    $rose(next_stage_execute) |-> prev_secret_locked
  ) else $error("SVA FAIL: Next boot stage executed with previous secrets accessible");

  // Derivation error must halt boot (no execute after error)
  assert_error_halts_boot: assert property (
    @(posedge clk) disable iff (!rst_n)
    derivation_error |=> error_state && !next_stage_execute
  ) else $error("SVA FAIL: Boot continued after CDI derivation error");

  // Ordering: measurement -> CDI -> lock -> execute
  // (cover property to verify the expected sequence occurs)
  cover_normal_boot: cover property (
    @(posedge clk) disable iff (!rst_n)
    $rose(measurement_done) ##[1:100] $rose(cdi_derived)
    ##[1:100] $rose(prev_secret_locked) ##[1:100] $rose(next_stage_execute)
  );

endmodule


// -----------------------------------------------------------------------------
// Template: Debug Authentication FSM
// [TEMPLATE]
// -----------------------------------------------------------------------------
// INTENT: Verify that debug features are not enabled without completing
//         the authentication handshake. Secrets must be zeroized if debug
//         is unlocked.
// DOES NOT CHECK: Strength of the challenge-response authentication itself.

module sva_debug_auth_fsm (
  input logic       clk,
  input logic       rst_n,
  input logic [1:0] debug_state,        // [PLACEHOLDER] debug auth FSM state
  input logic       debug_challenge_sent,  // [PLACEHOLDER] challenge issued to debug port
  input logic       debug_response_valid,  // [PLACEHOLDER] valid response received
  input logic       debug_authenticated,   // [PLACEHOLDER] auth handshake complete
  input logic       debug_enabled,         // [PLACEHOLDER] debug features active
  input logic       secrets_zeroized,      // [PLACEHOLDER] sensitive keys cleared
  input logic       debug_locked_fuse      // [PLACEHOLDER] permanent debug disable fuse
);

  // Debug state encoding
  localparam logic [1:0] DBG_LOCKED       = 2'b00;
  localparam logic [1:0] DBG_CHALLENGE    = 2'b01;
  localparam logic [1:0] DBG_AUTHENTICATED = 2'b10;
  localparam logic [1:0] DBG_ACTIVE       = 2'b11;

  // Debug must not be enabled without authentication
  assert_auth_before_debug: assert property (
    @(posedge clk) disable iff (!rst_n)
    debug_enabled |-> debug_authenticated
  ) else $error("SVA FAIL: Debug enabled without authentication");

  // If permanent debug disable fuse is blown, debug must never enable
  assert_fuse_disables_debug: assert property (
    @(posedge clk) disable iff (!rst_n)
    debug_locked_fuse |-> !debug_enabled
  ) else $error("SVA FAIL: Debug enabled despite permanent disable fuse");

  // Debug unlock must trigger secret zeroization
  assert_debug_zeros_secrets: assert property (
    @(posedge clk) disable iff (!rst_n)
    $rose(debug_enabled) |=> secrets_zeroized
  ) else $error("SVA FAIL: Secrets not zeroized after debug unlock");

endmodule


// -----------------------------------------------------------------------------
// Template: DICE Layer Secret Locking
// [TEMPLATE]
// -----------------------------------------------------------------------------
// INTENT: Verify that UDS and CDI registers become inaccessible after the
//         DICE layer transition. Once locked, reads return zero or error.
// DOES NOT CHECK: Whether the CDI value itself was correctly derived.

module sva_dice_secret_lock (
  input logic       clk,
  input logic       rst_n,
  input logic       secret_lock_asserted,  // [PLACEHOLDER] lock signal for secret register
  input logic       secret_read_request,   // [PLACEHOLDER] attempt to read secret
  input logic       secret_read_returns_data, // [PLACEHOLDER] actual secret data returned
  input logic       layer_transition       // [PLACEHOLDER] DICE layer transition event
);

  // After lock, reads must not return secret data
  assert_locked_no_data: assert property (
    @(posedge clk) disable iff (!rst_n)
    (secret_lock_asserted && secret_read_request) |-> !secret_read_returns_data
  ) else $error("SVA FAIL: Secret register returned data after lock");

  // Lock must be irreversible within a boot cycle (once set, stays set)
  assert_lock_irreversible: assert property (
    @(posedge clk) disable iff (!rst_n)
    $rose(secret_lock_asserted) |-> ##[1:$] secret_lock_asserted
  ) else $error("SVA FAIL: Secret lock was deasserted after being set");

  // Layer transition must coincide with or follow lock
  assert_lock_before_transition: assert property (
    @(posedge clk) disable iff (!rst_n)
    $rose(layer_transition) |-> secret_lock_asserted
  ) else $error("SVA FAIL: Layer transition occurred without secret lock");

endmodule
