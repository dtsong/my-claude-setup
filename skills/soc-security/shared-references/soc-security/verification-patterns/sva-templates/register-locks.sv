// =============================================================================
// SVA Templates: Register Lock Assertions
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
//   2. Adjust parameters for your design's specifics
//   3. Review DOES NOT CHECK sections for coverage gaps
//   4. Mark as [READY] after integration and signal binding
//
// =============================================================================

// -----------------------------------------------------------------------------
// Template: Write-Once Lock Bit (Sticky)
// [TEMPLATE]
// -----------------------------------------------------------------------------
// INTENT: Verify that a lock bit, once set, cannot be cleared until the next
//         reset. This is the fundamental primitive for security configuration
//         locks, anti-rollback counters, and DICE secret locking.
// DOES NOT CHECK: Whether the lock bit was set at the correct time.

module sva_write_once_lock (
  input logic clk,
  input logic rst_n,
  input logic lock_bit,       // [PLACEHOLDER] the lock bit register value
  input logic lock_write,     // [PLACEHOLDER] attempt to write the lock bit
  input logic lock_write_val  // [PLACEHOLDER] value being written
);

  // Once lock bit is set, it must remain set until reset
  assert_sticky_lock: assert property (
    @(posedge clk) disable iff (!rst_n)
    $rose(lock_bit) |-> ##[1:$] lock_bit until (!rst_n)
  ) else $error("SVA FAIL: Lock bit cleared without reset");

  // Alternative formulation: lock bit can only transition 0->1, never 1->0
  assert_no_unlock: assert property (
    @(posedge clk) disable iff (!rst_n)
    lock_bit |=> lock_bit
  ) else $error("SVA FAIL: Lock bit transitioned from 1 to 0");

  // Attempt to clear a set lock bit must be ignored
  assert_clear_ignored: assert property (
    @(posedge clk) disable iff (!rst_n)
    (lock_bit && lock_write && !lock_write_val) |=> lock_bit
  ) else $error("SVA FAIL: Write of 0 to set lock bit was not ignored");

endmodule


// -----------------------------------------------------------------------------
// Template: Register Field Write Protection (Lock-Gated)
// [TEMPLATE]
// -----------------------------------------------------------------------------
// INTENT: Verify that a register field becomes read-only when its associated
//         lock bit is set. Used for security configuration registers that
//         must be frozen after boot or after TDISP LOCK state entry.
// DOES NOT CHECK: Whether the register value itself is correct.

module sva_register_field_lock #(
  parameter int FIELD_WIDTH = 32
)(
  input logic                    clk,
  input logic                    rst_n,
  input logic                    lock_bit,         // [PLACEHOLDER] controlling lock bit
  input logic [FIELD_WIDTH-1:0]  reg_field,        // [PLACEHOLDER] the protected register field
  input logic                    field_write_en,   // [PLACEHOLDER] attempt to write the field
  input logic [FIELD_WIDTH-1:0]  field_write_data  // [PLACEHOLDER] data being written
);

  // When locked, register field must not change
  assert_locked_no_change: assert property (
    @(posedge clk) disable iff (!rst_n)
    lock_bit |=> ($stable(reg_field))
  ) else $error("SVA FAIL: Locked register field changed value");

  // When locked, write attempts must be silently dropped (value unchanged)
  assert_locked_write_dropped: assert property (
    @(posedge clk) disable iff (!rst_n)
    (lock_bit && field_write_en) |=> ($stable(reg_field))
  ) else $error("SVA FAIL: Write to locked register field was not dropped");

  // When unlocked, writes should take effect (basic functionality check)
  cover_unlocked_write: cover property (
    @(posedge clk) disable iff (!rst_n)
    !lock_bit && field_write_en ##1 (reg_field == $past(field_write_data))
  );

endmodule


// -----------------------------------------------------------------------------
// Template: Monotonic Counter (Anti-Rollback)
// [TEMPLATE]
// -----------------------------------------------------------------------------
// INTENT: Verify that a monotonic counter (used for anti-rollback, sequence
//         numbers, or security version numbers) can only increment, never
//         decrement or wrap around.
// DOES NOT CHECK: Whether the counter is incremented at the correct time
//                 or by the correct amount.

module sva_monotonic_counter #(
  parameter int COUNTER_WIDTH = 32
)(
  input logic                       clk,
  input logic                       rst_n,
  input logic [COUNTER_WIDTH-1:0]   counter_value,  // [PLACEHOLDER] current counter value
  input logic                       counter_write,  // [PLACEHOLDER] counter write attempt
  input logic [COUNTER_WIDTH-1:0]   counter_wdata   // [PLACEHOLDER] value being written
);

  // Counter must never decrease
  assert_never_decrement: assert property (
    @(posedge clk) disable iff (!rst_n)
    ##1 (counter_value >= $past(counter_value))
  ) else $error("SVA FAIL: Monotonic counter decremented from %0d to %0d",
                 $past(counter_value), counter_value);

  // Write of a value less than current must be rejected (counter unchanged)
  assert_reject_rollback_write: assert property (
    @(posedge clk) disable iff (!rst_n)
    (counter_write && (counter_wdata < counter_value)) |=>
    (counter_value == $past(counter_value))
  ) else $error("SVA FAIL: Rollback write to monotonic counter was accepted");

  // Counter must not overflow/wrap (if near max, increment must not wrap to 0)
  assert_no_wrap: assert property (
    @(posedge clk) disable iff (!rst_n)
    (counter_value == {COUNTER_WIDTH{1'b1}}) |=> (counter_value == {COUNTER_WIDTH{1'b1}})
  ) else $error("SVA FAIL: Monotonic counter wrapped around at max value");

endmodule


// -----------------------------------------------------------------------------
// Template: OTP Fuse Protection
// [TEMPLATE]
// -----------------------------------------------------------------------------
// INTENT: Verify that OTP (One-Time Programmable) fuse values are read-only
//         after programming and cannot be reprogrammed. The fuse controller
//         must gate programming access based on lifecycle state.
// DOES NOT CHECK: Physical fuse reliability or programming voltage correctness.

module sva_otp_fuse_protection #(
  parameter int FUSE_WIDTH = 256
)(
  input logic                    clk,
  input logic                    rst_n,
  input logic [FUSE_WIDTH-1:0]  fuse_value,         // [PLACEHOLDER] current fuse value
  input logic                    fuse_program_req,   // [PLACEHOLDER] programming request
  input logic                    fuse_programmed,    // [PLACEHOLDER] fuse has been programmed (not blank)
  input logic                    lifecycle_allows,   // [PLACEHOLDER] lifecycle state permits programming
  input logic                    program_accepted    // [PLACEHOLDER] programming request accepted
);

  // Already-programmed fuses must not accept reprogramming
  assert_no_reprogram: assert property (
    @(posedge clk) disable iff (!rst_n)
    (fuse_program_req && fuse_programmed) |-> !program_accepted
  ) else $error("SVA FAIL: OTP fuse accepted reprogramming after already programmed");

  // Programming must be rejected if lifecycle does not allow it
  assert_lifecycle_gate: assert property (
    @(posedge clk) disable iff (!rst_n)
    (fuse_program_req && !lifecycle_allows) |-> !program_accepted
  ) else $error("SVA FAIL: OTP fuse programming accepted in wrong lifecycle state");

  // Fuse value must not change without a programming event
  assert_stable_without_program: assert property (
    @(posedge clk) disable iff (!rst_n)
    !program_accepted |=> $stable(fuse_value)
  ) else $error("SVA FAIL: Fuse value changed without programming event");

endmodule


// -----------------------------------------------------------------------------
// Template: SPDM Session Sequence Number Monotonicity
// [TEMPLATE]
// -----------------------------------------------------------------------------
// INTENT: Verify that SPDM session message sequence numbers are strictly
//         monotonically increasing. Replayed or out-of-order messages must
//         be rejected.
// DOES NOT CHECK: Whether the sequence number is correctly bound to the
//                 message content or session key.

module sva_spdm_sequence_number #(
  parameter int SEQ_WIDTH = 64
)(
  input logic                  clk,
  input logic                  rst_n,
  input logic                  msg_received,       // [PLACEHOLDER] SPDM message received
  input logic [SEQ_WIDTH-1:0]  msg_seq_num,        // [PLACEHOLDER] message sequence number
  input logic                  msg_accepted,       // [PLACEHOLDER] message accepted for processing
  input logic                  session_active      // [PLACEHOLDER] SPDM session is active
);

  logic [SEQ_WIDTH-1:0] last_seq_num;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      last_seq_num <= '0;
    else if (msg_received && msg_accepted && session_active)
      last_seq_num <= msg_seq_num;
  end

  // Accepted message sequence number must be greater than last accepted
  assert_seq_increasing: assert property (
    @(posedge clk) disable iff (!rst_n)
    (msg_received && msg_accepted && session_active && (last_seq_num > 0))
    |-> (msg_seq_num > last_seq_num)
  ) else $error("SVA FAIL: SPDM message accepted with non-increasing sequence number");

  // Message with old/replayed sequence number must be rejected
  assert_reject_replay: assert property (
    @(posedge clk) disable iff (!rst_n)
    (msg_received && session_active && (msg_seq_num <= last_seq_num) && (last_seq_num > 0))
    |-> !msg_accepted
  ) else $error("SVA FAIL: SPDM message with replayed sequence number was accepted");

endmodule
