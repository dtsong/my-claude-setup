// =============================================================================
// SVA Templates: Access Control Assertions
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
// Template: Register Write Protection (Privilege-Gated)
// [TEMPLATE]
// -----------------------------------------------------------------------------
// INTENT: Verify that a security-critical register can only be written by
//         an entity with sufficient privilege level.
// DOES NOT CHECK: Whether the privilege level itself is correctly assigned
//                 to the requesting master. Only checks the gate.

module sva_register_privilege_gate #(
  parameter int REQUIRED_PRIV = 2  // Minimum privilege level for write access
)(
  input logic        clk,
  input logic        rst_n,
  input logic        reg_write_en,      // [PLACEHOLDER] register write enable
  input logic [1:0]  requester_priv,    // [PLACEHOLDER] privilege level of requester
  input logic        reg_write_success  // [PLACEHOLDER] register write completes
);

  // Write must not succeed if privilege is insufficient
  assert_priv_gate: assert property (
    @(posedge clk) disable iff (!rst_n)
    (reg_write_en && (requester_priv < REQUIRED_PRIV)) |-> !reg_write_success
  ) else $error("SVA FAIL: Register write succeeded with insufficient privilege");

  // Write with sufficient privilege should be able to succeed (liveness)
  cover_priv_write: cover property (
    @(posedge clk) disable iff (!rst_n)
    reg_write_en && (requester_priv >= REQUIRED_PRIV) && reg_write_success
  );

endmodule


// -----------------------------------------------------------------------------
// Template: Bus Firewall Address Range Check
// [TEMPLATE]
// -----------------------------------------------------------------------------
// INTENT: Verify that a bus firewall blocks transactions to protected address
//         ranges from unauthorized masters.
// DOES NOT CHECK: Completeness of the firewall rule set (whether all sensitive
//                 ranges are covered). Only checks one range.

module sva_bus_firewall_range #(
  parameter int ADDR_WIDTH = 32,
  parameter logic [ADDR_WIDTH-1:0] PROT_BASE = 32'hFF00_0000,
  parameter logic [ADDR_WIDTH-1:0] PROT_SIZE = 32'h0010_0000
)(
  input logic                    clk,
  input logic                    rst_n,
  input logic                    txn_valid,          // [PLACEHOLDER] transaction valid
  input logic [ADDR_WIDTH-1:0]  txn_addr,           // [PLACEHOLDER] transaction address
  input logic                    txn_is_authorized,  // [PLACEHOLDER] master is authorized
  input logic                    txn_blocked         // [PLACEHOLDER] transaction blocked by firewall
);

  localparam logic [ADDR_WIDTH-1:0] PROT_END = PROT_BASE + PROT_SIZE - 1;

  // Unauthorized access to protected range must be blocked
  assert_firewall_block: assert property (
    @(posedge clk) disable iff (!rst_n)
    (txn_valid && !txn_is_authorized &&
     (txn_addr >= PROT_BASE) && (txn_addr <= PROT_END))
    |-> txn_blocked
  ) else $error("SVA FAIL: Unauthorized transaction to protected range not blocked");

  // Authorized access to protected range should not be blocked
  assert_firewall_pass: assert property (
    @(posedge clk) disable iff (!rst_n)
    (txn_valid && txn_is_authorized &&
     (txn_addr >= PROT_BASE) && (txn_addr <= PROT_END))
    |-> !txn_blocked
  ) else $error("SVA FAIL: Authorized transaction to protected range incorrectly blocked");

endmodule


// -----------------------------------------------------------------------------
// Template: TDISP TDI Access Control (State-Dependent)
// [TEMPLATE]
// -----------------------------------------------------------------------------
// INTENT: Verify that TDI resources (MMIO, DMA) are accessible only when
//         the TDI is in RUN state AND the accessor is the owning trust domain.
// DOES NOT CHECK: Correctness of trust domain ID assignment or TDI state
//                 machine transition logic (see fsm-transitions.sv).

module sva_tdi_access_control #(
  parameter int TD_ID_WIDTH = 4
)(
  input logic                     clk,
  input logic                     rst_n,
  input logic [2:0]               tdi_state,        // [PLACEHOLDER] TDI state (encoded)
  input logic [TD_ID_WIDTH-1:0]   tdi_owner_id,     // [PLACEHOLDER] owning trust domain ID
  input logic                     access_request,    // [PLACEHOLDER] access to TDI resources
  input logic [TD_ID_WIDTH-1:0]   accessor_id,      // [PLACEHOLDER] requesting trust domain ID
  input logic                     access_granted     // [PLACEHOLDER] access permitted
);

  // TDI state encoding (adjust to match design)
  localparam logic [2:0] TDI_CONFIG = 3'b000;
  localparam logic [2:0] TDI_LOCK   = 3'b001;
  localparam logic [2:0] TDI_RUN    = 3'b010;
  localparam logic [2:0] TDI_ERROR  = 3'b011;

  // Access granted only in RUN state by owning trust domain
  assert_tdi_run_only: assert property (
    @(posedge clk) disable iff (!rst_n)
    (access_request && access_granted) |->
    (tdi_state == TDI_RUN) && (accessor_id == tdi_owner_id)
  ) else $error("SVA FAIL: TDI access granted outside RUN state or by non-owner");

  // Access must be blocked in ERROR state regardless of accessor
  assert_tdi_error_block: assert property (
    @(posedge clk) disable iff (!rst_n)
    (access_request && (tdi_state == TDI_ERROR)) |-> !access_granted
  ) else $error("SVA FAIL: TDI access granted in ERROR state");

  // Access must be blocked for non-owning trust domains in RUN state
  assert_tdi_owner_only: assert property (
    @(posedge clk) disable iff (!rst_n)
    (access_request && (tdi_state == TDI_RUN) && (accessor_id != tdi_owner_id))
    |-> !access_granted
  ) else $error("SVA FAIL: TDI access granted to non-owning trust domain");

endmodule


// -----------------------------------------------------------------------------
// Template: CHERI Capability Bounds Check
// [TEMPLATE]
// -----------------------------------------------------------------------------
// INTENT: Verify that every memory access through a capability is within
//         the capability's bounds. Out-of-bounds access must raise an exception.
// DOES NOT CHECK: Capability derivation monotonicity (see dedicated assertion).
//                 Only checks bounds at point of memory access.

module sva_cheri_bounds_check #(
  parameter int ADDR_WIDTH = 64
)(
  input logic                    clk,
  input logic                    rst_n,
  input logic                    mem_access_valid,   // [PLACEHOLDER] memory access attempted
  input logic [ADDR_WIDTH-1:0]  access_addr,        // [PLACEHOLDER] target address
  input logic [ADDR_WIDTH-1:0]  cap_base,           // [PLACEHOLDER] capability base
  input logic [ADDR_WIDTH-1:0]  cap_top,            // [PLACEHOLDER] capability top (base + length)
  input logic                    cap_tag_valid,      // [PLACEHOLDER] capability tag bit is set
  input logic                    bounds_exception,   // [PLACEHOLDER] bounds fault raised
  input logic                    access_committed    // [PLACEHOLDER] memory access committed
);

  // Out-of-bounds access must raise exception
  assert_bounds_fault: assert property (
    @(posedge clk) disable iff (!rst_n)
    (mem_access_valid && cap_tag_valid &&
     ((access_addr < cap_base) || (access_addr >= cap_top)))
    |-> bounds_exception
  ) else $error("SVA FAIL: Out-of-bounds capability access did not raise exception");

  // Out-of-bounds access must not commit
  assert_bounds_no_commit: assert property (
    @(posedge clk) disable iff (!rst_n)
    (mem_access_valid && cap_tag_valid &&
     ((access_addr < cap_base) || (access_addr >= cap_top)))
    |-> !access_committed
  ) else $error("SVA FAIL: Out-of-bounds capability access committed to memory");

  // In-bounds access should not raise bounds exception
  assert_inbounds_ok: assert property (
    @(posedge clk) disable iff (!rst_n)
    (mem_access_valid && cap_tag_valid &&
     (access_addr >= cap_base) && (access_addr < cap_top))
    |-> !bounds_exception
  ) else $error("SVA FAIL: In-bounds capability access raised spurious bounds exception");

endmodule


// -----------------------------------------------------------------------------
// Template: IOMMU DMA Filtering
// [TEMPLATE]
// -----------------------------------------------------------------------------
// INTENT: Verify that DMA transactions from devices are filtered by the IOMMU
//         and that only authorized address ranges are accessible.
// DOES NOT CHECK: IOMMU page table correctness or TLB consistency.

module sva_iommu_dma_filter #(
  parameter int ADDR_WIDTH = 64,
  parameter int DEV_ID_WIDTH = 16
)(
  input logic                      clk,
  input logic                      rst_n,
  input logic                      dma_request,        // [PLACEHOLDER] DMA transaction initiated
  input logic [DEV_ID_WIDTH-1:0]   dma_device_id,      // [PLACEHOLDER] originating device ID
  input logic [ADDR_WIDTH-1:0]     dma_target_addr,    // [PLACEHOLDER] target host address
  input logic                      iommu_enabled,       // [PLACEHOLDER] IOMMU is active
  input logic                      iommu_authorized,    // [PLACEHOLDER] IOMMU permits this access
  input logic                      dma_completed        // [PLACEHOLDER] DMA transaction completed
);

  // When IOMMU is enabled, unauthorized DMA must not complete
  assert_iommu_block: assert property (
    @(posedge clk) disable iff (!rst_n)
    (dma_request && iommu_enabled && !iommu_authorized) |-> !dma_completed
  ) else $error("SVA FAIL: Unauthorized DMA transaction completed despite IOMMU");

  // DMA must not complete when IOMMU is not yet enabled (pre-boot protection)
  // Note: This is a strict policy — adjust if design allows pre-IOMMU DMA for boot devices
  assert_no_dma_without_iommu: assert property (
    @(posedge clk) disable iff (!rst_n)
    (dma_request && !iommu_enabled) |-> !dma_completed
  ) else $error("SVA FAIL: DMA transaction completed with IOMMU disabled");

endmodule
