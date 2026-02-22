# Verification Methodology — Three-Tier Model Overview

## Purpose

Overview of the 3-tier verification model and tier boundary rules. Covers rationale for tier separation, detailed criteria for tier assignment, and tier boundary violations.

**Primary consumer:** verification-scaffold-skill (Phase 1 tier assignment)

---

## Quick Reference

| Tier | Name | Confidence | Artifact | Verification Tool | Applicable Properties |
|------|------|-----------|----------|------------------|----------------------|
| 1 | Mechanical/Structural | HIGH | SVA assertion templates | Simulation + formal | Access control, FSM, register locks, address ranges |
| 2 | Protocol/Behavioral | MEDIUM | NL property descriptions | Directed simulation, protocol checkers | DICE sequence, TDISP handshake, CXL protocol, SPDM flows |
| 3 | Specification-Only | REFERENCE | Spec descriptions + checklists | Specialized tools, manual review | Information flow, side-channel, crypto strength |

---

## Why Three Tiers?

Not all security properties are created equal in verifiability through RTL assertions.

**Tier 1 properties** are about **structural invariants** — relationships between signals that must hold at every clock cycle or during specific state transitions. These are the sweet spot for SVA because they can be expressed as temporal logic properties over observable signals.

**Tier 2 properties** are about **protocol compliance** — multi-step behavioral sequences that must occur in a specific order with specific conditions at each step. While individual steps might be checkable via SVA, the overall protocol requires higher-level reasoning. Natural-language property descriptions serve as specifications for verification engineers.

**Tier 3 properties** are about **system-level guarantees** — information flow, physical side-channel resistance, or mathematical properties of cryptographic implementations. These fundamentally cannot be expressed as signal-level temporal properties because they require reasoning about information, physics, or mathematics rather than signals.

**The tier boundary is not about complexity.** A Tier 1 property may be complex (e.g., verifying a 64-state FSM). A Tier 3 property may be simple to state ("no information flows from A to B"). The boundary is about the nature of the property and the appropriate verification methodology.

---

## Tier Boundary Violations

The most dangerous error is generating a Tier 1 (SVA) artifact for a Tier 3 property. This creates false confidence — the engineer sees an assertion "passing" and believes the property is verified, when the assertion cannot capture the property at all.

**Example of a Tier 3 property incorrectly expressed as SVA:**

```systemverilog
// BAD: Attempting to check information flow with SVA
// This assertion checks that key_out does not change when key_in changes,
// but this does NOT verify information flow — it only checks a specific
// temporal correlation. Information could flow through intermediate signals
// or across multiple cycles without triggering this check.
property p_bad_info_flow;
  @(posedge clk) $changed(key_in) |-> $stable(key_out);
endproperty
// THIS IS WRONG AND DANGEROUS — gives false confidence
```

The correct approach is Tier 3: specify the information flow property in natural language and recommend a tool-based verification methodology (e.g., GLIFT, SecVerilog).
