# Verification Methodology — Tier 1: Mechanical/Structural Properties

## Purpose

Detailed criteria, property categories, and worked example for Tier 1 SVA assertion generation.

**Primary consumer:** verification-scaffold-skill (Phase 2 SVA template generation)

---

## Definition

Tier 1 properties express structural invariants or guarded state transitions that can be directly observed in the RTL signal space. They are "mechanical" — checking them requires only observing signals and comparing against a specification.

## Tier 1 Criteria

A property belongs in Tier 1 if ALL of the following are true:

1. **Observable:** Can be checked by observing RTL signals (inputs, outputs, internal registers, FSM state)
2. **Temporal:** Can be expressed in LTL or SVA temporal operators
3. **Local:** Involves signals within a single module or small set of connected modules
4. **Deterministic:** Truth value is determined by signal values alone
5. **Self-contained:** Does not depend on behavior of unmodeled components

## Common Tier 1 Property Categories

### Access Control Properties

- "Only master with ID in allowed set can write to security configuration registers"
- "Read access to key storage blocked when component is in user mode"
- "Bus firewall rejects transactions with addresses outside permitted range"

**Key signals:** Master ID, transaction type, address, access control configuration, permission registers
**SVA pattern:** Implication — `(access_request && condition) |-> permitted`

### FSM Transition Properties

- "Security FSM cannot transition from LOCKED to OPEN without unlock sequence completing"
- "After ERROR state, FSM can only return to IDLE via reset"
- "Boot FSM advances to AUTHENTICATED only if signature verification pass asserted"

**Key signals:** FSM state register, transition guard signals, reset, enable
**SVA pattern:** State sequence — `(state == A) ##1 (state == B) |-> guard_was_true`

### Register Lock Properties

- "After lock_bit is set, key register cannot be written"
- "Security policy registers not writable after boot completes"
- "Fuse shadow register matches fuse value and cannot be overwritten"

**Key signals:** Lock bits, register values, write enable, boot complete
**SVA pattern:** Stability — `$rose(lock) |-> ##1 $stable(register)[*]`

### Address Range Properties

- "DMA transactions within assigned address range"
- "BAR decoding prevents access outside configured window"
- "Memory protection unit enforces region boundaries"

**Key signals:** Transaction address, base/limit registers, valid, region config
**SVA pattern:** Range check — `valid |-> (addr >= base) && (addr < limit)`

### Encoding Integrity Properties

- "FSM state register maintains one-hot encoding"
- "Error detection code on security registers is valid"
- "Parity on key bus is correct"

**Key signals:** Encoded registers, parity/ECC signals
**SVA pattern:** Invariant — `$onehot(state)` or `parity == ^data`

## Worked Example: Key Storage Access Control

**Source Threat:** TF-TM-2026-001-007 — "An attacker with bus master access can read the AES key from the key storage register by issuing a read transaction during the brief window when the key is loaded from fuses but the access control has not yet been configured."

**Tier Assignment Rationale:** Access control property — observable signals (read request, key storage address, access control configuration state), expressible as implication. Tier 1.

**Property Decomposition:** This single threat generates multiple Tier 1 assertions:

1. **Key read blocked when unconfigured:** Access control must be active before key register is readable
2. **Key read blocked in user mode:** Only secure-world masters can read key register
3. **Key register default is zero:** Before key is loaded, register reads as zero

**Assertion 1:**

```systemverilog
// INTENT: Key storage register returns zero (or bus error) for any read
//         when access control policy has not been configured. Prevents
//         key leakage during boot window before access control is active.
// DOES NOT CHECK: Whether access control policy itself is correct,
//                  whether key is loaded securely, or whether "configured"
//                  signal accurately reflects the security state.

property p_key_read_unconfigured;
  @(posedge <clk>) disable iff (!<rst_n>)
  (<key_read_request> && !<access_control_configured>) |->
    (<key_read_data> == '0) || (<bus_error_response>);
endproperty
```
