---
name: rtl-security-review
department: "forge"
description: "Use when reviewing RTL designs for security vulnerabilities including access control gate bypasses, insecure FSM transitions, timing-dependent information leakage, and unintended data paths. Covers Verilog, SystemVerilog, and VHDL modules with security-critical functions. Do not use for physical implementation review (use physical-design-security) or microarchitectural attack analysis (use microarch-analysis)."
version: 1
triggers:
  - "RTL"
  - "Verilog"
  - "SystemVerilog"
  - "FSM"
  - "access control"
  - "gate-level"
  - "hardware design"
  - "hardware verification"
  - "register access"
  - "security policy"
---

# RTL Security Review

## Purpose
Review RTL designs for security vulnerabilities including access control gate bypasses, insecure FSM transitions, timing-dependent information leakage, and unintended data paths.

## Scope Constraints

Reads RTL source files (Verilog/SystemVerilog/VHDL), testbenches, and security policy documents. Does not modify RTL files or execute simulation. Does not access proprietary IP blocks outside the review scope.

## Inputs
- RTL module(s) under review (Verilog/SystemVerilog/VHDL)
- Security policy specification (what access controls should be enforced)
- Trust boundary definitions (which interfaces are exposed to untrusted agents)
- Intended FSM behavior and state transition rules

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Step 1: Identify Security-Critical RTL Modules
Enumerate all modules that enforce security policies: access control checkers, permission registers, firewall/filter logic, key storage, crypto engines, interrupt controllers, debug interfaces. Classify each by the trust boundary it enforces.

### Step 2: Check Access Control Gates
For each access control module, verify:
- All paths through the logic respect the access policy (no bypass paths)
- Default-deny: unrecognized requests are blocked, not passed through
- Access checks happen before data is forwarded (no time-of-check/time-of-use gaps)
- Reset state is secure (permissions are restrictive, not permissive)
- Lock bits cannot be cleared once set

### Step 3: Verify FSM Transition Security
For each security-relevant FSM, verify:
- All state transitions are explicitly defined (no implicit transitions via default cases)
- Invalid input in any state leads to a safe/error state, not an exploitable state
- State encoding resists fault injection (Hamming distance, one-hot vs binary)
- Reset enters the most restrictive state
- Glitch-sensitive transitions have synchronization or filtering

### Step 4: Review Timing Paths
For each security-critical path, verify:
- Security checks are on the critical path (cannot be bypassed by timing)
- No combinational paths that could glitch during clock transitions
- Multi-cycle paths have proper handshaking (no window where unchecked data is visible)
- Clock domain crossings near security logic have proper synchronization

### Step 5: Check for Information Leakage
Review the design for unintended information paths:
- Shared buses or interconnects that expose data across trust boundaries
- Debug/test interfaces that bypass access controls
- Error responses that leak internal state
- Power/timing side-channels in security-critical operations
- Scan chains that expose key material or security state

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what system is being analyzed, then resume from the earliest incomplete step.

## Output Format

### Module Security Classification

| Module | Security Function | Trust Boundary | Review Status |
|--------|------------------|----------------|---------------|
| `access_ctrl` | Memory access filtering | CPU ↔ Peripheral | Reviewed |
| ... | ... | ... | ... |

### Finding Table

| ID | Module | Category | Description | Severity | Recommendation |
|----|--------|----------|-------------|----------|----------------|
| F1 | `access_ctrl` | Bypass | Default case forwards request | Critical | Change default to deny |
| ... | ... | ... | ... | ... | ... |

### FSM Security Summary
- [FSM name]: [State count] states, [Transition count] transitions — [Issues found]

## Handoff

- Hand off to microarch-analysis if microarchitectural side-effects are discovered during RTL review.
- Hand off to physical-design-security if physical implementation changes are needed for security.

## Quality Checks
- [ ] All security-critical modules are identified and reviewed
- [ ] Access control gates are verified for bypass paths
- [ ] FSMs have no implicit transitions through default/wildcard cases
- [ ] Reset state is verified as secure for all security-relevant registers
- [ ] Debug interfaces are checked for access control bypass
- [ ] Timing paths through security logic are verified
- [ ] Information leakage paths are enumerated and assessed

## Evolution Notes
<!-- Observations appended after each use -->
