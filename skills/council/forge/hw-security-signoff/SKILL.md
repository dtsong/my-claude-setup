---
name: hw-security-signoff
department: "forge"
description: "Use when a hardware design needs security sign-off before tape-out. Defines the builder-to-auditor handoff contract between Foundry (constructive design) and Forge (security review). Covers security review prerequisites, artifact checklist, sign-off criteria, and conditional approval workflow. Do not use for RTL security review itself (use rtl-security-review) or design flow guidance (use foundry/chip-design-flow)."
version: 1
triggers:
  - "security signoff"
  - "tape-out security"
  - "hw security review"
  - "design handoff"
  - "security checklist"
  - "pre-tapeout"
  - "security gate"
---

# HW Security Sign-Off

## Purpose

Define the handoff contract between Foundry (builder) and Forge (security auditor) for hardware security sign-off. Ensure all security-critical design artifacts are delivered, reviewed, and approved before tape-out commitment.

## Scope Constraints

Coordinates the handoff process between builder and auditor roles. Does not perform the security review itself (delegates to rtl-security-review, microarch-analysis, physical-design-security). Does not modify design files.

## Inputs

- Design name and tape-out target date
- Security-critical modules identified by Foundry
- Trust boundary definitions
- Threat model (if available) or threat categories in scope
- Any prior security review findings

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Verify builder artifact delivery
- [ ] Step 2: Validate security scope agreement
- [ ] Step 3: Coordinate security reviews
- [ ] Step 4: Track finding resolution
- [ ] Step 5: Issue sign-off decision

### Step 1: Verify Builder Artifact Delivery

Foundry must deliver the following before security review begins:

- [ ] RTL source for all security-critical modules (final, synthesis-ready)
- [ ] Security-critical module list with trust boundary annotations
- [ ] Register map with access control policy per register
- [ ] FSM state diagrams for security-relevant state machines
- [ ] Clock domain crossing report
- [ ] DFT/scan chain documentation (which chains touch security logic)
- [ ] Debug interface specification (JTAG, trace ports)
- [ ] Known limitations or accepted risks documented

Reject handoff if any artifact is missing. Document gaps and return to Foundry.

### Step 2: Validate Security Scope Agreement

- Confirm threat categories in scope (side-channel, fault injection, logical bypass, debug access).
- Agree on security-critical module boundaries (which modules are in-scope for full review).
- Define review depth per module: full RTL review, interface-only, or documentation review.
- Set severity classification: critical (blocks tape-out), high (requires mitigation plan), medium (accept with justification), low (track).
- Confirm timeline and review capacity.

### Step 3: Coordinate Security Reviews

Dispatch to Forge specialist skills based on scope:

- **rtl-security-review**: Access control gates, FSM transitions, information leakage for all in-scope modules.
- **microarch-analysis**: Speculative execution, cache timing, branch predictor attacks if CPU/core is in scope.
- **physical-design-security**: Power domain isolation, clock domain security, layout-level leakage if physical design is available.

Track review progress per module and per skill.

### Step 4: Track Finding Resolution

- Maintain finding tracker with: ID, module, category, severity, status, owner, target date.
- For each critical finding: Foundry implements fix, Forge re-reviews.
- For each high finding: Foundry provides mitigation plan, Forge approves plan.
- For each medium finding: Foundry documents accepted risk with justification.
- Verify all critical findings are resolved before sign-off.

### Step 5: Issue Sign-Off Decision

- **Approved**: All critical/high findings resolved, no open blockers.
- **Conditional approval**: All critical resolved, high findings have approved mitigation plans with committed timelines.
- **Blocked**: Open critical findings or unresolved high findings without mitigation plans.

Document decision with: reviewer, date, scope covered, open items (if conditional), and next review trigger.

> **Compaction resilience**: If context was lost, re-read the Inputs section for the design under review, check the Progress Checklist, then resume from the earliest incomplete step.

## Output Format

### Sign-Off Summary

| Field | Value |
|-------|-------|
| Design | ... |
| Reviewer | Forge |
| Date | ... |
| Decision | Approved / Conditional / Blocked |
| Scope | Modules A, B, C |
| Open items | ... |

### Finding Tracker

| ID | Module | Category | Severity | Status | Owner |
|----|--------|----------|----------|--------|-------|
| F1 | access_ctrl | Bypass | Critical | Fixed | Foundry |
| F2 | debug_if | Leakage | High | Mitigated | Foundry |

## Handoff

- Hand off to forge/rtl-security-review for detailed RTL security analysis.
- Hand off to forge/microarch-analysis for microarchitectural attack surface review.
- Hand off to foundry/chip-design-flow for design fixes required by findings.

## Quality Checks

- [ ] All builder artifacts delivered and complete
- [ ] Security scope and threat categories agreed
- [ ] All security-critical modules reviewed by appropriate Forge skill
- [ ] All critical findings resolved
- [ ] All high findings resolved or have approved mitigation plans
- [ ] Sign-off decision documented with scope and conditions

## Evolution Notes
<!-- Observations appended after each use -->
