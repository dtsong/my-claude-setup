# Verification Methodology — Tier 2 & Tier 3 Properties

## Contents

- [Purpose](#purpose)
- [Tier 2: Protocol/Behavioral Properties](#tier-2-protocolbehavioral-properties)
  - [Definition](#definition)
  - [Tier 2 Criteria](#tier-2-criteria)
  - [Common Tier 2 Categories](#common-tier-2-categories)
  - [Tier 2 Description Requirements](#tier-2-description-requirements)
  - [Worked Example: TDISP Assignment Handshake](#worked-example-tdisp-assignment-handshake)
- [Tier 3: Specification-Only Properties](#tier-3-specification-only-properties)
  - [Definition](#definition-1)
  - [Tier 3 Criteria](#tier-3-criteria)
  - [Why No SVA for Tier 3](#why-no-sva-for-tier-3)
  - [Tier 3 Verification Recommendations](#tier-3-verification-recommendations)
  - [Tier 3 Output Requirements](#tier-3-output-requirements)
- [Tier Promotion and Demotion](#tier-promotion-and-demotion)

## Purpose

Criteria, property categories, and worked examples for Tier 2 (protocol/behavioral) and Tier 3 (specification-only) verification properties.

**Primary consumer:** verification-scaffold-skill (Phase 3 NL properties, Phase 4 spec-only)

---

## Tier 2: Protocol/Behavioral Properties

### Definition

Tier 2 properties describe multi-step behavioral sequences where correct behavior depends on ordering and conditions of multiple events over time.

### Tier 2 Criteria

A property belongs in Tier 2 if ANY of the following are true:

1. **Multi-step:** Involves a sequence of 3+ ordered events with conditions at each step
2. **Protocol-dependent:** Meaning depends on understanding a communication protocol
3. **Cross-module:** Involves coordinated behavior across multiple modules sharing no common state
4. **State-history-dependent:** Depends on history of states, not just current state
5. **Requires test scenarios:** Best verified by directed test cases rather than continuous monitoring

### Common Tier 2 Categories

**DICE Layer Properties** — "Layer N measurement must be computed before Layer N+1 CDI is derived." Why not Tier 1: spans multiple boot stages and hardware modules, requires DICE protocol semantics. Verification: directed simulation with boot sequence checker.

**TDISP Handshake** — "Full state sequence IDLE -> CONFIG -> LOCK -> RUN must be traversed in order." Why not Tier 1: complete handshake requires full sequence plus SPDM authentication and timeout handling. Verification: protocol compliance checker.

**CXL Protocol** — "IDE stream encryption active before any data TLPs transmitted." Why not Tier 1: multi-message exchanges, timing across clock domains. Verification: CXL protocol checker augmented with security checks.

**SPDM Authentication** — "Mutual authentication completes before any secured data exchange." Why not Tier 1: multi-message protocol with branching, nonce management, certificate chain traversal. Verification: SPDM reference implementation as golden reference.

### Tier 2 Description Requirements

Every Tier 2 property must include:

1. **Temporal statement:** "Before X, Y must have occurred" / "While in state S, C holds" / "After E, within N cycles, R occurs"
2. **Preconditions:** What must be true for this property to apply
3. **Test scenarios:** Normal operation, attack scenario, and edge case (minimum)
4. **Formalization path:** Whether and how this could become a formal property

### Worked Example: TDISP Assignment Handshake

**Source Threat:** TF-TM-2026-001-001
**Temporal Statement:** Before any data transfer through an assigned TDI, the sequence IDLE -> CONFIG -> LOCK -> RUN must have completed in order, with no steps skipped. Any attempt to transition directly from IDLE or CONFIG to RUN must be rejected.
**Preconditions:** Component powered and out of reset, PCIe link active, TDISP capability enabled.
**Test Scenarios:** (1) Normal full handshake -> data transfer succeeds. (2) Attack: inject RUN from IDLE -> rejected. (3) Attack: inject RUN from CONFIG -> rejected. (4) Edge: timeout during LOCK -> abort to IDLE. (5) Edge: SPDM auth fails -> stays in LOCK.
**Formalization:** Individual transitions can be Tier 1 FSM assertions. Overall property best verified by testbench sequence checker.

---

## Tier 3: Specification-Only Properties

### Definition

Tier 3 properties are security guarantees that fundamentally cannot be verified by observing RTL signals. They require specialized tools, physical measurement, mathematical analysis, or system-level reasoning beyond RTL simulation and formal checking.

### Tier 3 Criteria

A property belongs in Tier 3 if ANY of the following are true:

1. **Information-theoretic:** About information flow (what an observer can learn), not signal values
2. **Physical:** Depends on physical phenomena (power, timing, EM emissions)
3. **Mathematical:** About mathematical correctness of algorithms (cryptographic strength)
4. **System-level:** Requires reasoning about the entire SoC, not individual modules
5. **Non-functional:** About a quality attribute not observable in functional simulation

### Why No SVA for Tier 3

**Information flow:** SVA checks signal values, not information content. An assertion can verify key_out != key_in but cannot verify statistical correlation is zero.

**Side-channel:** Power consumption is not represented in RTL. Even gate-level simulation cannot fully capture analog behavior.

**Cryptographic:** Proving correctness for ALL inputs requires mathematical proof or exhaustive testing of 2^512 combinations.

### Tier 3 Verification Recommendations

| Property Type | Approach | Tools |
|--------------|---------|-------|
| Information flow | Formal information flow analysis | GLIFT, SecVerilog, JasperGold SecureCheck |
| Timing side-channel | Constant-time analysis | ct-verif, manual review |
| Power side-channel | Power analysis simulation + silicon measurement | DPA/SPA simulation, oscilloscope |
| Crypto correctness | Known-answer testing + certification | FIPS 140-3 CAVP/CMVP |
| Architectural isolation | System-level formal verification | TLA+, NuSMV |

### Tier 3 Output Requirements

Every Tier 3 item must include: (1) No SVA rationale. (2) Property description. (3) Recommended methodology. (4) Review checklist. (5) Specification reference.

---

## Tier Promotion and Demotion

**Tier 2 -> Tier 1:** When engineer provides enough state machine detail that individual protocol steps become SVA-checkable. Usually means generating multiple Tier 1 assertions, not replacing Tier 2.

**Tier 3 -> Tier 2:** When specialized tools can check the property, or a behavioral approximation provides meaningful partial coverage.

**Tier 1 -> Tier 2:** When property spans too many modules or exceeds practical SVA temporal depth.

**Tier 2 -> Tier 3:** When property cannot be meaningfully tested even with directed simulation.

Document all tier changes: `Tier Change: [VI-ID], From: Tier N -> To: Tier M, Reason: [specific], Impact: [coverage gained/lost]`.
