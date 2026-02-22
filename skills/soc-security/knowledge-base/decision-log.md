# Decision Log

Tracks security architecture decisions with rationale, alternatives considered, and traceability to requirements and findings. Decisions recorded here inform future analysis sessions and prevent re-deriving previously settled questions.

## Entry Format

```markdown
## [DECISION-YYYY-NNN] — Title
- Date: YYYY-MM-DD
- Status: [proposed|accepted|superseded|deprecated]
- SoC Family: [compute|automotive|client|data-center]
- Technology Domain: [confidential-ai|tdisp-cxl|supply-chain|secure-boot-dice|cheri]
- Context: [what prompted this decision]
- Decision: [what was decided]
- Alternatives Considered:
  1. [alternative 1] — [why rejected]
  2. [alternative 2] — [why rejected]
- Consequences: [implications of this decision]
- Related: [finding IDs, requirement IDs, document IDs]
```

## Usage

- **Before making an architectural choice:** Check this log for prior decisions on the same topic.
- **When a decision is superseded:** Update the original entry's status to `superseded` and link to the new decision.
- **During compliance mapping:** Reference decisions to explain design rationale to auditors.

---

## Decisions

### [DECISION-2026-001] — TDISP Responder FSM Validation Strategy
- Date: 2026-02-13
- Status: accepted
- SoC Family: data-center
- Technology Domain: tdisp-cxl
- Context: FINDING-2026-001 identified a DMA isolation gap in the TDISP responder FSM where TLP field validation was incomplete during the LOCK_INTERFACE_REPORT handshake. Need to decide the verification approach.
- Decision: Implement two-tier verification — Tier 1 SVA assertions for FSM state transition validity (mechanical), plus Tier 2 protocol-level assertions for DMA isolation enforcement post-transition. Defer Tier 3 timing analysis to v2.
- Alternatives Considered:
  1. Single comprehensive SVA assertion covering both FSM and DMA — Rejected because coupling transition validity with isolation enforcement makes the assertion brittle and hard to debug.
  2. Formal model checking only — Rejected because it requires a complete formal model of the TDISP state machine, which exceeds MVP scope.
  3. Runtime monitoring approach — Rejected because it does not catch issues pre-silicon.
- Consequences: Requires two assertion development efforts (Tier 1 + Tier 2). Tier 3 deferral means timing side-channels remain unverified until v2. Accepted risk: no formal proof of isolation completeness in v1.
- Related: [FINDING-2026-001, SR-2026-001, TF-2026-001, VI-2026-001]

### [DECISION-2026-002] — DICE Measurement Order Specification Per SoC Family
- Date: 2026-02-13
- Status: accepted
- SoC Family: compute, automotive
- Technology Domain: secure-boot-dice
- Context: FINDING-2026-002 revealed that DICE certificate chain validation can fail when boot ROM measurement ordering diverges across SoC families. Need to decide how to handle per-family measurement ordering.
- Decision: Document canonical measurement ordering per SoC family in the cross-cutting SoC family profiles. Add an explicit SecurityRequirement mandating that each SoC family's DICE configuration specifies its measurement order, and that SPDM verifiers be configured with the correct expected chain for each family.
- Alternatives Considered:
  1. Enforce a single canonical ordering across all families — Rejected because boot ROM constraints differ between automotive (safety-critical sequencing) and data-center (performance-optimized boot).
  2. Make ordering detection automatic in the verifier — Rejected because it increases verifier complexity and attack surface (an attacker could exploit flexible ordering to present a valid-looking chain from a compromised layer).
- Consequences: Each new SoC family requires an explicit measurement order specification before DICE attestation can be verified. Adds a documentation burden but eliminates a class of attestation failures.
- Related: [FINDING-2026-002, SR-2026-015, TM-2026-002]
