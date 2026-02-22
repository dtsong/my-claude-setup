# Eval Case: Full Refinement Mapping from Abstract to Implementation Spec

## Metadata
- **Case ID:** TS-005
- **Tier:** 3 (complex)
- **Skill Route:** tlaplus-security-skill
- **Estimated Complexity:** high

## Input
```json
{
  "user_prompt": "Write a TLA+ refinement mapping that proves our implementation-level TDISP (TEE Device Interface Security Protocol) state machine correctly refines the abstract security specification. We need both the abstract spec and implementation spec, plus the refinement mapping.\n\nAbstract specification (high-level security property):\n- TDISP device states: {IDLE, LOCKED, RUN}\n- Security property: a device in RUN state has completed mutual authentication AND has an active IDE (Integrity and Data Encryption) stream\n- Abstract transitions:\n  - IDLE -> LOCKED (host initiates TDISP, device locks configuration)\n  - LOCKED -> RUN (authentication complete + IDE stream established)\n  - RUN -> IDLE (teardown or error)\n  - LOCKED -> IDLE (authentication failure)\n- Abstract invariant: state = RUN => authenticated /\\ ideActive\n\nImplementation specification (detailed protocol):\n- Implementation states: {IDLE, CONFIG_LOCK, SPDM_INIT, SPDM_CHALLENGE, SPDM_DONE, IDE_KEY_PROG, IDE_KEY_SET, IDE_STREAM_START, RUN, ERROR, TEARDOWN}\n- Implementation transitions:\n  - IDLE -> CONFIG_LOCK (lock device config registers)\n  - CONFIG_LOCK -> SPDM_INIT (begin SPDM handshake)\n  - SPDM_INIT -> SPDM_CHALLENGE (send challenge)\n  - SPDM_CHALLENGE -> SPDM_DONE (challenge response verified) | SPDM_CHALLENGE -> ERROR (verification failed)\n  - SPDM_DONE -> IDE_KEY_PROG (program IDE encryption keys)\n  - IDE_KEY_PROG -> IDE_KEY_SET (keys loaded into hardware)\n  - IDE_KEY_SET -> IDE_STREAM_START (activate IDE stream on link)\n  - IDE_STREAM_START -> RUN (IDE stream confirmed active)\n  - RUN -> TEARDOWN (host-initiated or timeout)\n  - TEARDOWN -> IDLE (cleanup complete)\n  - ERROR -> IDLE (error recovery)\n  - Any state -> ERROR (protocol violation or timeout)\n\n- Implementation variables:\n  - implState: current implementation state\n  - spdmSessionId: SPDM session identifier (null when no session)\n  - spdmCertChain: certificate chain received from device\n  - ideKeyId: IDE key identifier (null when no key)\n  - ideStreamId: IDE stream identifier (null when no stream)\n  - errorCode: last error (null when no error)\n\nRefinement mapping:\n- Abstract IDLE maps to implementation {IDLE, TEARDOWN, ERROR}\n- Abstract LOCKED maps to implementation {CONFIG_LOCK, SPDM_INIT, SPDM_CHALLENGE, SPDM_DONE, IDE_KEY_PROG, IDE_KEY_SET, IDE_STREAM_START}\n- Abstract RUN maps to implementation {RUN}\n- Abstract 'authenticated' is true iff implState \\in {SPDM_DONE, IDE_KEY_PROG, IDE_KEY_SET, IDE_STREAM_START, RUN}\n- Abstract 'ideActive' is true iff implState \\in {IDE_STREAM_START, RUN}\n\nSecurity properties to verify:\n1. (Safety) The implementation refines the abstract spec — every behavior of the implementation is a behavior of the abstract spec under the refinement mapping\n2. (Safety) Implementation invariant: implState = RUN => spdmSessionId /= null /\\ ideStreamId /= null\n3. (Safety) No implementation state can reach RUN without traversing SPDM_CHALLENGE and IDE_STREAM_START\n4. (Liveness) From SPDM_INIT, the system eventually reaches either RUN or ERROR (no stuck handshake)\n\nUpstream findings:\n- TF-2026-003 — 'TDISP state skip allows RUN without IDE stream'\n- TF-2026-007 — 'SPDM handshake timeout allows indefinite LOCKED state'\n\nFairness: protocol actions are weakly fair (network eventually delivers messages).",
  "context": "Refinement mapping between abstract and implementation TDISP specs. 3 abstract states, 11 implementation states. Multiple security properties: refinement, safety invariants, liveness. Requires INSTANCE mechanism in TLA+ for refinement checking. Medium state space — feasible for TLC with appropriate constants."
}
```

## Expected Output
A comprehensive FormalSecSpec with:
- Abstract TLA+ module (TDISPAbstract) with 3 states, 2 boolean flags, safety invariant
- Implementation TLA+ module (TDISPImpl) with 11 states, session/key/stream variables
- Refinement mapping module using TLA+ INSTANCE to prove implementation refines abstract
- All 4 security properties formalized
- TLC configuration for both standalone invariant checking and refinement checking
- Detailed assumptions and limitations

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output contains at least two TLA+ modules: abstract spec and implementation spec
- [ ] Abstract module has Init, Next, and the safety invariant (RUN => authenticated /\ ideActive)
- [ ] Implementation module has Init, Next with all 11 states and transitions
- [ ] Refinement mapping defined — maps implementation states to abstract states
- [ ] At least one safety property and one liveness property formalized as TLA+ formulas
- [ ] TLC configuration provided for checking at least one property
- [ ] Both upstream finding IDs (TF-2026-003, TF-2026-007) referenced

### Should Pass (partial credit)
- [ ] INSTANCE mechanism used correctly for refinement checking (or equivalent technique explained)
- [ ] Refinement mapping correctly maps: IDLE->{IDLE,TEARDOWN,ERROR}, LOCKED->{CONFIG_LOCK,...,IDE_STREAM_START}, RUN->{RUN}
- [ ] Implementation invariant (RUN => spdmSessionId /= null /\ ideStreamId /= null) formalized
- [ ] No-skip property formalized: path to RUN must traverse SPDM_CHALLENGE and IDE_STREAM_START
- [ ] Liveness property (SPDM_INIT ~> RUN \/ ERROR) with weak fairness on protocol actions
- [ ] Fairness documented: liveness holds only under WF, without fairness the handshake can stall
- [ ] State space estimated and feasibility assessed for TLC
- [ ] Assumptions list includes: atomic transitions, reliable SPDM session, no physical fault injection
- [ ] Limitations list includes: does not model network latency, message reordering, or concurrent TDISP sessions

### Bonus
- [ ] Models the "any state -> ERROR" transition and proves it does not break refinement (ERROR maps to abstract IDLE)
- [ ] Notes that spdmCertChain verification is abstracted to a boolean — real certificate chain validation has sub-states not modeled
- [ ] Provides separate TLC configurations for: (a) implementation invariant checking, (b) refinement checking, (c) liveness checking with different state constraints
- [ ] Discusses the stuttering equivalence requirement for TLA+ refinement — implementation steps within abstract LOCKED are stuttering steps
- [ ] Identifies that timeout-based transitions (Any -> ERROR) require a fairness assumption to prevent indefinite delay in the ERROR recovery path

## Raw Trace Log
