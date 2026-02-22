# Eval Case: Multi-Domain Routing — Full Security Pipeline Request

## Metadata
- **Case ID:** COORD-003
- **Tier:** 3 (complex)
- **Skill Route:** threat-model-skill -> verification-scaffold-skill -> executive-brief-skill (pipeline sequence)
- **Estimated Complexity:** high

## Input
```json
{
  "user_prompt": "We have a security review board meeting in two weeks for our CXL 3.1 memory expander SoC. I need the full workup: identify all threats to the CXL.mem and CXL.cache interfaces including the IDE key management subsystem, generate SVA assertion templates and a verification checklist for the critical findings, and then produce a board-level executive summary with a risk register we can present to the VP of Engineering. The SoC also has a TDISP endpoint for device assignment in VM environments.",
  "context": "CXL 3.1 memory expander SoC in late RTL phase. TDISP 1.0 and CXL 3.1 specs available. Prior threat model TM-2025-042 covers CXL.io but not CXL.mem or CXL.cache. No prior verification scaffold exists. Board presentation format must follow corporate risk register template."
}
```

## Expected Output
The coordinator should:
1. Decompose the request into three sequential skill activations
2. Identify the correct pipeline order: threat-model -> verification-scaffold -> executive-brief
3. Start with threat-model-skill (P0) and plan handoffs
4. Recognize the multi-domain scope (CXL + TDISP)
5. Note the prior art (TM-2025-042) that the threat model should build on

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Coordinator identifies all three skills needed: threat-model, verification-scaffold, executive-brief
- [ ] Coordinator establishes threat-model-skill as the first skill to load (P0 pipeline priority)
- [ ] Coordinator does NOT attempt to load multiple specialists simultaneously
- [ ] Pipeline sequence is correct: threat-model -> verification-scaffold -> executive-brief

### Should Pass (partial credit)
- [ ] Coordinator identifies CXL and TDISP as the relevant technology domains
- [ ] Coordinator notes prior threat model TM-2025-042 as baseline to build on
- [ ] Coordinator plans the handoff payload structure (threat findings -> verification items -> executive summary)
- [ ] Coordinator acknowledges the two-week timeline as context for scope decisions

### Bonus
- [ ] Coordinator identifies that compliance-pipeline-skill might also be relevant for CXL 3.1 standards traceability
- [ ] Coordinator suggests scoping the threat model to CXL.mem and CXL.cache interfaces specifically (since CXL.io was covered in prior art)
- [ ] Coordinator notes that IDE key management subsystem may warrant input from emerging-hw-security-skill for CXL 3.1-specific security paradigms

## Raw Trace Log
