# Eval Case: Ambiguous Routing — Security Review of Crypto Engine

## Metadata
- **Case ID:** COORD-002
- **Tier:** 2 (medium)
- **Skill Route:** threat-model-skill (primary), physical-sca-skill (possible)
- **Estimated Complexity:** medium

## Input
```json
{
  "user_prompt": "Review the security of this AES-GCM crypto engine. It's a hardened IP block with DPA countermeasures (threshold implementation, random delays) and we need to understand if the protection is adequate for our Common Criteria EAL5+ target. The block processes TEE-encrypted workloads on our confidential computing SoC.",
  "context": "RTL and gate-level netlist available. Power model exists from a prior DPA evaluation. The block has both a threat model gap (no formal STRIDE done) and a physical side-channel evaluation gap. User did not specify which analysis they want."
}
```

## Expected Output
The coordinator should:
1. Recognize the ambiguity — the prompt touches threat modeling (security review, understanding protection adequacy) AND physical side-channel analysis (DPA countermeasures, Common Criteria)
2. Ask the user to clarify which analysis they want, OR default to threat-model-skill (P0 in the pipeline) and note physical-sca as a follow-up
3. Not silently pick one without acknowledging the other

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Coordinator identifies that both threat-model-skill and physical-sca-skill are relevant
- [ ] Coordinator does NOT silently route to only one skill without mentioning the other
- [ ] If routing without clarification, threat-model-skill is chosen (P0 pipeline priority)

### Should Pass (partial credit)
- [ ] Coordinator explains why both skills are relevant with specific reasoning (STRIDE gap vs. DPA countermeasure evaluation)
- [ ] Coordinator proposes a sequence: threat-model first, then physical-sca
- [ ] Coordinator notes the Common Criteria EAL5+ target as relevant context for both skills

### Bonus
- [ ] Coordinator identifies that compliance-pipeline-skill may also be needed for Common Criteria gap analysis
- [ ] Coordinator frames the multi-skill need using the standard pipeline: threat-model -> verification-scaffold -> compliance-pipeline

## Raw Trace Log
