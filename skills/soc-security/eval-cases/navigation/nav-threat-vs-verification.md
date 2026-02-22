# Navigation Eval Case: Threat Modeling vs Verification — AES Key Extraction

## Metadata
- **Case ID:** NAV-001
- **Tier:** 1 (simple)
- **Expected Route:** threat-model-skill
- **Navigation Challenge:** "check if secure" and "attacks" overlap threat modeling and verification; threat-model is the correct first step since no threats have been identified yet

## Input
```json
{
  "user_prompt": "I need to check if my AES block is secure against key extraction attacks",
  "context": "No prior threat model exists. No verification plan exists. User has RTL but no formal threat findings to verify against. The word 'check' could imply verification, but 'attacks' implies threat identification."
}
```

## Expected Routing Behavior
The coordinator should route to threat-model-skill. The request mentions "attacks" which maps to threat identification (STRIDE, attack trees). While "check if secure" could suggest verification, verification-scaffold requires upstream threat findings to generate checklists against. Without an existing threat model, threat-model-skill is the correct P0 entry point. The coordinator may note that verification-scaffold is a logical follow-up after threats are identified.

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Routes to threat-model-skill as the primary skill
- [ ] Does NOT route to verification-scaffold-skill as the primary skill
- [ ] Recognizes "key extraction attacks" as a threat identification task

### Should Pass (partial credit)
- [ ] Explains that threat modeling must precede verification in the pipeline
- [ ] Mentions verification-scaffold as a recommended follow-up step
- [ ] Identifies the AES block as the target component for STRIDE analysis

### Bonus
- [ ] Notes that physical-sca-skill may be relevant if key extraction refers to DPA/SPA
- [ ] Proposes a two-phase approach: threat-model then verification-scaffold

## Raw Trace Log
