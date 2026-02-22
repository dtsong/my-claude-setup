# Navigation Eval Case: Compliance vs Executive Brief — FIPS Board Summary

## Metadata
- **Case ID:** NAV-002
- **Tier:** 1 (simple)
- **Expected Route:** sequential: compliance-pipeline-skill -> executive-brief-skill
- **Navigation Challenge:** "FIPS compliance" triggers compliance-pipeline, but "summarize for the board" triggers executive-brief; correct answer is compliance first to generate findings, then executive-brief to format for board audience

## Input
```json
{
  "user_prompt": "Summarize our FIPS compliance status for the board",
  "context": "The SoC has undergone partial FIPS 140-3 evaluation. Some compliance mapping exists but is incomplete. The user wants a board-ready summary, implying both compliance analysis and executive communication."
}
```

## Expected Routing Behavior
The coordinator should route to compliance-pipeline-skill first. The request requires FIPS 140-3 compliance mapping and gap analysis before any summary can be produced. Once compliance-pipeline generates a ComplianceState entity with gap findings, those findings should be handed off to executive-brief-skill to produce a board-appropriate 4-layer abstraction summary. Routing directly to executive-brief without compliance data would produce an unfounded summary.

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Identifies compliance-pipeline-skill as the first routing target
- [ ] Recognizes that executive-brief-skill is needed as a downstream step
- [ ] Does NOT route exclusively to executive-brief-skill

### Should Pass (partial credit)
- [ ] Explicitly states the sequential handoff: compliance-pipeline then executive-brief
- [ ] Mentions FIPS 140-3 as the relevant compliance standard
- [ ] Explains that compliance findings are required input for the executive brief

### Bonus
- [ ] References the handoff protocol entity types (ComplianceState -> BriefSections)
- [ ] Notes that the board audience implies CISO/executive layer in the executive-brief 4-layer model

## Raw Trace Log
