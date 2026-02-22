# Navigation Eval Case: Full Pipeline — Complete IoT SoC Security Assessment

## Metadata
- **Case ID:** NAV-010
- **Tier:** 3 (complex)
- **Expected Route:** sequential: threat-model-skill -> verification-scaffold-skill -> compliance-pipeline-skill -> executive-brief-skill
- **Navigation Challenge:** Request explicitly requires the full four-stage pipeline; coordinator must identify all four skills, sequence them in correct dependency order, and articulate the handoff protocol between each stage

## Input
```json
{
  "user_prompt": "Starting from scratch, give me a complete security assessment of our IoT SoC including threats, verification plan, compliance mapping, and executive brief",
  "context": "The IoT SoC is a new design with a Cortex-M33 secure core, TrustZone isolation, AES-256 crypto engine, TRNG, secure boot chain, and OTA update mechanism. No prior security analysis of any kind exists. The user wants a comprehensive end-to-end assessment covering all four pipeline stages. Target standards include PSA Certified Level 2 and FIPS 140-3."
}
```

## Expected Routing Behavior
The coordinator should identify this as a full pipeline request and sequence all four core skills in dependency order: (1) threat-model-skill produces ThreatFindings covering all interfaces and trust boundaries of the IoT SoC via STRIDE analysis, (2) verification-scaffold-skill consumes ThreatFindings to generate tiered verification checklists and SVA assertions targeting the identified threats, (3) compliance-pipeline-skill maps findings and verification coverage against PSA Certified Level 2 and FIPS 140-3 requirements, producing ComplianceState with gap analysis, (4) executive-brief-skill consumes all upstream outputs to produce a 4-layer abstraction executive summary for board/CISO presentation. The coordinator must route to threat-model-skill first and complete each stage before loading the next.

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Identifies all four skills: threat-model, verification-scaffold, compliance-pipeline, executive-brief
- [ ] Routes to threat-model-skill as the FIRST skill
- [ ] Specifies sequential execution with correct dependency order
- [ ] Does NOT attempt to load multiple skills simultaneously

### Should Pass (partial credit)
- [ ] Correct full sequence: threat-model -> verification-scaffold -> compliance-pipeline -> executive-brief
- [ ] Explains the data dependency between each stage (upstream output feeds downstream input)
- [ ] Mentions the handoff protocol for passing entity types between skills
- [ ] Identifies PSA Certified Level 2 and FIPS 140-3 as the target compliance standards
- [ ] Recognizes the IoT SoC's key components as relevant attack surfaces

### Bonus
- [ ] References specific entity types in the handoff chain (ThreatFindings -> VerificationChecklist -> ComplianceState -> BriefSections)
- [ ] Notes that additional specialist skills (physical-sca, kernel-security) could supplement but are not in the core pipeline
- [ ] Estimates relative complexity or time allocation across the four stages

## Raw Trace Log
