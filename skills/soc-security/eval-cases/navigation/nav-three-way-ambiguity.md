# Navigation Eval Case: Three-Way Ambiguity — PQC Threat Model + Verification + Compliance

## Metadata
- **Case ID:** NAV-007
- **Tier:** 3 (complex)
- **Expected Route:** sequential: threat-model-skill -> verification-scaffold-skill -> compliance-pipeline-skill
- **Navigation Challenge:** Request explicitly spans three specialist domains; coordinator must sequence them correctly following pipeline priority order rather than attempting parallel or arbitrary ordering

## Input
```json
{
  "user_prompt": "We need to threat model our PQC migration, verify the implementation, and check FIPS compliance",
  "context": "The SoC is migrating from RSA/ECDSA to ML-KEM and ML-DSA (post-quantum algorithms). The user wants a complete security assessment covering threat identification for the migration, verification of the PQC implementation, and FIPS 140-3 compliance validation for the new algorithms. No prior analysis exists."
}
```

## Expected Routing Behavior
The coordinator should identify all three specialist skills and sequence them in pipeline priority order: (1) threat-model-skill to identify threats in the PQC migration (new algorithm attack surfaces, hybrid scheme risks, key management changes), (2) verification-scaffold-skill to generate verification checklists and SVA assertions for the PQC implementation based on the identified threats, (3) compliance-pipeline-skill to map the PQC implementation against FIPS 140-3 requirements. Each skill's output feeds the next via the handoff protocol. The coordinator should not attempt to load all three simultaneously.

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Identifies all three skills: threat-model, verification-scaffold, and compliance-pipeline
- [ ] Routes to threat-model-skill as the FIRST skill in the sequence
- [ ] Specifies sequential execution, not parallel loading

### Should Pass (partial credit)
- [ ] Correct full sequence: threat-model -> verification-scaffold -> compliance-pipeline
- [ ] Explains why threat-model must come first (threats inform verification targets)
- [ ] Explains why verification precedes compliance (implementation must be verified before compliance can be assessed)
- [ ] Mentions PQC-specific concerns (ML-KEM, ML-DSA, hybrid schemes)

### Bonus
- [ ] Notes that emerging-hw-security-skill could supplement with PQC-specific architectural guidance
- [ ] References handoff protocol entity types for inter-skill data flow
- [ ] Identifies FIPS 140-3 as specifically relevant to PQC algorithm validation

## Raw Trace Log
