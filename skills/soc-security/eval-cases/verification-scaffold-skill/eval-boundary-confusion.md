# Eval Case: Boundary Confusion — Compliance-Sounding Prompt That Needs Verification Scaffolding

## Metadata
- **Case ID:** VS-005
- **Tier:** 3 (complex)
- **Skill Route:** verification-scaffold-skill
- **Estimated Complexity:** high

## Input
```json
{
  "user_prompt": "I need to track our coverage against the SESIP Level 3 requirements for the crypto subsystem. We have 14 threat findings from the threat model and I need to show the review board which ones have formal verification evidence and which ones are gaps. Can you map the findings to verification artifacts and produce a coverage matrix?\n\nHere are the critical findings that need verification mapping:\n- TF-041: AES key schedule accessible via debug scan chain (CRITICAL/GROUNDED, SVA-verifiable)\n- TF-042: HMAC intermediate state not zeroized after completion (HIGH/GROUNDED, SVA-verifiable)\n- TF-043: TRNG entropy source health test bypass (HIGH/INFERRED, needs formal analysis)\n- TF-044: DPA leakage in modular exponentiation (CRITICAL/SPECULATIVE, needs physical test)\n- TF-045: Certificate parsing buffer overflow in X.509 handler (HIGH/GROUNDED, needs simulation)",
  "context": "User language sounds like compliance-pipeline-skill ('track coverage', 'SESIP Level 3', 'show the review board'). But the actual task is mapping threat findings to verification tiers and producing verification artifacts — this is verification-scaffold-skill territory. The compliance layer would consume the verification scaffold output, not produce it. ThreatFindings are provided as input, which matches verification-scaffold-skill's expected input format."
}
```

## Expected Output
The skill should:
1. Recognize that despite compliance-sounding language, the core task is verification scaffolding
2. Activate verification-scaffold-skill (not compliance-pipeline-skill)
3. Map each finding to the correct verification tier
4. Produce a coverage matrix showing verification tier and confidence per finding
5. Generate appropriate artifacts (SVA templates for Tier 1, NL properties for Tier 2, spec descriptions for Tier 3)

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Task is handled as verification scaffolding, NOT as compliance tracking
- [ ] Output contains VerificationItem entities (not compliance traceability entries)
- [ ] TF-041 (debug scan chain access) assigned to Tier 1 with SVA template for scan chain isolation
- [ ] TF-042 (HMAC zeroization) assigned to Tier 1 with SVA template for post-operation register clearing
- [ ] TF-044 (DPA leakage) assigned to Tier 3 with NO SVA and explicit rationale (physical side-channel)
- [ ] Coverage matrix present showing all 5 findings with tier, confidence, and verification status

### Should Pass (partial credit)
- [ ] TF-043 (TRNG health test bypass) assigned to Tier 2 or Tier 3 (formal analysis, not simple SVA)
- [ ] TF-045 (certificate parsing overflow) assigned to Tier 2 (simulation-based, behavioral property)
- [ ] Confidence propagation correct: TF-044 SPECULATIVE upstream caps verification confidence at SPECULATIVE
- [ ] SVA templates for TF-041 and TF-042 include INTENT and DOES NOT CHECK annotations
- [ ] Skill explicitly notes that compliance-pipeline-skill should consume this output for SESIP Level 3 mapping

### Bonus
- [ ] Skill recognizes SESIP Level 3 as context that affects verification rigor expectations (not just coverage but evidence quality)
- [ ] Coverage matrix includes a column for "evidence strength" distinguishing formal (SVA) from informal (review) verification
- [ ] Skill notes that 5 of 14 findings are provided and offers to process the remaining 9 when available

## Raw Trace Log
