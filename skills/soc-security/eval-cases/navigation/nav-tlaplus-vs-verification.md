# Navigation Eval Case: TLA+ vs Verification Scaffold — Formal Access Control Properties

## Metadata
- **Case ID:** NAV-005
- **Tier:** 2 (medium)
- **Expected Route:** tlaplus-security-skill
- **Navigation Challenge:** "verify the access control module" sounds like verification-scaffold, but "generate formal properties" specifically targets TLA+ formal specification; the keyword "formal" disambiguates toward tlaplus-security

## Input
```json
{
  "user_prompt": "Generate formal properties to verify the access control module",
  "context": "The SoC has a memory protection unit (MPU) that enforces access control between secure and non-secure regions. The user wants safety and liveness properties expressed formally, not an SVA assertion checklist or a verification tier assignment."
}
```

## Expected Routing Behavior
The coordinator should route to tlaplus-security-skill. The keyword "formal properties" directly maps to TLA+ formal security property specification, which produces safety/liveness properties in TLA+ notation. Verification-scaffold-skill generates SVA assertions and tiered verification checklists, which is a different output format and methodology. The distinction is formal mathematical properties (TLA+) vs implementation-level verification artifacts (SVA). The coordinator should recognize "formal" + "properties" as the disambiguating signal.

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Routes to tlaplus-security-skill as the primary skill
- [ ] Recognizes "formal properties" as a TLA+ keyword
- [ ] Does NOT route to verification-scaffold-skill as the primary skill

### Should Pass (partial credit)
- [ ] Explains the distinction between TLA+ formal properties and SVA verification assertions
- [ ] Identifies "safety and liveness properties" as TLA+ output artifacts
- [ ] Notes that verification-scaffold could be a follow-up for implementation-level checks

### Bonus
- [ ] Mentions that TLA+ properties can inform downstream SVA generation in verification-scaffold
- [ ] Identifies access control as a good candidate for formal specification (invariant-heavy domain)

## Raw Trace Log
