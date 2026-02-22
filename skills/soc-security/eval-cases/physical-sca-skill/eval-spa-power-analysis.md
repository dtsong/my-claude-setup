# Eval Case: Simple Power Analysis Assessment for RSA

## Metadata
- **Case ID:** PS-002
- **Tier:** 1 (simple)
- **Skill Route:** physical-sca-skill
- **Estimated Complexity:** low

## Input
```json
{
  "user_prompt": "Assess the SPA (Simple Power Analysis) vulnerability of our RSA-2048 software implementation running on an ARM Cortex-M4 in a smart card SoC. Details:\n- RSA-2048, CRT mode, software implementation\n- Private key stored in secure NVM, loaded to SRAM for computation\n- Square-and-multiply exponentiation (textbook, not constant-time)\n- No blinding countermeasures (no message blinding, no exponent blinding)\n- Attacker has physical access, can trigger RSA signature operations with chosen messages\n- Power measurement via EM near-field probe (no decapping required)\n- Single trace attack is the concern — SPA, not DPA\n\nSoC family: Smart Card. Technology domain: Cryptographic Operations.",
  "context": "Textbook square-and-multiply RSA on Cortex-M4. SPA-vulnerable due to key-dependent control flow (square vs. multiply). Single-trace attack. Software implementation on a microcontroller — power trace directly reveals operation sequence."
}
```

## Expected Output
A PhysicalSCAFinding for SPA on the RSA-2048 square-and-multiply implementation:
- Identification of key-dependent control flow as the leakage source
- SPA attack class — single trace distinguishes square from multiply operations
- JIL score reflecting moderate expertise but single-trace feasibility
- Severity HIGH — full private key recovery from one trace
- Recommendation for Montgomery ladder or always-multiply countermeasures

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output contains at least one PhysicalSCAFinding for SPA on RSA-2048
- [ ] Finding identifies key-dependent control flow (square vs. multiply) as the leakage source
- [ ] Finding specifies attackClass as spa (simple power analysis)
- [ ] JIL score present with all five subtotals and total
- [ ] Finding has a confidence tier and severity rating
- [ ] Finding has a research reference or `[FROM TRAINING]` marker (e.g., Kocher 1996, or Mangard/Oswald/Popp)

### Should Pass (partial credit)
- [ ] Single-trace attack feasibility explicitly stated — no need for statistical averaging
- [ ] Severity rated HIGH or CRITICAL — full 2048-bit private key recoverable from a single power trace
- [ ] Countermeasure recommendation includes constant-time exponentiation (Montgomery ladder or always square-and-multiply)
- [ ] JIL rating reflects practical attack (Enhanced-Basic to Moderate range — single trace, moderate equipment)
- [ ] ISO 17825 status set to not-assessed

### Bonus
- [ ] Notes that CRT mode introduces additional vulnerability: p and q can be independently recovered from the two half-exponentiations
- [ ] Identifies EM near-field probe as sufficient equipment (no decapping), which lowers the JIL equipment score
- [ ] Recommends RSA blinding (randomize message before exponentiation) as complementary defense even with constant-time implementation

## Raw Trace Log
