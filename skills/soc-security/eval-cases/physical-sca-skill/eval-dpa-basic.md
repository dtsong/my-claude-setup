# Eval Case: Basic DPA Assessment for AES Implementation

## Metadata
- **Case ID:** PS-001
- **Tier:** 1 (simple)
- **Skill Route:** physical-sca-skill
- **Estimated Complexity:** low

## Input
```json
{
  "user_prompt": "Assess the DPA vulnerability of our AES-128 hardware crypto engine in an IoT secure element SoC. Details:\n- AES-128, ECB and CBC modes, hardware implementation\n- Key stored in OTP eFuse, loaded into key register at boot\n- No masking countermeasures deployed\n- No hiding countermeasures (no random delays, no dual-rail logic)\n- Attacker has physical access to the device and can supply chosen plaintexts\n- Attacker can measure power consumption via a shunt resistor on VDD\n- No voltage glitch detection sensors\n- Target: recover the 128-bit secret key\n\nSoC family: IoT Secure Element. Technology domain: Cryptographic Operations.",
  "context": "Unprotected AES-128 hardware engine. No countermeasures. Attacker has full physical access with chosen-plaintext capability. Classic DPA target. First assessment — no prior findings."
}
```

## Expected Output
A PhysicalSCAFinding for DPA/CPA on the unprotected AES-128 engine:
- Identification of first-round S-box output as the DPA target intermediate
- Hamming weight or Hamming distance leakage model
- JIL attack potential score with all five subtotals
- Low trace count estimate (hundreds to low thousands for unprotected AES)
- Severity rated HIGH or CRITICAL given no countermeasures
- ISO 17825 status as not-assessed (no lab data)

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output contains at least one PhysicalSCAFinding for DPA or CPA on AES-128
- [ ] Finding identifies a specific intermediate value as the attack target (e.g., S-box output in round 1)
- [ ] Finding includes a leakage model (hamming-weight, hamming-distance, or identity)
- [ ] JIL score present with all five subtotals (elapsed, expertise, knowledge, access, equipment) and total
- [ ] Finding has a confidence tier and severity rating
- [ ] Finding has a research reference or `[FROM TRAINING]` marker

### Should Pass (partial credit)
- [ ] Trace count estimated — order of magnitude (hundreds to low thousands for unprotected AES)
- [ ] JIL rating maps to Enhanced-Basic or Moderate (unprotected AES with physical access is practical)
- [ ] Absence of masking explicitly noted as the reason for low trace count requirement
- [ ] Countermeasure assessment recommends at minimum first-order Boolean masking
- [ ] ISO 17825 status set to not-assessed with note recommending TVLA measurement

### Bonus
- [ ] Notes that both first-round and last-round attacks are feasible, with last-round CPA requiring known ciphertext
- [ ] Distinguishes DPA (difference of means) from CPA (correlation) and recommends CPA for higher efficiency
- [ ] Identifies key schedule as a secondary leakage source if key expansion is performed in hardware at each encryption

## Raw Trace Log
