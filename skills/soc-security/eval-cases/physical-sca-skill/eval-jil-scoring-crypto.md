# Eval Case: JIL Scoring for a Crypto Accelerator

## Metadata
- **Case ID:** PS-004
- **Tier:** 2 (medium)
- **Skill Route:** physical-sca-skill
- **Estimated Complexity:** medium

## Input
```json
{
  "user_prompt": "Perform a full JIL attack potential scoring for our AES-256-GCM hardware crypto accelerator in a payment terminal SoC. We need scores for every applicable physical SCA attack vector. Details:\n\nCrypto engine:\n- AES-256-GCM, dedicated hardware accelerator\n- 1st-order Boolean masking on S-box (DOM — Domain-Oriented Masking)\n- Random clock jitter (hiding countermeasure, +/- 5% frequency variation)\n- No dual-rail logic\n- GHASH computation for authentication tag — unmasked\n\nPhysical protections:\n- Active metal shield mesh (top 2 metal layers)\n- Voltage glitch sensor (threshold-based, 100ns detection window)\n- Temperature sensor with operating range enforcement\n- No light sensor (no laser FI detection)\n\nAttacker model:\n- Standard lab equipment: oscilloscope (1GHz bandwidth, 5GS/s), EM probe (near-field H-field), ChipWhisperer for glitching\n- Can trigger encryptions with chosen plaintexts (API access)\n- Cannot decap without triggering shield mesh tamper response\n- Has datasheet but no RTL source code\n\nTarget: Recover 256-bit AES key. CC EAL4+ certification target.\nSoC family: Payment Terminal. Technology domain: Cryptographic Operations.",
  "context": "Payment terminal crypto accelerator with multiple countermeasures. 1st-order masking, clock jitter, active shield, glitch sensor. JIL scoring is the primary deliverable for CC evaluation. Multiple attack classes need scoring: DPA/CPA, EMA, fault injection."
}
```

## Expected Output
Multiple PhysicalSCAFindings with detailed JIL scoring for each attack vector:
- 2nd-order CPA bypassing 1st-order DOM masking (power and EM channels)
- EM analysis targeting GHASH computation (unmasked)
- Voltage glitch DFA considering the glitch sensor's 100ns detection window
- Each with complete 5-factor JIL scoring, total, and CC AVA_VAN mapping
- Countermeasure effectiveness assessment per attack vector

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output contains at least 3 PhysicalSCAFindings covering power/CPA, EM, and fault injection attack vectors
- [ ] Every finding has a complete JIL score with all 5 subtotals (elapsed, expertise, knowledge, access, equipment), total, and rating
- [ ] JIL ratings correctly map to CC AVA_VAN levels
- [ ] Every finding has a confidence tier and severity rating
- [ ] Every finding has a research reference or `[FROM TRAINING]` marker
- [ ] 1st-order masking assessed for 2nd-order attack bypass with appropriate trace count scaling

### Should Pass (partial credit)
- [ ] 2nd-order CPA finding includes N^2 trace count scaling factor (masking order + 1) for DOM bypass
- [ ] GHASH finding separately scored — unmasked GHASH is a weaker target than masked AES
- [ ] Active shield mesh impacts JIL access/equipment scores (prevents decapping for invasive EM probing)
- [ ] Voltage glitch sensor's 100ns window assessed — can sub-100ns glitches evade detection?
- [ ] Countermeasure summary table present with effectiveness rating per countermeasure per attack

### Bonus
- [ ] Notes that DOM (Domain-Oriented Masking) has specific leakage characteristics in glitch scenarios — glitch can collapse shares
- [ ] Identifies clock jitter as reducing trace alignment quality, increasing trace count requirement by estimated factor
- [ ] Recommends masking GHASH computation to close the authentication tag leakage gap

## Raw Trace Log
