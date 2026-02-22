# Eval Case: Attack Tree — Key Derivation Module

## Metadata
- **Case ID:** TM-003
- **Tier:** 2 (medium)
- **Skill Route:** threat-model-skill
- **Estimated Complexity:** medium

## Input
```json
{
  "user_prompt": "Build an attack tree for compromising the hardware key derivation function (KDF) module in our secure element. The root goal is: 'Extract or reconstruct the platform root key from the KDF output observations.'\n\nKDF details:\n- NIST SP 800-108 compliant HMAC-based KDF\n- Input: 256-bit root key from PUF, 128-bit context/label, 32-bit counter\n- Output: 256-bit derived keys via AXI-Lite read interface\n- Root key never leaves the KDF — only derived keys are observable\n- Clock: single 200MHz domain\n- Debug: JTAG port with HMAC-authenticated lock (disabled after production fuse blow)\n- Anti-tamper: voltage/temperature glitch detectors with zeroization trigger\n\nSoC family: Automotive. Technology domain: Secure Boot/DICE.",
  "context": "No prior threat model for this module. The security architect wants a feasibility-focused attack tree to justify the anti-tamper budget to management. Adversary model: well-funded attacker with lab access (JIL attack potential 'Enhanced-Basic')."
}
```

## Expected Output
An attack tree with:
- Clear root goal and AND/OR decomposition
- Multiple attack paths (side-channel, fault injection, debug, interface exploitation)
- Leaf-level feasibility assessment (difficulty, access, detectability)
- Minimal cut sets identifying the cheapest mitigation combinations

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Attack tree has a clearly stated root goal matching the input
- [ ] Tree uses AND/OR decomposition with at least 3 distinct sub-goals
- [ ] At least 4 leaf-level attack actions with feasibility assessment (difficulty, access level, detectability)
- [ ] At least one side-channel attack path (power/EM analysis of KDF computation)
- [ ] At least one fault injection attack path (glitch detector bypass or zeroization defeat)
- [ ] JTAG debug path assessed even though it has HMAC lock (authenticated debug bypass is a known attack vector)

### Should Pass (partial credit)
- [ ] Each leaf maps to the JIL attack potential framework (given the adversary model specifies Enhanced-Basic)
- [ ] Minimal cut sets identified — the smallest set of mitigations that blocks all paths to root goal
- [ ] AXI-Lite interface exploitation path considered (differential analysis of derived key outputs)
- [ ] PUF reliability/stability as an attack surface (environmental manipulation to shift PUF response)
- [ ] Anti-tamper sensor bypass path includes voltage glitching below detector threshold

### Bonus
- [ ] Cost-benefit analysis linking minimal cut sets to the anti-tamper budget justification
- [ ] Finding that the counter input (only 32 bits) limits the derivation space and may enable exhaustive analysis of derived keys
- [ ] Cross-family reuse assessment noting that KDF attack trees apply broadly across automotive and IoT families

## Raw Trace Log
