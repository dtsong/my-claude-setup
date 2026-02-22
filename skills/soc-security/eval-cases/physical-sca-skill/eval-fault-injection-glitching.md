# Eval Case: Voltage Glitching Fault Injection Assessment

## Metadata
- **Case ID:** PS-003
- **Tier:** 2 (medium)
- **Skill Route:** physical-sca-skill
- **Estimated Complexity:** medium

## Input
```json
{
  "user_prompt": "Assess the voltage glitching fault injection attack surface on our secure boot processor in an automotive SoC. Details:\n\nTarget: Secure boot ROM executing signature verification (ECDSA P-256)\n- Boot ROM is immutable (mask ROM)\n- ECDSA verification uses a hardware crypto accelerator for scalar multiplication\n- Boot chain: ROM -> first-stage bootloader (authenticated) -> OS kernel (authenticated)\n- Signature verification result is a boolean (pass/fail) checked by the ROM code\n\nFault injection surface:\n- External VDD supply pin accessible on the PCB (no internal LDO for secure domain)\n- Clock source: external crystal oscillator, PLL internally\n- No voltage glitch detection sensors deployed\n- No clock glitch detection sensors deployed\n- No instruction flow redundancy (no dual execution or instruction counter checks)\n- Boot time is deterministic (~50ms from reset to first-stage bootloader handoff)\n\nAttacker model:\n- Physical access to PCB\n- Can control VDD with sub-nanosecond glitch injector (e.g., ChipWhisperer)\n- Can trigger reset and observe boot sequence timing via GPIO/UART debug output\n- Goal: bypass signature verification to boot unsigned firmware\n\nSoC family: Automotive. Technology domain: Secure Boot/DICE.",
  "context": "Secure boot with ECDSA P-256 signature verification. No fault injection countermeasures. External VDD accessible. Deterministic boot timing makes glitch timing feasible. Attacker wants to bypass boot authentication."
}
```

## Expected Output
PhysicalSCAFindings for voltage glitching attacks on the secure boot process:
- Glitch on signature verification comparison (skip the conditional branch)
- Glitch on ECDSA scalar multiplication (DFA to recover signing key)
- JIL scores for each attack vector
- Assessment of the absent countermeasures (no sensors, no redundancy)
- Severity CRITICAL for boot bypass

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output contains at least one PhysicalSCAFinding for voltage glitch fault injection
- [ ] Finding identifies signature verification bypass as a primary attack target
- [ ] Finding specifies attackClass as voltage-glitch
- [ ] JIL score present with all five subtotals and total for at least one attack vector
- [ ] Finding has a confidence tier and severity rating
- [ ] Finding has a research reference or `[FROM TRAINING]` marker

### Should Pass (partial credit)
- [ ] Two distinct attack vectors identified: (1) skip signature check branch, (2) fault ECDSA computation for DFA
- [ ] Deterministic boot timing (~50ms) noted as reducing the glitch timing difficulty
- [ ] Absence of voltage glitch sensors explicitly flagged as a critical gap
- [ ] Absence of instruction flow redundancy noted — single glitch can skip a branch instruction
- [ ] Countermeasure recommendations include: voltage glitch sensor, instruction redundancy (double-check), internal LDO

### Bonus
- [ ] Notes that DFA on ECDSA P-256 can recover the private signing key with as few as 1-2 faulty signatures (Biehl-Meyer-Muller attack)
- [ ] Identifies the boolean comparison instruction as the specific single-point-of-failure for boot bypass
- [ ] Recommends defense-in-depth: sensor + redundant verification + anti-rollback to prevent downgrade after bypass

## Raw Trace Log
