# Eval Case: Basic Routing — STRIDE Analysis Request

## Metadata
- **Case ID:** COORD-001
- **Tier:** 1 (simple)
- **Skill Route:** threat-model-skill
- **Estimated Complexity:** low

## Input
```json
{
  "user_prompt": "Run a STRIDE analysis on the AES-256 encryption block in our secure boot pipeline. The block handles key unwrapping from OTP fuses and feeds decrypted firmware images to the boot ROM. Interfaces: APB config register bank, 128-bit AXI data bus, key ladder input from fuse controller, interrupt line to boot FSM.",
  "context": "Working directory contains RTL for a data center SoC secure boot subsystem. No prior threat model exists for this component."
}
```

## Expected Output
The coordinator should:
1. Classify the task as threat modeling (STRIDE analysis keyword + hardware component description)
2. Route to `skills/threat-model-skill/SKILL.md`
3. Not load any other specialist

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Coordinator routes to threat-model-skill (not verification-scaffold, not physical-sca)
- [ ] Routing decision happens without requesting additional clarification
- [ ] The loaded specialist receives the full component description and interface list

### Should Pass (partial credit)
- [ ] Coordinator identifies the technology domain as Secure Boot/DICE
- [ ] Coordinator notes this is a new analysis (no prior findings)

### Bonus
- [ ] Coordinator identifies that downstream handoff to verification-scaffold-skill may follow after threat findings are produced

## Raw Trace Log
