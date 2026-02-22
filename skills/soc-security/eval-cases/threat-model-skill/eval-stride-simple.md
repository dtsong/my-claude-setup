# Eval Case: Simple STRIDE — AES Block with Clear Interfaces

## Metadata
- **Case ID:** TM-001
- **Tier:** 1 (simple)
- **Skill Route:** threat-model-skill
- **Estimated Complexity:** low

## Input
```json
{
  "user_prompt": "Threat model this AES-256 block. It's a standalone encryption engine in our IoT SoC with the following interfaces:\n- APB slave port for configuration (key select, mode, go bit)\n- 128-bit AXI-Stream input (plaintext)\n- 128-bit AXI-Stream output (ciphertext)\n- Key input bus from OTP fuse controller (256-bit, active during key load only)\n- Status/interrupt output to system controller\n\nThe block sits inside the secure enclave trust boundary. Only the secure processor should access it. No DMA. Single clock domain. Technology domain: Secure Boot/DICE. SoC family: IoT.",
  "context": "No prior threat model. No RTL available. User wants STRIDE analysis. Single-domain, single-component, well-defined interfaces."
}
```

## Expected Output
A STRIDE analysis covering all 5 interfaces across 6 STRIDE categories, producing ThreatFinding entities with:
- At least one finding per STRIDE category
- Correct confidence tiers (INFERRED or SPECULATIVE since no spec sections provided)
- Attack surface checklist with all 7 surfaces assessed
- Coverage boundary statement
- Caveat block noting training-knowledge grounding

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output contains at least 6 ThreatFinding entities (minimum one per STRIDE category)
- [ ] Every finding has a confidence tier (GROUNDED, INFERRED, SPECULATIVE, or ABSENT)
- [ ] Every finding has a severity rating (CRITICAL through INFORMATIONAL)
- [ ] Attack surface checklist present with all 7 standard surfaces assessed
- [ ] Key management attack surface marked as ANALYZED (key input bus is an explicit interface)
- [ ] Findings include `[FROM TRAINING]` markers since no spec sections were provided

### Should Pass (partial credit)
- [ ] Spoofing finding addresses unauthorized APB access (secure processor bypass)
- [ ] Information Disclosure finding addresses key exposure on the 256-bit bus during key load
- [ ] Elevation of Privilege finding addresses trust boundary crossing from non-secure to secure enclave
- [ ] Coverage boundary explicitly lists what was and was not analyzed
- [ ] Findings include verificationMethod field for downstream handoff

### Bonus
- [ ] Side-channel attack surface marked as NOT ANALYZED with rationale (no power model)
- [ ] Cross-family reuse assessment provided (IoT -> other families)
- [ ] Boot chain attack surface assessed as applicable (block is in secure boot pipeline)

## Raw Trace Log
