# Eval Case: Boundary Confusion — Verification-Sounding Prompt That Needs Threat Identification

## Metadata
- **Case ID:** TM-005
- **Tier:** 3 (complex)
- **Skill Route:** threat-model-skill
- **Estimated Complexity:** high

## Input
```json
{
  "user_prompt": "I need to verify that our DMA firewall correctly blocks unauthorized transactions. Can you check the address range enforcement and make sure the FSM transitions are safe? The firewall sits between the application processor and the shared SRAM. It has 8 configurable region descriptors (base/size/permissions) programmed via a locked APB interface. The lock bit is set by secure boot firmware and should be irreversible until next reset.\n\nThe regions protect: boot ROM (RO), secure SRAM (secure-only), crypto engine registers (secure-only), and general SRAM (read-write all). We had a silicon bug last tapeout where region 0 and region 7 overlapped and the firewall defaulted to permissive on the overlap.",
  "context": "User said 'verify' and 'check' which sound like verification-scaffold-skill triggers. But no ThreatFindings exist as input — the user is actually describing a component that needs threat identification first. The mention of a prior silicon bug is a strong signal that threat modeling (what can go wrong) should precede verification scaffolding (how to check it)."
}
```

## Expected Output
The skill should:
1. Recognize that despite verification-sounding language, the task requires threat identification first
2. Activate threat-model-skill (not verification-scaffold-skill)
3. Produce STRIDE findings covering the DMA firewall, including the region overlap class of bugs
4. Note the prior silicon bug as evidence grounding for overlap/priority threats

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Task is handled as threat identification, NOT as verification scaffolding
- [ ] Output contains ThreatFinding entities (not VerificationItem entities)
- [ ] Region descriptor overlap/priority threat is identified (directly grounded by the reported silicon bug)
- [ ] Lock bit bypass threat is identified (irreversible lock is a critical security property)
- [ ] APB interface threats are identified (unauthorized region descriptor modification)
- [ ] The prior silicon bug is used as grounding evidence (GROUNDED confidence for overlap threats)

### Should Pass (partial credit)
- [ ] Tampering finding: region descriptor modification after lock (APB write to locked registers)
- [ ] Elevation of Privilege finding: non-secure master accessing secure-only regions via misconfigured descriptors
- [ ] Denial of Service finding: all regions configured to deny, bricking the system
- [ ] Default-permissive behavior on overlap is flagged as a design philosophy threat (fail-open vs. fail-closed)
- [ ] Skill explicitly notes that verification-scaffold-skill should follow after threat findings are produced

### Bonus
- [ ] Suggests the overlap case requires specific attention because region priority logic is often implementation-defined
- [ ] Identifies the reset-only lock release as a availability trade-off (cannot update firewall rules without reset)
- [ ] Cross-family reuse assessment notes DMA firewalls exist across all SoC families with similar threat profiles

## Raw Trace Log
