# Eval Case: Risk Register Summary for Board Presentation

## Metadata
- **Case ID:** EB-002
- **Tier:** 1 (simple)
- **Skill Route:** executive-brief-skill
- **Estimated Complexity:** low

## Input
```json
{
  "user_prompt": "Produce a risk register summary for our quarterly board presentation. Use these four findings from our client SoC threat model:\n\nTF-2026-101: Secure Boot Bypass via Glitch Attack on Reset Vector\n- Severity: HIGH | Confidence: INFERRED | Verification: [LA]\n- SoC family: client | Domain: secure-boot-dice\n\nTF-2026-102: Key Material Exposure Through Debug Port Side-Channel\n- Severity: HIGH | Confidence: GROUNDED | Verification: [TV] (confirmed via power trace)\n- SoC family: client | Domain: secure-boot-dice\n\nTF-2026-103: OTA Firmware Downgrade Due to Weak Anti-Rollback Counter\n- Severity: MEDIUM | Confidence: GROUNDED | Verification: [HV]\n- SoC family: client | Domain: supply-chain\n\nTF-2026-104: Insufficient Entropy in TRNG During Cold Boot\n- Severity: MEDIUM | Confidence: SPECULATIVE | Verification: [LA]\n- SoC family: client | Domain: secure-boot-dice\n\nAudience: board\nOutput format: risk-entry",
  "context": "Four upstream ThreatFinding entities with mixed severities, confidence tiers, and verification statuses. Board audience. No prior brief exists. Engineer wants risk register entries suitable for a quarterly review deck."
}
```

## Expected Output
A risk register with four entries, each abstracted through the 4-layer model, with:
- Entries sorted by severity (HIGH before MEDIUM)
- Verification badges preserved and prominently displayed
- SPECULATIVE finding (TF-2026-104) presented with prominent caveat
- Mixed verification status clearly communicated (1 [TV], 1 [HV], 2 [LA])

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output contains exactly 4 risk register entries corresponding to the 4 input findings
- [ ] Severities preserved: 2 HIGH, 2 MEDIUM — none changed for audience
- [ ] Verification badges correctly shown: TF-102 as [TV], TF-103 as [HV], TF-101 and TF-104 as [LA]
- [ ] SPECULATIVE finding (TF-2026-104) carries prominent caveat language
- [ ] Every entry traces to its source ThreatFinding ID
- [ ] Caveat block present noting LLM-generated draft

### Should Pass (partial credit)
- [ ] Layer 2 business risk provided for each finding (not just technical restating)
- [ ] Layer 3 action items provided for each finding with recommended next steps
- [ ] Board-appropriate vocabulary — no jargon like "glitch attack" or "anti-rollback counter" in summaries
- [ ] Confidence summary shows breakdown: 2 GROUNDED, 1 INFERRED, 1 SPECULATIVE
- [ ] Verification status summary: 1 [TV], 1 [HV], 2 [LA] with explanation of badge meanings
- [ ] Trend column shows NEW for all entries (no prior brief)

### Bonus
- [ ] Risk register entries prioritized with recommended board action for each severity tier
- [ ] Reliability percentage calculated from verification mix
- [ ] Cross-finding pattern noted: 3 of 4 findings relate to secure-boot-dice domain, suggesting systemic concern

## Raw Trace Log
