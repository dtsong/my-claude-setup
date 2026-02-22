# Eval Case: Executive Brief for Single Critical Threat Finding

## Metadata
- **Case ID:** EB-001
- **Tier:** 1 (simple)
- **Skill Route:** executive-brief-skill
- **Estimated Complexity:** low

## Input
```json
{
  "user_prompt": "Generate a board-level executive brief for this critical finding from our data center DPU threat model:\n\nThreatFinding TF-2026-042:\n- Title: DMA Bypass via Malformed TLP in TDISP Handshake\n- Severity: CRITICAL\n- Description: During TDISP TDI state transition from CONFIG to RUN, a malformed PCIe TLP can bypass IDE stream establishment, allowing an attacker with physical PCIe access to perform DMA reads/writes to host memory regions assigned to confidential AI workloads.\n- Confidence: GROUNDED (traced to TDISP 1.0 Section 4.3)\n- Verification: [LA] LLM-assessed\n- Attack surface: Bus access control\n- Technology domain: tdisp-cxl\n- SoC family: data-center\n- Mitigation: Hardware-enforced IDE stream gating before DMA enable in RUN state\n- Estimated fix: 3-4 engineer-weeks in next silicon respin\n\nAudience: board\nOutput format: brief",
  "context": "Single upstream ThreatFinding entity. Board-level audience. No prior executive brief exists for this SoC family. No ComplianceResult or VerificationItem entities. Engineer wants the full 4-layer abstraction applied to this one finding."
}
```

## Expected Output
A board-level executive brief with:
- BLUF stating the critical risk, recommended action, timeline, and deferral consequence
- 4-layer abstraction from raw TLP bypass to executive action item
- Risk summary table with single entry
- Appropriate verification badges ([LA] throughout)
- Caveat block, confidence summary, and traceability appendix

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output follows the ExecutiveBrief template with DocumentEnvelope frontmatter
- [ ] BLUF present and contains: posture assessment, most critical risk, recommended action, timeline, deferral consequence
- [ ] 4-layer abstraction applied: Layer 0 (raw TLP bypass), Layer 1 (security impact), Layer 2 (business risk), Layer 3 (executive action)
- [ ] Severity remains CRITICAL — not downgraded for audience comfort
- [ ] All findings marked [LA] LLM-assessed — verification badge preserved from upstream
- [ ] Caveat block present stating LLM-generated draft requiring human verification

### Should Pass (partial credit)
- [ ] Layer 2 translates to business terms: customer data exposure in confidential AI pipelines
- [ ] Layer 3 includes timeline tied to silicon respin and 3-4 engineer-week estimate
- [ ] Board-appropriate vocabulary — no PCIe TLP jargon in BLUF or risk summary
- [ ] Trend marked as NEW (no prior brief)
- [ ] Confidence summary shows 1 GROUNDED finding
- [ ] Traceability appendix maps brief finding to TF-2026-042

### Bonus
- [ ] Deferral consequence quantified in business terms (customer trust, competitive position)
- [ ] Attack surface checklist included with bus access control marked ANALYZED
- [ ] Coverage boundary notes that only one finding was assessed — other domains NOT ANALYZED

## Raw Trace Log
