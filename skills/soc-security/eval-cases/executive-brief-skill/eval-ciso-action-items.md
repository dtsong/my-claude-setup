# Eval Case: CISO-Targeted Action Item Summary with Priority Ranking

## Metadata
- **Case ID:** EB-004
- **Tier:** 2 (medium)
- **Skill Route:** executive-brief-skill
- **Estimated Complexity:** medium

## Input
```json
{
  "user_prompt": "Produce a CISO action item brief from these combined threat model and compliance findings for our automotive V2X gateway SoC:\n\n**ThreatFindings:**\nTF-2026-301: V2X message spoofing — no IEEE 1609.2 certificate validation on receive path (CRITICAL, GROUNDED, [LA])\nTF-2026-302: HSM key extraction via voltage glitch during ECDSA signing (HIGH, INFERRED, [LA])\nTF-2026-303: CAN-FD gateway allows unfiltered message forwarding to safety-critical ECUs (HIGH, GROUNDED, [HV])\nTF-2026-304: OTA update manifest signature verification uses deprecated SHA-1 (MEDIUM, GROUNDED, [TV])\nTF-2026-305: Ethernet TSN stream authentication not enforced between SoC and camera modules (MEDIUM, INFERRED, [LA])\n\n**ComplianceResults:**\nCR-2026-401: ISO 21434 Clause 8 TARA — PARTIAL (vehicle interfaces only, SoC-internal gaps)\nCR-2026-402: ISO 21434 Clause 10 Product Development — GAP (no cybersecurity case document)\nCR-2026-403: FIPS 140-3 Self-Tests — NOT-MET (no power-up self-test in HSM)\nCR-2026-404: UNECE R155 Cybersecurity Management System — PARTIAL (policy exists, implementation gaps)\n\nSoC family: automotive\nTechnology domains: supply-chain, secure-boot-dice\nAudience: ciso\nOutput format: brief\n\nThe CISO needs a prioritized action list for the next 6 months with clear dependency ordering. The Q3 silicon respin is the hard deadline for hardware fixes.",
  "context": "Mixed upstream entities — 5 ThreatFindings and 4 ComplianceResults. CISO audience with specific timeline constraint (Q3 silicon respin). Automotive context adds regulatory urgency (EU type approval). Engineer wants action items ranked by priority with dependency chains."
}
```

## Expected Output
A CISO-level brief with:
- BLUF summarizing posture as Red/Amber with regulatory deadline pressure
- Action items ranked by priority with dependency ordering
- Clear distinction between hardware fixes (must hit Q3 respin) and firmware/process fixes (can be done post-silicon)
- Combined threat and compliance findings in unified risk view
- Timeline aligned to Q3 silicon respin deadline

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output follows ExecutiveBrief template with DocumentEnvelope frontmatter
- [ ] BLUF addresses the Q3 silicon respin deadline and regulatory context
- [ ] All 5 ThreatFindings and 4 ComplianceResults represented in the brief
- [ ] Action items explicitly prioritized with dependency ordering (not just severity sorting)
- [ ] Hardware fixes (voltage glitch mitigation, self-test implementation) flagged as respin-dependent
- [ ] Severities preserved from upstream — CRITICAL V2X spoofing remains CRITICAL
- [ ] Caveat block present

### Should Pass (partial credit)
- [ ] Action items separated into: (1) must-fix-before-respin (HW), (2) firmware fixable, (3) process/documentation
- [ ] ISO 21434 compliance gaps tied to EU type approval timeline as business risk
- [ ] FIPS self-test gap tied to US government fleet deployment as business risk
- [ ] Dependency chain identified: TARA completion (CR-401) must precede cybersecurity case (CR-402)
- [ ] Confidence and verification summaries present with correct counts
- [ ] Traceability appendix maps to both TF-IDs and CR-IDs

### Bonus
- [ ] 6-month roadmap with monthly milestones aligned to Q3 respin
- [ ] Resource estimate for each action item (marked `[ESTIMATED]`)
- [ ] Risk of deferral quantified per item: regulatory (EU type approval delay), safety (ASIL impact), customer (deployment block)
- [ ] CAN-FD unfiltered forwarding flagged as safety/security co-dependency requiring HARA cross-reference

## Raw Trace Log
