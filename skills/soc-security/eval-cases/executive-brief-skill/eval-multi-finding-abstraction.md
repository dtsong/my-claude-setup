# Eval Case: Abstract 10+ Technical Findings into 4-Layer Executive Brief

## Metadata
- **Case ID:** EB-003
- **Tier:** 2 (medium)
- **Skill Route:** executive-brief-skill
- **Estimated Complexity:** medium

## Input
```json
{
  "user_prompt": "Generate a CISO-level executive brief consolidating these 12 findings from our data center GPU accelerator SoC security assessment:\n\nCRITICAL:\n1. TF-2026-201: TDISP state machine bypass — DMA to host memory without IDE encryption (GROUNDED, [LA])\n2. TF-2026-202: SPDM authentication spoofing via weak HMAC truncation (GROUNDED, [TV])\n\nHIGH:\n3. TF-2026-203: CXL.mem isolation failure — cross-tenant memory access through shared HDM decoder (INFERRED, [LA])\n4. TF-2026-204: GPU firmware update lacks anti-rollback — enables downgrade to vulnerable version (GROUNDED, [HV])\n5. TF-2026-205: PCIe BAR remapping allows MMIO access to security-critical registers (INFERRED, [LA])\n6. TF-2026-206: TEE attestation key extractable via debug mailbox left enabled (GROUNDED, [TV])\n\nMEDIUM:\n7. TF-2026-207: Insufficient isolation between GPU compute contexts (INFERRED, [LA])\n8. TF-2026-208: SPDM session key not rotated during long-lived connections (GROUNDED, [LA])\n9. TF-2026-209: CXL Type-2 device memory not included in host integrity measurement (INFERRED, [LA])\n10. TF-2026-210: Thermal throttling timing side-channel leaks workload characteristics (SPECULATIVE, [LA])\n\nLOW:\n11. TF-2026-211: Firmware version string disclosure in unauthenticated SPDM GET_VERSION (GROUNDED, [HV])\n12. TF-2026-212: Non-security-critical logging buffer overflow causes denial of service (INFERRED, [LA])\n\nTechnology domains: tdisp-cxl, confidential-ai\nSoC family: data-center\nAudience: ciso\nOutput format: brief",
  "context": "12 upstream ThreatFinding entities spanning 4 severity levels, mixed confidence tiers, and mixed verification statuses. CISO audience requires more technical depth than board but still needs business risk framing. No prior brief. No ComplianceResult entities. Engineer wants findings consolidated into thematic groups rather than listed individually."
}
```

## Expected Output
A CISO-level executive brief with:
- BLUF summarizing overall posture (likely Red/Amber given 2 CRITICAL)
- Findings consolidated into thematic groups (e.g., "Protocol Security," "Memory Isolation," "Firmware Integrity," "Side-Channel")
- 4-layer abstraction applied per finding, with CISO-appropriate depth at Layers 1-2
- Risk summary table with all 12 findings
- SPECULATIVE finding (TF-210) clearly flagged
- Confidence and verification summaries

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output follows ExecutiveBrief template with DocumentEnvelope frontmatter
- [ ] BLUF present with posture assessment reflecting 2 CRITICAL findings
- [ ] All 12 findings represented in the risk summary table with correct severities
- [ ] Severities preserved from upstream — none changed for audience
- [ ] Verification badges correctly mapped for all 12 findings
- [ ] SPECULATIVE finding (TF-2026-210) has prominent caveat
- [ ] Caveat block and confidence summary are present

### Should Pass (partial credit)
- [ ] Findings grouped thematically rather than just listed by severity (e.g., TDISP/SPDM protocol issues grouped together)
- [ ] CISO-appropriate depth — more technical detail than board level but still abstracted from raw HW specifics
- [ ] Layer 3 action items include priority ordering based on severity and exploitability
- [ ] Traceability appendix maps all 12 brief findings to upstream TF-IDs
- [ ] Confidence summary: 7 GROUNDED, 4 INFERRED, 1 SPECULATIVE
- [ ] Verification summary: 2 [TV], 2 [HV], 8 [LA]

### Bonus
- [ ] Thematic grouping identifies systemic risk pattern in TDISP/CXL protocol stack
- [ ] CISO-specific recommended actions include resource allocation and timeline priorities
- [ ] Attack surface checklist marks bus access control, key management, and firmware update as ANALYZED
- [ ] Cost estimate for top-priority remediations marked `[ESTIMATED]`

## Raw Trace Log
