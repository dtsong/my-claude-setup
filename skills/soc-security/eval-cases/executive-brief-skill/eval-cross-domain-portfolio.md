# Eval Case: Cross-Domain Portfolio Risk Brief Spanning 3+ SoC Families

## Metadata
- **Case ID:** EB-005
- **Tier:** 3 (complex)
- **Skill Route:** executive-brief-skill
- **Estimated Complexity:** high

## Input
```json
{
  "user_prompt": "Generate a board-level portfolio risk brief spanning our three SoC product lines. This is for the annual security posture review with the board of directors.\n\n**Product Line 1: Data Center DPU (Argon-DC)**\nSoC family: data-center | Domains: tdisp-cxl, confidential-ai\nPrior brief: EB-2025-004 (Q3 2025 — Amber posture)\nFindings since last brief:\n- TF-2026-501: CXL.cache coherence snoop attack — cross-VM data extraction (CRITICAL, GROUNDED, [TV])\n- TF-2026-502: TDISP IDE key rotation failure under load (HIGH, GROUNDED, [LA])\n- CR-2026-601: FIPS 140-3 validation — IN PROGRESS (CAVP submitted, CMVP pending)\n- RESOLVED: TF-2025-301 DMA bypass (fixed in B0 silicon) — was CRITICAL\n\n**Product Line 2: Automotive ADAS (Helios-Auto)**\nSoC family: automotive | Domains: supply-chain, secure-boot-dice\nPrior brief: EB-2025-007 (Q4 2025 — Red posture)\nFindings since last brief:\n- TF-2026-503: V2X certificate revocation list not checked on message receive (HIGH, GROUNDED, [HV])\n- CR-2026-602: ISO 21434 full TARA — COMPLETED (was partial)\n- CR-2026-603: UNECE R155 CSMS audit — SCHEDULED Q2 2026\n- RESOLVED: TF-2025-405 CAN-FD unfiltered forwarding (firmware patch deployed) — was HIGH\n\n**Product Line 3: Client SoC (Vega-Client)**\nSoC family: client | Domains: secure-boot-dice, cheri\nNo prior brief — first assessment\nFindings:\n- TF-2026-504: CHERI capability forgery via uninitialized capability register (CRITICAL, INFERRED, [LA])\n- TF-2026-505: Secure boot bypass via electromagnetic fault injection on signature verify (HIGH, SPECULATIVE, [LA])\n- TF-2026-506: DRAM scrambling key reused across cold reboots (MEDIUM, GROUNDED, [TV])\n- CR-2026-604: PSA Certified Level 2 — GAP (no threat model submitted)\n\nAudience: board\nOutput format: brief\n\nBoard members will want to see: overall portfolio posture, trend from prior assessments, cross-family systemic risks, and resource allocation recommendations.",
  "context": "Complex multi-family portfolio brief. Three SoC families with different maturity levels, mixed prior brief history, resolved and new findings, and different compliance regimes. Board audience expects high-level portfolio view with trend analysis. 10 total findings (threat + compliance) plus 2 resolved items across 3 product lines."
}
```

## Expected Output
A board-level portfolio risk brief with:
- Portfolio-level BLUF with overall posture assessment across all three families
- Per-family posture with trend arrows (improving/worsening/new)
- Cross-family systemic risk identification
- Resolved findings shown as positive trend
- SPECULATIVE and INFERRED findings appropriately caveated
- Resource allocation recommendations across the portfolio

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output follows ExecutiveBrief template with DocumentEnvelope frontmatter listing all three SoC families
- [ ] BLUF provides portfolio-level posture assessment (not just per-family)
- [ ] All three product lines represented with per-family risk summaries
- [ ] Trend analysis present: Argon-DC compared to EB-2025-004, Helios-Auto compared to EB-2025-007, Vega-Client marked as NEW
- [ ] Resolved findings (TF-2025-301, TF-2025-405) shown as positive trend indicators
- [ ] SPECULATIVE finding (TF-2026-505) has prominent caveat and is not presented as confirmed
- [ ] Severities preserved from upstream across all families
- [ ] Caveat block present

### Should Pass (partial credit)
- [ ] Per-family posture trend: Argon-DC stable/worsening (new CRITICAL), Helios-Auto improving (TARA completed, finding resolved), Vega-Client new baseline
- [ ] Cross-family systemic risks identified (e.g., secure boot vulnerabilities appear in both automotive and client)
- [ ] Board-appropriate vocabulary throughout — no technical jargon in BLUF or risk summary
- [ ] Resource allocation recommendation addresses staffing across three product lines
- [ ] Compliance status per family summarized: FIPS in progress (DC), ISO 21434 progressing (Auto), PSA gap (Client)
- [ ] Confidence summary aggregated across all families
- [ ] Verification summary aggregated: [TV], [HV], [LA] counts across portfolio

### Bonus
- [ ] Portfolio heat map or matrix showing severity distribution across families and domains
- [ ] Strategic recommendation on shared security IP reuse across families (e.g., secure boot hardening benefits both automotive and client)
- [ ] Regulatory timeline overlay: FIPS CMVP queue, UNECE R155 Q2 audit, PSA certification path
- [ ] Year-over-year trend narrative for families with prior briefs
- [ ] CHERI capability forgery flagged as emerging technology risk requiring specialized expertise

## Raw Trace Log
