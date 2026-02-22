# Executive Brief Review Checklist

## Purpose

Checklist for reviewing the accuracy and appropriateness of executive briefs produced by the executive-brief-skill. Ensures that technical findings are correctly translated to business-risk language without distortion, and that the brief is calibrated for its target audience.

---

## Verification Tier Reference

- **Tier 1 (mechanical):** SVA assertions for access control, FSM, register locks — HIGH confidence
- **Tier 2 (protocol):** Natural-language property descriptions for DICE, CXL, protocol — needs review
- **Tier 3 (information flow):** Spec-only descriptions, no SVA — side-channel, info flow

---

## Audience Calibration

- [ ] Target audience identified (Board / CISO / Program)
- [ ] Vocabulary appropriate for audience level (no unexplained acronyms for Board; technical depth for Program)
- [ ] BLUF (Bottom Line Up Front) present in first paragraph
- [ ] Abstraction level matches audience (see cross-cutting/executive-communication.md):
  - Board: Business risk and strategic action only
  - CISO: Security impact and risk posture
  - Program: Technical findings with remediation detail

## Content Accuracy

### Finding Traceability
- [ ] Every finding in the brief traces to a specific threat model finding or compliance gap
- [ ] No findings fabricated or exaggerated beyond source material
- [ ] Risk severity (High/Medium/Low) consistent with threat model risk ratings
- [ ] Trend arrows (improving/stable/degrading) supported by evidence

### Technical Accuracy
- [ ] Technical claims accurately simplified (not distorted) for audience
- [ ] Standards referenced correctly (names, versions)
- [ ] Domain terminology used correctly (even if simplified)
- [ ] No conflation of different security properties (e.g., confidentiality vs. integrity)
- [ ] Verification tier correctly mapped to confidence language:
  - Tier 1 findings → "Verified" or "Confirmed"
  - Tier 2 findings → "Assessed" or "Evaluated" (needs expert review)
  - Tier 3 findings → "Identified" or "Flagged" (requires further analysis)

### Risk Assessment
- [ ] Risk ratings justified by impact and likelihood
- [ ] Business impact described in terms relevant to audience (revenue, reputation, compliance, safety)
- [ ] No risk inflation (presenting Low risks as High without justification)
- [ ] No risk minimization (downplaying High risks)
- [ ] Residual risk acknowledged for partially mitigated threats

## Structure and Format

- [ ] BLUF-first structure (recommendation before supporting evidence)
- [ ] Executive summary fits on one page
- [ ] Findings organized by severity (High first)
- [ ] Each finding has: description, impact, recommendation, timeline
- [ ] Action items are specific and assignable (not vague directives)
- [ ] Visual aids (if any) are accurate and not misleading

## Exclusion Check

- [ ] No raw RTL code or SVA assertions in the brief
- [ ] No specification requirement IDs without context
- [ ] No threat catalog IDs without plain-language description
- [ ] No implementation details inappropriate for audience level
- [ ] No speculative findings presented as confirmed

## Compliance Context

- [ ] Relevant compliance obligations mentioned where applicable
- [ ] Compliance gaps framed as business risk (penalties, audit failure, market access)
- [ ] Regulatory deadlines noted where relevant
- [ ] No compliance claims made without supporting evidence

---

## Review Outcome

| Outcome | Criteria |
|---|---|
| **Ready for Distribution** | Audience-appropriate; technically accurate; findings traceable |
| **Needs Revision** | Minor accuracy issues or audience calibration problems |
| **Significant Rework** | Technical inaccuracies, fabricated findings, or severely miscalibrated audience level |
