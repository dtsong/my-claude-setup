# Executive Templates — Executive Brief Skill

## Purpose

Ready-to-use templates for executive brief output formats. Includes the BLUF template, risk summary table template, and audience-specific section templates for board, CISO, and program-level audiences.

**Primary consumer:** executive-brief-skill (SKILL.md references this file for output formatting)

---

## BLUF (Bottom Line Up Front) Templates

### Board-Level BLUF

```
The [SoC family] security assessment identified [N] findings across [domains].
[Highest severity finding in one sentence — business risk language].

Recommended action: [Primary action in business terms]. Estimated investment:
[cost range]. Timeline: [milestone]. Risk of inaction: [consequence in
business terms].

Assessment reliability: [N]% of findings verified by domain experts.
[N] findings require additional verification before investment decisions.
```

**Constraints:**
- Maximum 5 sentences
- No technical terms (no acronyms except well-known: AI, IoT)
- First sentence: posture summary
- Second sentence: most critical risk
- Third sentence: recommended action with cost
- Fourth sentence: reliability disclaimer

### CISO-Level BLUF

```
The [SoC family] security assessment identified [N] findings: [N] Critical,
[N] High, [N] Medium. The most significant finding is [Layer 1 security
impact statement], affecting [scope]. [N] compliance gaps were identified
against [standards].

Recommended action: [Primary action with timeline and cost]. Secondary:
[Additional actions]. [N] findings correlate with compliance gaps, requiring
coordinated remediation.

Assessment confidence: [N] findings GROUNDED, [N] INFERRED, [N] SPECULATIVE.
[N] of [total] findings human-verified. Recommend engineer review of
INFERRED/SPECULATIVE items before next reporting cycle.
```

**Constraints:**
- Maximum 8 sentences
- Security terminology permitted (threat, vulnerability, compliance gap)
- No hardware-specific terms (no TLP, FSM, CDI in BLUF)
- Include confidence breakdown
- Include compliance correlation

### Program-Level BLUF

```
Security assessment of [SoC family] [component/subsystem]: [N] findings
([N] Critical, [N] High, [N] Medium, [N] Low). [N] compliance gaps against
[standards].

Critical path: [Finding #1] — [TF-ID]: [Layer 0 technical summary].
Impact: [Layer 1]. Recommended fix: [specific engineering action] targeting
[milestone]. Estimated effort: [engineer-weeks].

Additional findings requiring attention:
- [Finding #2]: [severity] — [brief description] — [target milestone]
- [Finding #3]: [severity] — [brief description] — [target milestone]

Verification status: [N] tool-verified, [N] human-verified, [N] LLM-assessed.
Upstream documents: [TM-ID], [CM-ID], [VC-ID].
```

**Constraints:**
- No sentence limit (completeness over brevity)
- Full technical terminology permitted
- Include entity IDs for traceability
- Include upstream document references
- Actionable engineering tasks with effort estimates

---

## Risk Summary Table Templates

### Standard Risk Summary Table

```markdown
| # | Finding | Severity | Trend | Verification | Source | Action Required | Target |
|---|---------|----------|-------|--------------|--------|-----------------|--------|
| 1 | {Layer 2 statement} | Critical | {arrow} | [LA] | {TF/CR-ID} | {Layer 3 action} | {date} |
| 2 | {Layer 2 statement} | High | {arrow} | [HV] | {TF/CR-ID} | {Layer 3 action} | {date} |
| 3 | {Layer 2 statement} | Medium | {arrow} | [TV] | {TF/CR-ID} | {Layer 3 action} | {date} |
```

### Severity Definitions (Include in Every Brief)

```markdown
**Severity definitions:**
- **Critical:** Active exploitation path identified or compliance blocker for
  certification. Requires immediate remediation before next milestone.
- **High:** Feasible attack path or significant compliance gap. Remediation
  required within current program phase.
- **Medium:** Attack path requires significant attacker capability or has
  limited blast radius. Schedule remediation in next available window.
- **Low:** Theoretical risk with no demonstrated attack path or informational
  finding. Track in risk register; remediate opportunistically.
```

### Trend Indicators (Include in Every Brief)

```markdown
**Trend indicators:**
- ^ Worsening — Risk increased since last assessment (new evidence,
  expanded scope, or failed remediation)
- v Improving — Remediation progress, new controls, or reduced exposure
- = Stable — No material change since last assessment
- * New — First identified in this assessment cycle
```

### Verification Badges (Include in Every Brief)

```markdown
**Verification status:**
- [HV] Human-verified — Finding reviewed and confirmed by domain expert
- [TV] Tool-verified — Finding validated by automated tooling (SVA pass,
  formal proof, simulation)
- [LA] LLM-assessed — Preliminary finding from automated analysis;
  requires human verification before use in decisions
```

---

## Audience-Specific Section Templates

### Board-Level: Detailed Finding Section

```markdown
### {Finding Title — Business Language}

**Risk Level:** {Critical / High / Medium / Low}
**Status:** {New / Open / In Remediation / Resolved}

**What this means:** {Layer 2 — 2-3 sentences in business language. Name
specific business assets, customer impact, and regulatory exposure.}

**What we recommend:** {Layer 3 — Investment language. Cost, timeline,
consequence of deferral.}

**Confidence in this finding:** {One sentence — "This finding is based on
[verified analysis / preliminary assessment / theoretical analysis]
and [has / has not] been confirmed by a domain expert."}
```

### CISO-Level: Detailed Finding Section

```markdown
### Finding {N}: {Layer 1 Title — Security Language}

**Severity:** {Critical / High / Medium / Low}
**Confidence:** {GROUNDED / INFERRED / SPECULATIVE}
**Verification:** {[HV] / [TV] / [LA]}
**Affected Domain:** {technology domain}
**Affected Families:** {SoC families}
**Source:** {TF-ID / CR-ID}

**Security Impact:** {Layer 1 — Security-aware language. Attack vector,
attacker profile, security property violated.}

**Business Risk:** {Layer 2 — Business impact, regulatory exposure,
customer impact.}

**Compliance Correlation:** {If this finding correlates with a compliance
gap, reference the ComplianceResult ID and standard clause.}

**Recommended Action:** {Layer 3 — Security program language. Remediate /
accept with compensating control / transfer risk. Timeline and cost.}

**Residual Risk if Deferred:** {What happens if action is not taken by
the recommended timeline.}
```

### Program-Level: Detailed Finding Section

```markdown
### Finding {N}: {Layer 0 Title — Technical Language}

**Severity:** {Critical / High / Medium / Low}
**Confidence:** {GROUNDED / INFERRED / SPECULATIVE}
**Verification:** {[HV] / [TV] / [LA]}
**Entity ID:** {TF-ID or CR-ID}
**Domain:** {technology domain}
**Families:** {SoC families}
**Related Entities:** TF: {list}, SR: {list}, VI: {list}, CR: {list}

**Technical Description (Layer 0):**
{Full technical finding from upstream entity. Include specific component
names, protocol states, signal names where available.}

**Security Impact (Layer 1):**
{Impact statement with attack vector and prerequisite.}

**Business Risk (Layer 2):**
{Business framing — for program-level, this is brief context, not the
primary focus.}

**Remediation Plan:**
- **Action:** {Specific engineering action — module, fix type, verification approach}
- **Owner:** {Suggested team or individual}
- **Effort:** {Engineer-weeks estimate}
- **Target:** {Milestone or date}
- **Verification:** {How to confirm fix — SVA tier, test approach}
- **Dependencies:** {Other findings or tasks that must complete first}

**Compliance Impact:**
{If fix addresses a compliance gap, reference CR-ID and standard clause.
Note: fixing this finding closes compliance gap CR-YYYY-NNN against
[standard] [clause].}
```

---

## Compliance Status Summary Templates

### Board-Level Compliance Summary

```markdown
## Regulatory Status

| Standard | Status | Impact |
|----------|--------|--------|
| {FIPS 140-3} | {On track / At risk / Gap identified} | {Required for [customer/market]} |
| {ISO 21434} | {On track / At risk / Gap identified} | {Required for [customer/market]} |

{1-2 sentences on most significant compliance finding in business terms.}
```

### CISO-Level Compliance Summary

```markdown
## Compliance Posture

| Standard | Total Reqs | Covered | Partial | Gap | Not Assessed | Confidence |
|----------|-----------|---------|---------|-----|--------------|------------|
| {standard} | {N} | {n} ({%}) | {n} | {n} | {n} | {avg tier} |

### Critical Compliance Gaps

| Gap ID | Standard | Clause | Description | Business Impact | Remediation |
|--------|----------|--------|-------------|-----------------|-------------|
| {CR-ID} | {std} | {clause} | {gap desc} | {impact} | {action} |

### Compliance Trend

{If prior assessment exists: improved/worsened/stable with specific metrics.}
{If no prior: "Baseline assessment — trend data will be available in next cycle."}
```

### Program-Level Compliance Summary

```markdown
## Compliance Status Detail

| CR-ID | Req ID | Standard | Clause | Status | Evidence | Gap | Remediation | Owner | Target |
|-------|--------|----------|--------|--------|----------|-----|-------------|-------|--------|
| {id} | {SR-id} | {std} | {clause} | {status} | {type} | {desc} | {action} | {TBD} | {date} |

### Cross-Family Compliance Comparison

| Requirement | Compute | Automotive | Client | Data Center |
|-------------|---------|------------|--------|-------------|
| {SR-ID}: {title} | {status} | {status} | {status} | {status} |
```

---

## Document Envelope Template

Every executive brief uses this DocumentEnvelope frontmatter:

```yaml
---
type: exec-brief
id: EB-{YYYY}-{NNN}
title: "{SoC Family} Security Posture Brief — {YYYY-MM-DD}"
created: {YYYY-MM-DD}
updated: {YYYY-MM-DD}
soc-family: [{families}]
technology-domain: [{domains}]
standards: [{standard versions referenced in findings}]
related-documents: [{upstream TM-IDs, CM-IDs, VC-IDs}]
status: draft
confidence-summary: {grounded: N, inferred: N, speculative: N, absent: N}
caveats: |
  LLM-generated executive brief. All findings marked [LA] require human
  verification before use in executive decision-making or investment
  planning. Risk ratings and cost estimates are preliminary. This brief
  does NOT constitute a formal security assessment, audit report, or
  certification opinion.
---
```

---

## Formatting Conventions

### Severity Color Coding (for rendered output)

When the output format supports color or styling:
- **Critical:** Bold, uppercase, or red highlight
- **High:** Bold or orange highlight
- **Medium:** Standard weight or yellow highlight
- **Low:** Standard weight, no highlight

In plain Markdown (default), use bold for Critical and High:
```
| 1 | **Customer data exposure** | **Critical** | * | [LA] | Fix in Q2 |
| 2 | **Attestation replay risk** | **High** | * | [LA] | FW update |
| 3 | Key rotation timing gap | Medium | * | [LA] | Track for Q3 |
```

### Number Formatting

- Percentages: One decimal place maximum ("78.5% coverage")
- Costs: Range format ("2-3 engineer-weeks", "$50K-$100K")
- Counts: Integer only ("12 findings", "5 GROUNDED")
- Dates: ISO-8601 (YYYY-MM-DD)

### Acronym Handling

- **Board-level:** Expand all acronyms on first use. Avoid acronyms in BLUF entirely.
- **CISO-level:** Expand security acronyms on first use. Hardware acronyms in appendix only.
- **Program-level:** No expansion needed for domain-standard acronyms.

---

*This template reference supports the executive-brief-skill and should be read in conjunction with SKILL.md and the executive communication guide in cross-cutting references.*
