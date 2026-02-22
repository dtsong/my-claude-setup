# Output Templates — Worked Examples

## Table of Contents

- [Coverage Boundary Template](#4-coverage-boundary-template)
- [Confidence Summary Template](#5-confidence-summary-template)
- [Caveat Block Template](#6-caveat-block-template)
- [Findings Ledger Entry Template](#7-findings-ledger-entry-template)
- [Attack Tree Output Template](#8-attack-tree-output-template)
- [Complete Threat Model Output Structure](#9-complete-threat-model-output-structure)

---

## 4. Coverage Boundary Template

```markdown
## Coverage Boundary

**This analysis covers:**
- [Component/subsystem name] as described in user-provided documentation
- [Technology domain(s)] threat patterns from shared-references
- [Standard(s)] requirements from sections [list]
- [Specific interfaces] analyzed per the interface map
- [Specific attack surfaces] as marked ANALYZED in the checklist

**This analysis does NOT cover:**
- [Specific component/subsystem] — [reason: out of scope / separate analysis / not provided]
- [Specific technology domain] — [reason]
- [Specific standard sections] — [reason]
- [Specific attack surface] — [reason, matching the checklist NOT ANALYZED entries]

**Interfaces not examined:**
- [Interface name] — [reason it was not examined]
- [Interface name] — [reason]

**Specifications not consulted:**
- [Spec name and version] — [reason: not relevant / not available / not in scope]

**Assumptions:**
- [List any assumptions made about the component or its environment]
- [List any assumptions about the adversary model]
```

### Coverage Boundary Rules

1. **Both "covers" and "does NOT cover" sections are mandatory.**
2. **Coverage must match the attack surface checklist.** Every NOT ANALYZED surface appears in "does NOT cover."
3. **Assumptions must be explicit.**
4. **Specificity over generality.** Cite why each surface was excluded.

---

## 5. Confidence Summary Template

```markdown
## Confidence Summary

| Tier | Count | Percentage | Description |
|------|-------|-----------|-------------|
| GROUNDED | [N] | [%] | Directly supported by cited spec section or user evidence |
| INFERRED | [N] | [%] | Logically derived, not explicitly stated |
| SPECULATIVE | [N] | [%] | Plausible but not grounded in provided context |
| ABSENT | [N] | [%] | Known attack category, no analysis performed |
| **Total** | **[N]** | **100%** | |

### Confidence Distribution Assessment

[2-3 sentences assessing the overall confidence quality of this analysis.
Address:
- Which domains have the strongest grounding?
- Which domains rely most heavily on training knowledge?
- What would improve confidence for the SPECULATIVE and INFERRED findings?
- What information is needed to convert ABSENT findings to ANALYZED?]

### Per-Domain Confidence Breakdown

| Domain | GROUNDED | INFERRED | SPECULATIVE | ABSENT |
|--------|----------|----------|-------------|--------|
| [Domain 1] | [N] | [N] | [N] | [N] |
| [Domain 2] | [N] | [N] | [N] | [N] |
```

### Confidence Summary Rules

1. **Counts must be exact.** Sum of all tiers must equal total findings count.
2. **Assessment must be honest.** If 80% of findings are SPECULATIVE, say so clearly.
3. **Per-domain breakdown is required** when multiple domains are in scope.
4. **Actionable improvement guidance** — what would the engineer need to provide to improve confidence?

---

## 6. Caveat Block Template

This block appears at the top of every threat model output.

```markdown
## Caveat

> **This threat model is an LLM-generated draft** produced by the threat-model-skill
> as part of the SoC Security Skills Suite. It is a structured starting point for
> expert review, not a finished security assessment.

**Scope of analysis:**
- Component: [name]
- Domain(s): [list]
- Framework(s): [STRIDE / Attack Tree / Standards-Derived / All]
- Specification(s): [list with versions]

**What was NOT analyzed:**
- [Specific item 1 — with reason]
- [Specific item 2 — with reason]

**Grounding quality:**
- [N]% of findings are GROUNDED in spec sections or user-provided evidence
- [N]% of findings are INFERRED from requirements and embedded references
- [N]% of findings are SPECULATIVE, based on training knowledge [FROM TRAINING]
- [N]% of attack surfaces are marked ABSENT (not analyzed)

**How to use this document:**
1. Review GROUNDED findings first — these have the strongest evidence basis
2. Validate INFERRED findings — check that the reasoning chain is sound for your context
3. Treat SPECULATIVE findings as hypotheses — confirm or discard based on your expertise
4. Address ABSENT findings — provide missing information or accept the coverage gap
5. Do NOT use SPECULATIVE or ABSENT findings in compliance or executive reporting without human verification
```

---

## 7. Findings Ledger Entry Template

```markdown
## [FINDING-YYYY-NNN] — [Brief description, max 60 characters]
- **Date:** [YYYY-MM-DD]
- **Source Document:** [TM-YYYY-NNN]
- **SoC Family:** [family or "all"]
- **Technology Domain:** [domain]
- **Standards:** [list with versions and section numbers]
- **Finding:** [1-2 sentence summary of the threat]
- **Severity:** [CRITICAL / HIGH / MEDIUM / LOW]
- **Confidence:** [GROUNDED / INFERRED / SPECULATIVE]
- **Resolution:** [pending / mitigated / accepted / deferred]
- **Reusability:** [High / Medium / Low] — [1 sentence rationale]
- **Related:** [comma-separated list of related finding IDs, TM IDs, or FINDING IDs]
```

### Ledger Entry Rules

1. **Only significant findings enter the ledger** — CRITICAL or HIGH severity, or novel threats not previously documented
2. **Resolution starts as "pending"** — updated by the engineer as the finding is addressed
3. **Reusability assessment is required** — enables cross-family reuse in future analyses
4. **Related field links to all relevant artifacts** — enables traceability

---

## 8. Attack Tree Output Template

```markdown
## Attack Tree: [Root Goal]

**Attacker Profile:** [brief description]
**Technology Domain:** [domain]
**Grounding:** [user-provided / embedded-reference / training-knowledge]
**Overall Confidence:** [tier]

### Tree Structure

```
[Root Goal] (OR)
├── [Sub-goal 1] (AND)
│   ├── [Leaf 1.1] — D:[L/M/H] A:[access] Det:[level]
│   │   Grounding: [source]
│   └── [Leaf 1.2] — D:[L/M/H] A:[access] Det:[level]
│       Grounding: [source]
├── [Sub-goal 2] (OR)
│   ├── [Leaf 2.1] — D:[L/M/H] A:[access] Det:[level]
│   │   Grounding: [source]
│   └── [Leaf 2.2] — D:[L/M/H] A:[access] Det:[level]
│       Grounding: [source]
└── [Sub-goal 3] (AND)
    ├── [Leaf 3.1] — D:[L/M/H] A:[access] Det:[level]
    │   Grounding: [source]
    └── [Leaf 3.2] — D:[L/M/H] A:[access] Det:[level]
        Grounding: [source]
```

### Path Analysis

| Path | Steps | Min Difficulty | Access Required | Overall Feasibility |
|------|-------|---------------|-----------------|---------------------|
| Path A (via Sub-goal 1) | [N] | [H/M/L] | [access] | [High / Medium / Low] |
| Path B (via Sub-goal 2) | [N] | [H/M/L] | [access] | [High / Medium / Low] |
| Path C (via Sub-goal 3) | [N] | [H/M/L] | [access] | [High / Medium / Low] |

### Minimal Cut Sets

| # | Mitigations | Paths Blocked | Cost/Complexity |
|---|-------------|---------------|-----------------|
| 1 | [Leaf X mitigation], [Leaf Y mitigation] | Paths A, B | [estimate] |
| 2 | [Leaf Z mitigation] | Path C | [estimate] |

### Recommendations

[1-2 sentences: Which cut set is recommended and why. Consider
cost, implementation complexity, and coverage breadth.]
```

---

## 9. Complete Threat Model Output Structure

This shows the full structure of a complete threat model output, combining all templates:

```markdown
---
[DocumentEnvelope YAML frontmatter]
---

# [Component] Threat Model — [Domain(s)]

## Caveat
[Caveat block — template 6]

## Attack Surface Coverage
[Attack surface checklist — template 3]

## Coverage Boundary
[Coverage boundary — template 4]

## Component Description
[User-provided component description, reformatted for clarity]

### Interface Map
[Interface enumeration from Phase 2]

## Threat Findings

### STRIDE Analysis Results
[STRIDE findings, grouped by category, each as ThreatFinding entity — template 1]

### Standards-Derived Findings
[Standards-derived findings, grouped by standard, each as ThreatFinding entity]

### Attack Trees
[Attack tree diagrams and analysis — template 8]

## Cross-Framework Synthesis
[De-duplication results, gap analysis, coverage mapping]

## Confidence Summary
[Confidence summary — template 5]

## Cross-Family Reuse Summary
[Summary of reusable vs. family-specific findings]

## Findings Ledger Entries (Proposed)
[Proposed ledger entries for significant findings — template 7]

## Downstream Handoff Notes
[Notes for verification-scaffold-skill and compliance-pipeline-skill]
```
