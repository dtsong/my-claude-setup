# Cross-Family Analysis — Reporting & Edge Cases

## Contents

- [Purpose](#purpose)
- [Cross-Family Reporting](#cross-family-reporting)
  - [Summary Template](#summary-template)
  - [Reuse Report Template](#reuse-report-template)
- [Compliance Regime Overlap Analysis](#compliance-regime-overlap-analysis)
- [Edge Cases](#edge-cases)
  - [Requirement Applies to Family Without the Standard](#requirement-applies-to-family-without-the-standard)
  - [Same RTL Block, Different IP Versions](#same-rtl-block-different-ip-versions)
  - [Evidence Exists for One Family Only](#evidence-exists-for-one-family-only)
  - [Engineer Provides Evidence Mid-Pipeline](#engineer-provides-evidence-mid-pipeline)

## Purpose

Cross-family reporting templates, compliance regime overlap analysis, and edge case guidance.

**Primary consumer:** compliance-pipeline-skill (Stage 3 gap analysis, output assembly)

---

## Cross-Family Reporting

### Summary Template

```markdown
## Cross-Family Compliance Summary: [Standard]

### Families Assessed: [list]
### Assessment Date: [date]

### Overall Coverage by Family

| Family | Total Reqs | Covered | Partial | Gap | Not Assessed | Not Applicable |
|---|---|---|---|---|---|---|
| Compute | [N] | [n] | [n] | [n] | [n] | [n] |
| Automotive | [N] | [n] | [n] | [n] | [n] | [n] |
| Client | [N] | [n] | [n] | [n] | [n] | [n] |
| Data Center | [N] | [n] | [n] | [n] | [n] | [n] |

### Family-Specific Gap Highlights

#### Compute
- [Gap summary -- top 3 critical gaps]

#### Automotive
- [Gap summary -- top 3, including ISO 21434 overlay gaps]

#### Client
- [Gap summary -- top 3]

#### Data Center
- [Gap summary -- top 3, including CXL-specific gaps]

### Cross-Family Findings

1. **Shared gaps:** [Requirements that are gaps across ALL families -- systemic issues]
2. **Family-isolated gaps:** [Gaps in only one family -- targeted remediation]
3. **Reuse opportunities:** [High-reuse items where evidence could accelerate]
4. **Compliance regime conflicts:** [Different standards imposing conflicting requirements]
```

### Reuse Report Template

```markdown
## Reuse Assessment: [Standard]

### High Reuse ([N] requirements)
Same IP, same integration. Evidence from one family applies to all.

| Req ID | Shared IP | Families | Evidence Reference | Notes |
|---|---|---|---|---|

### Medium Reuse ([N] requirements)
Same IP, different integration. RTL evidence shared; integration per family.

| Req ID | Shared IP | Delta | Per-Family Evidence Needed |
|---|---|---|---|

### Low Reuse ([N] requirements)
Different implementation. Independent compliance tracking.

| Req ID | Requirement | Why Low Reuse |
|---|---|---|

### No Reuse -- Family-Specific ([N] requirements)
Apply only to specific families.

| Req ID | Requirement | Family | Standard |
|---|---|---|---|
```

---

## Compliance Regime Overlap Analysis

When multiple standards apply to the same requirement:

```markdown
## Compliance Regime Overlap: [Requirement ID]

| Aspect | TCG DICE v1.2 | FIPS 140-3 | ISO 21434 |
|---|---|---|---|
| Clause | Section 6.1 | Section 7.2 | Clause 9.4 |
| Obligation | CDI derivation integrity | Key management lifecycle | Cybersecurity goal |
| Evidence needed | DICE cert chain | CAVP validation certificate | TARA work product |
| Applicable families | All | Compute, DC, Client | Automotive |
| Conflict? | None | Additional CAVP on crypto | Additional process docs |
```

When conflicts exist, flag prominently:

> "**COMPLIANCE CONFLICT:** TCG DICE v1.2 Section 6.1 permits CBOR certificate encoding, but FIPS 140-3 validation (CAVP) does not yet have a CBOR certificate test vector. For families requiring both, use X.509 encoding or document the CBOR gap with FIPS assessor."

---

## Edge Cases

### Requirement Applies to Family Without the Standard

Example: CXL 3.1 TSP requirements extracted, but automotive has no CXL.
Action: Mark `coverageStatus: not-applicable` with justification.

### Same RTL Block, Different IP Versions

Example: `dice_engine_v2` in compute/DC, `dice_engine_v1` in client.
Action: Separate rows with `[IPV]` delta. V2 evidence does NOT apply to v1. Flag client for independent verification.

### Evidence Exists for One Family Only

Example: SVA passes for compute; automotive has different bus wrapper, no SVA.
Action: Compute `covered` with SVA evidence. Automotive `gap: no-evidence` with delta `[VER]`. Reuse: Medium (RTL shared, bus wrapper verification needed).

### Engineer Provides Evidence Mid-Pipeline

1. Incorporate into appropriate requirement mapping
2. Update evidenceType, evidenceReference, confidenceTier
3. Note: "[Updated: evidence added during Stage 2 for SR-YYYY-NNN]"
4. Re-run gap classification for affected requirements
