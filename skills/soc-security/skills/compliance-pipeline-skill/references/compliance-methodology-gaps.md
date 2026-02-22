# Compliance Methodology — Gap Classification and Evidence Mapping

## Table of Contents

- [Stage 2: Evidence Mapping](#stage-2-evidence-mapping--detailed-rules)
- [Evidence Strength Hierarchy](#evidence-strength-hierarchy)
- [Evidence-to-Confidence Mapping](#evidence-to-confidence-mapping)
- [Confidence Propagation Rules](#confidence-propagation-rules)
- [Traceability Chain Requirements](#traceability-chain-requirements)
- [Stage 3: Gap Classification](#stage-3-gap-classification--detailed-taxonomy)
- [Gap Categories Decision Tree](#gap-categories-with-decision-tree)
- [Gap Severity Assessment](#gap-severity-assessment)
- [Remediation Plan Template](#remediation-plan-template)
- [Quality Checks](#quality-checks)

---

## Stage 2: Evidence Mapping — Detailed Rules

### Evidence Strength Hierarchy

Evidence is ranked by strength for compliance mapping:

| Rank | Evidence Type | Strength | Example |
|---|---|---|---|
| 1 | `tool-verified` results | Highest | Formal proof pass, SVA assertion pass over full coverage |
| 2 | `sva-result` | High | SVA assertion pass (may have coverage limitations) |
| 3 | `simulation-log` | Medium-High | Simulation showing correct behavior under test scenarios |
| 4 | `test-report` | Medium | System-level test results, penetration test results |
| 5 | `review-record` | Medium-Low | Human expert review with documented checklist |
| 6 | `design-document` | Low | Architecture description that claims to meet the requirement |
| 7 | `none` | None | No evidence available |

### Evidence-to-Confidence Mapping

The evidence type directly constrains the confidence tier:

| Evidence Type | Maximum Confidence |
|---|---|
| Tool-verified or SVA with full coverage | GROUNDED |
| SVA with partial coverage, simulation | GROUNDED (for covered subset) / INFERRED (for uncovered) |
| Test report with clear pass criteria | GROUNDED (if criteria met) / INFERRED (if criteria unclear) |
| Review record | INFERRED |
| Design document | INFERRED |
| None | ABSENT |

### Confidence Propagation Rules

When upstream entities feed into evidence mapping:

```
ComplianceResult.confidenceTier <= min(
  evidence_confidence,
  upstream_ThreatFinding.confidenceTier,
  upstream_VerificationItem.confidenceTier,
  requirement_extraction_confidence
)
```

The compliance confidence cannot exceed the weakest link in the chain. A GROUNDED compliance result requires GROUNDED extraction, GROUNDED threat finding (if linked), and GROUNDED verification item (if used as evidence).

### Traceability Chain Requirements

Every ComplianceResult must have a complete traceability chain:

```
Spec Section → SecurityRequirement → [ThreatFinding] → [VerificationItem] → ComplianceResult
```

Chain validation rules:
- `ComplianceResult.requirementId` must reference a valid SecurityRequirement
- `ComplianceResult.traceability.requirements` must be non-empty
- `ComplianceResult.traceability.threats` is populated if upstream ThreatFindings exist
- `ComplianceResult.traceability.verificationItems` is populated if upstream VerificationItems exist
- A ComplianceResult with `evidenceReference` must reference a real artifact (document, test log, assertion ID)

If a chain link is missing, flag it:
- Missing requirement reference: ERROR (cannot produce ComplianceResult without requirement)
- Missing threat link: WARNING (reduced traceability but not blocking)
- Missing verification link: WARNING (evidence mapping may be weaker)

---

## Stage 3: Gap Classification — Detailed Taxonomy

### Gap Categories with Decision Tree

```
Is the requirement in scope for this assessment?
  NO → coverageStatus: not-applicable (with justification)
  YES → Was it explicitly excluded from scope?
    YES → gap: scope-exclusion
    NO  → Was evidence searched for?
      NO → confidenceTier: ABSENT, gap: not-analyzed
      YES → Was any evidence found?
        NO → gap: no-evidence
        YES → Does the evidence show the requirement is met?
          FULLY → coverageStatus: covered
          PARTIALLY → gap: partial
          NO → gap: not-met
```

### Gap Severity Assessment

| Gap Type | Severity Factors | Typical Severity |
|---|---|---|
| `not-met` on mandatory requirement | Normative "shall"; critical security property | Critical or High |
| `not-met` on recommended requirement | Normative "should"; important but not mandatory | Medium |
| `no-evidence` on mandatory requirement | Possibly met, possibly not; creates audit risk | High (uncertainty risk) |
| `no-evidence` on recommended requirement | Lower audit risk but still an open item | Medium |
| `partial` on mandatory requirement | Partially met; gap size determines severity | Medium to High |
| `scope-exclusion` | Acknowledged boundary | Low (informational) |

### Remediation Plan Template

For each gap, produce a remediation plan with these elements:

```
Remediation for [SR-ID]: [Title]

1. Action: [What needs to be done]
   Owner: [Suggested owner — design, verification, firmware, compliance team]
   Effort: [Order-of-magnitude: hours, days, weeks, or "unknown"]

2. Evidence needed: [What evidence would demonstrate compliance]
   Type: [sva-result, simulation-log, review-record, design-document, test-report]

3. Dependencies: [Other requirements or remediation actions that must complete first]

4. Verification approach: [How to confirm the gap is closed]
   Tier: [1/2/3 from verification-scaffold-skill framework]
```

---

## Quality Checks

### Stage 1 Quality Checks (Requirement Extraction)

- [ ] Every requirement has a unique, sequential ID
- [ ] Every requirement has a spec section reference (or `[SECTION REFERENCE NEEDED]`)
- [ ] Every requirement maps to exactly one security property
- [ ] Every requirement maps to exactly one implementation layer
- [ ] Every requirement has a confidence tier with rationale
- [ ] Every `[FROM TRAINING]` requirement is explicitly flagged
- [ ] No duplicate requirements (same obligation extracted twice)
- [ ] Normative language correctly interpreted (shall vs. should vs. may)

### Stage 2 Quality Checks (Compliance Tracking)

- [ ] Every requirement has been mapped (even if to `none`)
- [ ] Evidence types are correctly classified
- [ ] Confidence tiers respect propagation rules (no inflation)
- [ ] Traceability chains are complete (no broken links)
- [ ] Cross-family matrices have per-family rows (not combined)
- [ ] Delta annotations present for requirements with per-family variation

### Stage 3 Quality Checks (Gap Analysis)

- [ ] Every gap has a classification (no-evidence, not-met, partial, scope-exclusion, not-applicable)
- [ ] `no-evidence` gaps are not presented as `not-met` (critical distinction)
- [ ] Every `partial` or `not-met` gap has a remediation plan
- [ ] SPECULATIVE claims have been through the review gate
- [ ] Confidence summary is accurate (counts match actual entity tiers)
- [ ] Caveat block is present and accurate
- [ ] Attack surface checklist is present with all areas marked
- [ ] Coverage boundary explicitly states what is and is not covered

### End-to-End Quality Checks

- [ ] DocumentEnvelope frontmatter is complete and well-formed
- [ ] All entity IDs are unique across the assessment
- [ ] All cross-references between entities resolve to valid IDs
- [ ] No compliance claims without evidence (covered status requires evidence)
- [ ] No SPECULATIVE claims in output without acknowledgment record
- [ ] Findings ledger has been checked and updated
