---
name: "regulatory-strategy"
department: "regulator"
description: "Determine optimal regulatory pathway and submission strategy for a medical device"
version: 1
triggers:
  - "regulatory"
  - "pathway"
  - "510(k)"
  - "PMA"
  - "De Novo"
  - "classification"
  - "predicate"
  - "submission"
---

# Regulatory Strategy

## Purpose

Determine the optimal FDA regulatory pathway and develop a submission strategy for a medical device, including device classification, predicate device analysis, and regulatory timeline planning.

## Scope Constraints

- Focuses on FDA pathways (510(k), De Novo, PMA, exempt). For international pathways (CE/MDR, PMDA), flag as handoff.
- Does not produce final submission documents — produces the strategic plan that guides submission authoring.
- Does not replace a regulatory affairs professional's judgment on novel classification questions — recommends pre-submission meeting when classification is ambiguous.

## Inputs

- Device description: intended use, indications for use, technology description
- Target patient population and clinical setting
- Known similar devices on the market (if any)
- Design phase: concept, detailed design, verification, validation, transfer
- Target markets: US, EU, Japan, other

## Input Sanitization

- If intended use is vague, ask for clarification before classifying — intended use drives classification.
- If no predicate candidates are provided, search FDA 510(k) database by product code and intended use.
- If device class is stated without justification, verify against 21 CFR product code classification.

## Procedure

1. **Classify the device.** Identify the FDA product code by matching intended use and technology to the classification database (21 CFR 862-892). Determine device class (I, II, III). State the regulation number and product code.

2. **Identify predicate devices.** For 510(k) pathway: search for legally marketed predicate devices with the same intended use and similar technological characteristics. Document each candidate's 510(k) number, clearance date, applicant, and key specifications.

3. **Assess technological characteristics.** Compare the subject device to each predicate candidate:
   - Same intended use? (Required for substantial equivalence)
   - Same technological characteristics? (If yes, SE is straightforward)
   - Different technological characteristics? (If yes, do differences raise new questions of safety or effectiveness?)
   - Document each difference and its regulatory significance.

4. **Evaluate pathway options.** Based on classification and predicate analysis:
   - **510(k):** Strong predicate exists, same intended use, technological differences do not raise new safety/effectiveness questions.
   - **De Novo:** No predicate exists, but device is low-to-moderate risk. New product code will be created.
   - **PMA:** Class III device, or no predicate and high risk. Clinical data likely required.
   - **Exempt:** Class I or certain Class II devices exempt from 510(k). Verify exemption limitations.
   - Recommend the optimal pathway with rationale.

5. **Identify required standards and special controls.** List recognized consensus standards applicable to the device (IEC 60601-1, IEC 62304, ISO 14971, etc.). For Class II devices, identify special controls from the classification regulation or De Novo decision summary.

6. **Draft regulatory timeline.** Map key milestones: pre-submission meeting, standards testing, biocompatibility testing (if applicable), software documentation, submission authoring, FDA review period, and potential additional information requests. Include dependencies on design verification and validation completion.

### Progress Checklist

- [ ] Product code and device class determined
- [ ] Predicate devices identified and documented
- [ ] Technological comparison completed
- [ ] Pathway recommendation made with rationale
- [ ] Applicable standards and special controls listed
- [ ] Regulatory timeline drafted with dependencies

### Compaction Resilience

If context is compacted mid-procedure, the output tables preserve state. Resume from the last incomplete checklist item. The Device Classification Table and Predicate Comparison Matrix are self-contained — they do not require earlier context to interpret.

## Output Format

```markdown
## Regulatory Strategy — [Device Name]

### Device Classification
| Field | Value |
|-------|-------|
| Intended Use | [Statement] |
| Product Code | [Code] |
| Regulation Number | [21 CFR §xxx.xxxx] |
| Device Class | [I / II / III] |
| Review Panel | [Panel name] |

### Predicate Device Comparison Matrix
| Attribute | Subject Device | Predicate 1 (K######) | Predicate 2 (K######) |
|-----------|---------------|----------------------|----------------------|
| Intended Use | [Statement] | [Statement] | [Statement] |
| Technology | [Description] | [Description] | [Description] |
| Key Specs | [Values] | [Values] | [Values] |
| Substantial Equivalence | — | [Yes/No + rationale] | [Yes/No + rationale] |

### Pathway Recommendation
**Recommended pathway:** [510(k) / De Novo / PMA / Exempt]
**Rationale:** [1-2 paragraphs citing classification, predicate analysis, and risk level]
**Alternative pathways considered:** [Why each was rejected]

### Required Standards and Special Controls
| Standard | Applicable Sections | Status |
|----------|-------------------|--------|
| IEC 60601-1 | [Clauses] | [To be tested / Compliant / N/A] |
| ISO 14971 | [Full] | [To be completed] |
| [Others] | [Sections] | [Status] |

**Special Controls:** [List from classification regulation or De Novo summary]

### Regulatory Timeline
| Milestone | Target Date | Dependencies | Duration |
|-----------|------------|--------------|----------|
| Pre-submission meeting | [Date] | Device description finalized | [Weeks] |
| Standards testing | [Date] | Design verification complete | [Weeks] |
| Submission authoring | [Date] | All testing complete | [Weeks] |
| FDA review | [Date] | Submission accepted | [Weeks] |
```

## Handoff

- If IEC 60601-1 gap analysis is needed for the required standards: handoff to **regulator/iec60601-review**
- If ISO 14971 risk management file is needed: handoff to **regulator/risk-management**
- If safety analysis is needed for applied parts classification: handoff to **shield/safety-analysis**
- If design controls and DHF structure is needed: handoff to **integrator/requirements-decomposition**

## Quality Checks

1. Product code verified against FDA classification database — not assumed from device description alone.
2. All listed predicate devices are legally marketed (cleared, not withdrawn or recalled for safety).
3. Technological differences between subject and predicate are explicitly documented with regulatory significance.
4. Pathway recommendation includes rationale for why alternative pathways were rejected.
5. Timeline accounts for pre-submission meeting lead time (typically 3-4 months from request).
6. Special controls are sourced from the actual classification regulation or De Novo decision summary, not generalized.
7. Applicable standards list includes edition/year — not just standard number.
8. If software is part of the device, IEC 62304 is included in the standards list.

## Evolution Notes

- Future versions may include EU MDR classification (Rule 1-22) and PMDA pathway analysis as parallel tracks.
- Integration with FDA CDRH product code database API for automated predicate searching is a candidate enhancement.
