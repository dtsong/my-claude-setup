---
name: "risk-management"
department: "regulator"
description: "Develop ISO 14971-compliant risk management file for a medical device design"
version: 1
triggers:
  - "risk"
  - "hazard"
  - "ISO 14971"
  - "FMEA"
  - "risk analysis"
  - "severity"
  - "probability"
  - "risk control"
---

# Risk Management

## Purpose

Develop an ISO 14971-compliant risk management file for a medical device design, including hazard identification, risk estimation, risk evaluation, risk control measures, and residual risk assessment.

## Scope Constraints

- Follows ISO 14971:2019 structure. Does not produce a process-level risk management plan — focuses on the device-level risk management file content.
- Produces risk analysis tables and risk control recommendations, not final validated risk management reports.
- Does not replace clinical risk-benefit analysis for PMA-class devices — flags when clinical evidence is needed for benefit-risk justification.

## Inputs

- Device description: intended use, indications for use, patient population
- Design architecture: block diagram, subsystem descriptions, applied parts, energy sources
- Known hazards or failure modes from prior analysis (if any)
- Risk acceptability criteria: ALARP, matrix-based, or organization-defined
- Applicable standards (IEC 60601-1, IEC 62304, etc.) for hazard category coverage

## Input Sanitization

- If intended use is missing, do not proceed — intended use defines the scope of reasonably foreseeable use and misuse.
- If risk acceptability criteria are not provided, default to a 5x5 matrix (S1-S5 x P1-P5) with ALARP region and state the assumption explicitly.
- If the design architecture is incomplete, document known gaps and flag subsystems that require further hazard analysis when design matures.

## Procedure

1. **Define intended use and reasonably foreseeable misuse.** Document the intended use statement, intended patient population, intended user profile, intended use environment, and reasonably foreseeable misuse scenarios per ISO 14971 Section 5.2. This frames the entire risk analysis scope.

2. **Identify hazards by category.** Systematically identify hazards using ISO 14971 Annex C categories:
   - Energy hazards: electrical (leakage current, defibrillation, electrosurgery), thermal (surface temperature, fire), mechanical (moving parts, sharp edges, pressure), radiation (ionizing, non-ionizing, EMF)
   - Biological hazards: biocompatibility, infection, cross-contamination
   - Chemical hazards: residues, leachables, battery chemicals
   - Operational hazards: incorrect output, delayed output, use error, software defects
   - Information hazards: labeling errors, inadequate instructions
   For each hazard, identify the hazardous situation and the resulting harm.

3. **Estimate risk for each hazardous situation.** Assign severity (S1-S5) and probability of occurrence (P1-P5):
   - S1: Negligible — inconvenience or temporary discomfort
   - S2: Minor — temporary injury, no intervention required
   - S3: Serious — injury requiring medical intervention
   - S4: Critical — permanent impairment or life-threatening
   - S5: Catastrophic — death
   - P1: Incredible — less than 1 in 10^6
   - P2: Remote — 1 in 10^6 to 1 in 10^4
   - P3: Occasional — 1 in 10^4 to 1 in 10^2
   - P4: Probable — 1 in 10^2 to 1 in 10
   - P5: Frequent — greater than 1 in 10
   Document the rationale for each severity and probability assignment.

4. **Evaluate risk acceptability.** Map each hazardous situation to the risk acceptability matrix:
   - Broadly acceptable (green): No risk control required, document rationale
   - ALARP region (yellow): Risk control required, reduce as low as reasonably practicable
   - Unacceptable (red): Risk control mandatory, design change required
   Flag any risks in the unacceptable region.

5. **Define risk control measures.** For each unacceptable or ALARP risk, define controls following the priority order per ISO 14971 Section 7.1:
   - **Option 1 — Inherent safety by design:** Eliminate the hazard or reduce severity/probability through design changes
   - **Option 2 — Protective measures:** Add barriers, alarms, or automatic shutoffs in the device or manufacturing process
   - **Option 3 — Information for safety:** Warnings, labeling, training, instructions for use
   Document why higher-priority options were not feasible when lower-priority options are selected.

6. **Evaluate residual risk and overall residual risk.** After applying risk controls:
   - Re-estimate risk for each hazardous situation with controls in place
   - Verify all residual risks are in the acceptable or ALARP region
   - Evaluate overall residual risk considering the cumulative effect of all individual residual risks
   - Determine if the overall residual risk is acceptable in light of the medical benefits per ISO 14971 Section 8

### Progress Checklist

- [ ] Intended use and misuse documented
- [ ] All ISO 14971 Annex C hazard categories systematically reviewed
- [ ] Risk estimation completed for all hazardous situations
- [ ] Risk acceptability evaluation completed
- [ ] Risk control measures defined with priority justification
- [ ] Residual risk and overall residual risk evaluated

### Compaction Resilience

If context is compacted mid-procedure, the Hazard Identification Table and Risk Control Measures Table are self-contained. Resume from the last incomplete checklist item. Each table row captures the full chain: hazard -> hazardous situation -> harm -> severity -> probability -> risk level -> control -> residual risk.

## Output Format

```markdown
## Risk Management File — [Device Name]

### Intended Use Statement
**Intended use:** [Statement]
**Patient population:** [Description]
**Intended user:** [Professional/lay user profile]
**Use environment:** [Clinical, home, ambulatory, etc.]
**Reasonably foreseeable misuse:** [List of misuse scenarios]

### Hazard Identification Table
| ID | Hazard Category | Hazard | Hazardous Situation | Foreseeable Harm |
|----|----------------|--------|--------------------|-----------------|
| H-001 | Energy — Electrical | [Hazard] | [Situation] | [Harm] |
| H-002 | Energy — Thermal | [Hazard] | [Situation] | [Harm] |
| ... | ... | ... | ... | ... |

### Risk Estimation Matrix
| ID | Hazardous Situation | Severity | Probability | Risk Level | Acceptability |
|----|--------------------|---------:|------------:|-----------:|--------------|
| H-001 | [Situation] | S[1-5] | P[1-5] | [Score] | [Acceptable/ALARP/Unacceptable] |

### Risk Acceptability Matrix
|  | P1 | P2 | P3 | P4 | P5 |
|--|----|----|----|----|-----|
| S5 | ALARP | Unacceptable | Unacceptable | Unacceptable | Unacceptable |
| S4 | ALARP | ALARP | Unacceptable | Unacceptable | Unacceptable |
| S3 | Acceptable | ALARP | ALARP | Unacceptable | Unacceptable |
| S2 | Acceptable | Acceptable | ALARP | ALARP | Unacceptable |
| S1 | Acceptable | Acceptable | Acceptable | Acceptable | ALARP |

### Risk Control Measures Table
| ID | Hazardous Situation | Pre-Control Risk | Control Type | Control Description | Post-Control Severity | Post-Control Probability | Residual Risk | Acceptable? |
|----|--------------------|-----------------:|-------------|--------------------:|---------------------:|------------------------:|-------------:|------------|
| H-001 | [Situation] | S[x]P[y] | [Inherent/Protective/Information] | [Description] | S[x] | P[y] | [Score] | [Yes/No] |

### Residual Risk Summary
**Individual residual risks:** [All acceptable / exceptions listed]
**Overall residual risk:** [Acceptable / Requires benefit-risk justification]
**Benefit-risk analysis:** [Summary if overall residual risk requires justification]
```

## Handoff

- If electrical safety hazards require detailed leakage current or dielectric analysis: handoff to **shield/leakage-current**
- If single-fault conditions need systematic analysis: handoff to **shield/single-fault-analysis**
- If risk controls require design architecture changes: handoff to the relevant design domain (analog, firmware, tracer)
- If IEC 60601-1 compliance status affects risk estimation: handoff to **regulator/iec60601-review**

## Quality Checks

1. All hazard categories from ISO 14971 Annex C are systematically reviewed — not just the obvious ones.
2. Severity ratings are justified with reference to the specific harm, not assigned by gut feeling.
3. Probability estimates include rationale (field data, similar device history, fault tree analysis, or engineering judgment with stated assumptions).
4. Risk controls follow the priority order: inherent safety first, protective measures second, information for safety third. Deviation from priority order is justified.
5. No residual risk is left in the unacceptable region without explicit benefit-risk justification per ISO 14971 Section 8.
6. Risk controls do not introduce new hazards — each control is checked for secondary hazard generation.
7. The link from hazard to harm is traceable through the hazardous situation — no hazards are listed without a credible sequence to patient harm.
8. Overall residual risk evaluation considers the cumulative effect, not just individual risk acceptability.

## Evolution Notes

- Future versions may integrate with FMEA (IEC 60812) for component-level failure mode analysis feeding into the ISO 14971 hazard table.
- Fault tree analysis (FTA) templates for probability estimation are a candidate addition for complex hazardous situations.
