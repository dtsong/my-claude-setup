---
name: "iec60601-review"
department: "regulator"
description: "Conduct IEC 60601-1 compliance gap analysis for a medical device design"
version: 1
triggers:
  - "IEC 60601"
  - "compliance"
  - "gap analysis"
  - "general requirements"
  - "particular standard"
  - "collateral"
---

# IEC 60601-1 Review

## Purpose

Conduct an IEC 60601-1 compliance gap analysis for a medical device design, identifying applicable general, collateral, and particular standards, assessing current compliance status, and producing a prioritized remediation plan.

## Scope Constraints

- Covers IEC 60601-1:2005+A1:2012+A2:2020 (Edition 3.2) general requirements and key collateral/particular standards.
- Produces a gap analysis and remediation plan, not a formal test report. Test reports require accredited laboratory testing.
- Does not perform actual measurements (leakage current, dielectric strength, temperature rise). Identifies what must be measured and the acceptance criteria.

## Inputs

- Device description: intended use, applied parts, mode of operation, power source
- Design documentation: schematic, PCB layout, mechanical drawings, block diagram
- Applied part classification from Shield's safety analysis (Type B, BF, or CF)
- Known compliance status from prior testing or analysis (if any)
- Target markets and applicable national deviations (US, EU, Japan, etc.)

## Input Sanitization

- If applied part classification is not provided, flag as a critical gap — applied part type determines MOPP/MOOP requirements, leakage current limits, and dielectric withstand test levels.
- If mode of operation is unstated, ask: continuous, short-time, intermittent? This affects temperature rise testing per Clause 11.
- If power source is unclear, determine: mains-powered, internally-powered, or combination. This drives Clause 8 applicability.

## Procedure

1. **Identify applicable IEC 60601 standards.** Determine the full set of applicable standards:
   - IEC 60601-1 (general requirements) — always applicable to ME equipment
   - Collateral standards (-1-X): -1-2 (EMC), -1-6 (usability), -1-8 (alarm systems), -1-9 (environmentally conscious design), -1-10 (physiologic closed-loop controllers), -1-11 (home healthcare), -1-12 (emergency and transport)
   - Particular standards (-2-X): identify the specific -2-X standard for this device type (e.g., -2-25 for electrocardiographs, -2-27 for ECG monitoring, -2-47 for ambulatory ECG)
   Document which are applicable and which are not applicable with rationale.

2. **Review ME equipment classification.** Document per IEC 60601-1 Clause 6:
   - Protection class: Class I (protective earth) or Class II (double/reinforced insulation)
   - Type of applied part: B, BF, or CF
   - Mode of operation: continuous, short-time, intermittent
   - Degree of protection against ingress: IP rating per IEC 60529
   - Degree of protection against ignition of flammable anesthetic gases: AP/APG category or not applicable
   Verify classification consistency with the device's intended use environment.

3. **Assess compliance against key clauses.** For each major clause area, evaluate the design:
   - **Clause 8 — Electrical hazards:** Means of protection (MOPP/MOOP), creepage/clearance per Table 12/13, dielectric strength per Table 6, leakage current limits per Table 3/4, protective earthing
   - **Clause 9 — Mechanical hazards:** Moving parts, surfaces/corners/edges, expelled parts, acoustic energy, pneumatic/hydraulic pressure
   - **Clause 11 — Temperature:** Maximum surface temperatures per Table 23/24, temperature rise during normal/single-fault conditions
   - **Clause 13 — Hazardous situations:** Overflow, spillage, leakage, humidity, ingress of liquids, cleaning/sterilization, applied parts requirements
   - **Clause 14 — Programmable electrical medical systems (PEMS):** If applicable, software lifecycle per IEC 62304, risk management for PEMS
   - **Clause 15 — Construction:** Materials, enclosure integrity, biocompatibility of applied parts, mains supply connection
   - **Clause 16 — ME systems:** If device is part of a system with non-ME equipment, system-level requirements
   - **Clause 17 — EMC:** Reference to IEC 60601-1-2 for emissions and immunity

4. **Identify applicable collateral standard requirements.** For each applicable collateral standard:
   - **IEC 60601-1-2 (EMC):** Intended use environment (professional healthcare, home), emissions class (Group 1/Class A or B), immunity test levels per Table 1-9, essential performance during immunity testing
   - **IEC 60601-1-6 (Usability):** Usability engineering process per IEC 62366-1, use-related risk analysis, formative and summative usability evaluation requirements
   - **IEC 60601-1-8 (Alarms):** If device has alarm functions: alarm categories (high/medium/low priority), auditory/visual characteristics, distributed alarm systems
   - **IEC 60601-1-10 (Closed-loop):** If device has physiologic closed-loop control: controller stability, failure modes, clinician override
   Document specific requirements applicable to this device.

5. **Document compliance status per clause.** For each clause and sub-clause assessed, assign a status:
   - **Compliant:** Design meets requirements, evidence available or clearly demonstrable
   - **Non-compliant:** Design does not meet requirements, remediation needed
   - **Needs testing:** Compliance cannot be determined without physical testing (leakage current, dielectric, temperature rise, EMC)
   - **Not applicable:** Clause does not apply to this device type, with rationale
   Capture the specific requirement, acceptance criterion, and current design status.

6. **Prioritize gaps by risk and timeline impact.** Rank non-compliant and needs-testing items:
   - **Priority 1 — Safety critical:** Basic safety or essential performance gaps (patient leakage current, dielectric withstand, single-fault conditions). These block submission.
   - **Priority 2 — Design change required:** Compliance gaps that require schematic, PCB, or mechanical design changes. Long lead time.
   - **Priority 3 — Documentation/testing:** Gaps that can be resolved by testing or documentation without design changes. Shorter lead time.
   Produce a remediation plan with estimated effort and dependencies.

### Progress Checklist

- [ ] Applicable standards identified (general, collateral, particular)
- [ ] ME equipment classification documented
- [ ] Key clauses assessed (8, 9, 11, 13, 14, 15, 16, 17)
- [ ] Collateral standard requirements documented
- [ ] Compliance status assigned per clause
- [ ] Gaps prioritized and remediation plan drafted

### Compaction Resilience

If context is compacted mid-procedure, the Applicable Standards Matrix and Clause-by-Clause Compliance Table are self-contained. Resume from the last incomplete checklist item. Each compliance row captures: clause reference, requirement summary, acceptance criterion, status, and remediation action.

## Output Format

```markdown
## IEC 60601-1 Compliance Gap Analysis — [Device Name]

### Applicable Standards Matrix
| Standard | Edition | Applicable? | Rationale |
|----------|---------|------------|-----------|
| IEC 60601-1 | Ed. 3.2 (2020) | Yes | ME equipment |
| IEC 60601-1-2 | Ed. 4.1 (2020) | Yes | EMC requirements |
| IEC 60601-1-6 | Ed. 2 (2020) | Yes | Usability |
| IEC 60601-2-XX | Ed. X | [Yes/No] | [Rationale] |
| ... | ... | ... | ... |

### Equipment Classification Summary
| Parameter | Classification | Reference |
|-----------|---------------|-----------|
| Protection class | [Class I / Class II] | Clause 6.2 |
| Applied part type | [B / BF / CF] | Clause 6.3 |
| Mode of operation | [Continuous / Short-time / Intermittent] | Clause 6.4 |
| IP rating | [IPxx] | Clause 6.5 |
| MOPP count | [1 / 2] | Table 4 |

### Clause-by-Clause Compliance Table
| Clause | Requirement Summary | Acceptance Criterion | Status | Remediation Action |
|--------|-------------------|---------------------|--------|-------------------|
| 8.5.1 | Creepage/clearance | [mm per Table 12/13] | [Status] | [Action] |
| 8.5.2 | Solid insulation | [Thickness/layers] | [Status] | [Action] |
| 8.7.3 | Earth leakage current | [≤ X mA per Table 3] | [Status] | [Action] |
| 8.7.4 | Patient leakage current | [≤ X µA per Table 4] | [Status] | [Action] |
| 8.8.3 | Dielectric strength | [X Vrms per Table 6] | [Status] | [Action] |
| 11.1.2 | Surface temperature limits | [°C per Table 23/24] | [Status] | [Action] |
| ... | ... | ... | ... | ... |

### Gap Summary (by priority)
#### Priority 1 — Safety Critical
| Gap ID | Clause | Description | Impact | Remediation |
|--------|--------|------------|--------|-------------|

#### Priority 2 — Design Change Required
| Gap ID | Clause | Description | Impact | Remediation |
|--------|--------|------------|--------|-------------|

#### Priority 3 — Documentation/Testing
| Gap ID | Clause | Description | Impact | Remediation |
|--------|--------|------------|--------|-------------|

### Remediation Plan
| Gap ID | Action | Owner | Est. Effort | Dependencies | Target Date |
|--------|--------|-------|------------|--------------|-------------|

### Test Plan Requirements
| Test | Standard Reference | Acceptance Criterion | Lab Required? |
|------|-------------------|---------------------|---------------|
| Patient leakage current | 8.7.4, Table 4 | [µA limit] | Yes — accredited |
| Dielectric strength | 8.8.3, Table 6 | [Vrms] | Yes — accredited |
| Temperature rise | 11.1.2, Table 23/24 | [°C limits] | Yes |
| EMC emissions | IEC 60601-1-2, Table 1-4 | [Class/Group] | Yes — accredited |
| EMC immunity | IEC 60601-1-2, Table 5-9 | [Test levels] | Yes — accredited |
```

## Handoff

- If applied part classification is unresolved: handoff to **shield/safety-analysis** for patient-contact analysis
- If leakage current or dielectric strength values need calculation: handoff to **shield/leakage-current**
- If single-fault condition analysis is needed for Clause 13: handoff to **shield/single-fault-analysis**
- If EMC strategy requires PCB layout or stackup changes: handoff to **tracer/emc-strategy**
- If software classification per IEC 62304 is needed for Clause 14: handoff to **firmware/iec62304-compliance**
- If risk management input is needed for essential performance identification: handoff to **regulator/risk-management**

## Quality Checks

1. All applicable -2-X particular standards identified — missing a particular standard means missing device-specific requirements that override general requirements.
2. Applied part classification is consistent with Shield's safety analysis — if Shield says CF, this review must use CF leakage limits and 2 MOPP.
3. EMC requirements per IEC 60601-1-2 Edition 4 are included — intended use environment determines immunity test levels.
4. Usability requirements per IEC 60601-1-6 are addressed — usability engineering process evidence is required for regulatory submission.
5. Essential performance is explicitly identified — functions whose loss creates unacceptable risk must maintain performance during single-fault and EMC immunity testing.
6. Creepage and clearance values reference the correct working voltage, pollution degree, and MOPP/MOOP classification from Table 12/13.
7. National deviations for target markets are noted (e.g., UL/ANSI differences for US market, MHLW deviations for Japan).
8. Each "not applicable" designation includes a rationale — reviewers will question blanket N/A designations.

## Evolution Notes

- Future versions may include automated clause cross-referencing between -1 general requirements and -2-X particular standard deviations.
- Edition tracking for standards updates (particularly IEC 60601-1-2 Edition 4 and IEC 62304 Amendment 1) is a candidate enhancement.
