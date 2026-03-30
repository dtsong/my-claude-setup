---
name: iec62304-compliance
department: firmware
description: "Assess firmware architecture for IEC 62304 software lifecycle compliance and determine required documentation"
version: 1
triggers:
  - IEC 62304
  - software safety
  - classification
  - SOUP
  - software lifecycle
  - documentation
  - Class A
  - Class B
  - Class C
---

# IEC 62304 Compliance

## Purpose

Assess a firmware architecture for IEC 62304 medical device software lifecycle compliance. Determine the software safety classification, inventory SOUP components, map required activities and documentation per class, evaluate architectural segregation of safety-critical functions, and produce a gap analysis with remediation plan.

## Scope Constraints

- IEC 62304:2006+A1:2015 (current edition with Amendment 1)
- Covers software lifecycle process assessment, not execution of all lifecycle activities
- Does not perform the ISO 14971 risk analysis — requires risk analysis outputs as input
- Does not generate the actual deliverable documents — identifies what documents are required and their content scope
- Does not cover IEC 62366 (usability) or IEC 60601-1 (general safety) — only software lifecycle

## Inputs

- Firmware architecture: block diagram, task decomposition, module structure
- ISO 14971 risk analysis outputs: hazardous situations involving software, severity ratings
- SOUP components: RTOS, libraries, drivers, middleware currently in use or planned
- Current documentation inventory: what lifecycle documents already exist
- Target regulatory markets: FDA (US), EU MDR, or other (affects guidance interpretation)
- Development team context: team size, existing QMS maturity

## Input Sanitization

- Reject requests without risk analysis results — safety classification cannot be determined without hazard analysis
- If SOUP list is incomplete, flag as critical gap — unlisted SOUP is uncontrolled SOUP
- Verify that claimed safety class is supported by the risk analysis (teams often under-classify)
- Confirm whether IEC 62304:2006 or IEC 62304:2006+A1:2015 is the target edition (Amendment 1 changes Class A requirements)

## Procedure

1. **Classify software safety class.** Review ISO 14971 hazardous situations involving software contribution. Apply IEC 62304 Clause 4.3 decision tree: Can software cause or contribute to a hazardous situation? If no -> Class A. If yes, can the hazardous situation result in serious injury? If no -> Class B. If yes -> Class C. Document the specific hazardous situations and severity ratings that drive the classification. Note: Amendment 1 allows risk control measures to reduce the class.

2. **Inventory SOUP components.** For each software component not developed under the device manufacturer's QMS: record name, version, manufacturer/source, license, anomaly list (known bugs), and functional description. Classify each SOUP item's risk contribution. For Class B and C, SOUP requires: published anomaly list review, defined functional and performance requirements, and a risk assessment of known anomalies per Clause 5.3.3.

3. **Map required activities per class.** Build an activity matrix from IEC 62304 Clauses 5-9 showing which activities are required for the determined software class. Key distinctions: Class A requires development planning and maintenance but minimal design documentation. Class B adds software architecture, risk analysis at architecture level, and integration testing. Class C adds detailed design, unit testing, and unit-level verification. Document the specific clause references for each required activity.

4. **Evaluate architecture for safety segregation.** Assess whether safety-critical functions (Class B/C) are architecturally isolated from non-critical functions (Class A). Segregation mechanisms include: separate tasks with defined interfaces, separate compilation units, memory protection (MPU), and input validation at safety boundaries. Effective segregation allows mixed-class systems where only the safety-critical partition requires Class C rigor.

5. **Assess configuration management and problem resolution.** Verify that software configuration management (Clause 8) covers: unique identification of software items, change control process, and traceability from requirements to verification. Verify problem resolution process (Clause 9) covers: problem reporting, investigation, change implementation, and trend analysis.

6. **Produce gap analysis and remediation plan.** Compare current documentation and processes against IEC 62304 requirements for the determined class. For each gap, specify: the IEC 62304 clause, the required artifact or activity, current status, and recommended remediation with estimated effort. Prioritize gaps by regulatory risk.

### Progress Checklist

- [ ] Software safety class determined with traceable rationale
- [ ] All SOUP components inventoried with version and risk classification
- [ ] Required activities matrix built for determined class
- [ ] Architecture segregation assessed for mixed-class feasibility
- [ ] Configuration management and problem resolution evaluated
- [ ] Gap analysis completed with prioritized remediation plan

### Compaction Resilience

If context is compacted mid-analysis, the Software Safety Classification rationale, SOUP Inventory Table, and Gap Analysis Table contain all values needed to resume. These three artifacts capture the complete compliance assessment state.

## Output Format

```markdown
## IEC 62304 Compliance Assessment: [System Name]

### Software Safety Classification
- **Determined class:** [A / B / C]
- **Rationale:** [Specific hazardous situations from ISO 14971 that drive the classification]
- **Applicable edition:** IEC 62304:2006+A1:2015
- **Risk control measures affecting class:** [if Amendment 1 class reduction applies]

### SOUP Inventory
| Component | Version | Source | License | Risk Class | Known Anomalies | Functional Req Defined |
|---|---|---|---|---|---|---|
| | | | | | | |

### Required Activities Matrix
| IEC 62304 Clause | Activity | Class A | Class B | Class C | Current Status |
|---|---|---|---|---|---|
| 5.1 | Software development planning | Req | Req | Req | |
| 5.2 | Software requirements analysis | Req | Req | Req | |
| 5.3 | Software architectural design | — | Req | Req | |
| 5.4 | Software detailed design | — | — | Req | |
| 5.5 | Software unit implementation | Req | Req | Req | |
| 5.6 | Software unit verification | — | — | Req | |
| 5.7 | Software integration and integration testing | — | Req | Req | |
| 5.8 | Software system testing | Req | Req | Req | |
| 5.9 | Software release | Req | Req | Req | |

### Architecture Segregation Assessment
- Safety-critical functions identified: [list]
- Segregation mechanism: [MPU / task isolation / module separation / none]
- Mixed-class feasibility: [yes/no with rationale]
- Segregation gaps: [list]

### Documentation Gap Analysis
| IEC 62304 Clause | Required Artifact | Current Status | Gap | Remediation | Effort |
|---|---|---|---|---|---|
| | | | | | |

### Remediation Plan (Prioritized)
| Priority | Gap | Regulatory Risk | Recommended Action | Estimated Effort |
|---|---|---|---|---|
| 1 | | | | |
| 2 | | | | |

### Recommendations
1.
2.
3.
```

## Handoff

- If RTOS architecture decisions are needed to enable safety segregation, handoff to **rtos-architecture**
- If firmware update mechanism requires maintenance process documentation, handoff to **bootloader-design**
- If risk analysis is incomplete or missing, escalate to ISO 14971 risk management process (outside firmware department scope)
- If SOUP components need replacement to reduce risk, flag for system-level architecture review

## Quality Checks

1. Safety classification traces to specific hazardous situations from ISO 14971, not generic assertions
2. All SOUP components are identified with exact version numbers, not just names
3. Class C functions have unit-level verification requirements defined
4. SOUP risk analysis considers published known anomalies, not just functional behavior
5. Architecture supports future class changes without complete system redesign
6. Amendment 1 class reduction is only applied when hardware risk control measures are documented and validated
7. Gap analysis references specific IEC 62304 clause numbers, not paraphrased requirements
8. Remediation plan is prioritized by regulatory risk, not by implementation ease

## Evolution Notes

- Future versions may add mapping to FDA software guidance documents (Level of Concern -> IEC 62304 class)
- Consider adding EU MDR-specific requirements (MDCG guidance on software lifecycle)
- Add support for SaMD (Software as a Medical Device) classification under IEC 62304 + IEC 82304-1
