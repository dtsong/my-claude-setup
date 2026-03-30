---
name: "requirements-decomposition"
department: "integrator"
description: "Use when decomposing system-level requirements into subsystem specifications with full traceability. Covers requirement categorization, subsystem allocation, derived requirements, acceptance criteria, and traceability matrices. Do not use for interface definitions (use interface-control) or V&V planning (use v-model-planning)."
version: 1
triggers:
  - "requirements"
  - "decomposition"
  - "specification"
  - "subsystem"
  - "design input"
  - "traceability"
  - "allocation"
  - "derived requirement"
  - "DOORS"
  - "JAMA"
---

# Requirements Decomposition

## Purpose

Decompose system-level requirements into subsystem specifications with measurable acceptance criteria and full traceability. Produces a requirements hierarchy, allocation matrix, and traceability matrix that can be imported into DOORS/JAMA.

## Scope Constraints

- Produces requirements documents and traceability matrices only; does not define interface details (hand off to interface-control).
- Covers requirement categorization, subsystem allocation, derived requirements, and acceptance criteria.
- Does not assign verification methods to requirements — hand off to v-model-planning.

## Inputs

- System-level requirements document (user needs, design inputs, regulatory requirements)
- Subsystem architecture or block diagram (defines allocation targets)
- Applicable standards (IEC 60601-1, ISO 14971, IEC 62304, etc.)
- Existing requirements database export (if modifying an existing decomposition)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
<!-- Track completion across compaction boundaries -->
- [ ] Step 1: Catalog System-Level Requirements
- [ ] Step 2: Identify Subsystem Boundaries
- [ ] Step 3: Allocate Requirements to Subsystems
- [ ] Step 4: Derive Subsystem Specifications
- [ ] Step 5: Identify Cross-Subsystem Dependencies
- [ ] Step 6: Flag Issues and Gaps

### Step 1: Catalog System-Level Requirements

Categorize all system-level requirements by type:
- **Functional** — What the system must do (sensing, processing, output, communication)
- **Performance** — How well it must do it (accuracy, noise, bandwidth, latency, throughput)
- **Safety** — Patient and operator protection (IEC 60601-1 applied part classification, fault conditions)
- **Regulatory** — Standards compliance mandates (biocompatibility, EMC, software class)
- **Environmental** — Operating and storage conditions (temperature, humidity, altitude, IP rating)

Assign each requirement a unique ID using the format SYS-[CAT]-[NNN] (e.g., SYS-FUNC-001, SYS-PERF-012).

### Step 2: Identify Subsystem Boundaries

From the system block diagram or architecture, enumerate all subsystems that will receive allocated requirements. For each subsystem, document:
- Subsystem name and ID prefix (e.g., AFE for analog front-end, PSU for power supply)
- Owner/responsible discipline (EE, ME, FW, electrochemistry)
- Key constraints (power budget, PCB area, component count)

### Step 3: Allocate Requirements to Subsystems

For each system-level requirement, allocate to one or more subsystems. Record in the Subsystem Allocation Matrix:
- System requirement ID
- Allocated subsystem(s)
- Allocation rationale (why this subsystem owns this requirement)
- If allocated to multiple subsystems, specify the responsibility split

Flag any system requirements that cannot be allocated — these indicate a gap in the subsystem architecture.

### Step 4: Derive Subsystem Specifications

For each allocated requirement, derive subsystem-level specifications with:
- Unique ID using format [SUBSYS]-[CAT]-[NNN] (e.g., AFE-PERF-003)
- Parent requirement ID (traceability link)
- Specification text using "shall" statements
- Measurable acceptance criteria with numeric thresholds, units, and test conditions
- Tolerance or acceptable range where applicable

Every derived requirement must be more specific than its parent. "The system shall have low noise" becomes "The AFE shall have input-referred noise density no greater than 1.0 uVrms over 0.5-150 Hz bandwidth, measured at 25C with 10 kohm source impedance."

### Step 5: Identify Cross-Subsystem Dependencies

Map dependencies where one subsystem's requirement constrains another:
- Shared resources (power rails, clock domains, communication buses)
- Timing dependencies (power sequencing, initialization order, data flow latency)
- Physical dependencies (thermal coupling, mechanical mounting, cable routing)

For each dependency, identify the interface requirement that must be defined in the ICD. Recommend handoff to interface-control for detailed interface specification.

### Step 6: Flag Issues and Gaps

Review the complete decomposition for:
- **Ambiguous requirements** — "shall" statements without measurable criteria
- **Untestable requirements** — requirements that cannot be verified by test, analysis, inspection, or demonstration
- **Conflicting requirements** — two requirements that cannot both be satisfied simultaneously
- **Orphan requirements** — system requirements not allocated to any subsystem
- **Gold-plated requirements** — derived requirements that exceed the parent requirement's intent
- **Missing requirements** — subsystem constraints implied by the architecture but not captured

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what system is being analyzed, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Handoff

- If the decomposition reveals interface requirements between subsystems, recommend loading integrator/interface-control.
- If requirements need verification method assignment, recommend loading integrator/v-model-planning.
- If safety requirements require hazard analysis, recommend loading shield/safety-analysis.

## Output Format

```markdown
# Requirements Decomposition: [System/Project Name]

## Requirements Hierarchy

| Level | ID | Category | Requirement Text | Acceptance Criteria |
|-------|-----|----------|-----------------|---------------------|
| System | SYS-FUNC-001 | Functional | ... | ... |
| Subsystem | AFE-FUNC-001 | Functional | ... | ... |

## Subsystem Allocation Matrix

| System Req ID | Allocated Subsystem(s) | Allocation Rationale |
|---------------|----------------------|---------------------|
| SYS-FUNC-001 | AFE, DSP | Signal acquisition split: AFE captures, DSP processes |

## Traceability Matrix

| System Req | Derived Subsystem Reqs | Verification Method | Status |
|-----------|----------------------|--------------------| -------|
| SYS-FUNC-001 | AFE-FUNC-001, DSP-FUNC-003 | TBD (assign in V&V planning) | Allocated |

## Cross-Dependency Map

| Dependency | From Subsystem | To Subsystem | Interface Req Needed |
|-----------|---------------|-------------|---------------------|
| ADC data bus | AFE | DSP | Yes — define in ICD |

## Issues and Gaps

| ID | Type | Description | Severity | Recommended Action |
|----|------|------------|----------|-------------------|
| GAP-001 | Ambiguous | SYS-PERF-003 lacks numeric threshold | High | Clarify with stakeholder |
```

## Quality Checks

- [ ] Every system requirement is allocated to at least one subsystem
- [ ] Every derived subsystem requirement has measurable acceptance criteria with numeric thresholds
- [ ] No circular dependencies in the requirements hierarchy
- [ ] All "shall" statements are testable by at least one verification method (test, analysis, inspection, demonstration)
- [ ] No orphan system requirements (allocated to zero subsystems)
- [ ] No gold-plated derived requirements exceeding parent intent
- [ ] Cross-subsystem dependencies are identified and flagged for ICD definition
- [ ] Requirement IDs follow the naming convention consistently

## Evolution Notes
<!-- Observations appended after each use -->
