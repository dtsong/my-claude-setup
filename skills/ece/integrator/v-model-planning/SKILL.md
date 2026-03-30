---
name: "v-model-planning"
department: "integrator"
description: "Use when planning verification and validation activities aligned to the V-model lifecycle. Covers design phase mapping, verification method assignment, design review planning (PDR/CDR/TRR), and V&V scheduling. Do not use for requirements decomposition (use requirements-decomposition) or interface definitions (use interface-control)."
version: 1
triggers:
  - "V-model"
  - "V&V"
  - "verification"
  - "validation"
  - "design review"
  - "test plan"
  - "qualification"
  - "PDR"
  - "CDR"
  - "TRR"
  - "design transfer"
---

# V-Model Planning

## Purpose

Plan verification and validation activities aligned to the V-model lifecycle. Produces a verification method assignment table, design review plan with entry/exit criteria, design transfer checklist, and V&V schedule. Ensures that every requirement has a defined path from specification to verified evidence.

## Scope Constraints

- Produces V&V planning documents only; does not execute tests or generate test procedures.
- Covers verification method assignment, design review planning, and V&V scheduling.
- Does not decompose requirements — hand off to requirements-decomposition.
- Does not define interface specifications — hand off to interface-control.

## Inputs

- Requirements hierarchy with subsystem allocations (from requirements-decomposition)
- Interface register (from interface-control)
- Project timeline and milestone dates
- Available test infrastructure (lab equipment, test fixtures, environmental chambers)
- Applicable standards requiring specific verification methods (IEC 60601-1, IEC 61000-4-x, IEC 62304)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
<!-- Track completion across compaction boundaries -->
- [ ] Step 1: Map Design Phases (Left Side of V)
- [ ] Step 2: Map Verification Phases (Right Side of V)
- [ ] Step 3: Assign Verification Methods
- [ ] Step 4: Plan Design Reviews
- [ ] Step 5: Define Design Transfer Criteria
- [ ] Step 6: Build V&V Schedule

### Step 1: Map Design Phases (Left Side of V)

Define the design decomposition levels for this project:
1. **User Needs** — Clinical/user requirements, intended use, use environment
2. **Design Inputs** — System-level requirements derived from user needs (per 21 CFR 820.30(c))
3. **System Design** — System architecture, subsystem partitioning, interface definitions
4. **Subsystem Design** — Detailed design of each subsystem (schematics, firmware architecture, mechanical CAD)
5. **Implementation** — PCB layout, firmware coding, mechanical fabrication, component procurement

For each level, identify the design output documents (specifications, schematics, layout files, source code) and their review/approval requirements.

### Step 2: Map Verification Phases (Right Side of V)

Define the verification levels that mirror the design levels:
1. **Unit/Component Verification** — Verify individual components and circuits meet subsystem specs (mirrors Implementation)
2. **Integration Testing** — Verify subsystem interfaces work correctly when connected (mirrors Subsystem Design)
3. **System Verification** — Verify the integrated system meets design inputs (mirrors System Design)
4. **Design Validation** — Validate the system meets user needs in the intended use environment (mirrors User Needs/Design Inputs)

For each verification level, define:
- What is being verified (which requirements at this level)
- Who performs it (design engineer, test engineer, independent V&V)
- Where it is performed (bench, environmental chamber, simulated use, clinical)
- Required documentation (test protocol, test report, deviation handling)

### Step 3: Assign Verification Methods

For each requirement in the hierarchy, assign one or more verification methods:
- **Test (T)** — Measure a parameter and compare to acceptance criteria. Use for quantitative performance requirements.
- **Analysis (A)** — Calculate, simulate, or model the parameter. Use when testing is impractical (e.g., worst-case circuit analysis, thermal simulation, FMEA).
- **Inspection (I)** — Visual or dimensional examination. Use for physical attributes (labeling, color coding, mechanical dimensions).
- **Demonstration (D)** — Show that a function operates correctly without measuring a specific parameter. Use for functional requirements that are pass/fail.

Document in the Verification Method Assignment Table. Flag any requirements where:
- No verification method can be assigned (requirement is untestable — escalate to requirements-decomposition)
- The required test equipment is not available (schedule or procurement risk)
- The verification method requires regulatory witness testing (e.g., third-party EMC lab)

### Step 4: Plan Design Reviews

Define the major design reviews with entry and exit criteria:

**Preliminary Design Review (PDR):**
- Entry: System requirements baselined, subsystem architecture defined, key trade studies complete
- Scope: Review system architecture, subsystem partitioning, interface definitions, risk assessment
- Exit: Architecture approved, ICDs baselined, risk mitigations assigned, no open critical findings

**Critical Design Review (CDR):**
- Entry: Detailed design complete (schematics, firmware architecture, mechanical CAD), analysis results available
- Scope: Review detailed design against requirements, worst-case analysis, component selections, manufacturing feasibility
- Exit: Design approved for prototype build, BOM released, test plans approved, no open critical findings

**Test Readiness Review (TRR):**
- Entry: Prototype units built and functionally checked out, test procedures written and reviewed, test equipment calibrated
- Scope: Review test readiness, sample size, acceptance criteria, deviation handling process
- Exit: Approval to begin formal verification testing

For each review, specify the review board composition, required attendees, action item tracking process, and finding severity classification (Critical, Major, Minor).

### Step 5: Define Design Transfer Criteria

Specify the criteria that must be met before design transfer to manufacturing:
- All design verification testing complete with no open critical findings
- All design validation activities complete (or planned with justified timeline)
- Manufacturing process validated (IQ/OQ/PQ or equivalent)
- Production test procedures written and validated
- BOM finalized with approved suppliers and alternates identified
- Assembly and inspection work instructions released
- Packaging and labeling validated
- Risk management file updated with residual risk assessment
- Design history file (DHF) complete and reviewed

### Step 6: Build V&V Schedule

Create the V&V schedule with:
- Activity name and description
- Prerequisites (what must be complete before this activity can start)
- Duration estimate
- Required resources (test equipment, personnel, prototype units, external labs)
- Milestone dependencies (which design reviews gate which verification activities)
- Critical path identification

Highlight schedule risks:
- Long-lead test equipment or external lab bookings
- Activities requiring multiple prototype units (sample size for statistical testing)
- Regulatory submission dependencies (e.g., EMC testing must be complete before 510(k) submission)

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what system is being analyzed, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Handoff

- If verification method assignment reveals untestable requirements, recommend loading integrator/requirements-decomposition to rewrite them.
- If integration testing reveals undefined interfaces, recommend loading integrator/interface-control.
- If safety verification planning is needed, recommend loading shield/safety-analysis.
- If EMC/environmental qualification planning is needed, recommend loading tracer/emc-strategy.

## Output Format

```markdown
# V-Model Plan: [System/Project Name]

## V-Model Diagram

```
User Needs ─────────────────────────────────── Design Validation
  │                                                   ▲
  ▼                                                   │
Design Inputs ──────────────────────── System Verification
  │                                           ▲
  ▼                                           │
System Design ──────────────── Integration Testing
  │                                   ▲
  ▼                                   │
Subsystem Design ──── Unit Verification
  │                       ▲
  ▼                       │
  └── Implementation ─────┘
```

## Verification Method Assignment Table

| Req ID | Requirement Text | V-Level | Method | Equipment/Facility | Acceptance Criteria | Notes |
|--------|-----------------|---------|--------|-------------------|--------------------|----- |
| SYS-PERF-001 | Input noise <= 1.0 uVrms | System | Test | Signal analyzer, shielded room | Measured noise < 1.0 uVrms, 0.5-150 Hz, 25C | Requires shielded enclosure |

## Design Review Plan

### PDR
- **Entry criteria:** [List]
- **Exit criteria:** [List]
- **Review board:** [Roles]
- **Target date:** [Date]

### CDR
- **Entry criteria:** [List]
- **Exit criteria:** [List]
- **Review board:** [Roles]
- **Target date:** [Date]

### TRR
- **Entry criteria:** [List]
- **Exit criteria:** [List]
- **Review board:** [Roles]
- **Target date:** [Date]

## Design Transfer Checklist

- [ ] All DVT complete — no open critical findings
- [ ] Design validation complete or justified timeline
- [ ] Manufacturing process validated (IQ/OQ/PQ)
- [ ] Production test procedures validated
- [ ] BOM finalized with approved alternates
- [ ] Work instructions released
- [ ] Packaging and labeling validated
- [ ] Risk management file updated
- [ ] DHF complete and reviewed

## V&V Schedule

| Activity | Prerequisites | Duration | Resources | Start | End | Critical Path |
|----------|-------------|----------|-----------|-------|-----|--------------|
| Unit verification — AFE | CDR exit, prototype build | 3 weeks | Bench equipment | TBD | TBD | No |
| EMC pre-compliance | Integration test complete | 2 weeks | EMC chamber | TBD | TBD | Yes |
```

## Quality Checks

- [ ] Every requirement in the hierarchy has a verification method assigned (T, A, I, or D)
- [ ] Design reviews have defined entry and exit criteria with no vague statements
- [ ] Verification sequence respects dependencies (unit before integration, integration before system)
- [ ] Test equipment and facility needs are identified for every Test-method verification
- [ ] Critical path through the V&V schedule is identified
- [ ] Design transfer criteria are complete and measurable
- [ ] Requirements flagged as untestable have been escalated for rewrite
- [ ] External lab and regulatory submission dependencies are captured in the schedule

## Evolution Notes
<!-- Observations appended after each use -->
