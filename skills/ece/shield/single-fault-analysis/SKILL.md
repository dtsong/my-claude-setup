---
name: single-fault-analysis
department: "shield"
description: "Use when systematically evaluating circuit behavior under single-fault conditions to verify patient safety. Covers safety-critical component identification, failure mode enumeration (open, short, drift), hazard analysis per failure, remaining protection assessment, and design change recommendations. Do not use for general safety analysis (use safety-analysis) or focused leakage current calculations (use leakage-current)."
version: 1
triggers:
  - "single fault"
  - "fault condition"
  - "component failure"
  - "open circuit"
  - "short circuit"
  - "FMEA"
  - "failure mode"
  - "safety-critical component"
---

# Single-Fault Analysis

## Purpose

Systematically evaluate circuit behavior under single-fault conditions to verify that patient and operator safety is maintained when any one protective measure or safety-critical component fails.

## Scope Constraints

Analyzes safety-critical components for failure modes and their impact on patient/operator safety per IEC 60601-1 single-fault philosophy. Does not perform general safety classification (hand off to safety-analysis skill) or detailed leakage current calculations under fault conditions (hand off to leakage-current skill). Requires the safety analysis and applied part classification as input context.

## Inputs

- Circuit schematic with component references and values
- Applied part classification (from safety-analysis)
- Means of protection map (from safety-analysis)
- List of safety-critical components (if previously identified) or full BOM for identification
- Component datasheets for safety-critical parts (failure mode data, ratings)
- Operating conditions (voltage, current, temperature range)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Safety-critical components identified
- [ ] Step 2: Failure modes enumerated
- [ ] Step 3: Circuit behavior analyzed per failure
- [ ] Step 4: Remaining protection assessed
- [ ] Step 5: Scenarios classified
- [ ] Step 6: Design changes recommended

### Step 1: Identify Safety-Critical Components

- A component is safety-critical if its failure could:
  - Create a hazardous voltage on an accessible part or patient connection
  - Increase leakage current beyond Table 3 limits
  - Defeat a means of protection (MOPP or MOOP)
  - Cause excessive temperature (fire or burn risk per Clause 11)
  - Disable a safety function (alarm, current limiter, isolation monitor)
- Systematically review each component in the protection paths identified by the safety-analysis means of protection map
- Include: isolation transformers, optocouplers, Y-capacitors, X-capacitors, MOVs, fuses, protective earth connections, current-limiting resistors, voltage regulators in safety paths, isolation barrier components
- Document each component with: reference designator, function in safety path, rated values, and the safety function it provides

### Step 2: Enumerate Failure Modes

- For each safety-critical component, enumerate all credible failure modes:
  - **Open circuit** — component becomes high impedance (broken lead, internal fracture, fuse blow)
  - **Short circuit** — component becomes low impedance (dielectric breakdown, solder bridge, moisture ingress)
  - **Drift** — parameter changes beyond tolerance (aging, temperature, radiation — resistors drift, capacitors degrade, semiconductors shift threshold)
  - **Intermittent** — component alternates between functional and failed states (cracked solder joint, loose connector, thermal cycling)
- Use component-specific failure mode data where available:
  - Capacitors: open, short, reduced capacitance, increased ESR, increased leakage
  - Resistors: open, drift high, drift low (short is rare for film resistors)
  - Transformers: shorted turns, open winding, insulation breakdown between windings
  - Semiconductors: open, short (any two terminals), parametric drift
  - Connectors: open (single pin), intermittent contact, short between adjacent pins

### Step 3: Analyze Circuit Behavior per Failure

- For each component-failure mode combination:
  - Modify the circuit model to reflect the failure
  - Determine the resulting voltages at all accessible parts and patient connections
  - Determine the resulting currents through all patient paths
  - Determine the resulting temperatures of adjacent components (power dissipation redistribution)
  - Identify any new hazards created by the failure (not just degradation of existing protection)
- Use worst-case analysis: maximum mains voltage, maximum load, end-of-life component values for all non-failed components

### Step 4: Assess Remaining Protection

- For each failure scenario, evaluate:
  - **Leakage current** — Does any leakage type exceed the SFC limits in Table 3? (Use the SFC column, not NC)
  - **Isolation** — Is at least 1 MOPP still maintained between hazardous voltages and patient connections?
  - **Temperature** — Does any accessible surface exceed the temperature limits in Table 24? Does any component exceed its rated temperature?
  - **Mechanical** — Does the failure create a mechanical hazard (ejected parts, sharp edges from melted components)?
  - **Fire** — Could the failure cause sustained arcing or component ignition?
- Document which remaining protective measures still function and their adequacy

### Step 5: Classify Each Scenario

- **Safe** — All remaining protective measures maintain patient and operator safety within IEC 60601-1 limits. Quantitative evidence required (leakage values, temperature values, remaining MOPP count).
- **Conditionally safe** — Safety is maintained only if an additional condition is met (e.g., fuse clears within rated time, thermal cutout activates, operator intervention within specified time). Document the condition and its reliability.
- **Unsafe** — Remaining protective measures are insufficient. Patient or operator is exposed to hazard exceeding acceptable limits. Design change required.
- No scenario may be classified as "safe" without quantitative justification showing specific values versus specific limits

### Step 6: Recommend Design Changes

- For each unsafe scenario:
  - Propose a specific design change that eliminates or mitigates the hazard
  - Verify the proposed change does not introduce new failure modes or degrade other safety functions
  - Quantify the improvement (new leakage value, new MOPP count, new temperature)
- For each conditionally safe scenario:
  - Evaluate whether the condition is sufficiently reliable (e.g., fuse clearing time vs. thermal damage time)
  - If reliability is insufficient, treat as unsafe and propose design change
  - If reliability is sufficient, document the rationale and any required testing
- Common design change patterns:
  - Add redundant protection (second isolation barrier, redundant current limiter)
  - Uprate components (higher voltage rating, lower power dissipation, wider creepage)
  - Add fault detection (isolation monitoring, overcurrent detection with shutdown)
  - Change topology (replace single reinforced insulation with double insulation)

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct the circuit context and applied part classification, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Output Format

### Safety-Critical Component List

| Ref | Component | Safety Function | Rated Values | Failure Consequence if Unmitigated |
|-----|-----------|-----------------|--------------|-------------------------------------|
| T1 | Isolation transformer | 2 MOPP mains-to-secondary | 4kVac hipot, Cw=15pF | Patient exposed to mains |
| C_Y1 | Y1 capacitor | EMI filter, leakage path | 4.7nF, 250Vac Y1 | Increased patient leakage |

### Failure Mode Table

| Ref | Failure Mode | Circuit Effect | Resulting Hazard | Remaining Protection | Leakage/Voltage | Classification |
|-----|-------------|----------------|------------------|---------------------|-----------------|----------------|
| T1 | Insulation breakdown (short between windings) | Mains voltage on secondary | Patient exposed to mains | Optocoupler isolation (1 MOPP) | Patient leakage = 35uA | Conditionally safe |
| C_Y1 | Short circuit | Full mains on secondary earth | Increased earth leakage | Fuse F1 (clears in <10ms) | Earth leakage = 2.3A (transient) | Safe (fuse clears) |

### Unsafe Scenario Summary

| Scenario | Hazard | Why Remaining Protection is Insufficient | Required Design Change |
|----------|--------|------------------------------------------|------------------------|
| ... | ... | ... | ... |

### Design Change Recommendations

| Scenario | Proposed Change | Before | After | New Failure Modes Introduced | Verification Method |
|----------|----------------|--------|-------|------------------------------|---------------------|
| ... | ... | ...uA / ...MOPP | ...uA / ...MOPP | None / [describe] | [Test method per IEC 60601-1] |

## Handoff

- Hand off to leakage-current if detailed leakage current calculations are needed for any fault scenario (beyond worst-case estimates).
- Hand off to safety-analysis if the analysis reveals that the applied part classification or means of protection map needs revision.
- Hand off to Analog (front-end-design) if design changes affect the signal acquisition circuit topology.
- Hand off to Regulator (risk-management) if risk classification of failure scenarios requires formal ISO 14971 risk assessment.

## Quality Checks

- [ ] Every safety-critical component in the protection paths analyzed
- [ ] Both open and short failure modes evaluated for every component (plus drift where relevant)
- [ ] No scenario classified as "safe" without quantitative justification (specific values vs. specific limits)
- [ ] All unsafe scenarios have specific, actionable design change recommendations
- [ ] Design change recommendations verified to not introduce new failure modes
- [ ] Analysis covers both patient hazards and operator hazards
- [ ] Conditionally safe scenarios have documented reliability justification for the required condition
- [ ] Failure mode table traces from component failure through circuit effect to patient/operator hazard

## Evolution Notes
<!-- Observations appended after each use -->
