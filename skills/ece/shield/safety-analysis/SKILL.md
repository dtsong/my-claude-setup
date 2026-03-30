---
name: safety-analysis
department: "shield"
description: "Use when performing IEC 60601-1 safety analysis for a medical device circuit design. Covers applied parts classification, hazardous voltage identification, means of protection mapping, MOPP/MOOP verification, and creepage/clearance analysis. Do not use for detailed leakage current calculations (use leakage-current) or systematic component failure analysis (use single-fault-analysis)."
version: 1
triggers:
  - "safety"
  - "IEC 60601"
  - "applied part"
  - "classification"
  - "MOPP"
  - "MOOP"
  - "isolation"
  - "hazard"
  - "creepage"
  - "clearance"
  - "means of protection"
---

# Safety Analysis

## Purpose

Perform a comprehensive IEC 60601-1 safety analysis for a medical device circuit design, systematically verifying applied parts classification, means of protection, and insulation coordination.

## Scope Constraints

Analyzes circuit designs against IEC 60601-1 (3rd edition + amendments) safety requirements. Does not perform detailed leakage current calculations (hand off to leakage-current skill) or systematic component failure analysis (hand off to single-fault-analysis skill). Produces a structured safety analysis report suitable for inclusion in a technical file for a notified body.

## Inputs

- Circuit schematic or block diagram
- Intended use statement (patient contact type, body region, clinical application)
- Mains supply voltage and frequency (or battery specification)
- Environmental conditions (pollution degree, altitude, temperature range)
- Enclosure classification (Class I or Class II)
- Existing applied parts classification (if predetermined by system-level risk analysis)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Applied parts classified
- [ ] Step 2: Hazardous voltages identified
- [ ] Step 3: Means of protection mapped
- [ ] Step 4: MOPP/MOOP counts verified
- [ ] Step 5: Creepage/clearance verified
- [ ] Step 6: Findings documented

### Step 1: Classify Applied Parts

- Identify all patient connections (electrodes, sensors, fluid paths, conductive accessible parts that contact the patient)
- For each patient connection, determine the applied part type:
  - **Type B** — No direct patient contact, or contact that is not relied upon for diagnosis/treatment. Example: enclosure of a bedside monitor.
  - **Type BF** — Patient contact required for function, not direct cardiac. Example: ECG surface electrodes, SpO2 finger clip.
  - **Type CF** — Direct cardiac contact or intracardiac application. Example: pacing leads, intracardiac catheters, direct myocardial electrodes.
- Document the classification rationale citing the intended use and IEC 60601-1 Clause 3.10 (applied part definition)
- Determine if defibrillation withstand is required (CF applied parts per Clause 8.5.5; BF if specified)

### Step 2: Identify Hazardous Voltages

- Enumerate all voltage sources: mains input, internal DC rails, any voltage exceeding 25Vac or 60Vdc (Clause 8.4.2)
- For each hazardous voltage, document: source, nominal value, maximum value (including tolerance and transient), and energy storage capacity
- Identify all accessible parts (conductive parts that can be touched by operator or patient)
- Identify all signal input/output ports (SIP/SOPs) and their connection to internal circuits

### Step 3: Map Means of Protection

- For every path from a hazardous voltage to a patient connection: identify each insulation barrier, air gap, creepage distance, or protective earth connection
- Rate each barrier: 1 MOPP (means of patient protection) or 1 MOOP (means of operator protection)
- A single barrier providing reinforced insulation = 2 MOPP or 2 MOOP
- Protective earth counts as 1 MOOP for operator protection (not MOPP)
- Draw or describe the protection map showing hazard sources, barriers, and patient/operator accessible parts

### Step 4: Verify MOPP/MOOP Counts

- Compare MOPP/MOOP counts against Table 3 requirements:
  - Type B: 1 MOPP between mains and patient connection
  - Type BF: 2 MOPP between mains and patient connection (or 1 MOPP + protective earth for Class I)
  - Type CF: 2 MOPP between mains and patient connection, 1 MOPP between secondary circuits and patient connection
- For Class I equipment: verify protective earth path meets Clause 8.6 requirements (impedance, current capacity)
- Flag any path with insufficient MOPP/MOOP count as a non-conformance

### Step 5: Verify Creepage and Clearance

- For each insulation barrier, determine the working voltage (rms or DC, across the barrier)
- Look up required creepage and clearance from:
  - Table 4 (clearance for transient voltages)
  - Table 11 (creepage for working voltage, pollution degree, material group)
  - Table 13 (additional requirements for reinforced insulation)
- Apply altitude derating if operating above 2000m (Clause 8.9.1.11)
- Measure or estimate actual creepage and clearance from the PCB layout or mechanical design
- Flag any distance below the required minimum as a non-conformance

### Step 6: Document Findings

- Compile all findings into the output format below
- For each non-conformance: state the requirement, the actual value, the gap, and a recommended corrective action
- Identify items requiring handoff to leakage-current or single-fault-analysis skills

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct the design parameters and applied part information, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Output Format

### Applied Part Classification Table

| Patient Connection | Type | Rationale | Defib Withstand Required |
|--------------------|------|-----------|--------------------------|
| ... | B / BF / CF | [Clause reference + clinical justification] | Yes / No |

### Hazardous Voltage Inventory

| Source | Nominal | Maximum | Energy | Location |
|--------|---------|---------|--------|----------|
| ... | ...Vrms | ...Vrms | ...J | [Component/net reference] |

### Means of Protection Map

| Path (From -> To) | Barrier 1 | Barrier 2 | Total MOPP | Required MOPP | Status |
|--------------------|-----------|-----------|------------|---------------|--------|
| Mains -> Patient electrode | [Transformer] 1 MOPP | [Optocoupler] 1 MOPP | 2 MOPP | 2 MOPP (CF) | PASS |

### Creepage/Clearance Verification Table

| Location | Working Voltage | Required Clearance | Actual Clearance | Required Creepage | Actual Creepage | Status |
|----------|----------------|--------------------|--------------------|--------------------|--------------------|--------|
| ... | ...Vrms | ...mm (Table 4) | ...mm | ...mm (Table 11) | ...mm | PASS/FAIL |

### Non-Conformance List

| ID | Requirement | Actual | Gap | Recommended Corrective Action |
|----|-------------|--------|-----|-------------------------------|
| NC-01 | ... | ... | ... | ... |

## Handoff

- Hand off to leakage-current if detailed leakage current calculations are needed for any path identified in the means of protection map.
- Hand off to single-fault-analysis if safety-critical components are identified that require systematic failure mode evaluation.
- Hand off to Tracer (stackup-design) if PCB layout changes are needed to achieve required creepage/clearance distances.

## Quality Checks

- [ ] Every applied part classified with clinical rationale and IEC clause reference
- [ ] All hazardous voltages identified (including internal rails exceeding 25Vac/60Vdc)
- [ ] MOPP/MOOP counts verified for every path from hazardous voltage to patient connection
- [ ] MOOP counts verified for every path from hazardous voltage to operator accessible parts
- [ ] Creepage distances account for pollution degree (environment of intended use)
- [ ] Clearance distances account for altitude derating if applicable
- [ ] Defibrillation withstand requirement identified for CF (and BF if applicable) applied parts
- [ ] All non-conformances have recommended corrective actions

## Evolution Notes
<!-- Observations appended after each use -->
