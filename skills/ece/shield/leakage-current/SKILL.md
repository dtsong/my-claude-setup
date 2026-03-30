---
name: leakage-current
department: "shield"
description: "Use when analyzing patient, touch, and earth leakage current paths under normal and single-fault conditions. Covers impedance network modeling, capacitive coupling through isolation barriers, frequency-weighted measurements, and comparison against IEC 60601-1 Table 3 limits. Do not use for general safety analysis (use safety-analysis) or systematic component failure evaluation (use single-fault-analysis)."
version: 1
triggers:
  - "leakage current"
  - "patient current"
  - "touch current"
  - "earth leakage"
  - "normal condition"
  - "single fault"
  - "Y-capacitor"
  - "isolation impedance"
---

# Leakage Current Analysis

## Purpose

Analyze patient, touch, and earth leakage current paths under normal and single-fault conditions, verifying compliance with IEC 60601-1 Table 3 limits for the applicable applied part classification.

## Scope Constraints

Models leakage current paths through impedance networks including capacitive coupling through isolation barriers. Does not perform general safety analysis (hand off to safety-analysis skill) or systematic component FMEA (hand off to single-fault-analysis skill). Requires applied part classification as input — if not yet determined, request safety-analysis first.

## Inputs

- Applied part classification (Type B, BF, or CF) from safety-analysis
- Circuit schematic with isolation barrier details (transformer interwinding capacitance, optocoupler capacitance, PCB parasitic capacitance)
- Y-capacitor values and locations
- Mains voltage and frequency (or range)
- Protective earth impedance (for Class I equipment)
- Patient connection circuit topology
- Component datasheets for isolation components (transformer, optocoupler, isolator IC)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Conductive paths identified
- [ ] Step 2: Impedance network modeled
- [ ] Step 3: Normal condition leakage calculated
- [ ] Step 4: Single-fault condition leakage calculated
- [ ] Step 5: Values compared against Table 3 limits
- [ ] Step 6: Mitigation recommendations provided

### Step 1: Identify Conductive Paths

- Trace all conductive paths from patient connections to: earth, mains (L and N), and other accessible parts
- Include intentional paths (Y-capacitors, EMI filter components) and parasitic paths (transformer interwinding capacitance, PCB trace coupling, enclosure capacitance)
- Identify all three leakage types per IEC 60601-1 Clause 8.7:
  - **Earth leakage current** — from mains part through protective earth conductor
  - **Touch current** — through an accessible part (not applied part) to earth via a person
  - **Patient leakage current** — through the patient connection to earth via the patient (from the applied part), including patient auxiliary current between applied parts
- Draw the leakage path diagram showing all paths with component references

### Step 2: Model Impedance Network

- For each path, build an impedance model at the mains frequency (50/60Hz) and relevant harmonics
- Key impedance elements:
  - Y-capacitors: use rated capacitance + tolerance (worst case = maximum capacitance)
  - Transformer interwinding capacitance: from datasheet or estimate (typically 10-100pF for medical-grade)
  - Optocoupler/isolator capacitance: from datasheet (typically 0.5-2pF)
  - PCB parasitic capacitance: estimate from trace geometry and board stackup (typically 1-10pF)
  - Protective earth impedance: maximum allowed per Clause 8.6 (typically <100 milliohms)
- Use worst-case values: maximum capacitance, minimum impedance for paths that increase leakage

### Step 3: Calculate Normal Condition Leakage

- Calculate earth leakage current at maximum mains voltage (264Vac for 230V systems) through all paths to protective earth
- Calculate touch current at maximum mains voltage through all accessible parts
- Calculate patient leakage current at maximum mains voltage through all patient connections
- For AC leakage: apply IEC 60601-1 frequency weighting if applicable (DC and frequencies up to 1kHz are weighted equally; above 1kHz the limit increases proportionally)
- Document calculation for each path showing: voltage source, impedance elements, resulting current

### Step 4: Calculate Single-Fault Condition Leakage

- **SFC 1 — Open protective earth:** Remove earth connection. Recalculate touch current and patient leakage current (earth leakage is not applicable).
- **SFC 2 — Open neutral (or open one supply conductor):** Apply full mains voltage between L and the now-floating neutral. Recalculate all leakage currents — this often creates new paths through Y-capacitors.
- **SFC 3 — Mains voltage on accessible parts:** Apply mains voltage to any accessible conductive part. Calculate resulting patient leakage current.
- **SFC 4 — Mains voltage on SIP/SOP:** Apply mains voltage to signal input/output ports. Calculate patient leakage current through the applied part.
- For each SFC: identify the worst-case leakage path and calculate the maximum current

### Step 5: Compare Against Table 3 Limits

- IEC 60601-1 Table 3 limits (DC values; AC values are the same for frequencies up to 1kHz):

| Leakage Type | Type B NC | Type B SFC | Type BF NC | Type BF SFC | Type CF NC | Type CF SFC |
|-------------|-----------|------------|------------|-------------|------------|-------------|
| Earth | 5mA | 10mA | 5mA | 10mA | 5mA | 10mA |
| Touch | 100uA | 500uA | 100uA | 500uA | 100uA | 500uA |
| Patient | 100uA | 500uA | 100uA | 500uA | 10uA | 50uA |

- Calculate margin for each measurement: (Limit - Actual) / Limit x 100%
- Flag any value exceeding the limit or with margin below 20% (insufficient design margin)

### Step 6: Mitigation Recommendations

- For any exceedance or insufficient margin:
  - Reduce Y-capacitor values (trade-off: may increase EMI emissions)
  - Add common-mode chokes (increases impedance of leakage paths)
  - Use lower interwinding capacitance transformers (specify Cw requirement to transformer vendor)
  - Increase PCB isolation gap (reduces parasitic capacitance)
  - Add shield winding to transformer (redirects leakage current to earth instead of patient)
- Quantify the effect of each mitigation on the leakage budget

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct the applied part classification and circuit topology, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Output Format

### Leakage Path Diagram

```
[Annotated diagram showing all leakage paths with component references and impedance values]
```

### Impedance Model

| Path | Elements | Total Impedance at 50Hz | Total Impedance at 60Hz |
|------|----------|-------------------------|-------------------------|
| Mains L -> Patient via C_Y1, C_transformer | C_Y1=4.7nF, C_xfmr=22pF | ... | ... |

### Normal Condition Leakage Table

| Leakage Type | Path | Calculated Value | Limit | Margin | Status |
|-------------|------|------------------|-------|--------|--------|
| Earth | Via Y-caps to PE | ...mA | 5mA | ...% | PASS/FAIL |
| Touch | Via enclosure | ...uA | 100uA | ...% | PASS/FAIL |
| Patient | Via isolation barrier | ...uA | 10uA (CF) | ...% | PASS/FAIL |

### Single-Fault Condition Leakage Table

| SFC | Leakage Type | Path | Calculated Value | Limit | Margin | Status |
|-----|-------------|------|------------------|-------|--------|--------|
| Open earth | Touch | ... | ...uA | 500uA | ...% | PASS/FAIL |
| Open neutral | Patient | ... | ...uA | 50uA (CF) | ...% | PASS/FAIL |

### Margin Analysis

| Measurement | Worst-Case Value | Limit | Margin | Dominant Path | Risk Level |
|------------|-----------------|-------|--------|---------------|------------|
| ... | ... | ... | ...% | ... | HIGH/MEDIUM/LOW |

### Mitigation Recommendations

| Issue | Current Value | Target | Recommended Action | Expected Result |
|-------|--------------|--------|-------------------|-----------------|
| ... | ... | ... | ... | ... |

## Handoff

- Hand off to safety-analysis if applied part classification needs to be determined or revised.
- Hand off to single-fault-analysis if component failure modes (beyond the standard SFCs) could create additional leakage paths.
- Hand off to Tracer (stackup-design) if PCB layout changes are needed to reduce parasitic capacitance.
- Hand off to Analog (front-end-design) if Y-capacitor reduction affects EMC filter performance.

## Quality Checks

- [ ] All three leakage types analyzed (earth, touch, patient) under normal condition
- [ ] Single-fault conditions cover all required faults per Clause 8.7 (open earth, open neutral, mains on accessible parts, mains on SIP/SOP)
- [ ] Capacitive coupling through transformers included in impedance model with datasheet values
- [ ] Frequency-weighted measurements noted where applicable (>1kHz components)
- [ ] Y-capacitor values justified against both leakage budget and EMC requirements
- [ ] Worst-case mains voltage used (264Vac for 230V systems, 132Vac for 120V systems)
- [ ] Margin analysis identifies dominant leakage path for each measurement
- [ ] All exceedances have quantified mitigation recommendations

## Evolution Notes
<!-- Observations appended after each use -->
