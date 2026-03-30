---
name: defibrillation-protection
department: analog
description: "Design defibrillation withstand protection for patient-connected analog circuits per IEC 60601-1 Clause 8.5.5"
version: 1
triggers:
  - defibrillation
  - defib protection
  - high voltage
  - CF applied part
  - energy clamping
  - surge
  - patient protection
---

# Defibrillation Protection

## Purpose

Design defibrillation withstand protection for patient-connected analog circuits. Ensure the signal chain survives repeated defibrillation pulses per IEC 60601-1 Clause 8.5.5, recovers within clinically acceptable time, and maintains measurement accuracy post-event.

## Scope Constraints

- CF (cardiac floating) applied parts requiring defibrillation withstand
- BF applied parts where defibrillation withstand is specified
- Covers protection circuit design from patient electrode to first active IC
- Does not cover creepage/clearance requirements (refer to isolation/safety skill)
- Does not cover defibrillator design — only protection of monitoring circuits

## Inputs

- Applied part classification: CF or BF with defibrillation withstand
- Defibrillation test waveform: standard IEC 60601-1 (360J/50 ohm) or custom
- Number of test applications: standard is 15 (10 same polarity + 5 reversed)
- Signal chain input circuit: schematic showing first active components
- Downstream IC absolute maximum ratings: voltage, current, ESD
- Recovery time requirement: clinical context (monitoring during/after resuscitation)
- Existing protection elements (if retrofitting)

## Input Sanitization

- Reject if applied part classification is not specified — protection requirements differ for B, BF, CF
- Verify defibrillation energy level (360J is standard; some regions use 200J biphasic)
- If downstream IC part numbers are missing, require absolute maximum voltage ratings at minimum
- Confirm whether device must maintain monitoring during defibrillation or only recover after
- Flag if no recovery time requirement is stated — default to < 5 seconds per typical clinical expectation

## Procedure

1. **Define defibrillation test waveform.** Per IEC 60601-1 Clause 8.5.5.1: 360J discharged into 50 ohm yields ~5kV peak open-circuit. Waveform is a damped sinusoid. Calculate peak voltage and current at the applied part terminals. Document test configuration: direct application between applied parts and earth, and between applied parts.

2. **Design protection network.** Layer protection in stages: (a) Gas discharge tube (GDT) or spark gap as primary clamp — fast response, high energy handling. (b) Current-limiting resistors — limit peak current to downstream components. (c) TVS diodes or MOVs as secondary clamp — clamp residual voltage below IC damage threshold. (d) Optional: back-to-back diode clamps to supply rails at IC input. Calculate component values: R_limit = V_peak_after_GDT / I_max_allowed.

3. **Calculate peak voltage and current at each protection stage.** Model the protection network as a voltage divider during defibrillation. Stage 1: voltage across GDT during spark-over, current through GDT. Stage 2: voltage across current-limiting resistor, power dissipation. Stage 3: voltage at TVS clamp point, current through TVS. Stage 4: residual voltage and current at IC input pins. Verify all values remain within component ratings.

4. **Verify component ratings for repetitive pulsed energy.** GDT: verify impulse spark-over voltage, arc voltage, surge current rating for the specified waveform. Current-limiting resistor: calculate single-pulse energy (E = integral of I^2*R*dt), verify pulse derating curve for 15 applications. TVS: verify peak pulse power rating (Ppk), clamping voltage at peak current, repetitive pulse capability. All components must survive 15 applications without degradation.

5. **Analyze post-defibrillation recovery.** Calculate signal path impedance added by protection components (current-limiting resistors add to source impedance). Evaluate offset voltage: GDT arc residue, TVS leakage change, capacitor charge. Determine recovery time: RC time constants of protection network with input coupling capacitors. Verify signal path accuracy post-recovery: gain error from added resistance, bandwidth reduction.

6. **Verify downstream component survival.** Map the maximum residual voltage at each IC input pin. Compare against absolute maximum ratings with margin (use 80% of abs max as design target). Verify ESD structures in ICs do not latch up from sustained over-voltage. Check for secondary damage paths: power supply pins, digital interface pins, reference pins. Document any components that require additional local protection.

### Progress Checklist

- [ ] Defibrillation waveform defined with peak voltage/current
- [ ] Multi-stage protection network designed
- [ ] Peak voltage/current calculated at each stage
- [ ] Component pulse ratings verified for 15 applications
- [ ] Post-defibrillation recovery time analyzed
- [ ] Downstream IC survival verified against abs max ratings

### Compaction Resilience

If context is compacted mid-design, the Energy Absorption Budget Table and Component Rating Verification Table together capture the complete protection design state.

## Output Format

```markdown
## Defibrillation Protection: [Application Name]

### Test Waveform
- Standard: IEC 60601-1 Clause 8.5.5
- Energy: [J]
- Peak open-circuit voltage: [kV]
- Number of applications: [N]

### Protection Circuit Schematic
[ASCII schematic: Electrode -- GDT -- R_limit -- TVS -- IC Input]

### Energy Absorption Budget
| Stage | Component | Peak V | Peak I | Energy (J) | Rating (J) | Margin |
|---|---|---|---|---|---|---|
| Primary clamp | | | | | | |
| Current limiter | | | | | | |
| Secondary clamp | | | | | | |

### Component Stress Analysis
| Component | Parameter | Stress | Rating | Derating | Pass/Fail |
|---|---|---|---|---|---|
| | | | | | |

### Peak Voltage/Current at Each Stage
| Node | Peak Voltage (V) | Peak Current (mA) | Duration |
|---|---|---|---|
| Electrode terminal | | | |
| After GDT | | | |
| After R_limit | | | |
| At TVS clamp | | | |
| At IC input | | | |

### Recovery Time Analysis
- Protection network time constant: [ms]
- Input coupling recovery: [ms]
- Offset settling: [ms]
- **Total recovery time: [s]**
- Requirement: [s]
- **Pass / Fail**

### Component Rating Verification
| Component | Part Number | Critical Rating | Test Condition | Margin |
|---|---|---|---|---|
| | | | | |

### Test Recommendations
1. [Bench test with defibrillation simulator]
2. [Post-test functional verification]
3. [Repetitive application endurance test]
```

## Handoff

- If front-end topology needs redesign to accommodate protection impedance, handoff to **front-end-design** skill
- If noise budget is affected by added protection resistance, handoff to **noise-analysis** skill
- If creepage/clearance analysis is needed, flag for safety/isolation review
- If component sourcing is constrained, flag for supply chain review

## Quality Checks

1. GDT spark-over voltage is appropriate — low enough to protect, high enough to not false-trigger from common-mode voltages
2. Current-limiting resistor power rating includes pulse derating curve analysis, not just continuous rating
3. TVS clamping voltage at peak current is below downstream IC absolute maximum ratings with 20% margin
4. Recovery time meets clinical requirements for the intended monitoring application
5. All protection components have documented pulse ratings from manufacturer datasheets
6. Protection network does not degrade signal path performance beyond acceptable limits (noise, bandwidth, CMRR)
7. Both polarities of defibrillation pulse are addressed (10 same polarity + 5 reversed)
8. Secondary damage paths verified (supply pins, digital pins, reference pins)

## Evolution Notes

- Future versions may include specific GDT/TVS component recommendation database
- Consider adding biphasic defibrillation waveform analysis (IEC 60601-2-27)
- Add thermal analysis for repetitive pulse heating of protection components
