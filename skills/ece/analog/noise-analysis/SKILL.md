---
name: noise-analysis
department: analog
description: "Build complete noise budget for an analog signal chain, identifying dominant contributors and optimization opportunities"
version: 1
triggers:
  - noise
  - SNR
  - noise budget
  - input-referred
  - spectral density
  - noise floor
  - resolution
  - dynamic range
---

# Noise Analysis

## Purpose

Build a complete noise budget for an analog signal chain. Identify every noise contributor, calculate input-referred noise, determine dominant sources, and recommend optimizations to meet SNR or ENOB targets.

## Scope Constraints

- Analog signal chains from source to ADC input (or ADC inclusive)
- Frequency range: DC to 100 MHz (beyond 100 MHz, refer to RF department)
- Does not cover EMI/EMC compliance testing — only intrinsic circuit noise
- Does not design the signal chain — analyzes an existing or proposed topology

## Inputs

- Signal parameters: amplitude range (Vpp or Vrms), bandwidth of interest (fL to fH)
- Required performance: target SNR (dB) or target resolution (ENOB)
- Signal chain topology: block diagram or schematic with gain stages
- Component selections: op-amp part numbers, resistor values, ADC part number
- Operating conditions: temperature range, supply voltages

## Input Sanitization

- Reject requests without defined signal bandwidth — noise is meaningless without bandwidth
- If component part numbers are missing, flag as assumption and use representative devices
- Verify units consistency: V vs. mV vs. uV, Hz vs. kHz, nV/rtHz vs. uV/rtHz
- Confirm whether 1/f noise region is relevant (signal bandwidth extending below 10 Hz)

## Procedure

1. **Define signal parameters.** Extract signal amplitude range, bandwidth of interest (fL, fH), and required SNR or ENOB. Convert ENOB to equivalent noise floor if needed: V_noise_rms = V_FSR / (6.02 * ENOB + 1.76 dB).

2. **Model each gain stage.** For every active stage, identify noise sources: op-amp voltage noise (en), op-amp current noise (in), resistor thermal noise (4kTR). For each passive element, calculate thermal noise contribution. Note 1/f corner frequencies.

3. **Calculate input-referred noise density.** For each stage, refer noise to the signal chain input by dividing by the cumulative gain preceding that stage. Plot noise density vs. frequency for each contributor.

4. **Integrate noise over signal bandwidth.** For white noise: V_rms = en * sqrt(BW * pi/2) accounting for noise bandwidth factor. For 1/f noise: V_rms = en_1Hz * sqrt(ln(fH/fL)). Account for filter order effects on noise bandwidth (NBW = f_3dB * pi/2 for 1st order, etc.).

5. **Compute total RSS noise and resulting SNR/ENOB.** RSS all input-referred noise contributions. Calculate SNR = 20*log10(V_signal_rms / V_noise_rms). Calculate ENOB = (SNR - 1.76) / 6.02. Include ADC quantization noise: V_q = LSB / sqrt(12).

6. **Identify dominant contributors and recommend optimization.** Rank noise sources by percentage contribution. For dominant sources, recommend: gain redistribution, component upgrade, bandwidth reduction, or topology change. Quantify improvement for each recommendation.

### Progress Checklist

- [ ] Signal parameters defined (amplitude, bandwidth, target SNR/ENOB)
- [ ] All gain stages modeled with noise sources
- [ ] Input-referred noise calculated per stage
- [ ] Noise integrated over signal bandwidth
- [ ] Total RSS noise and SNR/ENOB computed
- [ ] Dominant contributors identified with optimization recommendations

### Compaction Resilience

If context is compacted mid-analysis, the output tables contain all intermediate values needed to resume. The Noise Budget Table is the single artifact that captures the complete state of the analysis.

## Output Format

```markdown
## Noise Analysis: [Signal Chain Name]

### Signal Parameters
- Signal amplitude: [range, Vpp]
- Bandwidth of interest: [fL] to [fH]
- Target SNR: [dB] / Target ENOB: [bits]

### Signal Chain Block Diagram
[ASCII block diagram: Source -> Stage 1 (Gain, en) -> Stage 2 (Gain, en) -> ADC]

### Noise Source Inventory
| Stage | Source | Type | Density (nV/rtHz) | 1/f Corner (Hz) |
|---|---|---|---|---|
| | | | | |

### Noise Budget Table
| Source | Density at Input (nV/rtHz) | Integrated RMS (uVrms) | % Contribution |
|---|---|---|---|
| | | | |
| **Total (RSS)** | | **[total]** | **100%** |

### SNR / ENOB Summary
- Total input-referred noise: [uVrms]
- Signal RMS: [mVrms]
- SNR: [dB]
- ENOB: [bits]
- Margin vs. target: [dB or bits]

### Dominant Contributors
1. [Source] — [%] of total noise. [Why it dominates.]
2. [Source] — [%] of total noise.

### Optimization Recommendations
| Recommendation | Expected Improvement | Trade-off |
|---|---|---|
| | | |
```

## Handoff

- If noise is dominated by EMI pickup, handoff to **PCB layout / EMC** skill
- If ADC selection needs revisiting, handoff to **front-end-design** skill
- If power supply noise is a significant contributor, flag for power integrity review

## Quality Checks

1. Noise density values sourced from datasheet min/max specifications, not typical marketing values
2. 1/f noise included and correctly integrated for applications with bandwidth extending below 10 Hz
3. ADC quantization noise included as a noise floor contributor
4. Noise bandwidth calculation accounts for filter order (NBW != signal bandwidth)
5. Resistor thermal noise included for all signal-path resistors (especially feedback and gain-setting)
6. Current noise times source impedance included for high-impedance sources
7. RSS summation used (not linear addition) for uncorrelated noise sources
8. Gain distribution evaluated — first-stage gain should suppress downstream noise contributions

## Evolution Notes

- Future versions may integrate SPICE noise simulation cross-checks
- Consider adding correlated noise source handling (e.g., supply-coupled noise)
- Add support for switched-capacitor (kT/C) noise in sampled systems
