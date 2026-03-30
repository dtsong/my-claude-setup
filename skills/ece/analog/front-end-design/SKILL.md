---
name: front-end-design
department: analog
description: "Design biopotential or sensor analog front-end topology from electrode/transducer to ADC input"
version: 1
triggers:
  - front end
  - biopotential
  - ECG
  - EEG
  - electrode
  - instrumentation amplifier
  - analog front end
  - ADS1299
  - signal conditioning
---

# Front-End Design

## Purpose

Design a complete analog front-end topology from electrode or transducer to ADC input. Covers input protection, signal conditioning, gain staging, filtering, common-mode rejection, and ADC interfacing for biopotential and sensor applications.

## Scope Constraints

- Electrode/transducer to ADC input (inclusive of ADC selection, exclusive of digital processing)
- Biopotential signals: ECG, EEG, EMG, EOG, ECoG
- Sensor signals: strain gauge, thermocouple, RTD, pressure transducer, photodiode
- Does not cover wireless telemetry, digital signal processing, or firmware
- For defibrillation protection on CF applied parts, handoff to **defibrillation-protection** skill

## Inputs

- Signal source: type (electrode, sensor), impedance, amplitude range, bandwidth
- Application context: clinical/research/consumer, regulatory class, patient contact type (B, BF, CF)
- Channel count and configuration (single-ended, differential, reference scheme)
- Performance requirements: resolution (uV or bits), noise floor, CMRR, bandwidth
- Power and size constraints: supply voltage, current budget, board area
- Environmental: temperature range, interference environment (clinical, ambulatory, industrial)

## Input Sanitization

- Reject if signal source type is undefined — topology depends entirely on source characteristics
- If no CMRR requirement stated, apply defaults: ECG >= 100 dB, EEG >= 120 dB, EMG >= 90 dB
- If resolution requirement is in bits, convert to uV using expected signal amplitude
- Verify patient contact classification if medical application (B, BF, or CF)
- Flag if channel count exceeds 8 without specifying integrated AFE preference

## Procedure

1. **Characterize signal source.** Document source impedance (and mismatch range), signal amplitude (min, typical, max), bandwidth (diagnostic vs. monitoring), common-mode voltage range, and electrode configuration (monopolar, bipolar, reference). For biopotentials, specify electrode type (Ag/AgCl wet, dry, capacitive).

2. **Select front-end topology.** Choose between: discrete instrumentation amplifier (INA333, AD8421, etc.), integrated analog front end (ADS1299, ADS1298, MAX30003), or custom multi-stage design. Decision factors: channel count, noise requirements, integration level, power budget, and cost target. Document trade-offs for the selected approach.

3. **Design input protection and filtering.** ESD protection (TVS diodes, series resistors). RFI filtering (capacitors at input, common-mode chokes). DC blocking if required (AC-coupled vs. DC-coupled with digital HPF). For CF applied parts, include defibrillation protection (handoff to defibrillation-protection skill). Calculate input filter cutoff and verify it does not attenuate the signal band.

4. **Design gain and filtering stages.** Set first-stage gain to minimize total input-referred noise (typically 10-100x for biopotentials). Design anti-aliasing filter: order and cutoff frequency to achieve >= 60 dB attenuation at Nyquist. Choose filter topology (Sallen-Key, MFB, or integrated). Verify signal levels do not clip at any stage across full dynamic range.

5. **Design driven-right-leg or common-mode feedback circuit.** For biopotential applications: DRL circuit inverts and feeds back common-mode signal to patient reference electrode. Set DRL bandwidth (typically < 1 kHz) and current limit (< 50 uA per IEC 60601-1). For non-biopotential: common-mode feedback or reference buffer as needed. Analyze CMRR improvement from DRL.

6. **Specify ADC interface.** Select ADC: type (sigma-delta, SAR), resolution, sampling rate, input range. Match front-end output swing to ADC input range. Specify reference voltage source (internal, external precision reference). Design anti-aliasing for selected sampling rate. Verify settling time if multiplexed. Document digital interface (SPI, I2C, parallel).

### Progress Checklist

- [ ] Signal source fully characterized
- [ ] Front-end topology selected with trade-off analysis
- [ ] Input protection and filtering designed
- [ ] Gain and anti-aliasing filter stages designed
- [ ] DRL or common-mode feedback circuit designed
- [ ] ADC interface specified and input range matched

### Compaction Resilience

If context is compacted mid-design, the Component Selection Table and Performance Summary contain all critical design parameters needed to resume or hand off.

## Output Format

```markdown
## Front-End Design: [Application Name]

### Signal Source Characterization
| Parameter | Value |
|---|---|
| Source type | |
| Source impedance | |
| Signal amplitude | |
| Bandwidth | |
| Common-mode voltage | |
| Electrode configuration | |

### Front-End Topology
[ASCII block diagram: Electrodes -> Protection -> INA/AFE -> Filter -> ADC]

**Selected approach:** [Discrete / Integrated AFE / Custom]
**Rationale:** [Why this topology]

### Component Selection Table
| Stage | Component | Key Specification | Rationale |
|---|---|---|---|
| | | | |

### Input Protection Scheme
- ESD: [components, ratings]
- RFI: [filter topology, cutoff]
- DC blocking: [method]
- Defibrillation: [if applicable, reference defib-protection output]

### Gain and Filter Chain
| Stage | Gain | Bandwidth | Noise Density | Output Swing |
|---|---|---|---|---|
| | | | | |

### DRL / Common-Mode Feedback
- Topology: [circuit description]
- Bandwidth: [Hz]
- Current limit: [uA]
- CMRR improvement: [dB]

### ADC Interface Specification
| Parameter | Value |
|---|---|
| ADC | |
| Type | |
| Resolution | |
| Sampling rate | |
| Input range | |
| Reference | |
| Interface | |

### Performance Summary
| Metric | Achieved | Required |
|---|---|---|
| Input-referred noise | | |
| CMRR | | |
| Bandwidth | | |
| Dynamic range | | |
| Power consumption | | |
```

## Handoff

- If defibrillation protection required (CF applied part), load **defibrillation-protection** skill
- If detailed noise analysis needed for component selection, load **noise-analysis** skill
- If PCB layout guidance needed for noise performance, flag for layout review
- If power supply design affects PSRR, flag for power integrity review

## Quality Checks

1. Input-referred noise meets signal resolution requirements with margin
2. CMRR adequate for expected common-mode interference at mains frequency and harmonics
3. Anti-aliasing filter provides >= 60 dB attenuation at Nyquist frequency
4. Input protection survives defibrillation if CF applied part
5. DRL current limit complies with IEC 60601-1 (< 50 uA under single fault)
6. Signal levels verified at each stage — no clipping across full dynamic range
7. Power supply rejection ratio evaluated at mains frequency
8. Input impedance does not load the signal source beyond acceptable levels

## Evolution Notes

- Future versions may include integrated AFE register configuration templates
- Consider adding differential-to-single-ended conversion stage guidance
- Add electrode impedance measurement circuit design as optional sub-procedure
