---
name: power-integrity
department: tracer
description: "Design and validate power delivery network from voltage regulator output to IC power pins"
version: 1
triggers:
  - PDN
  - power integrity
  - decoupling
  - target impedance
  - ripple
  - voltage drop
  - power plane
  - capacitor
---

# power-integrity

## Purpose

Design and validate power delivery network from voltage regulator output to IC power pins. Produce a complete PDN design with target impedance analysis, decoupling network, and placement constraints.

## Scope Constraints

- Board-level PDN only — does not cover voltage regulator selection or control loop design.
- Analytical impedance modeling — does not perform full 3D EM simulation of power planes.
- Assumes regulator output is stable — input filtering is covered by emc-strategy skill.
- Handles up to 20 independent power domains — beyond this, break into subsystem analyses.

## Inputs

- **Power domains:** Voltage, tolerance band (e.g., 3.3V +/- 5%), nominal current, peak transient current.
- **IC specifications:** Power pin count, maximum di/dt, recommended decoupling from datasheet.
- **Frequency range of interest:** DC to maximum frequency (typically clock frequency or data rate / 2).
- **Board constraints:** Available area near IC, layer count, power plane assignment from stackup.
- **Regulator characteristics:** Output impedance, bandwidth, output capacitor requirements.

## Input Sanitization

- Reject requests missing voltage and current specifications — these are mandatory.
- If transient current is not specified, estimate from IC datasheet maximum current with 50% step assumption and flag.
- If frequency range is unspecified, default to DC through 1 GHz and flag.
- If regulator bandwidth is unknown, assume 100 kHz crossover and flag.

## Procedure

1. **Define PDN requirements.** For each power domain, document: voltage, tolerance, maximum steady-state current, maximum transient current (di/dt), and frequency range. Calculate allowable voltage ripple from tolerance band.

2. **Calculate target impedance.** Ztarget = V_tolerance / I_transient. This is the maximum allowable PDN impedance across the entire frequency range. Example: 3.3V +/- 5% with 500 mA transient -> Ztarget = 0.165V / 0.5A = 330 mohm.

3. **Design decoupling capacitor network.** Select capacitors for three frequency bands: bulk (electrolytic/tantalum, 100uF-1000uF) for regulator bandwidth to ~100 kHz, mid-frequency (ceramic 1uF-10uF) for 100 kHz to ~10 MHz, high-frequency (ceramic 10nF-100nF) for 10 MHz to hundreds of MHz. Account for capacitor ESR and ESL in each band.

4. **Calculate PDN impedance vs. frequency.** Model each capacitor as series RLC (C, ESR, ESL). Combine in parallel with power plane capacitance. Verify impedance stays below Ztarget across the full frequency range. Identify and address anti-resonance peaks where parallel capacitors interact.

5. **Verify DC voltage drop.** Calculate IR drop from regulator output to the furthest load through power plane copper. Account for via resistance, trace resistance, and plane sheet resistance. Verify drop is within the voltage tolerance budget.

6. **Specify placement constraints.** Define maximum distance from IC power pins for each capacitor tier: high-frequency caps within 2 mm, mid-frequency within 10 mm, bulk within 25 mm. Specify via count and size for capacitor connections to planes. Define keep-out zones.

### Progress Checklist

- [ ] Power domain requirements documented
- [ ] Target impedance calculated for each domain
- [ ] Decoupling network designed (bulk, mid, high-freq)
- [ ] PDN impedance vs. frequency verified below target
- [ ] DC IR drop analysis complete
- [ ] Placement constraints specified

### Compaction Resilience

If context is compacted mid-task, reconstruct from the Power Domain Requirements Table and Decoupling Network Design table. Target impedance can be recalculated from requirements. Placement constraints derive from the network design.

## Output Format

```markdown
## Power Integrity Analysis: [Project Name]

### Power Domain Requirements Table
| Domain | Voltage | Tolerance | Max Steady Current | Max Transient Current | Frequency Range |
|--------|---------|-----------|--------------------|-----------------------|-----------------|

### Target Impedance Calculation
| Domain | V_tolerance (V) | I_transient (A) | Ztarget (mohm) |
|--------|-----------------|------------------|----------------|

### Decoupling Network Design
| Domain | Tier | Value | Qty | ESR (mohm) | ESL (nH) | Effective Range | Package |
|--------|------|-------|-----|------------|----------|-----------------|---------|

### PDN Impedance vs. Frequency
[Description of impedance profile with key frequencies noted]
- Regulator bandwidth: [freq] — regulator controls impedance below this
- Bulk cap range: [freq range] — impedance dominated by bulk caps
- Mid-freq range: [freq range] — ceramic mid-freq caps dominant
- High-freq range: [freq range] — MLCC high-freq caps dominant
- Anti-resonance peaks: [frequencies and magnitudes]
- Margin to Ztarget: [worst-case margin in dB]

### IR Drop Analysis
| Domain | Regulator Output | Furthest Load | Path Resistance (mohm) | Voltage Drop (mV) | Remaining Budget (mV) |
|--------|-----------------|---------------|----------------------|--------------------|-----------------------|

### Placement Constraints
| Cap Tier | Max Distance from IC (mm) | Via Count | Via Size | Pad Geometry |
|----------|--------------------------|-----------|----------|-------------|
| High-freq | 2 | 2 per pad | 0.2 mm drill | Direct to plane |
| Mid-freq | 10 | 2 per pad | 0.25 mm drill | Short trace OK |
| Bulk | 25 | 4 minimum | 0.3 mm drill | Via array |
```

## Handoff

- From **stackup-design**: Receive power plane assignments, dielectric thicknesses, and copper weights for plane capacitance and resistance calculations.
- From **emc-strategy**: Receive switching frequency constraints that affect decoupling strategy.
- To **other council agents**: Provide power pin requirements and placement constraints for component placement and routing.

## Quality Checks

1. Target impedance met across the full frequency range from DC to maximum frequency of interest.
2. Anti-resonance peaks between capacitor tiers identified and addressed (peaks below Ztarget).
3. Capacitor placement distance from IC power pins specified in mm with explicit rationale.
4. Bulk capacitor ESR verified within voltage regulator stability requirements (not too low for ceramic-sensitive regulators).
5. Power plane via sizing adequate for maximum DC current — current density below 30 A/mm^2.
6. Analog power supplies have separate filtering from digital — LC filter or ferrite bead isolation specified.
7. Capacitor quantity accounts for derating — voltage derating for MLCC Class II ceramics.
8. Mounting inductance (pad-to-via-to-plane) included in ESL estimates, not just component ESL.

## Evolution Notes

- Future versions may integrate with SPICE-based PDN simulation for more accurate impedance modeling.
- Frequency-dependent capacitor models (vendor S-parameter data) to replace ideal RLC models.
- Multi-rail simultaneous switching noise (SSN) analysis planned for high-pin-count ICs.
