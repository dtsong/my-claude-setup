---
name: emc-strategy
department: tracer
description: "Develop board-level EMC/EMI compliance strategy for medical device per IEC 60601-1-2"
version: 1
triggers:
  - EMC
  - EMI
  - radiated
  - conducted
  - emissions
  - immunity
  - ESD
  - surge
  - IEC 61000
  - CISPR
  - shielding
  - filtering
---

# emc-strategy

## Purpose

Develop board-level EMC/EMI compliance strategy for medical device per IEC 60601-1-2. Produce an actionable EMC design rules document, filtering specifications, and pre-compliance test plan with expected margins.

## Scope Constraints

- Board-level and cable/connector-level EMC design only — does not cover system-level enclosure shielding design.
- Targets IEC 60601-1-2 (medical) as the primary standard — other standards (FCC, CE, automotive) require explicit request.
- Analytical harmonic analysis only — does not perform numerical EM simulation.
- Assumes the stackup is defined (or requests it from stackup-design skill).

## Inputs

- **Clock frequencies:** All oscillators, crystals, and clock generators with their frequencies.
- **Switching regulator frequencies:** Topology, switching frequency, input/output voltages.
- **High-speed interfaces:** USB, HDMI, Ethernet, DDR, SerDes — data rates and connector types.
- **External cables and connectors:** Type, length, shielded/unshielded.
- **Target standard and class:** IEC 60601-1-2 Group 1 Class A/B, CISPR 11/32.
- **Enclosure type:** Metal, plastic, hybrid — affects shielding assumptions.

## Input Sanitization

- Reject requests missing clock frequencies — these are the primary emission sources.
- If target standard is not specified, default to IEC 60601-1-2 Group 1 Class B (most restrictive) and flag.
- If enclosure type is unknown, assume plastic (worst case for shielding) and flag.

## Procedure

1. **Identify emission sources.** Catalog all clock oscillators, switching regulators, high-speed digital interfaces, and motor/actuator drivers. Record fundamental frequency and signal rise time for each.

2. **Calculate harmonic frequencies.** For each source, compute harmonics to at least 1 GHz. Estimate spectral envelope using trapezoidal model (1/pi*f*tau). Compare each harmonic against applicable CISPR 11 or CISPR 32 emission limits. Flag harmonics within 6 dB of the limit.

3. **Design board-level EMC controls.** Define ground plane integrity rules, current loop area minimization, component placement zones (noisy vs. sensitive), and routing keep-out areas. Specify guard traces, ground stitching via spacing, and board edge ground via fencing.

4. **Specify cable/connector filtering.** For each external interface, define: common-mode choke (impedance at target frequency), feedthrough capacitors, ferrite beads (impedance vs. frequency), and TVS/ESD protection. Include part number recommendations where possible.

5. **Design immunity countermeasures.** For each IEC 61000-4-x test: ESD (4-2), radiated immunity (4-3), EFT (4-4), surge (4-5), conducted immunity (4-6). Specify TVS voltage/clamping on external ports, power line filtering, and PCB grounding strategy for ESD.

6. **Develop pre-compliance test checklist.** List each test, applicable limit, expected margin, and board-level mitigation. Identify highest-risk items and recommend near-field probe measurements during prototype bring-up.

### Progress Checklist

- [ ] Emission source inventory complete
- [ ] Harmonic analysis to 1 GHz complete
- [ ] Board-level EMC design rules defined
- [ ] Filtering specified for all external interfaces
- [ ] Immunity countermeasures designed for all IEC 61000-4-x tests
- [ ] Pre-compliance test checklist with expected margins

### Compaction Resilience

If context is compacted mid-task, reconstruct from the Emission Source Inventory and Filtering Specification tables. These are the critical artifacts — all other outputs derive from them.

## Output Format

```markdown
## EMC Strategy: [Project Name]

### Emission Source Inventory
| Source | Type | Fundamental Freq | Rise Time | Key Harmonics | Risk Level |
|--------|------|-----------------|-----------|---------------|------------|

### Harmonic Analysis Table
| Source | Harmonic | Frequency | Estimated Level (dBuV/m) | CISPR Limit | Margin |
|--------|----------|-----------|-------------------------|-------------|--------|

### Board-Level EMC Design Rules
1. [Rule with quantified parameter]
2. ...

### Filtering Specification
| Interface | CM Choke | Capacitor | Ferrite | TVS/ESD | Notes |
|-----------|----------|-----------|---------|---------|-------|

### Immunity Protection Scheme
| Test (IEC 61000-4-x) | Level | Protection Method | Components | Placement |
|-----------------------|-------|-------------------|------------|-----------|

### Pre-Compliance Test Plan
| Test | Standard | Limit | Expected Margin | Risk | Board Mitigation |
|------|----------|-------|-----------------|------|------------------|

### Expected Margin Analysis
[Summary of weakest margins and recommended contingencies]
```

## Handoff

- From **stackup-design**: Receive stackup cross-section and layer assignments for grounding analysis.
- To **power-integrity**: Provide switching regulator EMC constraints that affect decoupling strategy.
- To **other council agents**: Provide filtering component requirements for BOM integration and connector selection constraints.

## Quality Checks

1. All clock harmonics checked to at least 1 GHz against applicable limit lines.
2. Switching regulator layout follows manufacturer EMC application note guidelines.
3. Shield grounding strategy specified — 360-degree ground where possible, single-point only when justified.
4. Every external interface has filtering defined with specific component values.
5. IEC 60601-1-2 immunity levels correctly referenced for the device classification.
6. Pre-compliance test plan includes near-field probe measurements for early risk identification.
7. Common-mode choke impedance specified at the frequency of concern, not just DC resistance.
8. ESD protection placement within 5 mm of connector — distance explicitly stated.

## Evolution Notes

- Future versions may integrate CISPR limit line data for automated margin calculation.
- Shielding effectiveness estimation for common enclosure types to be added.
- Automotive EMC standards (CISPR 25, ISO 11452) planned as variant procedures.
