---
name: stackup-design
department: tracer
description: "Design PCB layer stackup optimized for signal integrity, power integrity, and EMC compliance"
version: 1
triggers:
  - stackup
  - layer
  - impedance
  - controlled impedance
  - dielectric
  - prepreg
  - core
  - cross-section
---

# stackup-design

## Purpose

Design PCB layer stackup optimized for signal integrity, power integrity, and EMC compliance. Produce a complete stackup specification with impedance calculations, layer assignments, and fabrication notes.

## Scope Constraints

- Board-level stackup only — does not cover component selection or schematic design.
- Assumes standard FR-4 or specified laminate material — exotic substrates (Rogers, PTFE) require explicit user input.
- Does not perform full-wave electromagnetic simulation — provides analytical impedance calculations.
- Maximum 24-layer stackups — beyond this, escalate to specialized tooling.

## Inputs

- **Signal types and count:** Single-ended, differential, analog, digital, RF, high-current power.
- **Impedance targets:** Typically 50 ohm single-ended, 90/100 ohm differential (user confirms).
- **Layer count budget or constraint:** Fixed or flexible.
- **Fabrication house capabilities:** Minimum trace/space, via drill, available prepreg/core thicknesses.
- **Special requirements:** Flex-rigid, blind/buried vias, back-drilling, controlled dielectric.

## Input Sanitization

- Reject requests that omit signal types entirely — ask for at least a high-level signal inventory.
- If impedance targets are not specified, default to 50 ohm SE / 100 ohm differential and flag the assumption.
- If fab capabilities are unknown, assume standard capabilities (4 mil trace/space, 0.2 mm drill) and flag.

## Procedure

1. **Inventory signal types.** Catalog all signal categories and their requirements: single-ended 50 ohm, differential 100 ohm, analog sensitive, high-current power. Count estimated routes per category.

2. **Determine minimum layer count.** Based on signal density, power domain count, isolation requirements, and return path needs. Rule: every signal layer needs an adjacent reference plane.

3. **Design layer assignment.** Assign signal layers, ground planes, power planes, and mixed layers. Place ground planes adjacent to every high-speed signal layer. Separate analog and digital domains with a ground plane.

4. **Calculate impedance.** For each signal type, compute trace width and spacing using dielectric constant (Dk), dielectric thickness, and copper weight. Use microstrip for outer layers, stripline for inner layers. Document formulas used.

5. **Verify return current path continuity.** For every critical signal, confirm the reference plane is continuous (no splits, no slots, no plane changes without stitching vias). Flag any unavoidable reference plane transitions.

6. **Confirm manufacturability.** Verify stackup against target fab capabilities: available prepreg/core thicknesses, minimum trace/space achievable on each layer, aspect ratio for vias, symmetry for warpage control.

### Progress Checklist

- [ ] Signal inventory complete
- [ ] Layer count determined with rationale
- [ ] Layer assignment table drafted
- [ ] Impedance calculated for all signal types
- [ ] Return current paths verified
- [ ] Fab capability check passed

### Compaction Resilience

If context is compacted mid-task, reconstruct state from the Progress Checklist and the most recent output artifact. The Layer Assignment Table and Impedance Calculation Table are the critical state — regenerate from these.

## Output Format

```markdown
## Stackup Design: [Project Name]

### Cross-Section Diagram
[ASCII cross-section showing layers, thicknesses, materials]

### Layer Assignment Table
| Layer | Type | Function | Reference Plane | Notes |
|-------|------|----------|-----------------|-------|

### Impedance Calculation Table
| Signal Type | Target (ohm) | Calculated (ohm) | Trace Width | Spacing | Layer | Geometry |
|-------------|-------------|-------------------|-------------|---------|-------|----------|

### Dielectric Properties
- Material: [laminate type]
- Dk: [value] at [frequency]
- Df: [value]
- Prepreg thicknesses: [list]
- Core thicknesses: [list]

### Fabrication Notes
- Minimum trace/space: [value]
- Via drill/pad: [value]
- Aspect ratio: [value]
- Stack symmetry: [yes/no + notes]
- Special processes: [if any]

### Cost/Performance Trade-off Summary
[Brief analysis of layer count vs. alternatives]
```

## Handoff

- To **emc-strategy**: Provide stackup cross-section and layer assignments for EMC analysis.
- To **power-integrity**: Provide power plane assignments and dielectric thicknesses for PDN impedance calculation.
- From **other council agents**: Accept signal type inventories, power domain definitions, and mechanical constraints.

## Quality Checks

1. Every high-speed signal layer has an adjacent ground plane — no exceptions.
2. No split planes under high-speed signal routes — verified explicitly.
3. Impedance calculations use actual fab dielectric constants, not textbook values.
4. Analog and digital signal domains separated by at least one ground plane.
5. Thermal relief specified for power planes carrying > 1A.
6. Stackup is symmetric about the center for warpage control.
7. Calculated impedance within +/- 10% of target (standard fab tolerance).
8. All prepreg/core thicknesses are standard offerings from the target fab.

## Evolution Notes

- Future versions may integrate with field solver APIs for more accurate impedance modeling.
- HDI stackup patterns (any-layer via, coreless) to be added when design complexity warrants.
- Flex-rigid stackup support planned as a variant procedure.
