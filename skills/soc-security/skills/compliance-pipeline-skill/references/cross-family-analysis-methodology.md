# Cross-Family Analysis — Traceability & Delta Methodology

## Contents

- [Purpose](#purpose)
- [Overview](#overview)
  - [Key Principle: Independence by Default](#key-principle-independence-by-default)
- [Traceability Matrix Format](#traceability-matrix-format)
  - [Column Definitions](#column-definitions)
  - [Rules](#rules)
- [Delta Annotation Format](#delta-annotation-format)
  - [Delta Categories](#delta-categories)
  - [Syntax](#syntax)
- [Reuse Assessment](#reuse-assessment)
  - [Reuse Levels](#reuse-levels)
  - [Decision Tree](#decision-tree)
  - [Shared IP Catalog](#shared-ip-catalog)

## Purpose

Defines the traceability matrix format, delta annotation conventions, and reuse assessment methodology for cross-family compliance analysis.

**Primary consumer:** compliance-pipeline-skill (Stage 2 cross-family traceability)

---

## Overview

Cross-family analysis tracks the same security requirements across multiple SoC families (compute, automotive, client, data center). The goal is to identify reuse opportunities and family-specific gaps.

### Key Principle: Independence by Default

Even when two families share the same RTL IP block, compliance evidence does not automatically transfer. Each family has different integration context (bus, power, clock), compliance regime, threat environment, and verification emphasis. Reuse must be explicitly justified.

---

## Traceability Matrix Format

One row per requirement-family pair. Never combine families in a single row.

```markdown
| Spec Req ID | Req Text | Security Domain | SoC Family | RTL Module | Verification Asset | Compliance Evidence | Status | Gap Flag | Delta Notes |
```

### Column Definitions

| Column | Description | Required |
|---|---|---|
| Spec Req ID | Requirement ID from standards registry | Yes |
| Req Text | Abbreviated requirement text | Yes |
| Security Domain | Technology domain from ontology | Yes |
| SoC Family | Target family | Yes |
| RTL Module | Implementation module or `TBD` | Yes |
| Verification Asset | VerificationItem ID or `---` | Yes |
| Compliance Evidence | Evidence type and reference or `None` | Yes |
| Status | Covered / Partial / Gap / Not Assessed / Not Applicable | Yes |
| Gap Flag | Gap description or `None` | Yes |
| Delta Notes | Family-specific notes | Yes |

### Rules

1. One row per requirement-family pair
2. Never combine families in a single row
3. Empty cells not allowed — use `TBD`, `---`, or `None`
4. RTL Module `TBD` acceptable — flag for module mapping
5. Sort by Spec Req ID, then SoC Family

---

## Delta Annotation Format

### Delta Categories

| Category | Code | Description | Example |
|---|---|---|---|
| Bus Wrapper | `BUS` | Different bus interface | `BUS: AXI for auto, CXL for DC` |
| Compliance Regime | `COMP` | Different compliance overlay | `COMP: ISO 21434 for auto, FIPS for compute` |
| Power Domain | `PWR` | Different power management | `PWR: Always-on for compute, power-gated for auto` |
| Verification Approach | `VER` | Different strategy | `VER: Formal for compute, simulation for client` |
| Evidence Format | `EVID` | Different artifacts | `EVID: ISO work product for auto, FIPS report for compute` |
| IP Version | `IPV` | Different IP version | `IPV: v2 for compute/DC, v1 for client` |
| Integration Depth | `INT` | Different complexity | `INT: Full CXL for DC, PCIe-only for compute` |
| Feature Subset | `FEAT` | Family uses subset | `FEAT: No TSP for automotive (no CXL)` |

### Syntax

```
[BUS] AXI wrapper for automotive; CXL.io for data center
[COMP] ISO 21434 for automotive; FIPS 140-3 for compute
[IPV] dice_engine_v2 for compute/DC; dice_engine_v1 (legacy) for client
```

Multiple deltas separated by semicolons, each tagged.

---

## Reuse Assessment

### Reuse Levels

| Level | Definition | Evidence Action | Verification Action |
|---|---|---|---|
| **High** | Same RTL, same integration, same verification | Reference shared evidence directly | Shared assertions apply |
| **Medium** | Same RTL, different integration (bus/power) | Shared RTL-level; per-family integration | RTL assertions shared; add integration |
| **Low** | Same requirement, different implementation | Independent per family | Independent per family |
| **None** | Family-specific requirement | N/A | N/A |

### Decision Tree

```
Same RTL module across families?
  NO -> Same security property? YES -> Low | NO -> None
  YES -> Integration identical?
    YES -> High
    NO -> RTL self-contained? YES -> Medium-High | NO -> Medium
```

### Shared IP Catalog

| Component | Typical Reuse | Delta Factors |
|---|---|---|
| Crypto engine | High | Algorithm selection; bus wrapper |
| Boot ROM | High | ROM size; security model identical |
| DICE identity engine | High | Number of layers; CDI logic identical |
| Fuse controller | High | Fuse count; access control shared |
| Debug auth FSM | High | Features vary; auth protocol shared |
| TDISP state machine | Medium-High | PCIe-equipped only; FSM shared |
| SPDM responder | High | Transport binding varies (MCTP/DOE) |
| Bus firewall | Medium | Logic shared; rules family-specific |
| Key management unit | Medium | Hierarchy shared; policy family-specific |
