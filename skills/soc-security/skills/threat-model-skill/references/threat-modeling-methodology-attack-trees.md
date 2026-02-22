# Threat Modeling Methodology — Attack Tree Construction

## Contents

- [Purpose](#purpose)
- [Quick Reference](#quick-reference)
- [Background](#background)
  - [Notation](#notation)
- [Construction Process](#construction-process)
  - [Step 1: Define the Root Goal](#step-1-define-the-root-goal)
  - [Step 2: Define the Attacker Profile](#step-2-define-the-attacker-profile)
  - [Step 3: Top-Down Decomposition](#step-3-top-down-decomposition)
  - [Step 4: Annotate Leaf Nodes](#step-4-annotate-leaf-nodes)
  - [Step 5: Minimal Cut Set Analysis](#step-5-minimal-cut-set-analysis)
- [Worked Example: Attack Tree for DICE Key Extraction](#worked-example-attack-tree-for-dice-key-extraction)
- [Attack Tree Quality Checks](#attack-tree-quality-checks)

## Purpose

Methodology for building attack trees for multi-step hardware attack scenarios. Covers notation, construction process, annotation, and minimal cut set analysis.

**Primary consumer:** threat-model-skill (Phase 3 threat identification, Framework 2)

---

## Quick Reference

| Methodology | Use When | Output | Typical Scope |
|---|---|---|---|
| Attack Tree Construction | Multi-step attack scenarios requiring feasibility analysis | Goal-oriented attack trees with cut sets | Complex attack paths |

---

## Background

Attack trees model how individual weaknesses combine to enable a high-level attack goal. They are valuable for: identifying which mitigations have the most impact (cut set analysis), communicating attack feasibility, comparing difficulty of different attack paths, and identifying prerequisite conditions.

### Notation

- **Root node (goal):** The attacker's ultimate objective
- **AND nodes:** All children must be achieved (arc connecting children)
- **OR nodes:** Any child suffices (no arc)
- **Leaf nodes:** Atomic actions or conditions that cannot be further decomposed
- **Annotations:** Each leaf carries difficulty, access requirement, and detectability

---

## Construction Process

### Step 1: Define the Root Goal

The root goal should be specific and from the attacker's perspective.

**Good:** "Extract AES-256 key from the crypto engine during runtime", "Execute arbitrary code in secure world before boot authentication", "Forge a DICE attestation certificate for a compromised platform"

**Poor (too vague):** "Compromise the SoC", "Break security", "Gain access"

### Step 2: Define the Attacker Profile

```
Attacker Profile
================
Name: [descriptive name, e.g., "Malicious Cloud Tenant"]
Access level: [remote / local logical / local physical / invasive physical]
Resources: [commodity / specialized / nation-state]
Motivation: [financial / espionage / disruption / research]
Persistence: [one-shot / persistent access / supply chain]
```

### Step 3: Top-Down Decomposition

**Rules:** (1) Each level is one logical step more specific. (2) AND/OR decisions explicit. (3) Stop at atomic actions assessable for difficulty. (4) Aim for 3-5 levels of depth.

### Step 4: Annotate Leaf Nodes

| Annotation | Values | Meaning |
|-----------|--------|---------|
| **Difficulty** | Low / Medium / High | Equipment, skill, and time required |
| **Access** | Remote / Local-Logical / Local-Physical / Invasive | Physical access level needed |
| **Detectability** | Stealthy / Detectable / Obvious | How likely the attack is to be noticed |

**Difficulty calibration for hardware:**

| Level | Description | Examples |
|-------|-------------|---------|
| Low | Commodity tools, publicly documented | USB JTAG adapter, public exploit code |
| Medium | Specialized equipment, domain expertise | Oscilloscope + glitch generator, custom PCB |
| High | Advanced lab equipment, extensive expertise | FIB station, EM probe array, custom ASIC |

### Step 5: Minimal Cut Set Analysis

A **minimal cut set** is the smallest set of leaf nodes that, if mitigated, prevents the root goal through any path.

**Finding cut sets:** (1) For OR nodes: at least one child in every branch must be in the set. (2) For AND nodes: only one child needed. (3) The minimal cut set is the smallest such set.

**Reporting:**
```
Minimal Cut Sets for [Root Goal]:

Cut Set 1 (recommended — blocks 3 of 4 paths):
  - Mitigate [Leaf X]: [specific mitigation]
  - Mitigate [Leaf Y]: [specific mitigation]

Cut Set 2 (alternative — blocks all paths but more expensive):
  - Mitigate [Leaf Z]: [specific mitigation]
```

---

## Worked Example: Attack Tree for DICE Key Extraction

```
ROOT: Extract DICE Layer 1 Device Identity Key (OR)
+-- Path A: Extract from memory during runtime (AND)
|   +-- A1: Gain code execution in Layer 1 context
|   |   +-- A1a: Exploit vulnerability in L1 firmware -- D:Med, A:Remote, Det:Detectable
|   |   +-- A1b: Bypass boot auth to load modified L1 -- D:High, A:Local-Physical, Det:Obvious
|   +-- A2: Read key from key storage
|       +-- A2a: Key stored in accessible SRAM region -- D:Low, A:Local-Logical, Det:Stealthy
|       +-- A2b: Key in protected region, bypass access ctrl -- D:High, A:Local-Logical, Det:Detectable
|
+-- Path B: Extract via debug interface (AND)
|   +-- B1: Enable debug access
|   |   +-- B1a: Debug fuse not blown (mfg error) -- D:Low, A:Local-Physical, Det:Obvious
|   |   +-- B1b: Bypass debug authentication -- D:Med, A:Local-Physical, Det:Detectable
|   +-- B2: Read key storage via debug port -- D:Low, A:Local-Physical, Det:Stealthy
|
+-- Path C: Extract via side-channel (AND)
|   +-- C1: Trigger key-dependent operation -- D:Low, A:Remote, Det:Stealthy
|   +-- C2: Measure side-channel emission
|       +-- C2a: Power analysis (DPA/SPA) -- D:Med, A:Local-Physical, Det:Stealthy
|       +-- C2b: EM analysis -- D:High, A:Local-Physical, Det:Stealthy
|
+-- Path D: Extract from supply chain (AND)
    +-- D1: Access device during manufacturing -- D:High, A:Invasive, Det:Detectable
    +-- D2: Read key material before fuses programmed -- D:Med, A:Invasive, Det:Detectable

Minimal Cut Sets:
1. {A2b, B1b, C2a, D1} -- Protect key storage, enforce debug auth, add DPA countermeasures, secure supply chain [Recommended]
2. {A1, B1, C1} -- Prevent code execution in L1, disable debug entirely, prevent triggering key ops externally [Alternative]
```

---

## Attack Tree Quality Checks

1. **Completeness:** Are all known attack paths represented? Cross-reference with STRIDE findings.
2. **Granularity:** Are leaf nodes truly atomic? Decompose further if possible.
3. **Consistency:** Are difficulty assessments calibrated consistently?
4. **Specificity:** Are leaf nodes specific to this component, not generic?
5. **Grounding:** Is each path grounded in evidence, or speculative? Mark accordingly.
