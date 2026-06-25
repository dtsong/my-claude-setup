---
name: microarch-analysis
department: "forge"
description: "Use when analyzing microarchitectural attack surfaces by mapping shared hardware structures, identifying speculative execution vectors, quantifying speculative windows, and proposing countermeasures. Covers cache timing, transient execution, and contention channels. Do not use for RTL-level design review (use rtl-security-review) or physical implementation analysis (use physical-design-security)."
version: 1
triggers:
  - "microarchitecture"
  - "pipeline"
  - "cache"
  - "speculation"
  - "speculative execution"
  - "side-channel"
  - "Spectre"
  - "Meltdown"
  - "branch predictor"
  - "cache timing"
  - "transient execution"
  - "covert channel"
---

# Microarchitectural Analysis

## Purpose
Map microarchitectural structures, identify shared state across trust boundaries, enumerate speculative execution attack vectors, and propose hardware/software countermeasures.

## Scope Constraints

Reads hardware documentation, microarchitectural specifications, and system configuration. Does not modify files or execute code. Does not perform active exploitation or benchmark execution.

## Inputs
- System or component architecture being analyzed
- Microarchitectural features in scope (cache hierarchy, branch predictor, pipeline depth, etc.)
- Trust boundary definitions (which software domains share which hardware resources)
- Threat model (local attacker, cross-VM, cross-process, same-core, cross-core)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Map microarchitectural structures
- [ ] Step 2: Identify shared state across trust boundaries
- [ ] Step 3: Enumerate attack vectors
- [ ] Step 4: Assess speculative window
- [ ] Step 5: Propose countermeasures
- [ ] Step 6: Document residual exposure

### Step 1: Map Microarchitectural Structures
Enumerate all microarchitectural structures that hold state: L1I/L1D/L2/L3 caches, TLBs, branch predictors (PHT, BTB, RSB), store buffers, fill buffers, line fill buffers, load ports, MOB entries. For each structure, document sharing domain (per-thread, per-core, per-socket, system-wide).

### Step 2: Identify Shared State Across Trust Boundaries
For each microarchitectural structure, determine which trust domains share it. A shared L3 cache across VMs is a cross-VM channel. A shared BTB across hyperthreads is a cross-thread channel. Map the sharing matrix: structure x trust boundary.

### Step 3: Enumerate Attack Vectors
For each shared structure, enumerate known and potential attack vectors:
- **Cache timing**: Prime+Probe, Flush+Reload, Evict+Time, Cache Occupancy
- **Speculative execution**: Spectre v1 (PHT), v2 (BTB), v4 (STLF), RSB stuffing
- **Transient execution**: Meltdown-class, MDS, TAA, LVI
- **Contention**: Port contention, bandwidth contention, scheduling-based channels

### Step 4: Assess Speculative Window
For each speculative execution vector, determine the speculative window depth (in clock cycles), the number of transient operations possible within the window, and the observable microarchitectural side-effects (cache fills, TLB fills, port contention). Estimate bandwidth: bytes per invocation, invocations per second.

### Step 5: Propose Countermeasures
For each identified attack vector, propose countermeasures at the appropriate level:
- **Hardware**: Speculation barriers, cache partitioning, domain-tagged structures, constant-time functional units
- **Microcode**: IBRS, STIBP, SSBD, MDS mitigation buffers
- **Software**: LFENCE/speculation barriers, retpolines, cache-line alignment, constant-time implementations
- **System**: Core scheduling, hyperthread disabling, cache coloring/partitioning

### Step 6: Document Residual Exposure
After countermeasures, document what attack surface remains. Note accepted risks, performance cost of mitigations, and monitoring approaches for detecting exploitation attempts.

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what system is being analyzed, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Output Format

### Microarchitectural Sharing Matrix

| Structure | Sharing Domain | Trust Boundaries Crossed | Attack Class |
|-----------|---------------|------------------------|--------------|
| L1D Cache | Per-core (HT shared) | Cross-thread | Flush+Reload, Prime+Probe |
| ... | ... | ... | ... |

### Attack Vector Table

| Vector | Structure | Window (cycles) | Bandwidth | Severity | Countermeasure | Cost |
|--------|-----------|----------------|-----------|----------|----------------|------|
| Spectre v1 | PHT | ~14 cycles | ~1 B/invoke | High | LFENCE after bounds check | ~5% perf |
| ... | ... | ... | ... | ... | ... | ... |

### Residual Exposure Summary
- [Vector]: [Remaining risk] — [Monitoring approach]

## Handoff

- Hand off to rtl-security-review if RTL-level mitigations are needed for identified attack vectors.
- Hand off to physical-design-security if physical side-channel countermeasures are required.

## Quality Checks
- [ ] All microarchitectural structures with shared state are enumerated
- [ ] Sharing domains are correctly mapped to trust boundaries
- [ ] Known attack classes are applied to each shared structure
- [ ] Speculative windows are quantified in clock cycles
- [ ] Countermeasures are proposed at the appropriate level (HW/ucode/SW/system)
- [ ] Performance cost of mitigations is estimated
- [ ] Residual exposure is documented

## Evolution Notes
<!-- Observations appended after each use -->
