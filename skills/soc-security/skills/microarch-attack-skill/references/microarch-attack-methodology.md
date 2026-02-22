# Microarchitectural Attack Analysis Methodology

## Purpose

Detailed methodology for classifying and analyzing microarchitectural attacks against SoC hardware components. Provides the analytical framework referenced by the microarch-attack-skill's Phase 3 (Attack Pattern Matching).

---

## Attack Classification Framework

### Taxonomy

Microarchitectural attacks are classified along three dimensions:

1. **Mechanism:** How the information channel is created
2. **Observable:** What microarchitectural state change reveals information
3. **Domain Pair:** Which security domains are connected by the channel

```
Mechanism Classification
========================
Transient Execution:
  ├── Misprediction-based (Spectre class)
  │   ├── Conditional branch misprediction (Spectre-v1 / PHT)
  │   ├── Indirect branch misprediction (Spectre-v2 / BTB)
  │   ├── Return prediction (Spectre-RSB)
  │   └── Store-to-load forwarding (Spectre-v4 / SSBD)
  ├── Exception-based (Meltdown class)
  │   ├── Supervisor access bypass (Meltdown / Rogue Data Cache Load)
  │   ├── Terminal fault (L1TF / Foreshadow)
  │   └── Lazy FP state restore (Meltdown-FP)
  └── Buffer-sampling (MDS class)
      ├── Line fill buffer sampling (RIDL)
      ├── Store buffer sampling (Fallout)
      ├── Load port sampling (ZombieLoad)
      └── Vector register leakage (Downfall, Zenbleed)

Side-Channel (non-transient):
  ├── Cache-based
  │   ├── Access-driven (Prime+Probe, Evict+Time)
  │   ├── Trace-driven (Flush+Reload — requires shared memory)
  │   └── Occupancy-based (LLC occupancy covert channel)
  ├── Predictor-based
  │   ├── BTB contention (branch target inference)
  │   ├── PHT contention (branch direction inference)
  │   └── RSB contention (call stack inference)
  ├── TLB-based
  │   ├── TLB set contention (TLBleed)
  │   └── Page table walk timing
  └── Execution-based
      ├── Port contention (PortSmash, SMoTherSpectre)
      └── Prefetch timing (data-dependent prefetch)
```

### Observable Classification

| Observable | Measurement Method | Typical Resolution | Noise Level |
|-----------|-------------------|-------------------|-------------|
| Cache hit/miss timing | RDTSC/RDTSCP, performance counters | ~3-10 ns | Low (L1), Moderate (LLC) |
| TLB hit/miss timing | Memory access timing | ~5-20 ns | Moderate |
| Branch misprediction timing | Branch-dependent code timing | ~10-30 ns | High |
| Port contention timing | Instruction latency measurement | ~1-5 ns | High |
| Cache occupancy | LLC miss rate monitoring | Aggregate metric | Low |

---

## Speculative Execution Window Analysis

### Window Estimation Methodology

The speculative execution window determines how much data an attacker can access before speculation is resolved. Estimation requires:

1. **Pipeline depth:** Number of stages from fetch to retirement
2. **Branch resolution latency:** Cycles from branch fetch to resolution (typically at execute stage)
3. **Memory access latency:** Cycles for the speculative load to reach the cache
4. **Squash latency:** Cycles from misprediction detection to pipeline flush

```
Speculative Window (cycles) = Branch Resolution Latency + Squash Latency

Typical ranges by microarchitecture class:
  - In-order (embedded): 5-15 cycles (limited speculative depth)
  - Out-of-order (mobile): 30-80 cycles
  - Out-of-order (server): 80-200 cycles
  - Wide out-of-order (HPC): 150-300+ cycles
```

### Window Impact on Attack Feasibility

| Window Size | Spectre-v1 | Spectre-v2 | MDS | Cache SC |
|------------|-----------|-----------|-----|----------|
| < 20 cycles | Limited — few speculative instructions | Unlikely — insufficient gadget execution | Still feasible — buffer sampling is independent | Feasible |
| 20-80 cycles | Feasible with short gadgets | Feasible with targeted gadgets | Feasible | Feasible |
| 80-200 cycles | Highly feasible | Highly feasible — complex gadget chains possible | Feasible | Feasible |
| > 200 cycles | Maximum bandwidth — long gadget chains, wide exfiltration | Full exploitation — arbitrary speculative code execution | Feasible | Feasible |

---

## Cross-Domain Analysis Methodology

### Step 1: Enumerate Security Domain Pairs

For each pair of security domains in scope, identify:
- **Shared microarchitectural state:** Which structures are shared (caches, predictors, buffers)
- **Isolation mechanisms:** What partitioning or flushing exists at domain transitions
- **Transition frequency:** How often do domain transitions occur (context switch rate, VM exit rate)

### Step 2: Assess Channel Bandwidth

For each shared structure, estimate information leakage bandwidth:

| Channel | Typical Bandwidth | Conditions |
|---------|------------------|-----------|
| L1D Prime+Probe | 100-500 KB/s | Same core, no noise |
| LLC Prime+Probe | 10-100 KB/s | Cross-core |
| Flush+Reload | 500 KB/s - 1 MB/s | Shared memory, same NUMA node |
| BTB contention | 1-10 KB/s | Same core or SMT |
| Port contention | 10-100 KB/s | SMT only |

### Step 3: Apply Attack Pattern

For each applicable catalog entry:
1. Map the abstract attack to the specific microarchitecture
2. Identify the attacker's required access (same core? same package? remote?)
3. Assess whether deployed mitigations break the attack chain
4. Estimate residual bandwidth after mitigations

---

## Mitigation Effectiveness Assessment

### Hardware Mitigation Classes

| Mitigation | Targeted Attacks | Effectiveness | Bypass Conditions |
|-----------|-----------------|---------------|-------------------|
| IBRS/eIBRS (Indirect Branch Restricted Speculation) | Spectre-v2 | High | Newer variants (Inception, Training Solo) may bypass |
| STIBP (Single Thread Indirect Branch Predictors) | Spectre-v2 cross-thread | High | Performance cost; sometimes disabled |
| SSBD (Speculative Store Bypass Disable) | Spectre-v4 | High | Performance cost |
| L1D flush on VM entry | L1TF, cache side-channels | High for L1D | Does not address LLC |
| VERW (MD_CLEAR) | MDS attacks | High | Must be applied at every domain transition |
| Cache Allocation Technology (CAT) | LLC side-channels | Moderate | Coarse-grained; timing still leaks occupancy |
| CSV2 (Cache Speculation Variant 2) | Spectre-BTB | High | ARM-specific; partitions BTB by context |
| DIT (Data-Independent Timing) | Timing side-channels in crypto | High | Only ARM; must be explicitly enabled per context |

### Software Mitigation Classes

| Mitigation | Targeted Attacks | Effectiveness | Performance Cost |
|-----------|-----------------|---------------|-----------------|
| Retpoline | Spectre-v2 | Moderate-High | 5-20% on some workloads |
| LFENCE after bounds check | Spectre-v1 | High for targeted gadgets | Low per-instance |
| Index masking | Spectre-v1 | High | Low |
| KPTI | Meltdown | High | 5-30% on syscall-heavy workloads |
| Site isolation (browsers) | Spectre cross-origin | High | Memory overhead |
| Core scheduling (CFS) | Cross-VM SMT attacks | High | Reduced SMT utilization |

---

## Analysis Output Templates

### Per-Attack Assessment Template

```
Assessment: [UARCH-NNN] — [Attack Name]
========================================
Applicability: APPLICABLE / MITIGATED / NOT APPLICABLE / NOT ASSESSED
Rationale: [Why this determination]

If APPLICABLE:
  Affected Domain Pairs: [list]
  Speculative Window: [cycles] / N/A
  Information Channel: [mechanism]
  Estimated Bandwidth: [KB/s range]
  Deployed Mitigations: [list with effectiveness]
  Residual Risk: [description]
  Recommended Additional Mitigations: [if any]
  Research Reference: [citation]

If MITIGATED:
  Original Risk: [severity]
  Deployed Mitigations: [list with effectiveness]
  Residual Risk: [description]
  Confidence in Mitigation: [GROUNDED/INFERRED/SPECULATIVE]

If NOT APPLICABLE:
  Rationale: [specific microarchitectural reason]
  Example: "BTB is fully partitioned by VMID in this microarchitecture; cross-VM BTB injection is not feasible."

If NOT ASSESSED:
  Missing Information: [what is needed]
  Impact of Gap: [what could be missed]
```

---

*[FROM TRAINING] Attack descriptions, bandwidth estimates, and mitigation effectiveness are based on published research and general domain knowledge. Specific values depend on exact microarchitectural implementation. Verify against vendor documentation and lab measurements. Last verified: 2026-02-13.*
