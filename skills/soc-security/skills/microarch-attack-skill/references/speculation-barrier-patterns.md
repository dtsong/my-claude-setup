# Speculation Barrier Patterns — Mitigation Catalog

## Purpose

Catalog of hardware and software mitigation patterns for microarchitectural attacks. Each pattern includes the targeted attack class, implementation mechanism, effectiveness assessment, performance impact, and residual risk. Referenced by the microarch-attack-skill's Phase 4 (Mitigation Assessment).

---

## Pattern Index

| Pattern | Target Attacks | Class | Scope |
|---------|---------------|-------|-------|
| P1: Speculation Barriers | Spectre-v1 | Serialization | Per-gadget |
| P2: Retpoline | Spectre-v2 | Serialization | Indirect branches |
| P3: IBRS/eIBRS | Spectre-v2 | Partitioning | Hardware, per-mode |
| P4: STIBP | Spectre-v2 cross-thread | Partitioning | SMT |
| P5: SSBD | Spectre-v4 | Serialization | Store-load forwarding |
| P6: L1D Flush | L1TF, cache SC | Cleansing | Per-VM-entry |
| P7: VERW / MD_CLEAR | MDS attacks | Cleansing | Per-domain-transition |
| P8: KPTI | Meltdown | Isolation | Kernel/user boundary |
| P9: Cache Partitioning (CAT) | LLC side-channels | Partitioning | Per-domain |
| P10: Core Scheduling | SMT attacks | Isolation | Per-core |
| P11: Index Masking | Spectre-v1 | Masking | Per-access |
| P12: BTB/BHB Flush | Spectre-v2, Inception | Cleansing | Per-domain-transition |
| P13: RSB Filling | Spectre-RSB | Cleansing | Per-domain-transition |
| P14: DIT (Data-Independent Timing) | Timing side-channels | Isolation | Per-context (ARM) |
| P15: Zkt Extension | Timing side-channels | Isolation | Per-instruction (RISC-V) |

---

## Pattern Details

### P1: Speculation Barriers (LFENCE / CSDB / fence)

**Target:** Spectre-v1 (bounds check bypass), general speculation containment

**Mechanism:** Insert a serializing instruction after a security-relevant bounds check to prevent speculative execution past the check.

**Implementation:**
```
// x86
if (index < array_size) {
    __asm__ __volatile__("lfence");  // Serialize — no speculative execution past this point
    value = array[index];
}

// ARM
if (index < array_size) {
    __asm__ __volatile__("csdb");    // Conditional Speculation Dependency Barrier
    value = array[index];
}
```

**Effectiveness:** HIGH — prevents speculative access past the barrier
**Performance Impact:** LOW per-instance (pipeline stall ~10-30 cycles), but scales with number of bounds checks in hot paths
**Residual Risk:** Does not address attacks that do not cross a bounds check (Spectre-v2, MDS)
**Deployment Scope:** Per-gadget — must be inserted at each vulnerable bounds check

---

### P2: Retpoline (Return Trampoline)

**Target:** Spectre-v2 (indirect branch target injection)

**Mechanism:** Replace indirect branches (`jmp *reg`, `call *reg`) with a return trampoline that captures speculation into an infinite loop, preventing speculative execution of attacker-controlled targets.

**Implementation:**
```asm
; Instead of: jmp *%rax
; Use:
  call retpoline_rax
  ...
retpoline_rax:
  mov %rax, (%rsp)    ; Overwrite return address with target
  ret                   ; Speculative execution follows RSB (the infinite loop below)

; Speculation trap:
  pause
  lfence
  jmp retpoline_rax    ; Infinite loop — speculation trapped here
```

**Effectiveness:** MODERATE-HIGH — effective for many Spectre-v2 variants; bypassed by some newer attacks (Inception, Training Solo on certain microarchitectures)
**Performance Impact:** 5-20% on indirect-branch-heavy workloads (kernel, interpreters)
**Residual Risk:** Newer attacks that train predictors using same-domain branches (Training Solo) may bypass retpoline
**Deployment Scope:** All indirect branches in security-sensitive code (kernel, hypervisor)

---

### P3: IBRS / eIBRS (Indirect Branch Restricted Speculation)

**Target:** Spectre-v2 (all indirect branch variants)

**Mechanism:** Hardware mode that restricts indirect branch prediction to only use predictions from the current security domain (privilege level, VMID). eIBRS makes this persistent without re-enabling on each domain transition.

**Effectiveness:** HIGH — hardware-enforced predictor isolation
**Performance Impact:** LOW (eIBRS), MODERATE (legacy IBRS — requires MSR write per transition)
**Residual Risk:** Does not protect against same-domain training attacks; Inception demonstrated bypass on some microarchitectures
**Deployment Scope:** Hardware feature, enabled via MSR

---

### P4: STIBP (Single Thread Indirect Branch Predictors)

**Target:** Cross-thread (SMT) Spectre-v2

**Mechanism:** Restricts indirect branch predictions to only use training from the current logical thread, preventing cross-thread predictor poisoning.

**Effectiveness:** HIGH for cross-SMT attacks
**Performance Impact:** MODERATE — reduces predictor accuracy by limiting training data
**Residual Risk:** Does not address same-thread or cross-core attacks
**Deployment Scope:** SMT-enabled processors, per-thread MSR

---

### P5: SSBD (Speculative Store Bypass Disable)

**Target:** Spectre-v4 (speculative store bypass)

**Mechanism:** Disables speculative store-to-load forwarding bypass, preventing speculative loads from reading stale values before a store completes.

**Effectiveness:** HIGH
**Performance Impact:** MODERATE — affects store-load forwarding performance
**Residual Risk:** Minimal for Spectre-v4 specifically
**Deployment Scope:** Per-thread MSR or per-process PRCTL

---

### P6: L1D Flush on VM Entry

**Target:** L1TF (Foreshadow), cross-VM L1D cache side-channels

**Mechanism:** Flush the entire L1D cache when entering a virtual machine, ensuring no host or other-VM data remains in L1D.

**Effectiveness:** HIGH for L1D-based attacks
**Performance Impact:** MODERATE — L1D cold start on every VM entry; impact depends on VM exit frequency
**Residual Risk:** Does not address L2/LLC side-channels; does not address MDS (buffer-based leakage)
**Deployment Scope:** Hypervisor VM entry path

---

### P7: VERW / MD_CLEAR

**Target:** MDS attacks (RIDL, Fallout, ZombieLoad)

**Mechanism:** Execute VERW instruction (which triggers MD_CLEAR microcode on affected CPUs) to overwrite CPU internal buffers (store buffer, fill buffer, load ports) at security domain transitions.

**Effectiveness:** HIGH — clears the specific buffers exploited by MDS
**Performance Impact:** LOW-MODERATE — depends on transition frequency
**Residual Risk:** Must be applied at every domain transition (VM exit, context switch, syscall return)
**Deployment Scope:** All domain transitions in kernel/hypervisor

---

### P8: KPTI (Kernel Page Table Isolation)

**Target:** Meltdown (rogue data cache load from kernel memory)

**Mechanism:** Maintain separate page tables for user and kernel mode. User-mode page tables do not map kernel memory, preventing even speculative access to kernel addresses.

**Effectiveness:** HIGH — eliminates the Meltdown attack surface
**Performance Impact:** 5-30% on syscall-heavy workloads (page table switch on every syscall)
**Residual Risk:** Does not address Spectre or MDS; performance impact may lead to selective deployment
**Deployment Scope:** OS kernel, per-process page tables

---

### P9: Cache Allocation Technology (CAT) / Cache Partitioning

**Target:** LLC (Last Level Cache) side-channel attacks

**Mechanism:** Partition LLC ways between security domains, preventing one domain's cache activity from evicting another domain's cache lines.

**Effectiveness:** MODERATE — reduces LLC Prime+Probe channel bandwidth; does not eliminate timing-based occupancy observations
**Performance Impact:** LOW-MODERATE — reduced effective cache size per domain
**Residual Risk:** Coarse-grained partitioning (way-based); timing side-channels through LLC access latency still possible; does not address L1/L2 sharing
**Deployment Scope:** Hardware feature (Intel CAT, ARM MPAM), configured per-domain

---

### P10: Core Scheduling / SMT Isolation

**Target:** All SMT-based cross-thread attacks (port contention, TLBleed, cache sharing)

**Mechanism:** Schedule only mutually trusted workloads on sibling SMT threads. Alternatively, disable SMT entirely for security-critical workloads.

**Effectiveness:** HIGHEST — eliminates the SMT shared-resource attack surface
**Performance Impact:** HIGH — 15-30% throughput reduction from reduced SMT utilization
**Residual Risk:** Does not address cross-core attacks; high performance cost may limit adoption
**Deployment Scope:** OS scheduler (Linux `core_scheduling`), hypervisor thread assignment

---

### P11: Index Masking

**Target:** Spectre-v1 (bounds check bypass)

**Mechanism:** Mask array indices to ensure they cannot exceed array bounds, even during speculative execution.

```c
// Instead of:
value = array[index];

// Use:
index &= (array_size - 1);  // Mask — speculative access stays within bounds
value = array[index];
```

**Effectiveness:** HIGH for arrays with power-of-2 sizes; requires careful application
**Performance Impact:** VERY LOW — single AND instruction
**Residual Risk:** Only applies to simple array access patterns; does not protect complex pointer chasing
**Deployment Scope:** Per-access site; compiler support (`__builtin_speculation_safe_value`)

---

### P12: BTB/BHB Flush

**Target:** Spectre-v2, Inception, Training Solo (branch predictor poisoning)

**Mechanism:** Flush branch history and BTB state at security domain transitions, preventing cross-domain branch target injection.

**Effectiveness:** HIGH — eliminates cross-domain predictor state
**Performance Impact:** MODERATE — branch prediction cold start after flush; ~5-15% on transition-heavy workloads
**Residual Risk:** Inception showed that even intra-domain training can be exploited on some architectures; BHB flush may not cover all predictor structures
**Deployment Scope:** Kernel entry, VM entry, context switch

---

### P13: RSB Filling / RSB Stuffing

**Target:** Spectre-RSB (return stack buffer underflow/poisoning)

**Mechanism:** Fill the RSB with benign entries at domain transitions to prevent underflow into the less-precise fallback predictor (which may use attacker-controlled BTB entries).

**Effectiveness:** HIGH
**Performance Impact:** LOW — ~20 cycles per domain transition for RSB filling
**Residual Risk:** RSB depth must match or exceed hardware RSB depth; varies by microarchitecture
**Deployment Scope:** VM entry, context switch for untrusted contexts

---

### P14: DIT (Data-Independent Timing) — ARM

**Target:** Timing side-channels in cryptographic operations

**Mechanism:** ARM processor mode (PSTATE.DIT) that guarantees data-independent timing for a defined set of instructions. When DIT=1, instructions like AES, SHA, and integer multiply execute in constant time regardless of operand values.

**Effectiveness:** HIGH for covered instructions
**Performance Impact:** LOW — may disable some timing optimizations for covered instructions
**Residual Risk:** Only covers a defined instruction set; does not cover memory access patterns or cache timing
**Deployment Scope:** Per-context (PSTATE bit); must be explicitly enabled by security-sensitive code

---

### P15: Zkt Extension — RISC-V

**Target:** Timing side-channels in cryptographic operations

**Mechanism:** RISC-V ISA extension that guarantees constant-time execution for scalar crypto instructions and specified integer operations. Implementations conforming to Zkt must not have data-dependent timing for these instructions.

**Effectiveness:** HIGH for conforming implementations
**Performance Impact:** LOW — implementation must be inherently constant-time
**Residual Risk:** Only covers Zkt-specified instructions; cache access patterns are not covered
**Deployment Scope:** ISA extension; must be implemented in hardware and advertised via ISA discovery

---

## Mitigation Selection Decision Tree

```
Is the attack transient execution?
├── Yes → Is it Spectre-v1 (bounds bypass)?
│   ├── Yes → P1 (barrier) or P11 (index masking)
│   └── No → Is it Spectre-v2 (indirect branch)?
│       ├── Yes → P3 (eIBRS) + P12 (BHB flush) + P2 (retpoline as fallback)
│       └── No → Is it Meltdown class?
│           ├── Yes → P8 (KPTI) + P6 (L1D flush for L1TF)
│           └── No → Is it MDS?
│               └── Yes → P7 (VERW/MD_CLEAR)
└── No → Is the attack cache-based?
    ├── Yes → P9 (CAT for LLC) + P6 (L1D flush for L1)
    └── No → Is the attack SMT-based?
        ├── Yes → P10 (core scheduling) + P4 (STIBP)
        └── No → Is it timing-based?
            └── Yes → P14 (DIT) or P15 (Zkt) for crypto; P1 (barriers) for general
```

---

*[FROM TRAINING] Mitigation effectiveness and performance impact estimates are based on published research and vendor documentation. Specific values depend on microarchitecture, workload, and configuration. Verify against vendor mitigation guides. Last verified: 2026-02-13.*
