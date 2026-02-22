# Microarchitectural Attacks — Threat Catalog

## Overview

Microarchitectural attacks exploit implementation-level behaviors of processor pipelines, caches, branch predictors, and other hardware structures that are not visible at the architectural (ISA) level. These attacks leverage speculative execution, timing variations, and resource contention to leak secrets across security boundaries — often entirely through software, without physical access. They are the primary threat vector for cross-domain information disclosure in multi-tenant and confidential computing environments.

---

## UARCH-001: Spectre-v1 (Bounds Check Bypass)

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I) |
| **Description** | Attacker mistrains the Pattern History Table (PHT) so the processor speculatively bypasses an array bounds check, causing an out-of-bounds read whose value is encoded into cache state. The attacker then recovers the secret via a cache side-channel (e.g., Flush+Reload). The speculative window between the mispredicted branch and its retirement exposes data the program should never access. |
| **Target Assets** | PHT (Pattern History Table), L1 data cache, branch prediction logic, speculative execution pipeline |
| **Affected Domains** | Microarch Security, Kernel Security, Confidential AI / TEE, TDISP / CXL |
| **Affected SoC Families** | Compute, Data Center, Client — all out-of-order processors with speculative branch prediction |
| **Preconditions** | Code execution on the same physical or logical core; a gadget (bounds check followed by dependent memory access) in victim code; shared cache with the victim |
| **Key Mitigations** | Speculation barriers (e.g., lfence, csdb) after bounds checks, index masking on speculative paths, Speculative Load Hardening (SLH) compiler pass, hardware-assisted bound clipping on speculative loads |
| **Verification Approach** | Tier 3 — microarchitectural simulation to confirm speculative data cannot reach cache without bounds validation; Tier 2 — firmware/compiler review for barrier placement |
| **Related Requirements** | REQ-CHERI-002 (bounds checking), REQ-CHERI-007 (compartment isolation) |

---

## UARCH-002: Spectre-v2 (Branch Target Injection)

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I) |
| **Description** | Attacker poisons the Branch Target Buffer (BTB) to redirect the victim's indirect branch to an attacker-chosen gadget address during speculative execution. The gadget executes speculatively with the victim's privilege and data, leaking secrets through a cache covert channel before the misprediction is resolved. |
| **Target Assets** | BTB (Branch Target Buffer), indirect branch predictor, L1/L2 cache hierarchy, speculative execution pipeline |
| **Affected Domains** | Microarch Security, Kernel Security, Confidential AI / TEE, TDISP / CXL |
| **Affected SoC Families** | Compute, Data Center, Client — all processors with shared indirect branch predictors |
| **Preconditions** | Code execution sharing a physical core with the victim (SMT or same core); ability to train the BTB for the victim's branch addresses |
| **Key Mitigations** | Retpoline (indirect branch thunking), IBRS / eIBRS (Indirect Branch Restricted Speculation), STIBP (Single Thread Indirect Branch Predictors), BTB flushing on context switch, hardware predictor domain tagging |
| **Verification Approach** | Tier 3 — microarchitectural simulation of BTB aliasing across privilege domains; Tier 2 — firmware review for IBRS/STIBP enablement |
| **Related Requirements** | REQ-CHERI-007 (compartment isolation), REQ-CXL-011 (coherence protocol isolation) |

---

## UARCH-003: Spectre-RSB (Return Stack Buffer Poisoning)

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I) |
| **Description** | Attacker manipulates the Return Stack Buffer (RSB) — the hardware structure predicting return instruction targets — to redirect speculative execution of victim returns to an attacker-chosen gadget. RSB poisoning can occur through deliberate call/return mismatches, context switch without RSB filling, or RSB underflow (where the processor may fall back to the BTB). |
| **Target Assets** | RSB (Return Stack Buffer), speculative execution pipeline, L1 data cache, call/return stack |
| **Affected Domains** | Microarch Security, Kernel Security, Confidential AI / TEE |
| **Affected SoC Families** | Compute, Data Center, Client — processors with RSB-based return prediction |
| **Preconditions** | Code execution on the same physical core as victim; ability to manipulate RSB entries (via call depth manipulation or cross-context residual entries) |
| **Key Mitigations** | RSB stuffing/filling on context switch, RSB underflow mitigation (prevent BTB fallback), call-depth tracking, IBRS mode covering return predictions, retpoline for returns where supported |
| **Verification Approach** | Tier 3 — microarchitectural simulation verifying RSB isolation on context/privilege transitions; Tier 2 — firmware review for RSB stuffing on VM exit and context switch |
| **Related Requirements** | REQ-CHERI-007 (compartment isolation) |

---

## UARCH-004: Meltdown (Rogue Data Cache Load)

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I), Elevation of Privilege (E) |
| **Description** | Processor speculatively executes a load that accesses kernel or hypervisor memory from user mode before the privilege check raises an exception. The speculatively read data is forwarded to dependent instructions that encode it into cache state. Although the faulting instruction is eventually squashed, the cache side-effect persists and can be measured. This breaks the fundamental user/kernel memory isolation assumption. |
| **Target Assets** | Page table permission bits (U/S), speculative load pipeline, L1 data cache, TLB permission enforcement |
| **Affected Domains** | Microarch Security, Kernel Security, Confidential AI / TEE |
| **Affected SoC Families** | Primarily Intel (pre-Whiskey Lake), some ARM cores — processors that defer privilege-check fault to retirement |
| **Preconditions** | Code execution at user level; kernel memory mapped (but protected) in user address space; processor that speculatively forwards data before privilege check completes |
| **Key Mitigations** | KPTI / KAISER (unmap kernel from user page tables), hardware fixes that check permissions before speculative forwarding, L1 data cache flush on privilege transitions |
| **Verification Approach** | Tier 3 — microarchitectural analysis confirming privilege check is enforced before speculative data forwarding; Tier 1 — SVA for page table U/S bit enforcement at the architectural level |
| **Related Requirements** | REQ-CHERI-003 (permission enforcement), REQ-CHERI-011 (PMP/capability interaction) |

---

## UARCH-005: MDS — RIDL (Rogue In-Flight Data Load)

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I) |
| **Description** | Speculative load instructions can sample stale data from microarchitectural line fill buffers (LFBs), which are shared across hardware threads and privilege levels on the same physical core. When a load encounters certain fault or assist conditions, the processor may speculatively forward data from an LFB entry belonging to a different security context. The attacker encodes the leaked data into cache state for later extraction. |
| **Target Assets** | Line fill buffers (LFBs), speculative load pipeline, L1 data cache, SMT thread shared structures |
| **Affected Domains** | Microarch Security, Kernel Security, Confidential AI / TEE, TDISP / CXL |
| **Affected SoC Families** | Primarily Intel — processors with shared line fill buffers across SMT threads |
| **Preconditions** | Code execution on the same physical core (especially SMT sibling) as victim; ability to trigger faulting or assisting loads that read from LFBs |
| **Key Mitigations** | VERW-based buffer overwrite (MD_CLEAR), disabling SMT in high-security contexts, L1D flush on context switch, microcode updates to drain LFBs on privilege transitions |
| **Verification Approach** | Tier 3 — microarchitectural simulation verifying LFB data is not forwarded across security domains; Tier 2 — firmware review for MD_CLEAR usage |
| **Related Requirements** | REQ-CXL-011 (coherence protocol isolation) |

---

## UARCH-006: MDS — Fallout (Store Buffer Data Sampling)

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I) |
| **Description** | A variant of MDS where the attacker samples stale data from the store buffer. When a speculative load encounters an assist or page fault, the processor may forward data from a store buffer entry belonging to a different privilege domain. This can leak recent store values from kernel or hypervisor execution, including data written during exception handlers. The attack is particularly effective because store buffers are not fully partitioned across privilege levels. |
| **Target Assets** | Store buffer, speculative load pipeline, page fault handling path, L1 data cache |
| **Affected Domains** | Microarch Security, Kernel Security, Confidential AI / TEE |
| **Affected SoC Families** | Primarily Intel — processors with store-buffer forwarding on faulting loads |
| **Preconditions** | Code execution on the same physical core as victim; ability to trigger page faults or assists that lead to store buffer sampling |
| **Key Mitigations** | VERW-based buffer overwrite (MD_CLEAR), store buffer partitioning in hardware, disabling SMT, microcode updates to prevent cross-domain store buffer forwarding |
| **Verification Approach** | Tier 3 — microarchitectural simulation confirming store buffer isolation across privilege domains; Tier 2 — firmware review for MD_CLEAR on context switch |
| **Related Requirements** | REQ-CXL-011 (coherence protocol isolation) |

---

## UARCH-007: MDS — ZombieLoad (Fill Buffer Leakage Under TSX Abort)

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I) |
| **Description** | Exploits Intel TSX (Transactional Synchronization Extensions) abort behavior combined with fill buffer leakage. When a TSX transaction aborts, the processor squashes the transactional work but may speculatively forward stale data from fill buffers during the abort window. The attacker wraps faulting loads inside a TSX transaction, suppressing the fault while retaining the cache side-effects of speculatively accessed fill buffer data. This provides a reliable, exception-free Meltdown/MDS primitive. |
| **Target Assets** | TSX abort handling, line fill buffers, speculative execution pipeline, L1 data cache |
| **Affected Domains** | Microarch Security, Kernel Security, Confidential AI / TEE |
| **Affected SoC Families** | Intel — processors with TSX support and shared fill buffers |
| **Preconditions** | TSX enabled on the target processor; code execution on the same physical core as victim; ability to craft TSX transactions that trigger aborts |
| **Key Mitigations** | Disabling TSX (tsx=off), VERW-based buffer overwrite (MD_CLEAR), TAA-specific microcode mitigations, disabling SMT, hardware redesign to drain buffers on TSX abort |
| **Verification Approach** | Tier 3 — microarchitectural analysis of TSX abort paths for data leakage from fill buffers; Tier 2 — configuration review for TSX disable policy |
| **Related Requirements** | REQ-CXL-011 (coherence protocol isolation) |

---

## UARCH-008: L1 Terminal Fault / Foreshadow (L1 Cache Speculation on Terminal PTEs)

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I), Elevation of Privilege (E) |
| **Description** | When the processor encounters a terminal page table entry (PTE with Present=0 or Reserved bits set), it raises a fault. However, before the fault is delivered, the speculative execution pipeline may use the physical address from the PTE (even though it is invalid) to read from L1 data cache if data matching that physical address is resident. This allows an attacker to read any L1-resident data by crafting PTEs pointing to the victim's physical addresses. Foreshadow variants target SGX enclaves (original), OS/VMM data (L1TF-OS), and cross-VM data (L1TF-VMM). |
| **Target Assets** | L1 data cache, page table entries (terminal/invalid), SGX enclave memory, VM physical memory, speculative load pipeline |
| **Affected Domains** | Microarch Security, Kernel Security, Confidential AI / TEE, TDISP / CXL |
| **Affected SoC Families** | Primarily Intel — processors that speculatively access L1D using physical address from terminal PTEs |
| **Preconditions** | Ability to manipulate page table entries (e.g., unmapping pages to create terminal PTEs); target data must be L1D-resident; for cross-VM variant, attacker VM on the same physical core |
| **Key Mitigations** | L1D flush on VM entry/exit, PTE inversion (ensure physical address in non-present PTEs does not alias valid frames), disabling EPT A/D bits, core scheduling (no untrusted SMT sibling), hardware fixes to block speculative access on terminal PTEs |
| **Verification Approach** | Tier 3 — microarchitectural analysis of PTE handling in speculative pipeline; Tier 2 — firmware review for L1D flush policy on VM transitions |
| **Related Requirements** | REQ-TDISP-005 (RUN state access control), REQ-CXL-007 (memory partition isolation) |

---

## UARCH-009: Downfall (Gather Data Sampling)

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I) |
| **Description** | The AVX2/AVX-512 GATHER instruction, which loads data from non-contiguous memory addresses into a vector register, can speculatively expose data from other security contexts through the shared gather buffer. When a gather operation encounters a fault or assist, stale data from prior gather operations (potentially from a different privilege domain or SMT sibling) may be forwarded. This leaks data from vector register files and caches across security boundaries. |
| **Target Assets** | AVX gather buffer, vector register file, speculative gather execution unit, L1/L2 cache |
| **Affected Domains** | Microarch Security, Kernel Security, Confidential AI / TEE |
| **Affected SoC Families** | Intel — processors with AVX2/AVX-512 gather support (6th–11th generation) |
| **Preconditions** | Code execution on the same physical core as victim; victim uses AVX/AVX-512 operations (common in cryptographic libraries, ML inference, multimedia); ability to execute gather instructions with faulting addresses |
| **Key Mitigations** | Microcode update (GDS mitigation), gather instruction serialization, disabling AVX-512 gather in untrusted contexts, clearing vector registers on context switch, hardware redesign of gather data path |
| **Verification Approach** | Tier 3 — microarchitectural simulation of gather data path across privilege boundaries; Tier 2 — firmware review for GDS microcode mitigation enablement |
| **Related Requirements** | REQ-CXL-011 (coherence protocol isolation) |

---

## UARCH-010: Zenbleed (VZEROUPPER Speculative Register State Leak)

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I) |
| **Description** | A bug in AMD Zen 2 processors where the VZEROUPPER instruction (which clears the upper 128 bits of YMM registers) can interact incorrectly with speculative execution and register renaming. Under specific conditions involving mispredicted branches and XMM register save/restore operations, the processor may expose stale data from the physical register file — data that belonged to another thread, process, or privilege level. This leaks register contents at 30 bytes per core per second without requiring any special privileges. |
| **Target Assets** | YMM/XMM register file, physical register rename table, VZEROUPPER execution unit, speculative execution pipeline |
| **Affected Domains** | Microarch Security, Kernel Security, Confidential AI / TEE |
| **Affected SoC Families** | AMD Zen 2 family — EPYC Rome, Ryzen 3000/4000 series |
| **Preconditions** | Code execution on a core sharing the physical register file; no special privileges required; the vulnerability is a hardware bug, not a design-level speculation issue |
| **Key Mitigations** | Microcode update (chicken bit DE_CFG[9]), software workaround setting MSR bit, hardware fix in subsequent Zen generations, clearing vector registers on context switch as defense-in-depth |
| **Verification Approach** | Tier 3 — microarchitectural simulation of VZEROUPPER interaction with register renaming and speculative rollback; Tier 1 — SVA for register clearing on context switch |
| **Related Requirements** | REQ-CXL-011 (coherence protocol isolation) |

---

## UARCH-011: Inception (Phantom Speculation via Recursive Branch Predictor Poisoning)

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I) |
| **Description** | Combines two techniques: Phantom Speculation (triggering speculative execution at non-branch instructions through branch predictor aliasing) and Training in Transient Execution (recursive poisoning of branch predictor state during speculative windows). The attacker forces the processor to speculatively execute instructions at an address of the attacker's choosing, even if no branch exists at that point in the victim code. The recursion amplifies the speculative window, enabling full Spectre-like data extraction without requiring a real gadget in the victim. |
| **Target Assets** | Branch predictor (BPU), BTB, return predictor, speculative execution pipeline, L1 data cache |
| **Affected Domains** | Microarch Security, Kernel Security, Confidential AI / TEE |
| **Affected SoC Families** | AMD — Zen 1 through Zen 4 family processors |
| **Preconditions** | Code execution on the same physical core; ability to train the branch predictor to create phantom branches at victim code addresses; deep understanding of microarchitectural predictor aliasing |
| **Key Mitigations** | Microcode updates (IBPB-like flush for phantom prediction), SRSO (Safe Return Speculation on Overflow) mitigation, ensuring IBPB flushes all predictor state including phantom entries, hardware predictor redesign in newer generations |
| **Verification Approach** | Tier 3 — microarchitectural simulation verifying branch predictor cannot be trained to create phantom branches across privilege domains; Tier 2 — firmware review for IBPB and SRSO mitigation |
| **Related Requirements** | REQ-CHERI-007 (compartment isolation) |

---

## UARCH-012: GhostRace (Speculative Race Conditions)

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I), Elevation of Privilege (E) |
| **Description** | Synchronization primitives (mutexes, spinlocks, rwlocks) that enforce mutual exclusion at the architectural level can be speculatively bypassed. When the processor mispredicts a branch guarding a lock acquisition (e.g., predicting the lock is free when it is held), it speculatively executes the critical section without holding the lock. This creates a speculative race condition where the attacker's speculative execution overlaps with the victim's legitimate access to shared data, enabling use-after-free-like reads and data leakage through cache side-channels. |
| **Target Assets** | Synchronization primitives (locks, semaphores), speculative execution pipeline, shared data structures protected by locks, L1 data cache |
| **Affected Domains** | Microarch Security, Kernel Security, Confidential AI / TEE |
| **Affected SoC Families** | All — any processor with speculative execution across synchronization primitives (Intel, AMD, ARM, RISC-V out-of-order cores) |
| **Preconditions** | Concurrent execution with the victim (same core or SMT); victim uses conditional synchronization (branches guarding lock checks); attacker can influence branch prediction state |
| **Key Mitigations** | Speculation barriers after lock acquisition checks, Speculative-Safe synchronization primitives (serialize after lock), hardware lock awareness in speculation pipeline, IPI-based flush for speculative concurrent use-after-free |
| **Verification Approach** | Tier 3 — concurrency-aware microarchitectural analysis of synchronization primitive speculation; Tier 2 — kernel code review for speculation barriers in lock paths |
| **Related Requirements** | REQ-CHERI-007 (compartment isolation) |

---

## UARCH-013: Training Solo (Intra-Domain Spectre via Same-Domain BTB Training)

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I) |
| **Description** | Bypasses existing Spectre mitigations (IBRS, STIBP, IBPB) by exploiting the fact that these defenses focus on cross-domain branch predictor isolation. Training Solo demonstrates that an attacker can train the branch predictor from within the same security domain — the same privilege level and address space — and still redirect speculative execution to leak data. This leverages self-training gadgets that exist within the victim domain (e.g., the kernel itself) to mount Spectre v2-style attacks without cross-domain BTB poisoning. |
| **Target Assets** | BTB (same-domain entries), indirect branch predictor, kernel/hypervisor code gadgets, speculative execution pipeline |
| **Affected Domains** | Microarch Security, Kernel Security, Confidential AI / TEE |
| **Affected SoC Families** | Intel, AMD — processors where intra-domain BTB training can redirect speculation to arbitrary gadgets |
| **Preconditions** | Code execution within the target security domain (e.g., user-space syscall entry); existence of usable gadgets within the domain; current IBRS/STIBP mitigations in place (attack bypasses them) |
| **Key Mitigations** | Fine-grained branch predictor flushing (intra-domain), BHI (Branch History Injection) mitigations, hardware predictor redesign with per-context BTB state, gadget elimination in kernel (retpoline, BHB clearing sequences) |
| **Verification Approach** | Tier 3 — microarchitectural analysis of intra-domain BTB training effectiveness with current mitigations; Tier 2 — kernel review for gadget-free paths on privilege transitions |
| **Related Requirements** | REQ-CHERI-007 (compartment isolation) |

---

## UARCH-014: Prime+Probe Cache Side-Channel

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I) |
| **Description** | The attacker fills (primes) specific cache sets with their own data, waits for the victim to execute, then probes the same cache sets by timing re-accesses. If the victim accessed memory mapping to a primed cache set, the attacker's data will have been evicted, and the probe access will be slow (cache miss). By monitoring which cache sets experienced evictions, the attacker infers the victim's memory access patterns. Unlike Flush+Reload, Prime+Probe does not require shared memory with the victim, making it applicable across VM boundaries and against hardened targets. |
| **Target Assets** | L1/L2/LLC cache (set-associative structure), cache replacement policy, memory access patterns of victim, timing measurement infrastructure |
| **Affected Domains** | Microarch Security, Kernel Security, Confidential AI / TEE, TDISP / CXL |
| **Affected SoC Families** | All — any processor with shared set-associative caches |
| **Preconditions** | Code execution sharing cache resources with the victim (same core, or same LLC); ability to perform precise timing measurements; knowledge of cache geometry (sets, ways, replacement policy) |
| **Key Mitigations** | Cache partitioning (CAT/way-partitioning for LLC, set-partitioning for L1/L2), cache randomization (CEASER, ScatterCache), noise injection on timing measurements, constant-time algorithm implementation in sensitive code |
| **Verification Approach** | Tier 3 — microarchitectural simulation measuring cross-domain cache set contention; Tier 2 — review of cache partitioning configuration in hypervisor/firmware |
| **Related Requirements** | REQ-CXL-011 (coherence protocol isolation), REQ-CXL-007 (memory partition isolation) |

---

## UARCH-015: Flush+Reload Cache Side-Channel

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I) |
| **Description** | The attacker flushes a shared memory line from the cache (using instructions like CLFLUSH), waits for the victim to execute, then reloads the same address and measures the access time. If the victim accessed the shared line, it will be in cache (fast reload); otherwise it will be a cache miss (slow reload). This provides bit-level granularity of the victim's memory accesses. Flush+Reload is the primary cache covert channel used in Spectre, Meltdown, and other transient execution attacks as the data exfiltration mechanism. |
| **Target Assets** | Shared memory pages (shared libraries, deduplicated pages, shared executables), L1/L2/LLC cache, CLFLUSH instruction, timing measurement infrastructure |
| **Affected Domains** | Microarch Security, Kernel Security, Confidential AI / TEE |
| **Affected SoC Families** | All — any processor with cache flush instructions and shared memory between security domains |
| **Preconditions** | Shared memory with the victim (shared libraries, page deduplication, memory-mapped files); ability to execute cache flush instructions; high-resolution timer access |
| **Key Mitigations** | Disable page deduplication (KSM) across security domains, restrict cache flush instruction to privileged code, timer coarsening/jittering, disable shared library mapping across trust boundaries, constant-time coding practices |
| **Verification Approach** | Tier 3 — microarchitectural analysis of shared memory cache behavior across security boundaries; Tier 2 — OS/hypervisor configuration review for page deduplication and CLFLUSH access policies |
| **Related Requirements** | REQ-CXL-011 (coherence protocol isolation), REQ-CHERI-007 (compartment isolation) |

---

## UARCH-016: Evict+Time Cache Side-Channel

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I) |
| **Description** | The attacker evicts specific cache sets by accessing conflicting addresses, then triggers victim execution and measures the victim's total execution time. If the victim's access hits evicted cache lines, execution is slower. Unlike Flush+Reload (which requires shared memory) and Prime+Probe (which monitors specific sets), Evict+Time measures overall timing difference, making it coarser but applicable in more restricted environments. It is effective for recovering coarse-grained access patterns such as which lookup table an AES implementation accesses. |
| **Target Assets** | L1/L2 cache, cache set eviction mechanism, victim execution timing, cryptographic lookup tables |
| **Affected Domains** | Microarch Security, Kernel Security, Confidential AI / TEE |
| **Affected SoC Families** | All — any processor with shared caches and observable timing differences |
| **Preconditions** | Code execution sharing cache with the victim; ability to evict specific cache sets through conflict accesses; ability to trigger and time victim operations |
| **Key Mitigations** | Cache partitioning, constant-time algorithm implementation (avoid secret-dependent table lookups), cache randomization, preloading sensitive data to eliminate timing variance, bitsliced cryptographic implementations |
| **Verification Approach** | Tier 3 — timing analysis of victim operations under controlled cache eviction; Tier 2 — cryptographic code review for table-lookup patterns |
| **Related Requirements** | REQ-CXL-011 (coherence protocol isolation) |

---

## UARCH-017: TLBleed (TLB Set Contention Side-Channel)

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I) |
| **Description** | Exploits contention on Translation Lookaside Buffer (TLB) sets between SMT sibling threads sharing the same physical core. The attacker monitors which TLB sets experience evictions caused by the victim's memory accesses, revealing the victim's page-level access patterns. Because TLB sets are indexed by virtual page number, TLBleed can distinguish which pages the victim accesses. This has been demonstrated to extract cryptographic keys from constant-time implementations that were believed immune to cache attacks, because TLB access patterns differ even when cache access patterns are constant. |
| **Target Assets** | TLB (instruction and data), TLB set-associative structure, SMT shared TLB partitions, page-level access patterns |
| **Affected Domains** | Microarch Security, Kernel Security, Confidential AI / TEE |
| **Affected SoC Families** | All — processors with shared or partitioned TLB between SMT threads (Intel, AMD) |
| **Preconditions** | SMT sibling execution with the victim on the same physical core; ability to perform precise TLB timing measurements; knowledge of TLB geometry |
| **Key Mitigations** | Disabling SMT for high-security workloads, TLB partitioning between SMT threads, core scheduling (dedicate physical cores to security domains), TLB flushing on context switch, PCID-based TLB tagging |
| **Verification Approach** | Tier 3 — microarchitectural simulation of TLB set contention across SMT threads; Tier 2 — configuration review for SMT policy and core scheduling |
| **Related Requirements** | REQ-CXL-011 (coherence protocol isolation) |

---

## UARCH-018: PortSmash (Execution Port Contention Side-Channel)

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I) |
| **Description** | Exploits contention on shared execution port resources between SMT sibling threads. The attacker issues instructions targeting specific execution ports and measures timing variations caused by the victim's instructions competing for the same ports. Because different instruction types use different execution ports, the attacker can infer which instruction sequence the victim is executing. This has been demonstrated to extract P-384 ECDSA private keys from OpenSSL by observing execution port usage patterns during scalar multiplication. |
| **Target Assets** | Execution ports (ALU, FPU, load/store, vector units), SMT shared execution resources, instruction scheduling/dispatch logic |
| **Affected Domains** | Microarch Security, Kernel Security, Confidential AI / TEE |
| **Affected SoC Families** | All — processors with SMT sharing execution ports (Intel, AMD) |
| **Preconditions** | SMT sibling execution with the victim on the same physical core; ability to perform precise timing measurements of port contention; knowledge of port allocation for specific instruction types |
| **Key Mitigations** | Disabling SMT for high-security workloads, constant-time coding (uniform instruction sequences regardless of secret), core scheduling, hardware port partitioning between SMT threads, execution port randomization |
| **Verification Approach** | Tier 3 — microarchitectural simulation of execution port contention across SMT threads; Tier 2 — cryptographic code review for non-uniform instruction patterns |
| **Related Requirements** | REQ-CXL-011 (coherence protocol isolation) |

---

## UARCH-019: Prefetch-Based Side-Channel (Data-Dependent Prefetch Leakage)

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I) |
| **Description** | Hardware prefetch units that observe memory access patterns and predict future accesses can leak information about the victim's access behavior. Data Memory-dependent Prefetcher (DMP) implementations may dereference data values as pointers, causing prefetch of memory addresses derived from the data itself — leaking the data content through cache state observable to the attacker. Software prefetch instructions can also be exploited: prefetch timing reveals whether an address is cached, providing a non-faulting probe mechanism that bypasses many Spectre/Meltdown mitigations. |
| **Target Assets** | Hardware prefetch unit (DMP, stride prefetcher, stream prefetcher), prefetch instruction (PREFETCH/PREFETCHNTA), L1/L2/LLC cache, memory access pattern predictor |
| **Affected Domains** | Microarch Security, Kernel Security, Confidential AI / TEE |
| **Affected SoC Families** | Apple (M-series with DMP), Intel (IP-based prefetcher), all processors with software-accessible prefetch instructions |
| **Preconditions** | For DMP: victim data resembles pointer values and DMP is active; for prefetch-probe: ability to execute prefetch instructions targeting victim address space; shared cache with the victim |
| **Key Mitigations** | Disable DMP for sensitive workloads (DIT bit on ARM), mask pointer values to prevent DMP-triggered prefetch of secrets, restrict software prefetch instruction to privileged mode, constant-time implementations avoiding data-dependent memory patterns |
| **Verification Approach** | Tier 3 — microarchitectural analysis of prefetcher behavior with secret-derived address patterns; Tier 2 — firmware/OS review for DMP control and prefetch instruction access policy |
| **Related Requirements** | REQ-CXL-011 (coherence protocol isolation) |

---

## UARCH-020: Cache Occupancy Channel (LLC Occupancy-Based Covert Channel)

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I) |
| **Description** | The attacker infers the victim's activity by monitoring the overall occupancy (fill level) of the Last-Level Cache (LLC). As the victim executes, its working set occupies LLC capacity, evicting the attacker's lines. By periodically measuring how many of its own cache lines remain resident, the attacker determines the victim's LLC footprint over time. This coarse-grained channel reveals program phases, working set sizes, and activity patterns. It is particularly concerning because it works across cores (LLC is shared) and is resistant to cache partitioning schemes that only isolate specific sets or ways. |
| **Target Assets** | LLC (Last-Level Cache), cache replacement policy (LRU/pseudo-LRU), LLC capacity, memory subsystem bandwidth |
| **Affected Domains** | Microarch Security, Kernel Security, Confidential AI / TEE, TDISP / CXL |
| **Affected SoC Families** | All — any SoC with shared LLC across cores or security domains |
| **Preconditions** | Code execution sharing the LLC with the victim (typically any core on the same die); ability to measure own cache residency (timing-based); no requirement for shared memory or same-core execution |
| **Key Mitigations** | LLC capacity partitioning (CAT — Cache Allocation Technology), QoS-based LLC isolation, memory bandwidth throttling, noise injection into cache replacement, dedicated LLC slices per security domain, physical core isolation |
| **Verification Approach** | Tier 3 — LLC occupancy measurements across security domains under varying workload; Tier 2 — review of CAT/QoS configuration and LLC partitioning policy |
| **Related Requirements** | REQ-CXL-007 (memory partition isolation), REQ-CXL-011 (coherence protocol isolation) |

---

*[FROM TRAINING] Threat descriptions are based on publicly known attack classes from academic literature (including original Spectre/Meltdown papers, MDS disclosures, and subsequent microarchitectural security research). Verify against current threat landscape assessments and vendor security advisories. Last verified: 2026-02-13.*
