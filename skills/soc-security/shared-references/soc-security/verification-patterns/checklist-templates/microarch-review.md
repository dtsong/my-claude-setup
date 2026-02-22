# Microarchitectural Security Assessment Checklist

## Purpose

Checklist for reviewing microarchitectural security properties of an SoC processor design. Covers speculative execution vulnerabilities, cache side-channel resistance, branch predictor security, and shared resource isolation. Used as a quality gate for processor cores and accelerators that handle security-sensitive workloads.

---

## Verification Tier Reference

- **Tier 1 (mechanical):** SVA assertions for barrier insertion, flush behavior, partitioning config — HIGH confidence
- **Tier 2 (protocol):** Natural-language property descriptions for microarchitectural behavior — needs review
- **Tier 3 (microarch simulation):** Requires microarchitectural simulation with side-channel oracles or lab measurement — cannot be verified in RTL simulation alone

---

## Speculative Execution

- [ ] **Speculation barrier at privilege transitions:** Verify that speculation barriers (e.g., CSDB, SSBB, lfence) are inserted at all privilege level transitions (user/kernel, kernel/hypervisor).
  - *Verification:* Tier 1 — SVA assertion that barrier instruction precedes first memory access after privilege change.
  - *Confidence:* HIGH if barrier insertion is architectural; MEDIUM if firmware-dependent.

- [ ] **Bounds check bypass (Spectre-PHT / v1):** Verify that array bounds checks are not bypassed by speculative execution of the taken path.
  - *Verification:* Tier 2 — Property description for PHT-based speculation behavior; Tier 3 — microarch simulation with cache oracle.
  - *Confidence:* LOW — requires microarchitectural analysis beyond RTL assertions.

- [ ] **Branch target injection (Spectre-BTB / v2):** Verify that the BTB is partitioned or flushed across security domain transitions.
  - *Verification:* Tier 1 — SVA assertion for BTB flush/invalidate at domain switch; Tier 2 — property for BTB partitioning policy.
  - *Confidence:* HIGH for flush verification; MEDIUM for partitioning completeness.

- [ ] **Return stack buffer poisoning (Spectre-RSB):** Verify that the RSB is managed (stuffed or flushed) at context switches to prevent cross-domain return target injection.
  - *Verification:* Tier 1 — SVA assertion for RSB management at context switch; Tier 2 — property description.
  - *Confidence:* HIGH if hardware-managed; MEDIUM if software-managed.

- [ ] **Speculative store bypass (Spectre-SSB / v4):** Verify that speculative loads cannot bypass pending stores to read stale data across security boundaries.
  - *Verification:* Tier 2 — property description for store buffer forwarding policy; Tier 3 — microarch simulation.
  - *Confidence:* LOW — store buffer behavior is microarchitecturally complex.

- [ ] **Meltdown-class (rogue data load):** Verify that speculative loads from privileged memory do not forward data to dependent operations before permission checks complete.
  - *Verification:* Tier 2 — property for permission check ordering relative to data forwarding; Tier 3 — microarch simulation.
  - *Confidence:* LOW — depends on pipeline implementation details.

- [ ] **Microarchitectural data sampling (MDS):** Verify that internal buffers (line fill, store, load port) do not leak data across security domains through speculative forwarding.
  - *Verification:* Tier 3 — requires microarchitectural simulation with buffer state oracles.
  - *Confidence:* LOW — buffer-level leakage requires detailed microarchitectural knowledge.

---

## Cache Side-Channels

- [ ] **Cache partitioning across security domains:** Verify that cache partitioning (way-based or set-based) is enforced between security domains (e.g., TEE vs. non-TEE, different VMs).
  - *Verification:* Tier 1 — SVA assertion for cache way/set allocation register configuration; Tier 2 — property for partition enforcement.
  - *Confidence:* HIGH for configuration; MEDIUM for enforcement completeness.

- [ ] **Flush+Reload resistance:** Verify that shared memory pages across security domains do not allow cache line state observation through flush and timing measurement.
  - *Verification:* Tier 3 — requires cache timing simulation or lab measurement.
  - *Confidence:* LOW — fundamentally a timing-based observation.

- [ ] **Prime+Probe resistance:** Verify that cache set contention across security domains does not create observable eviction patterns.
  - *Verification:* Tier 3 — requires cache set contention simulation.
  - *Confidence:* LOW — requires cache geometry and replacement policy analysis.

- [ ] **Cache line granularity leakage:** Verify that cache line-level access patterns within a security domain are not observable from outside the domain.
  - *Verification:* Tier 3 — requires access pattern simulation with cache oracle.
  - *Confidence:* LOW — sub-cache-line analysis is highly microarchitecture-specific.

- [ ] **L1/L2/LLC isolation on context switch:** Verify that cache flush or partition reconfiguration occurs at security domain context switches per the partitioning policy.
  - *Verification:* Tier 1 — SVA assertion for cache maintenance operations at domain switch.
  - *Confidence:* HIGH if flush-based; MEDIUM if partition-based.

---

## Branch Prediction

- [ ] **BTB domain tagging or partitioning:** Verify that BTB entries are tagged with security domain identifiers or that the BTB is partitioned to prevent cross-domain training.
  - *Verification:* Tier 1 — SVA assertion for BTB entry domain tag fields; Tier 2 — property for partitioning completeness.
  - *Confidence:* HIGH for tag presence; MEDIUM for collision resistance.

- [ ] **PHT isolation:** Verify that pattern history table entries cannot be trained by one security domain and exploited by another.
  - *Verification:* Tier 2 — property for PHT partitioning or clearing policy; Tier 3 — microarch simulation.
  - *Confidence:* LOW — PHT indexing schemes may create aliasing across domains.

- [ ] **Indirect branch predictor isolation:** Verify that indirect branch predictors are partitioned or flushed at security domain transitions.
  - *Verification:* Tier 1 — SVA assertion for indirect predictor flush at domain switch; Tier 2 — property description.
  - *Confidence:* HIGH for flush; MEDIUM for partitioning.

- [ ] **Branch predictor state not observable:** Verify that branch predictor state (taken/not-taken history) is not observable through timing differences from outside the security domain.
  - *Verification:* Tier 3 — requires timing analysis of branch prediction hit/miss.
  - *Confidence:* LOW — timing observation requires lab measurement.

---

## TLB Security

- [ ] **TLB flush at security domain transitions:** Verify that TLB entries are flushed or tagged at all security domain transitions (privilege changes, VM exits, TEE entry/exit).
  - *Verification:* Tier 1 — SVA assertion for TLB invalidation at domain transition.
  - *Confidence:* HIGH.

- [ ] **PCID/VMID/ASID enforcement:** Verify that TLB entries are tagged with process/VM/address space identifiers and that cross-domain lookups are prevented.
  - *Verification:* Tier 1 — SVA assertion for PCID/VMID tag matching on TLB lookup.
  - *Confidence:* HIGH.

- [ ] **TLB covert channel resistance:** Verify that TLB set contention does not create a cross-domain covert channel.
  - *Verification:* Tier 3 — requires TLB contention simulation.
  - *Confidence:* LOW — TLB geometry and replacement policy dependent.

---

## Shared Resources

- [ ] **Functional unit contention isolation:** Verify that shared functional units (ALU, FPU, crypto units) do not leak information through contention-based timing differences across security domains.
  - *Verification:* Tier 3 — requires timing analysis of functional unit contention.
  - *Confidence:* LOW — contention timing is microarchitecture-specific.

- [ ] **Memory bandwidth partitioning:** Verify that memory bandwidth allocation prevents one security domain from inferring another's memory access patterns through bandwidth contention.
  - *Verification:* Tier 2 — property for QoS/bandwidth partitioning policy; Tier 1 — SVA for QoS register configuration.
  - *Confidence:* MEDIUM — bandwidth partitioning effectiveness varies.

- [ ] **Prefetcher isolation:** Verify that hardware prefetchers do not create cross-domain observable state (prefetch requests from domain A do not affect cache state visible to domain B).
  - *Verification:* Tier 2 — property for prefetcher domain awareness; Tier 3 — cache state simulation.
  - *Confidence:* LOW — prefetcher behavior is complex and design-specific.

- [ ] **ROB/reservation station isolation:** Verify that reorder buffer and reservation station occupancy do not leak information across security domains through timing.
  - *Verification:* Tier 3 — requires pipeline timing simulation.
  - *Confidence:* LOW — internal pipeline state observation is subtle.

- [ ] **Interrupt/exception timing isolation:** Verify that interrupt and exception handling timing does not vary based on security-sensitive state from another domain.
  - *Verification:* Tier 2 — property for interrupt handling timing invariance; Tier 3 — timing measurement.
  - *Confidence:* LOW — interrupt latency variation is implementation-dependent.

---

## Mitigation Verification

- [ ] **Constant-time execution mode (DIT/Zkt):** If the processor supports a constant-time execution mode, verify that data-dependent timing variation is eliminated for all covered instruction classes.
  - *Verification:* Tier 1 — SVA assertion that DIT/Zkt mode selects constant-time datapaths; Tier 3 — timing measurement.
  - *Confidence:* HIGH for datapath selection; LOW for timing verification.

- [ ] **Speculation barrier effectiveness:** Verify that speculation barriers actually prevent speculative execution past the barrier point (not just architecturally ordered but microarchitecturally enforced).
  - *Verification:* Tier 2 — property for barrier microarchitectural semantics; Tier 3 — microarch simulation.
  - *Confidence:* MEDIUM — depends on barrier implementation.

- [ ] **KPTI / kernel page table isolation:** Verify that kernel page table entries are not mapped in user-mode page tables (or are marked non-accessible).
  - *Verification:* Tier 1 — SVA assertion for page table entry permission bits at privilege transition.
  - *Confidence:* HIGH.

- [ ] **SMAP/SMEP enforcement:** Verify that supervisor mode access prevention and execution prevention are hardware-enforced and cannot be bypassed during speculative execution.
  - *Verification:* Tier 1 — SVA assertion for SMAP/SMEP check logic; Tier 2 — property for speculative enforcement.
  - *Confidence:* HIGH for architectural enforcement; MEDIUM for speculative paths.

---

## Review Outcome

| Outcome | Criteria |
|---|---|
| **Pass** | All Tier 1 items checked; Tier 2/3 items assessed with documented gaps |
| **Pass with Findings** | Tier 1 items pass; some Tier 2/3 gaps with documented risk acceptance |
| **Revise** | Tier 1 failures or unassessed Tier 2/3 items for critical security domains |
