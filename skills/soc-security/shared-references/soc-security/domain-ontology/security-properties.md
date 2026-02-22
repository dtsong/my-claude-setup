# Security Properties — SoC Hardware Security Ontology

## Purpose

This reference defines the canonical set of hardware security properties used across all skills in the SoC Security Suite. Every threat model finding, verification assertion, compliance requirement, and executive brief traces back to one or more of these properties. Consistent use of these definitions prevents ambiguity when the same term carries different connotations across standards (e.g., "integrity" in DICE vs. "integrity" in CXL IDE).

**Primary consumers:** threat-model-skill, verification-scaffold-skill, compliance-pipeline-skill
**Secondary consumers:** executive-brief-skill (maps properties to business-risk language)

---

## Quick Reference

| Property | One-Line Definition | Key Standards |
|---|---|---|
| Confidentiality | Preventing unauthorized disclosure of data | CXL IDE, TEE, PCIe IDE, FIPS 140-3 |
| Integrity | Detecting unauthorized modification of data or code | DICE, SPDM, CXL IDE, PCIe IDE |
| Authenticity | Verifying the identity of an entity or origin of data | SPDM, DICE, TDISP, X.509 |
| Availability | Ensuring timely access to resources and services | ISO 21434, FIPS 140-3 |
| Isolation | Enforcing boundaries between security domains | TEE, TDISP, CHERI, CXL TSP |
| Attestation | Providing verifiable evidence of platform state | DICE, SPDM, TCG, CXL TSP |
| Non-Repudiation | Preventing denial of previously committed actions | DICE certificates, audit logs |
| Freshness | Guaranteeing recency of data, keys, or measurements | SPDM nonces, DICE CDI rotation |
| Access Control | Restricting operations based on identity or capability | CHERI, bus firewalls, register locks |
| Side-Channel Resistance | Mitigating information leakage through physical observables | FIPS 140-3, ISO 21434, custom |
| Speculation Safety | Ensuring speculative execution does not leak across domains | Speculation barriers, Zkt, DIT |
| Leakage Resistance | Preventing key-dependent information leakage through physical observables | ISO 17825, FIPS 140-3 Level 3+, JIL |
| Privilege Separation | Enforcing strict boundaries between privilege levels | RISC-V Priv Spec, ARM EL, KSPP |
| Formal Verifiability | Expressing security claims as mathematically checkable properties | TLA+, DO-333, CC EAL7 |

---

## Property Definitions

### 1. Confidentiality

**Definition:** The property that data is not disclosed to unauthorized entities — including hardware components, firmware layers, debug interfaces, and co-tenant workloads — at rest, in transit, or during processing.

**Relevance to SoC security:**
- Memory encryption engines (AES-XTS, AES-XEX) protect DRAM contents from physical probing and co-tenant read
- Link encryption (PCIe IDE, CXL IDE) protects data traversing on-chip and off-chip interconnects
- TEE memory isolation prevents hypervisor or adjacent VMs from reading enclave/realm memory
- Key material stored in hardware fuses, PUFs, or volatile SRAM must resist extraction through debug, fault injection, or side-channel

**Typical verification approaches:**
- Tier 1: SVA assertions that encrypted bus transactions do not appear in cleartext on unprotected interfaces
- Tier 2: Protocol-level checks that IDE stream setup completes before data transfer begins
- Tier 3: Information-flow analysis for covert channels across clock/power domains

**Related standards:** PCIe IDE (ECN), CXL 3.1 IDE, FIPS 140-3 (Section 7.2 — Key Management), ARM CCA (Realm Management Extension)

---

### 2. Integrity

**Definition:** The property that data, code, configuration, or hardware state has not been modified by unauthorized entities, and that any unauthorized modification is detectable.

**Relevance to SoC security:**
- Boot chain integrity: each stage measures the next before execution (DICE model)
- Link integrity: MACs on PCIe IDE / CXL IDE TLPs detect in-flight tampering
- Firmware integrity: signed firmware images verified against OTP-fused public key hashes
- Register integrity: one-time lock bits prevent reconfiguration of security-critical registers after boot
- Measurement integrity: DICE CDI chain ensures that any change in firmware produces a different identity

**Typical verification approaches:**
- Tier 1: SVA assertions for register lock behavior (write-once, sticky bits), MAC check completion before data acceptance
- Tier 2: Protocol property checks for DICE measurement chain correctness, SPDM measurement response integrity
- Tier 3: Formal verification of hash chain properties, information-flow integrity across trust boundaries

**Related standards:** TCG DICE v1.2 (CDI derivation), DMTF SPDM v1.4 (measurement), PCIe IDE (integrity mode), CXL 3.1 IDE, ISO 21434 (work product integrity)

---

### 3. Authenticity

**Definition:** The property that the identity of an entity (device, firmware layer, platform, or communication peer) can be verified, and that data can be attributed to a verified origin.

**Relevance to SoC security:**
- SPDM device authentication: responder proves identity via certificate chain rooted in a device identity key
- DICE identity: each firmware layer has a unique identity certificate derived from its measurement and the layer below
- TDISP device assignment: TDI authentication binds a physical function to a verified device identity
- Supply chain authenticity: provenance of firmware and hardware components verified through attestation

**Typical verification approaches:**
- Tier 1: SVA assertions that authentication handshake must complete before state transitions (e.g., TDISP lock-to-run)
- Tier 2: Protocol checks for certificate chain validation, signature verification, nonce freshness in challenges
- Tier 3: Specification-level analysis of identity binding strength and key hierarchy trust anchors

**Related standards:** DMTF SPDM v1.4 (CHALLENGE/CERTIFICATE), TCG DICE v1.2 (DeviceID, Alias), TDISP 1.0 (TDI authentication), X.509 v3

---

### 4. Availability

**Definition:** The property that authorized entities can access resources and services in a timely manner, and that denial-of-service conditions are detectable and recoverable.

**Relevance to SoC security:**
- Watchdog timers and bus timeout mechanisms prevent hung transactions from blocking system operation
- Interrupt injection attacks can starve legitimate interrupt handlers
- CXL fabric partitioning prevents one host from monopolizing shared memory bandwidth
- Automotive SoCs must meet functional safety timing requirements (ISO 26262 ASIL) alongside security
- Debug port denial-of-service: malformed JTAG sequences must not halt the security subsystem

**Typical verification approaches:**
- Tier 1: SVA assertions for watchdog expiration behavior, bus timeout enforcement, interrupt rate limiting
- Tier 2: Protocol-level checks for fair scheduling and bandwidth partitioning
- Tier 3: System-level analysis of cascading failure modes and recovery paths

**Related standards:** ISO 21434 (cybersecurity goals), ISO 26262 (functional safety), CXL 3.1 (QoS), FIPS 140-3 (degraded operation)

---

### 5. Isolation

**Definition:** The property that security domains, execution environments, memory regions, or communication channels are separated such that actions or data in one domain cannot affect or be observed by another domain without explicit authorization.

**Relevance to SoC security:**
- TEE isolation: VM/realm memory pages are cryptographically isolated from hypervisor and other VMs
- TDISP device isolation: a TDI in RUN state is bound exclusively to one trust domain; no other domain can access its MMIO or DMA
- CHERI compartmentalization: capability bounds enforce memory isolation at sub-process granularity without requiring MMU page-table isolation
- CXL multi-host isolation: TSP (Type-3 Security Protocol) partitions shared memory across hosts
- Bus firewall isolation: AXI/AHB firewalls restrict which bus masters can access which address ranges

**Typical verification approaches:**
- Tier 1: SVA assertions for address-range firewall enforcement, capability bounds checks (CHERI), TDI state-dependent access gates
- Tier 2: Protocol checks for TSP partition configuration, TDISP state machine isolation invariants
- Tier 3: Information-flow analysis for cross-domain leakage through shared microarchitectural resources

**Related standards:** TDISP 1.0 (TDI states), CXL 3.1 TSP, ARM CCA (Realm isolation), CHERI ISA (compartmentalization), PCIe ACS (Access Control Services)

---

### 6. Attestation

**Definition:** The property that a platform, device, or firmware layer can provide verifiable, tamper-evident evidence of its identity, configuration, and runtime state to a remote or local verifier.

**Relevance to SoC security:**
- DICE attestation: each layer produces an alias certificate binding its identity to its measurement; the certificate chain constitutes attestation evidence
- SPDM measurement: a responder reports its firmware measurements to a requester, signed by the device's identity key
- CXL TSP attestation: Type-3 devices report security configuration to hosts
- Confidential AI: TEE attestation allows a workload owner to verify that the GPU/accelerator executing their model is in a trusted state
- Supply chain attestation: firmware provenance records verified through attestation protocols

**Typical verification approaches:**
- Tier 1: SVA assertions that measurement registers are locked before attestation responses are generated
- Tier 2: Protocol checks for SPDM GET_MEASUREMENTS response completeness, DICE certificate chain well-formedness
- Tier 3: Specification-level analysis of attestation freshness, binding between evidence and identity

**Related standards:** TCG DICE v1.2, DMTF SPDM v1.4 (GET_MEASUREMENTS), CXL 3.1 TSP, TCG Platform Certificate Profile, IETF RATS (Remote Attestation Procedures)

---

### 7. Non-Repudiation

**Definition:** The property that an entity cannot deny having performed an action (firmware update, key rotation, security state transition, configuration change) after the fact, due to cryptographic or physical evidence binding the entity to the action.

**Relevance to SoC security:**
- DICE certificate chains provide non-repudiation of boot sequence: each layer's measurement is permanently recorded in the identity hierarchy
- Firmware update logs with signed timestamps prevent disputes about when and what was updated
- Fuse-blow records: OTP programming events are physically irreversible and attributable
- Audit trails for debug unlock sequences provide evidence of who accessed what and when

**Typical verification approaches:**
- Tier 1: SVA assertions that audit log writes are atomic and cannot be suppressed by firmware
- Tier 2: Protocol checks for signed timestamps and sequencing in update logs
- Tier 3: Specification-level analysis of evidence chain completeness and tamper resistance

**Related standards:** TCG DICE v1.2 (certificate chain), ISO 21434 (audit requirements), FIPS 140-3 (audit mechanism)

---

### 8. Freshness

**Definition:** The property that data, keys, measurements, or protocol messages are recent and not replayed from a previous session, boot cycle, or key epoch.

**Relevance to SoC security:**
- SPDM nonce-based freshness: challenge-response protocols include nonces to prevent replay of stale measurements
- DICE CDI rotation: each boot cycle produces a fresh CDI, ensuring that compromised previous-boot keys cannot be reused
- Key epoch management: encryption keys for IDE streams are rotated periodically; stale keys must be invalidated
- Anti-rollback counters: monotonic counters in OTP prevent firmware rollback to a version with known vulnerabilities
- Session freshness: TDISP and SPDM sessions include sequence numbers to detect replayed messages

**Typical verification approaches:**
- Tier 1: SVA assertions for monotonic counter increment-only behavior, nonce uniqueness within a session
- Tier 2: Protocol checks for SPDM session sequence number ordering, IDE key rotation handshake
- Tier 3: Specification-level analysis of rollback resistance and key epoch transition safety

**Related standards:** DMTF SPDM v1.4 (nonces, session IDs), TCG DICE v1.2 (CDI freshness), TDISP 1.0 (session binding), PCIe IDE (key rotation)

---

### 9. Access Control

**Definition:** The property that operations on resources (registers, memory regions, interfaces, keys) are permitted only when the requesting entity holds sufficient privilege, identity, or capability, as determined by a reference monitor that cannot be bypassed.

**Relevance to SoC security:**
- CHERI capability-based access: every pointer is a capability with bounds and permissions; hardware enforces that no operation exceeds the capability's authority
- Bus firewalls: AXI/AHB protection units filter transactions based on master ID, privilege level, and address range
- Register access control: security-critical registers have lock bits, privilege-level gates, and per-field write masks
- Debug access control: JTAG/SWD authentication requires challenge-response before debug features are enabled
- TDISP access control: TDI MMIO and DMA are gated by TDI state (only accessible in RUN state by the owning trust domain)

**Typical verification approaches:**
- Tier 1: SVA assertions for register lock enforcement, bus firewall address-range checks, capability bounds checks, debug auth FSM transitions
- Tier 2: Protocol checks for TDISP state-dependent access gating, CHERI compartment boundary enforcement
- Tier 3: Formal analysis of reference monitor completeness (no bypass paths)

**Related standards:** CHERI ISA (capability model), TDISP 1.0 (TDI states), ARM TrustZone (TZASC/TZPC), RISC-V PMP (Physical Memory Protection), PCIe ACS

---

### 10. Side-Channel Resistance

**Definition:** The property that an implementation does not leak security-sensitive information through observable physical phenomena (power consumption, electromagnetic emanation, timing variation, acoustic emission) or through microarchitectural state shared between security domains.

**Relevance to SoC security:**
- Cryptographic engines must resist differential power analysis (DPA) and differential electromagnetic analysis (DEMA)
- Timing-constant implementations prevent timing-based key extraction from AES, RSA, ECC operations
- Cache side channels (Flush+Reload, Prime+Probe) can leak information across TEE boundaries
- Speculative execution side channels (Spectre variants) affect processors with speculative pipelines
- Fault injection resistance: voltage/clock glitching can corrupt cryptographic computations to extract keys

**Typical verification approaches:**
- Tier 1: Limited — SVA can check for constant-time mux selection in crypto datapaths but cannot fully verify side-channel resistance
- Tier 2: Natural-language properties describing required countermeasures (masking, blinding, random delays)
- Tier 3: Specification-only — physical side-channel resistance requires lab measurement (TVLA, CPA) and cannot be verified in RTL simulation alone

**Related standards:** FIPS 140-3 (Level 3+ physical security), ISO 21434 (threat analysis), Common Criteria (AVA_VAN), NIST SP 800-90B (entropy sources)

---

### 11. Speculation Safety

**Definition:** The property that speculative or transient execution does not access, compute on, or transmit data beyond the boundaries that the architectural (non-speculative) execution would permit. Speculation must not create observable microarchitectural side-effects that leak information across security domains.

**Relevance to SoC security:**
- Transient execution attacks (Spectre, Meltdown, MDS, L1TF) exploit speculative execution to access data beyond architectural authorization, leaving observable cache or buffer state
- Branch predictor partitioning prevents cross-domain training attacks (Spectre-BTB, Spectre-PHT)
- Speculative store bypass protection ensures stores are not speculatively bypassed to leak stale data
- Return stack buffer (RSB) management prevents cross-domain return target injection

**Typical verification approaches:**
- Tier 1: SVA assertions for speculation barrier insertion at security domain transitions (limited — cannot fully model microarchitectural state)
- Tier 2: Property descriptions for BTB/PHT partitioning behavior, speculative access boundary checks
- Tier 3: Microarchitectural simulation with side-channel oracles; lab measurement of speculative leakage

**Related standards:** Intel/AMD/ARM speculation barrier ISA extensions, RISC-V Zkt, FIPS 140-3 (timing side-channels)

---

### 12. Leakage Resistance

**Definition:** The property that a cryptographic implementation does not leak key-dependent information through physical observables (power consumption, electromagnetic emanation, timing variation) or through computation artifacts (data-dependent memory access patterns, variable-time operations).

**Relevance to SoC security:**
- Cryptographic engines must resist differential power analysis (DPA) and electromagnetic analysis (DEMA) at the targeted Common Criteria or FIPS security level
- Masking countermeasures split sensitive intermediate values into random shares to decorrelate power/EM traces from secret data
- Hiding countermeasures (random delays, shuffling, dual-rail logic) reduce signal-to-noise ratio for the attacker
- TVLA (Test Vector Leakage Assessment) provides a standardized statistical test for leakage detection
- Fault injection countermeasures (redundancy, parity, infection) detect or resist glitch attacks on crypto operations

**Typical verification approaches:**
- Tier 1: SVA assertions for constant-time multiplexer selection in crypto datapaths (limited scope)
- Tier 2: Natural-language properties describing required masking order, shuffling requirements, detection mechanisms
- Tier 3: Physical measurement required — TVLA testing, CPA attacks in lab environment; ISO 17825 compliance testing

**Related standards:** ISO 17825 (TVLA), FIPS 140-3 (Level 3+ physical security), Common Criteria (AVA_VAN.4/5), JIL attack potential

---

### 13. Privilege Separation

**Definition:** The property that the system enforces strict boundaries between privilege levels (user, kernel, hypervisor, firmware, hardware) such that code executing at one privilege level cannot access resources, modify state, or influence execution at a higher privilege level without using authorized transition mechanisms.

**Relevance to SoC security:**
- Hardware privilege enforcement: MMU page tables with U/S bits, RISC-V PMP, ARM exception levels (EL0-EL3)
- Kernel isolation mechanisms: KPTI (kernel page table isolation), SMAP/SMEP (supervisor mode access/execution prevention)
- Container and VM isolation: seccomp-BPF syscall filtering, namespaces, cgroups, KVM/QEMU boundary
- IOMMU/SMMU: extends privilege separation to DMA-capable devices, preventing device-to-host escalation
- Privilege escalation paths: the primary kernel security concern — any path from user to kernel or kernel to hypervisor is a critical finding

**Typical verification approaches:**
- Tier 1: SVA assertions for privilege level transition checks, register access gating by privilege level
- Tier 2: Protocol checks for seccomp-BPF policy completeness, namespace isolation invariants
- Tier 3: Formal analysis of privilege boundary completeness — no unauthorized transition path exists

**Related standards:** RISC-V Privileged Spec, ARM Architecture Reference Manual, Common Criteria (separation kernel PPs), KSPP hardening guidelines

---

### 14. Formal Verifiability

**Definition:** The property that a security claim can be expressed as a precise mathematical statement (invariant, safety property, liveness property) amenable to formal verification through model checking, theorem proving, or abstract interpretation. A formally verifiable property has explicit assumptions, a well-defined state space, and decidable or tractable checking procedures.

**Relevance to SoC security:**
- Security-critical state machines (TDISP, DICE, authentication FSMs) can have safety properties formally verified via TLC model checking
- Information flow properties (noninterference) can be specified in TLA+ and checked for finite state spaces
- Formal specification forces explicit enumeration of assumptions that informal analysis often leaves implicit
- Model checking provides exhaustive verification within the state space — no simulation gaps
- Limitations must be explicitly stated: what the formal model does NOT capture (timing, physical side-channels, implementation bugs below the abstraction level)

**Typical verification approaches:**
- Tier 1: TLA+ specification with TLC model checking for safety/liveness properties
- Tier 2: Protocol-level temporal logic properties verified with bounded model checking
- Tier 3: Theorem proving (Isabelle/HOL, Coq) for unbounded verification of critical properties

**Related standards:** TLA+ (Lamport), RTCA DO-333 (formal methods supplement), Common Criteria EAL7 (formally verified design)

---

## Cross-Reference Matrix: Properties vs. Standards

| Property | DICE | SPDM | TDISP | CXL 3.1 | CHERI | PCIe IDE | FIPS 140-3 | ISO 21434 | ISO 17825 | FIPS 203-205 | UCIe 1.1 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Confidentiality | | | | X | | X | X | X | | | X |
| Integrity | X | X | | X | | X | X | X | | | X |
| Authenticity | X | X | X | X | | | | | | | X |
| Availability | | | | X | | | X | X | | | |
| Isolation | | | X | X | X | | | | | | X |
| Attestation | X | X | | X | | | | | | | |
| Non-Repudiation | X | | | | | | X | X | | | |
| Freshness | X | X | X | | | X | | | | | |
| Access Control | | | X | | X | | | | | | |
| Side-Channel Resistance | | | | | | | X | X | X | | |
| Speculation Safety | | | | | X | | X | | | | |
| Leakage Resistance | | | | | | | X | | X | X | |
| Privilege Separation | | | X | | X | | | | | | |
| Formal Verifiability | X | X | X | | | | | | | | |

---

## Cross-Reference Matrix: Properties vs. Verification Tiers

| Property | Tier 1 (SVA) | Tier 2 (Protocol) | Tier 3 (Info-Flow/Spec) |
|---|---|---|---|
| Confidentiality | Cleartext leak checks | IDE setup sequencing | Covert channel analysis |
| Integrity | Register locks, MAC checks | DICE chain, SPDM measurement | Hash chain formal properties |
| Authenticity | Auth handshake gating | Certificate chain validation | Identity binding analysis |
| Availability | Watchdog, bus timeout | Fair scheduling | Cascading failure modes |
| Isolation | Firewall, capability bounds | TSP partition, TDISP state | Cross-domain leakage |
| Attestation | Measurement register locks | SPDM response completeness | Evidence freshness binding |
| Non-Repudiation | Audit log atomicity | Signed timestamps | Evidence chain completeness |
| Freshness | Monotonic counters, nonce | Session sequencing | Rollback resistance |
| Access Control | Lock bits, firewall rules | State-dependent gating | Reference monitor completeness |
| Side-Channel Resistance | Constant-time mux (limited) | Countermeasure descriptions | Lab measurement required |
| Speculation Safety | Barrier insertion checks (limited) | BTB/PHT partitioning behavior | Microarch simulation with oracles |
| Leakage Resistance | Constant-time datapath selection | Masking order, shuffling reqs | TVLA, CPA lab measurement |
| Privilege Separation | Privilege transition gating | Seccomp-BPF, namespace invariants | Privilege boundary completeness |
| Formal Verifiability | TLA+ model checking (TLC) | Bounded model checking | Theorem proving (Isabelle/Coq) |

---

*[FROM TRAINING] All content in this file is derived from publicly available specifications and general domain knowledge. Specific requirement numbers and protocol details should be verified against authoritative spec documents. Last verified: 2026-02-13.*
