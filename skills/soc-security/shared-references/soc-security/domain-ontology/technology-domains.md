# Technology Domains — SoC Hardware Security Ontology

## Purpose

This reference defines the five technology domains that scope the SoC Security Suite. Each domain represents a distinct area of hardware security engineering with its own standards, threat landscape, and verification requirements. Skills use domain classifications to scope threat models, select applicable standards, and tailor verification strategies.

**Primary consumers:** threat-model-skill (domain scoping), verification-scaffold-skill (domain-specific assertions), compliance-pipeline-skill (standard selection)
**Secondary consumers:** executive-brief-skill (domain context for non-technical audiences)

---

## Quick Reference

| Domain | Scope | Primary Standards | Key Security Properties |
|---|---|---|---|
| Confidential AI / TEE | VM isolation, memory encryption, attestation | ARM CCA, SEV-SNP, TDX, DICE | Confidentiality, Isolation, Attestation |
| TDISP / CXL / C2C CHI | Device assignment, link security, cache coherence | TDISP 1.0, CXL 3.1, PCIe IDE | Isolation, Integrity, Authenticity |
| Supply Chain Security | Attestation, provenance, SBOM, SPDM | SPDM v1.4, TCG, NIST 800-161 | Authenticity, Integrity, Freshness |
| Secure Boot / DICE | Boot chain, measurement, layered identity | TCG DICE v1.2, UEFI Secure Boot | Integrity, Authenticity, Attestation |
| RISC-V CHERI | Capability addressing, compartmentalization | CHERI ISA, RISC-V specs | Access Control, Isolation, Integrity |

---

## Domain 1: Confidential AI / TEE

### Scope

Trusted Execution Environments (TEEs) that provide hardware-enforced isolation for confidential workloads — particularly AI/ML inference and training — on shared infrastructure. Covers the security boundary between guest VMs/realms and the host/hypervisor, memory encryption engines, and remote attestation of TEE state.

### Scope Boundaries

**In scope:**
- Hardware VM isolation mechanisms (ARM CCA Realms, AMD SEV-SNP, Intel TDX)
- Memory encryption engines (AES-XTS for DRAM, per-VM key management)
- TEE attestation (evidence generation, remote verifier interaction)
- GPU/accelerator TEE extensions (confidential compute on accelerators)
- Key hierarchy for per-VM encryption (key derivation, rotation, destruction)
- Interrupt and exception handling across trust boundaries

**Out of scope:**
- Software-only TEE implementations (e.g., application-level enclaves without hardware enforcement)
- General-purpose hypervisor security (unless it intersects with TEE isolation)
- Network-level encryption (covered under link security in Domain 2)

### Key Security Properties

| Property | Domain-Specific Manifestation |
|---|---|
| Confidentiality | Guest memory encrypted with per-VM keys; host/hypervisor cannot read plaintext |
| Isolation | Hardware page tables or GPT (Granule Protection Table) enforce VM-to-VM and VM-to-host separation |
| Attestation | TEE produces signed evidence of firmware version, configuration, and launch state |
| Integrity | Memory integrity (MAC tags) detect physical tampering with DRAM contents |
| Freshness | Attestation nonces prevent replay of stale evidence; key rotation bounds exposure |

### Standards Intersection

- **TCG DICE v1.2:** TEE firmware identity and measurement (see `standards-registry/dice/`)
- **DMTF SPDM v1.4:** Device attestation for accelerators within TEE boundary (see `standards-registry/spdm/`)
- **ARM CCA:** Realm Management Extension, Granule Protection Table [FROM TRAINING]
- **AMD SEV-SNP:** Secure Nested Paging, VMSA encryption [FROM TRAINING]
- **Intel TDX:** Trust Domain Extensions, SEAM module [FROM TRAINING]

### Typical SoC Families

- **Compute (server/HPC):** Primary target — multi-tenant cloud, confidential VM workloads
- **Data Center:** CXL-attached accelerators with TEE extensions
- **Client:** Emerging — local AI inference in confidential containers

### Cross-Domain Relationships

- Intersects with **Secure Boot / DICE** for TEE firmware measurement and identity
- Intersects with **TDISP / CXL** for device assignment into TEE trust domains
- Intersects with **Supply Chain Security** for attestation of accelerator firmware provenance

---

## Domain 2: TDISP / CXL / C2C CHI

### Scope

Security protocols and mechanisms for PCIe/CXL device assignment to trust domains, link-level encryption and integrity protection, and cache-coherent interconnect security. Covers the lifecycle of a device being securely assigned to a confidential VM and the protection of data in transit across chip-to-chip and host-to-device links.

### Scope Boundaries

**In scope:**
- PCIe TDISP (TEE Device Interface Security Protocol): TDI lifecycle, state machine, SPDM session binding
- CXL 3.1 security: IDE for CXL links, TSP (Type-3 Security Protocol), multi-host isolation
- PCIe IDE (Integrity and Data Encryption): link encryption, key management, selective/link IDE streams
- C2C CHI (Chip-to-Chip Coherent Hub Interface): cache coherence security, snoop filtering, directory protection
- SPDM session establishment for device authentication prior to assignment

**Out of scope:**
- PCIe performance optimization (non-security aspects of link training, equalization)
- CXL memory pooling performance (unless security-relevant partitioning is involved)
- Network-layer protocols above PCIe/CXL (e.g., RDMA, NVMe-oF security handled separately)

### Key Security Properties

| Property | Domain-Specific Manifestation |
|---|---|
| Isolation | TDI states enforce that an assigned device is accessible only to its owning trust domain |
| Integrity | IDE MACs on TLPs detect in-flight tampering on PCIe/CXL links |
| Confidentiality | IDE encryption (AES-GCM) protects TLP payloads from physical interposers |
| Authenticity | SPDM authentication verifies device identity before TDISP assignment |
| Freshness | IDE key rotation and SPDM session sequence numbers prevent replay |

### Standards Intersection

- **TDISP 1.0:** Full protocol specification (see `standards-registry/tdisp/`)
- **CXL 3.1:** Security chapter, TSP, IDE for CXL (see `standards-registry/cxl/`)
- **DMTF SPDM v1.4:** Underlying authentication and session protocol (see `standards-registry/spdm/`)
- **PCIe IDE ECN:** Link/selective stream IDE (see cross-reference in TDISP and CXL registries)
- **PCIe ACS:** Access Control Services for peer-to-peer isolation [FROM TRAINING]

### Typical SoC Families

- **Data Center:** Primary — CXL fabric, multi-host GPU/accelerator sharing
- **Compute (server/HPC):** PCIe device passthrough to confidential VMs
- **Client:** Emerging — Thunderbolt/USB4 security overlaps with PCIe IDE concepts

### Cross-Domain Relationships

- Intersects with **Confidential AI / TEE** for device assignment into TEE trust domains
- Intersects with **Supply Chain Security** for SPDM-based device authentication
- Intersects with **Secure Boot / DICE** for device firmware identity in TDISP flows

---

## Domain 3: Supply Chain Security

### Scope

Security mechanisms ensuring that hardware and firmware components are authentic, untampered, and traceable from manufacture through deployment and field updates. Covers cryptographic attestation of component identity, firmware provenance verification, and software bill of materials for hardware platforms.

### Scope Boundaries

**In scope:**
- SPDM device authentication and measurement (proving identity and firmware state to a platform)
- Firmware signing, verification, and anti-rollback protection
- Hardware component provenance (certificate-based identity, manufacturing attestation)
- Software/Firmware Bill of Materials (SBOM/FBOM) for SoC components
- OTA (Over-The-Air) firmware update security
- Debug interface authentication as a supply chain control (preventing unauthorized debug access)

**Out of scope:**
- Physical supply chain logistics (tamper-evident packaging, chain-of-custody for hardware shipments)
- PCB-level anti-counterfeit measures (unless they have a firmware/protocol component)
- Software supply chain (npm/pip/container supply chain attacks — this domain focuses on hardware/firmware)

### Key Security Properties

| Property | Domain-Specific Manifestation |
|---|---|
| Authenticity | Cryptographic verification that firmware and hardware originate from authorized manufacturers |
| Integrity | Signed firmware images and hash chains detect unauthorized modifications |
| Freshness | Anti-rollback counters and monotonic version numbers prevent downgrade attacks |
| Attestation | Devices prove their firmware state to platform verifiers via SPDM measurements |
| Non-Repudiation | Firmware update logs with signed timestamps provide audit trail |

### Standards Intersection

- **DMTF SPDM v1.4:** Authentication, measurement, secure session (see `standards-registry/spdm/`)
- **TCG DICE v1.2:** Layered identity for firmware attestation (see `standards-registry/dice/`)
- **NIST SP 800-161:** Supply chain risk management [FROM TRAINING]
- **NIST SP 800-193:** Platform Firmware Resiliency Guidelines [FROM TRAINING]
- **ISO 21434:** Automotive cybersecurity supply chain requirements (see compliance overlay)

### Typical SoC Families

- **All families:** Supply chain security is cross-cutting; every SoC family requires firmware provenance and update security
- **Automotive:** Heightened requirements due to ISO 21434 supply chain clauses and long field lifetimes
- **Data Center:** SPDM-based component attestation for rack-scale platforms

### Cross-Domain Relationships

- Intersects with **Secure Boot / DICE** for firmware measurement and identity establishment
- Intersects with **TDISP / CXL** for SPDM-based device authentication prior to assignment
- Intersects with **Confidential AI / TEE** for accelerator firmware provenance attestation

---

## Domain 4: Secure Boot / DICE

### Scope

The boot-time security architecture that establishes a chain of trust from immutable hardware through each firmware layer to the operating environment. Covers measurement, identity derivation, and the cryptographic mechanisms that ensure each boot stage is authentic and that the platform's runtime identity reflects its actual firmware composition.

### Scope Boundaries

**In scope:**
- TCG DICE (Device Identifier Composition Engine): UDS, CDI derivation, alias certificates, DeviceID
- Immutable ROM and first-stage bootloader security
- OTP fuse programming for root keys, configuration, and anti-rollback counters
- Measured boot: each stage measures the next before transfer of control
- UEFI Secure Boot and its interaction with DICE layering
- Key hierarchy from hardware root to application-layer keys

**Out of scope:**
- OS-level secure boot (e.g., Linux IMA/EVM, Windows Secure Boot policy above UEFI)
- Application-layer key management (unless it derives from the DICE chain)
- Runtime integrity monitoring (covered under attestation in Domain 1 and Domain 3)

### Key Security Properties

| Property | Domain-Specific Manifestation |
|---|---|
| Integrity | Each boot stage measures the next; any modification changes the CDI and identity chain |
| Authenticity | DICE alias certificates bind firmware identity to cryptographic keys |
| Attestation | The DICE certificate chain constitutes attestation evidence for the platform's firmware state |
| Freshness | Each boot cycle produces a fresh CDI; previous-boot keys are not reusable |
| Access Control | Fuse controllers restrict key material access based on boot stage and privilege |
| Non-Repudiation | Certificate chain provides evidence of which firmware versions were booted |

### Standards Intersection

- **TCG DICE v1.2:** Core specification (see `standards-registry/dice/`)
- **TCG Platform Certificate Profile:** Binding DICE identity to platform attestation [FROM TRAINING]
- **DMTF SPDM v1.4:** Carries DICE-derived measurements to remote verifiers (see `standards-registry/spdm/`)
- **UEFI Secure Boot Specification:** Integration with DICE at the UEFI firmware stage [FROM TRAINING]
- **FIPS 140-3:** Key management and entropy requirements for boot-time key derivation

### Typical SoC Families

- **All families:** Boot security is foundational; every SoC family implements some form of measured/secure boot
- **Compute (server/HPC):** Full DICE layering with SPDM attestation
- **Automotive:** Secure boot with ISO 21434 compliance overlay, HSM-backed key storage
- **Client:** TPM-integrated boot with DICE extensions for platform attestation

### Cross-Domain Relationships

- Intersects with **Confidential AI / TEE** for TEE firmware measurement and identity
- Intersects with **Supply Chain Security** for firmware provenance and anti-rollback
- Intersects with **TDISP / CXL** for device firmware identity used in TDISP authentication

---

## Domain 5: RISC-V CHERI

### Scope

Capability-based hardware extensions for RISC-V processors that enforce memory safety and compartmentalization at the instruction-set level. Covers capability encoding, bounds enforcement, sealing for cross-compartment calls, and the security implications of deploying CHERI in SoC contexts.

### Scope Boundaries

**In scope:**
- CHERI capability encoding: bounds, permissions, object type, tag bit
- Capability-based addressing: every pointer is a capability with hardware-enforced bounds
- Compartmentalization: sealed capabilities and sentries for cross-domain calls
- Capability revocation: mechanisms for revoking previously granted capabilities
- Memory safety invariants: spatial safety (bounds), referential safety (tags), monotonicity (no capability forgery)
- Integration with existing RISC-V privilege levels and PMP

**Out of scope:**
- General RISC-V ISA extensions not related to CHERI (vector, crypto, hypervisor extensions unless they interact with capabilities)
- Software-only capability systems (e.g., Capsicum, seL4 capabilities without hardware support)
- CHERI on non-RISC-V architectures (ARM Morello covered only for comparison where relevant)

### Key Security Properties

| Property | Domain-Specific Manifestation |
|---|---|
| Access Control | Capabilities encode fine-grained permissions; hardware prevents any operation exceeding capability authority |
| Isolation | Compartment boundaries enforced by sealed capabilities; cross-compartment communication only through defined sentries |
| Integrity | Tag bits protect capability integrity; any non-capability write to a capability register clears the tag, preventing forgery |
| Side-Channel Resistance | Compartmentalization limits the blast radius of microarchitectural side-channel attacks by reducing shared state |

### Standards Intersection

- **CHERI ISA Specification:** Core capability model (see `standards-registry/cheri/`)
- **RISC-V Privileged Specification:** PMP interaction with CHERI capabilities [FROM TRAINING]
- **CHERI C/C++ Specification:** Software model for capability-aware compilation [FROM TRAINING]
- **ARM Morello:** Reference implementation for comparison (not a standard per se) [FROM TRAINING]

### Typical SoC Families

- **Compute (server/HPC):** Emerging — memory safety for security-critical firmware components
- **Data Center:** Compartmentalized firmware for multi-tenant management controllers
- **Automotive:** Emerging — memory safety for AUTOSAR safety-critical software
- **Client:** Research stage — CHERI-enabled secure enclaves

### Cross-Domain Relationships

- Intersects with **Secure Boot / DICE** for capability-based access control in boot firmware
- Intersects with **Confidential AI / TEE** for sub-VM compartmentalization within TEE workloads
- Intersects with **Supply Chain Security** for firmware compartmentalization reducing blast radius of supply chain compromise

---

## Domain 6: Microarchitectural Security

### Scope

Security analysis of microarchitectural structures — caches, branch predictors, TLBs, store buffers, execution ports, and prefetchers — against transient execution attacks, cache side-channels, and contention-based information leakage. Covers the microarchitectural attack surface that exists below the ISA abstraction, where implementation details create unintended information channels.

### Scope Boundaries

**In scope:**
- Transient execution attacks (Spectre class, Meltdown class, MDS, L1TF, Downfall, Zenbleed, Inception, GhostRace, Training Solo)
- Cache side-channels (Prime+Probe, Flush+Reload, Evict+Time, Cache Occupancy)
- Branch predictor attacks (BTB injection, PHT manipulation, RSB stuffing)
- TLB-based attacks (TLBleed, page-table walk side-channels)
- Port contention attacks (SMoTherSpectre, PortSmash)
- Prefetch-based attacks (prefetch side-channels, data-dependent prefetch leakage)
- Microarchitectural covert channels across security domains
- Hardware and software mitigations (serialization barriers, partitioning, cleansing, masking)

**Out of scope:**
- Physical side-channels (power, EM) — covered under Domain 7 (Physical SCA)
- ISA-level security features (CHERI, PMP) — covered under Domain 5
- Software-only mitigations at the compiler or OS level (unless they interact with HW mechanisms)

### Key Security Properties

| Property | Domain-Specific Manifestation |
|---|---|
| Speculation Safety | Speculative execution does not access data beyond the architectural authorization boundary |
| Cache Isolation | Cache state of one security domain is not observable by another domain |
| Microarch State Separation | Branch predictor, TLB, and other shared microarchitectural state is partitioned or cleansed across domain transitions |
| Timing Invariance | Execution timing does not depend on secret data values |

### Standards Intersection

- **Intel/AMD/ARM Speculation Barriers:** LFENCE, CSDB, speculation barrier instructions [FROM TRAINING]
- **ARM DIT (Data-Independent Timing):** Instruction mode for constant-time execution [FROM TRAINING]
- **RISC-V Zkt Extension:** Constant-time crypto execution guarantee [FROM TRAINING]
- **FIPS 140-3 Level 3+:** Timing side-channel resistance requirements

### Typical SoC Families

- **Compute (server/HPC):** Primary — multi-tenant isolation across speculative boundaries
- **Data Center:** CXL-attached devices sharing cache hierarchies
- **Client:** Browser-based Spectre attacks, cross-origin isolation
- **Automotive:** Emerging — mixed-criticality workloads sharing microarchitectural resources

### Cross-Domain Relationships

- Intersects with **Confidential AI / TEE** — speculative execution can bypass TEE memory isolation
- Intersects with **RISC-V CHERI** — CHERI bounds interact with speculative execution windows
- Intersects with **Kernel Security** (Domain 8) — kernel mitigations (KPTI, retpoline) are responses to microarch attacks

---

## Domain 7: Physical Side-Channel Analysis

### Scope

Physical side-channel attacks and countermeasures targeting cryptographic implementations and security-critical operations. Covers power analysis (SPA/DPA/CPA), electromagnetic analysis (EMA/DEMA), fault injection (voltage/clock glitch, laser, EM), leakage assessment (ISO 17825 TVLA), and countermeasure evaluation (masking, hiding, detection).

### Scope Boundaries

**In scope:**
- Simple and differential power analysis (SPA, DPA, CPA, higher-order DPA)
- Electromagnetic analysis (EMA, DEMA, near-field EM probing)
- Fault injection attacks (voltage glitching, clock glitching, laser fault injection, EM fault injection)
- Combined attacks (fault + side-channel)
- Leakage assessment methodology (TVLA, specific t-test, non-specific t-test, chi-square)
- JIL attack potential scoring methodology
- Countermeasure evaluation: masking (Boolean, arithmetic, higher-order), hiding (random delays, shuffling, dual-rail), detection (parity, infection, alarm)
- ISO 17825 compliance for physical security testing

**Out of scope:**
- Microarchitectural side-channels (cache timing, branch prediction) — covered under Domain 6
- Software-level timing attacks not involving physical observables
- Physical probing and FIB attacks (board-level attacks beyond the SoC boundary)

### Key Security Properties

| Property | Domain-Specific Manifestation |
|---|---|
| Leakage Resistance | Cryptographic operations do not leak key-dependent information through power, EM, or timing |
| Fault Resilience | Security-critical computations detect or resist physical fault injection |
| Countermeasure Effectiveness | Masking, hiding, or detection countermeasures reduce leakage below exploitable threshold |
| Certification Readiness | Implementation meets ISO 17825 / FIPS 140-3 Level 3+ physical security requirements |

### Standards Intersection

- **ISO 17825:** Test methods for side-channel leakage assessment (TVLA) [FROM TRAINING]
- **FIPS 140-3 Level 3+:** Physical security requirements for crypto modules
- **Common Criteria AVA_VAN.5:** High-attack-potential vulnerability analysis
- **JIL Application of Attack Potential:** Scoring methodology for smartcard evaluation [FROM TRAINING]

### Typical SoC Families

- **All families:** Any SoC with embedded cryptographic engines
- **Automotive:** Highest scrutiny — HSM certification for ISO 21434 / Common Criteria
- **Client:** Secure element and TEE crypto engine evaluation
- **Data Center:** Emerging — attestation key protection in platform RoT

### Cross-Domain Relationships

- Intersects with **Secure Boot / DICE** — crypto engines in boot chain must resist DPA/FI
- Intersects with **Confidential AI / TEE** — memory encryption engine key protection
- Intersects with **Supply Chain Security** — HSM and secure element certification

---

## Domain 8: Kernel Security

### Scope

OS kernel security internals as they relate to hardware security mechanisms. Covers the kernel's use of hardware features (MMU, IOMMU/SMMU, SMAP/SMEP, MTE, CHERI) for memory management security, process isolation, and privilege boundary enforcement. Focuses on the hardware/software security interface where kernel configuration enables or undermines hardware security guarantees.

### Scope Boundaries

**In scope:**
- Kernel memory management security (KASLR, KPTI, SMAP, SMEP, MTE, shadow stacks)
- Process isolation mechanisms (seccomp-BPF, namespaces, cgroups, capabilities, Landlock)
- IOMMU/SMMU configuration and DMA protection
- Privilege escalation paths from user to kernel to hypervisor
- Kernel attack surface reduction (io_uring restrictions, syscall filtering, module signing)
- Kernel integrity subsystems (dm-verity, IMA, EVM)
- Hardware security interface configuration (IOMMU group assignment, MTE mode, PMP configuration)

**Out of scope:**
- Application-level security (user-space sandboxing not involving kernel mechanisms)
- Network protocol security (iptables, nftables rules)
- File system security (unless it involves dm-verity or integrity measurement)
- Embedded RTOS without MMU — covered under IoT/Embedded (Sentinel domain)

### Key Security Properties

| Property | Domain-Specific Manifestation |
|---|---|
| Privilege Separation | Kernel enforces strict boundaries between user, kernel, and hypervisor privilege levels |
| Memory Isolation | MMU/IOMMU/MTE ensure that processes, VMs, and DMA-capable devices cannot access memory outside their domain |
| Attack Surface Minimization | Kernel exposes minimal system call surface and disables unused subsystems |
| Integrity Enforcement | dm-verity, IMA, and module signing ensure kernel and filesystem integrity |

### Standards Intersection

- **KSPP (Kernel Self-Protection Project):** Linux kernel hardening guidelines [FROM TRAINING]
- **CIS Benchmarks:** Kernel configuration hardening baselines [FROM TRAINING]
- **NIST SP 800-123:** Guide to general server security (kernel hardening) [FROM TRAINING]
- **Common Criteria:** EAL4+ kernel security evaluation
- **ISO 21434:** Kernel configuration in automotive Linux deployments

### Typical SoC Families

- **Compute (server/HPC):** Multi-tenant isolation, container security, KVM/QEMU boundary
- **Data Center:** IOMMU configuration for SR-IOV device passthrough
- **Client:** User-space sandboxing, secure boot chain to kernel
- **Automotive:** Linux kernel in mixed-criticality systems, Xen/QEMU hypervisor boundaries

### Cross-Domain Relationships

- Intersects with **Microarchitectural Security** (Domain 6) — kernel mitigations for Spectre/Meltdown
- Intersects with **TDISP / CXL** — IOMMU configuration for device assignment
- Intersects with **RISC-V CHERI** — kernel capability management for CHERI-enabled processes
- Intersects with **Confidential AI / TEE** — KVM/hypervisor trust boundary with TEE guests

---

## Domain 9: Emerging Hardware Security

### Scope

Security implications of emerging hardware paradigms that are in active standardization or early adoption. Covers post-quantum cryptography hardware implementations, chiplet/UCIe multi-die security architectures, heterogeneous compute security (CPU+GPU+NPU trust boundaries), and AI accelerator security (model confidentiality, inference integrity, weight protection).

### Scope Boundaries

**In scope:**
- Post-quantum crypto HW: CRYSTALS-Kyber (ML-KEM/FIPS 203), CRYSTALS-Dilithium (ML-DSA/FIPS 204), SPHINCS+ (SLH-DSA/FIPS 205) hardware accelerator security
- Chiplet/UCIe security: die-to-die authentication, chiplet supply chain trust, UCIe 1.1 link security
- Heterogeneous compute: CPU+GPU+NPU trust boundary definition, shared memory security across heterogeneous compute elements
- AI accelerator security: model confidentiality (weight protection), inference integrity (preventing output manipulation), side-channel leakage of model architecture

**Out of scope:**
- PQC algorithm design or cryptanalysis (only implementation security)
- Software-level AI security (adversarial ML, model poisoning) unless it has hardware implications
- Quantum computing hardware (only post-quantum resistance of classical hardware)

### Key Security Properties

| Property | Domain-Specific Manifestation |
|---|---|
| Quantum Resistance | Cryptographic implementations resist known quantum attacks (Shor's, Grover's) |
| Die-to-Die Integrity | Inter-chiplet communication is authenticated and tamper-evident |
| Heterogeneous Isolation | Trust boundaries between CPU, GPU, and NPU are hardware-enforced |
| Model Confidentiality | AI model weights and architecture are protected from extraction via accelerator interfaces |
| Migration Readiness | Systems can transition to new security paradigms without full hardware replacement |

### Standards Intersection

- **FIPS 203 (ML-KEM):** Post-quantum key encapsulation mechanism [FROM TRAINING]
- **FIPS 204 (ML-DSA):** Post-quantum digital signature algorithm [FROM TRAINING]
- **FIPS 205 (SLH-DSA):** Hash-based post-quantum signatures [FROM TRAINING]
- **UCIe 1.1:** Universal Chiplet Interconnect Express security [FROM TRAINING]
- **DMTF SPDM v1.4+:** Extended for chiplet-level attestation

### Typical SoC Families

- **Data Center:** Primary — PQC migration, chiplet architectures, AI accelerator farms
- **Compute (server/HPC):** PQC key exchange, heterogeneous compute clusters
- **Client:** PQC in secure elements, NPU trust boundaries
- **Automotive:** Long-lifecycle PQC migration planning

### Cross-Domain Relationships

- Intersects with **Secure Boot / DICE** — PQC migration for boot chain signatures and attestation
- Intersects with **Confidential AI / TEE** — GPU/NPU TEE extensions, AI accelerator isolation
- Intersects with **Supply Chain Security** — chiplet provenance and die-level attestation
- Intersects with **Physical SCA** (Domain 7) — PQC hardware implementations need SCA resistance

---

## Domain Interaction Matrix

This matrix identifies pairwise interactions between domains. Each cell describes the nature of the interaction.

| | Conf. AI/TEE | TDISP/CXL | Supply Chain | Secure Boot/DICE | CHERI | Microarch | Physical SCA | Kernel Sec | Emerging HW |
|---|---|---|---|---|---|---|---|---|---|
| **Conf. AI/TEE** | — | Device assignment | Accel. attestation | TEE firmware ID | Sub-VM compartments | Speculative TEE escape | Memory encryption SCA | KVM trust boundary | GPU TEE extensions |
| **TDISP/CXL** | Device assignment | — | SPDM device auth | Device firmware ID | Capability DMA (R&D) | Cache timing on CXL | — | IOMMU config | UCIe link security |
| **Supply Chain** | Accel. provenance | Device ID verify | — | Firmware chain | Compartment updates | — | HSM certification | — | Chiplet provenance |
| **Secure Boot/DICE** | TEE boot measure | Device boot ID | Firmware provenance | — | Capability boot | — | Boot crypto SCA | dm-verity, IMA | PQC boot signatures |
| **CHERI** | TEE compartments | DMA cap. bounds | Firmware compartments | Boot capabilities | — | Speculative cap. bypass | — | Kernel cap. mgmt | — |
| **Microarch** | Speculative TEE escape | CXL cache sharing | — | — | Speculative cap. bypass | — | — | KPTI, retpoline | — |
| **Physical SCA** | MemEncrypt key protect | — | HSM certification | Boot crypto protect | — | — | — | — | PQC implementation SCA |
| **Kernel Sec** | KVM/hypervisor | IOMMU passthrough | — | dm-verity, IMA | Kernel capabilities | Spectre mitigations | — | — | NPU driver isolation |
| **Emerging HW** | GPU TEE | UCIe security | Chiplet provenance | PQC signatures | — | — | PQC SCA resistance | NPU driver isolation | — |

---

## Guidance for Skill Consumers

### threat-model-skill
When scoping a threat model, select one or more domains. The domain selection determines which standards, threat catalog entries, and verification patterns are relevant. Most threat models span 2-3 domains.

### verification-scaffold-skill
Domain classification determines which SVA template categories apply. Tier 1 assertions are domain-specific; Tier 2 and Tier 3 properties are often cross-domain.

### compliance-pipeline-skill
Domain selection maps directly to the standards registry. Each domain has primary and secondary standards. The compliance pipeline generates a traceability matrix from domain-specific requirements.

### executive-brief-skill
Map domain names to business-language equivalents:
- Confidential AI / TEE → "Data protection for AI workloads on shared infrastructure"
- TDISP / CXL → "Secure device connectivity and data-link protection"
- Supply Chain Security → "Hardware and firmware authenticity verification"
- Secure Boot / DICE → "Trusted startup and platform identity"
- RISC-V CHERI → "Hardware-enforced memory safety"
- Microarchitectural Security → "Processor-level side-channel and speculative execution defenses"
- Physical SCA → "Cryptographic implementation hardening against physical attacks"
- Kernel Security → "Operating system security boundaries and hardware interface protection"
- Emerging HW Security → "Next-generation hardware security readiness (post-quantum, chiplets, AI accelerators)"

### microarch-attack-skill
Domain 6 is the primary domain. Cross-references Domain 1 (TEE speculative escape), Domain 5 (CHERI speculative bypass), and Domain 8 (kernel mitigations).

### physical-sca-skill
Domain 7 is the primary domain. Cross-references Domain 4 (boot crypto protection) and Domain 9 (PQC implementation SCA).

### kernel-security-skill
Domain 8 is the primary domain. Cross-references Domain 2 (IOMMU for TDISP), Domain 6 (Spectre mitigations), and Domain 1 (KVM trust boundary).

### emerging-hw-security-skill
Domain 9 is the primary domain. Cross-references all other domains for migration impact assessment.

### tlaplus-security-skill
Consumes findings from any domain. Formal specifications are domain-agnostic but reference domain-specific properties.

---

*[FROM TRAINING] All content in this file is derived from publicly available specifications and general domain knowledge. Specific requirement numbers and protocol details should be verified against authoritative spec documents. Last verified: 2026-02-13.*
