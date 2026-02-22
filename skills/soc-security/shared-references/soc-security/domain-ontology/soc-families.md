# SoC Family Profiles — SoC Hardware Security Ontology

## Purpose

This reference defines four SoC family profiles that represent the primary deployment contexts for hardware security engineering. Skills use family profiles to tailor threat models, select applicable compliance regimes, and annotate verification assets with family-specific constraints. Approximately 70-80% of security architecture is shared across families; this document focuses on the 20-30% that varies.

**Primary consumers:** threat-model-skill (family-specific threat weighting), compliance-pipeline-skill (compliance regime selection), verification-scaffold-skill (constraint-aware assertion generation)
**Secondary consumers:** executive-brief-skill (audience context), cross-cutting references (traceability matrix annotations)

---

## Quick Reference

| Family | Primary Market | Key Compliance | Typical Interconnect | Power Model | Security Emphasis |
|---|---|---|---|---|---|
| Compute (Server/HPC) | Cloud, enterprise, HPC | FIPS 140-3, SOC 2, FedRAMP | PCIe Gen5/6, CXL 3.x | Always-on, high power budget | Multi-tenant isolation, confidential compute |
| Automotive | ADAS, infotainment, zonal | ISO 21434, ISO 26262, UNECE R155 | AXI, CAN-FD, Ethernet | Constrained, multi-domain power | Functional safety + security co-design |
| Client (PC/Laptop) | Consumer, enterprise desktops | TCG TPM 2.0, Windows/Linux requirements | PCIe, USB4/Thunderbolt | Battery-optimized | User-facing security UX, firmware update |
| Data Center | Rack-scale, multi-tenant | FIPS 140-3, PCI DSS, CSA STAR | CXL fabric, PCIe, Ethernet | High power, redundant | Fabric security, multi-host isolation |

---

## Shared Security Architecture (70-80% Reuse)

Before detailing per-family deltas, the following components are expected to be substantially shared across all four families. Variation in these components is implementation-specific rather than family-specific.

| Component | Reuse Expectation | Notes |
|---|---|---|
| Crypto engines (AES, SHA, ECC, RSA) | High | Algorithm selection varies (e.g., SM4 for China compliance); core architecture shared |
| Boot ROM / immutable first stage | High | ROM size and interface vary; security model identical |
| DICE layered identity | High | Number of layers may vary; CDI derivation logic identical |
| Fuse controller (OTP) | High | Fuse count and layout vary; access control model shared |
| Debug authentication FSM | High | Debug features exposed may vary; auth protocol shared |
| TDISP state machine | Medium-High | Present only in families with PCIe; state machine logic shared |
| CHERI capability rules | Medium | Present only in CHERI-enabled designs; rules are ISA-defined |
| SPDM responder/requester | High | Protocol stack shared; certificate provisioning varies |

---

## Family 1: Compute (Server / HPC)

### Market Context

Server and high-performance computing SoCs deployed in enterprise data centers, cloud infrastructure, and HPC clusters. Primary security concern is multi-tenant isolation: multiple untrusted workloads from different customers share the same physical hardware.

### Constraints and Characteristics

| Aspect | Description |
|---|---|
| **Threat environment** | Sophisticated adversaries (nation-state, insider); physical access to data center hardware possible but monitored |
| **Power budget** | High (200-500W TDP typical); not a constraint on security features |
| **Die area** | Large; dedicated security IP blocks feasible |
| **Boot time** | Tolerant (minutes acceptable for server boot); security checks can be thorough |
| **Field update** | Regular firmware updates via BMC/out-of-band management; update latency in hours acceptable |
| **Lifetime** | 5-7 years in deployment; long-term key management and crypto agility required |
| **Debug requirements** | Manufacturing debug, RMA debug, in-field diagnostics; must be authenticated post-production |

### Compliance Regimes

| Standard | Applicability | Notes |
|---|---|---|
| **FIPS 140-3** | Required for US government workloads; common baseline for enterprise | Level 2 minimum for cloud; Level 3 for HSM functions |
| **SOC 2 Type II** | Required by cloud service providers for platform components | Audit trail and access control evidence |
| **FedRAMP** | Required for US federal cloud deployments | Inherits FIPS + additional controls from NIST 800-53 |
| **Common Criteria** | Some enterprise/government procurement requirements | EAL4+ for security-critical subsystems |
| **PCI DSS** | If processing payment data | Applies to specific partitions, not whole SoC |

### Typical Bus and Interconnect

- **Primary:** PCIe Gen5/Gen6 for device connectivity, CXL 3.x for memory and accelerator fabric
- **On-chip:** AMBA AXI/ACE for coherent interconnect, proprietary NoC
- **Management:** BMC (Baseboard Management Controller) via I3C/SPI/LPC, MCTP for SPDM transport

### Family-Specific Security Considerations

1. **CXL fabric security:** Multi-host memory sharing requires TSP (Type-3 Security Protocol) for isolation; IDE for CXL link encryption
2. **Confidential VM support:** Hardware must enforce VM isolation even when hypervisor is untrusted (SEV-SNP, TDX, CCA)
3. **TDISP for accelerators:** GPUs and DPUs assigned to confidential VMs via TDISP require full state machine and SPDM session binding
4. **Attestation at scale:** Platform attestation for thousands of servers requires efficient certificate management and key rotation
5. **RAS (Reliability, Availability, Serviceability):** Error handling must not create security bypasses (e.g., uncorrectable errors must not downgrade isolation)

### Verification Emphasis

- Tier 1 focus: Bus firewall rules for multi-tenant isolation, register locks for security configuration, TDISP state machine transitions
- Tier 2 focus: CXL TSP partition configuration, SPDM authentication flows, IDE key rotation
- Tier 3 focus: Cross-VM information flow, speculative execution side channels, cache timing channels

---

## Family 2: Automotive

### Market Context

Automotive SoCs for Advanced Driver Assistance Systems (ADAS), infotainment, zonal controllers, and vehicle compute platforms. Unique requirement: functional safety (ISO 26262) and cybersecurity (ISO 21434) must be co-designed. A security failure that causes a safety failure has life-safety implications.

### Constraints and Characteristics

| Aspect | Description |
|---|---|
| **Threat environment** | Physical access by vehicle owner/attacker; OBD-II and CAN bus exposure; long unattended operation; OTA update surface |
| **Power budget** | Constrained (5-50W typical); security features compete with compute workloads for power and thermal budget |
| **Die area** | Medium; cost-sensitive market; dedicated security IP must justify area |
| **Boot time** | Critical (< 1 second for safety functions); security checks must not delay safety-critical startup |
| **Field update** | OTA updates with rollback protection; update must not brick the vehicle; A/B partition scheme common |
| **Lifetime** | 10-15 years in deployment; crypto agility mandatory (algorithm migration mid-life) |
| **Debug requirements** | Manufacturing, assembly line, dealer diagnostics, crash analysis; debug must be tightly controlled post-production |

### Compliance Regimes

| Standard | Applicability | Notes |
|---|---|---|
| **ISO 21434** | Mandatory for vehicles sold in UNECE markets (2024+) | Full lifecycle: concept, development, production, operations, decommissioning |
| **ISO 26262** | Functional safety; security must not violate safety | ASIL-B to ASIL-D for security-relevant functions |
| **UNECE R155/R156** | UN regulation for cybersecurity and software updates | Required for type approval in EU, Japan, South Korea |
| **AUTOSAR** | Secure communication, secure onboard communication (SecOC) | Applicable to classic and adaptive AUTOSAR stacks |
| **FIPS 140-3** | If processing payment data (in-vehicle commerce) or government fleet | Uncommon but emerging for fleet management |

### Typical Bus and Interconnect

- **Primary:** AXI/AHB on-chip; CAN-FD and Automotive Ethernet for inter-ECU
- **High-performance domain:** PCIe for ADAS accelerators (emerging)
- **Management:** SPI for external flash, I2C/I3C for sensor interfaces
- **Vehicle network:** CAN-FD, FlexRay (legacy), Ethernet TSN

### Family-Specific Security Considerations

1. **Safety-security co-design:** Security mechanisms must not violate ASIL requirements; e.g., a cryptographic operation that blocks a safety-critical interrupt is unacceptable
2. **Fast secure boot:** Boot time budgets require parallelized verification or deferred verification with rollback for non-safety functions
3. **HSM integration:** Dedicated Hardware Security Module (SHE/EVITA/custom) for key storage, crypto operations, and secure boot anchoring
4. **Secure OTA with rollback:** A/B partition scheme; anti-rollback counters in fuses; update verification before activation; dealer recovery path if update fails
5. **Long-lifetime crypto agility:** 15-year deployed lifetime means algorithms selected today may be deprecated; design must support algorithm migration without hardware replacement
6. **Dealer/OBD debug control:** Debug access hierarchy: manufacturing (full), dealer (restricted), owner (locked); debug unlock must not compromise security keys

### Verification Emphasis

- Tier 1 focus: HSM access control, secure boot FSM timing constraints, CAN-FD message authentication (SecOC), register locks for safety-security isolation
- Tier 2 focus: OTA update flow security, ASIL-compatible crypto scheduling, diagnostic session authentication
- Tier 3 focus: Safety-security interference analysis, long-term key management, OBD attack surface

---

## Family 3: Client (PC / Laptop)

### Market Context

Client SoCs for desktops, laptops, and workstations. Primary security concern is protecting user data and platform integrity while maintaining a responsive user experience. Must integrate with OS-level security frameworks (Windows Secured-core PC, ChromeOS Verified Boot, Linux Lockdown).

### Constraints and Characteristics

| Aspect | Description |
|---|---|
| **Threat environment** | Physical theft, evil-maid attacks, malicious peripherals (USB/Thunderbolt), OS-level malware, user error |
| **Power budget** | Battery-constrained (15-45W typical for laptop); security features must be power-efficient |
| **Die area** | Medium-large; integrated SoC with GPU, NPU, security; area shared across functions |
| **Boot time** | User-facing (< 10 seconds expected); security checks should not noticeably delay boot |
| **Field update** | OS-driven firmware update (LVFS, Windows Update); user must consent; rollback common for usability |
| **Lifetime** | 3-5 years typical; shorter than server/auto; crypto agility less critical |
| **Debug requirements** | Manufacturing only; production devices should have debug permanently locked |

### Compliance Regimes

| Standard | Applicability | Notes |
|---|---|---|
| **TCG TPM 2.0** | Required for Windows 11; recommended for enterprise Linux | Discrete or firmware TPM; DICE interaction |
| **Windows Secured-core PC** | Enterprise procurement requirement (Microsoft) | DRTM, firmware protection, VBS |
| **FIPS 140-3** | Government/enterprise deployment | Module validation for crypto subsystem |
| **Common Criteria** | Some government procurement | EAL4+ for specific security functions |
| **ChromeOS Verified Boot** | Chromebook ecosystem | Verified boot chain with recovery |

### Typical Bus and Interconnect

- **Primary:** PCIe for discrete GPU, NVMe; USB4/Thunderbolt for external connectivity
- **On-chip:** Proprietary NoC; AMBA for IP blocks
- **External:** USB4/Thunderbolt (security boundary for external devices), Wi-Fi, Bluetooth
- **Management:** Embedded controller (EC) via eSPI/LPC

### Family-Specific Security Considerations

1. **TPM integration:** Hardware TPM 2.0 or firmware TPM; DICE identity must complement (not conflict with) TPM-based attestation
2. **Thunderbolt/USB4 security:** External device DMA must be filtered; IOMMU enforcement before device enumeration; hot-plug security
3. **Full-disk encryption key management:** BitLocker/LUKS key sealed to TPM PCR values; boot chain integrity directly affects user data access
4. **Firmware update UX:** Updates must balance security (signed, verified) with usability (not blocking, recoverable); anti-rollback must not prevent legitimate recovery
5. **Evil-maid resistance:** Boot integrity must survive physical access when device is unattended; measured boot + sealed secrets detect tampering
6. **NPU/AI security:** On-die NPU for local inference must isolate model and data from other workloads

### Verification Emphasis

- Tier 1 focus: TPM command interface access control, IOMMU DMA filtering, firmware update signature verification, register locks for production fuse settings
- Tier 2 focus: TPM-DICE interaction, Thunderbolt enumeration security, BitLocker key sealing flow
- Tier 3 focus: Evil-maid attack resistance, NPU workload isolation, covert channel through shared GPU memory

---

## Family 4: Data Center

### Market Context

Data center infrastructure SoCs including DPUs (Data Processing Units), SmartNICs, storage controllers, and rack-scale management controllers. Distinguished from Compute family by focus on infrastructure services (networking, storage, management) rather than compute workloads. Primary security concern is fabric-level isolation and multi-host security.

### Constraints and Characteristics

| Aspect | Description |
|---|---|
| **Threat environment** | Adjacent tenants, compromised management plane, rogue firmware on DPUs, physical interposer on CXL/PCIe links |
| **Power budget** | Medium-high (50-200W for DPUs); power budget available for security features |
| **Die area** | Medium-large; dedicated security IP justified by infrastructure criticality |
| **Boot time** | Tolerant (infrastructure boots before workloads); thorough security checks acceptable |
| **Field update** | Automated fleet management; updates pushed to thousands of devices; rollback must be automated |
| **Lifetime** | 5-7 years; aligned with server refresh cycles |
| **Debug requirements** | Manufacturing, fleet diagnostics, RMA; remote debug capability required; must be authenticated |

### Compliance Regimes

| Standard | Applicability | Notes |
|---|---|---|
| **FIPS 140-3** | Baseline for crypto operations in DPUs/SmartNICs | Level 2 minimum; Level 3 for key management |
| **PCI DSS** | If DPU handles payment network traffic | Applies to specific data path partitions |
| **CSA STAR** | Cloud Security Alliance certification for cloud infrastructure | DPU/SmartNIC as infrastructure component |
| **SOC 2 Type II** | Cloud service provider infrastructure audit | Audit trail, access control evidence |
| **NIST 800-53** | US federal infrastructure | Inherited from FedRAMP requirements |

### Typical Bus and Interconnect

- **Primary:** CXL 3.x for memory fabric, PCIe Gen5/6 for device connectivity, high-speed Ethernet (100/400GbE)
- **On-chip:** AMBA AXI/ACE, proprietary NoC, hardware mailboxes for inter-core communication
- **Management:** BMC interfaces, MCTP transport for SPDM, I3C for environmental sensors
- **Fabric:** CXL switch ports, PCIe switch fabric, Ethernet fabric

### Family-Specific Security Considerations

1. **CXL fabric multi-host isolation:** Type-3 memory devices shared across multiple hosts require TSP for per-host memory partitioning and IDE for link encryption
2. **DPU as trust boundary:** DPU sits between network and host; must enforce security policies without trusting the host OS
3. **Fleet-scale attestation:** Thousands of DPUs/SmartNICs require efficient, automated attestation with certificate rotation
4. **Management plane security:** BMC and management controllers are high-value targets; must be isolated from data plane and independently attestable
5. **Multi-host key management:** IDE keys for CXL links must be managed per-host; key rotation must not disrupt active data transfers
6. **Disaggregated security:** In rack-scale disaggregated architectures, security boundaries span multiple physical devices; trust model must account for inter-device links

### Verification Emphasis

- Tier 1 focus: CXL TSP partition enforcement, DPU firewall rules, management plane isolation registers, IDE key management FSM
- Tier 2 focus: Multi-host SPDM session management, CXL IDE key rotation, DPU policy enforcement correctness
- Tier 3 focus: Cross-host information flow through shared CXL memory, management plane lateral movement, fabric-level side channels

---

## Family Comparison Matrix

### Security Feature Relevance by Family

| Feature | Compute | Automotive | Client | Data Center |
|---|---|---|---|---|
| Confidential VM / TEE | Critical | Emerging | Emerging | Critical (infra) |
| TDISP device assignment | Critical | N/A | Emerging | Critical |
| CXL IDE / TSP | Critical | N/A | N/A | Critical |
| SPDM authentication | Critical | Emerging | Limited | Critical |
| DICE identity | Critical | Critical | Critical | Critical |
| CHERI capabilities | Emerging | Emerging | Research | Emerging |
| HSM / Secure element | Standard | Critical | Standard (TPM) | Standard |
| OTA update security | Important | Critical | Important | Critical (fleet) |
| Debug authentication | Important | Critical | Important | Important |
| Bus firewall / IOMMU | Critical | Critical | Critical | Critical |

### Compliance Overlap

| Compliance | Compute | Automotive | Client | Data Center |
|---|---|---|---|---|
| FIPS 140-3 | X | Emerging | X | X |
| ISO 21434 | | X | | |
| ISO 26262 | | X | | |
| TCG TPM 2.0 | X | | X | |
| SOC 2 Type II | X | | | X |
| Common Criteria | Optional | Optional | Optional | Optional |
| PCI DSS | Partition | | | Partition |

---

## Traceability Matrix Template

The following template is used by the compliance-pipeline-skill to generate per-family traceability matrices. Each row traces a requirement from specification through verification to compliance evidence.

| Column | Description | Example |
|---|---|---|
| **Spec Req ID** | Requirement identifier from standards registry | REQ-DICE-003 |
| **Req Text** | Summary of the requirement | CDI must be derived from UDS and firmware measurement |
| **Security Domain** | Technology domain from domain-ontology | Secure Boot / DICE |
| **SoC Family** | Target family from this document | Compute |
| **RTL Module** | Implementation module in design | `dice_engine.sv` |
| **Verification Asset** | SVA assertion, testbench, or property | `dice_cdi_derivation_check` |
| **Compliance Evidence** | Document or artifact satisfying auditor | Simulation log + coverage report |
| **Status** | Current state | Verified / Gap / In Progress |
| **Gap Flag** | Issues or missing items | None / Description of gap |

**Family-specific annotations:** When a requirement has different implementation or verification approaches per family, add a row per family rather than combining. This ensures family-specific gaps are visible.

---

*[FROM TRAINING] All content in this file is derived from publicly available specifications and general domain knowledge. Specific compliance requirements and standard versions should be verified against authoritative sources. Last verified: 2026-02-13.*
