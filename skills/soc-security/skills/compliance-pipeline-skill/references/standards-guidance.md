## Contents

- [TCG DICE v1.2](#tcg-dice-v12)
- [PCIe TDISP 1.0](#pcie-tdisp-10)
- [CXL 3.1 Security](#cxl-31-security)
- [CHERI ISA](#cheri-isa)
- [DMTF SPDM v1.4](#dmtf-spdm-v14)
- [FIPS 140-3 (Compliance Overlay)](#fips-140-3-compliance-overlay)
- [ISO 21434 (Compliance Overlay)](#iso-21434-compliance-overlay)
- [Cross-Family Analysis](#cross-family-analysis)
  - [Identifying Shared Requirements](#identifying-shared-requirements)
  - [Delta Categories](#delta-categories)
  - [Reuse Assessment Levels](#reuse-assessment-levels)

## TCG DICE v1.2

**Extraction focus:** UDS protection, CDI derivation rules, certificate hierarchy, attestation evidence format, layer isolation.

**Key compliance areas:**
- UDS must not be accessible after first DICE layer executes
- CDI derivation must include firmware measurement
- Certificate chain must be well-formed X.509 or CBOR
- Each layer must have its own asymmetric key pair derived from CDI

**Cross-family delta:** Layering is architecturally consistent. Deltas: number of layers, certificate format (X.509 for server, CBOR for constrained automotive), key sizes.

## PCIe TDISP 1.0

**Extraction focus:** TDI state machine (CONFIG, LOCK, RUN, ERROR), SPDM session binding, IDE stream setup, device interface isolation, lock/unlock flow.

**Key compliance areas:**
- TDI state transitions must follow the defined state machine
- SPDM authentication must complete before TDI enters RUN state
- IDE stream must be established before DMA is permitted
- Device interface functions must be isolated between trust domains

**Cross-family delta:** Primarily compute and data center. Automotive may have PCIe-attached accelerators with simplified TDISP. Client has emerging Thunderbolt/USB4 overlap.

## CXL 3.1 Security

**Extraction focus:** TSP for shared memory, IDE for CXL link encryption/integrity, multi-host isolation, cache coherence security, memory encryption.

**Key compliance areas:**
- TSP must partition memory per host with hardware enforcement
- IDE must be active before security-sensitive data traverses CXL links
- Multi-host key management must support per-host keys
- Cache coherence must not leak cross-host data through snoop responses

**Cross-family delta:** Primarily compute and data center. Cache coherence security most critical in multi-socket compute. TSP most relevant for data center memory pooling.

## CHERI ISA

**Extraction focus:** Capability encoding invariants, memory safety properties, compartmentalization (sealing, sentries), revocation, PMP interaction.

**Key compliance areas:**
- Tag bit must be hardware-maintained and not forgeable by software
- Capability bounds must be enforced on every memory access
- Sealed capabilities must only be unsealed by authorized sentries
- Revocation must reliably invalidate all copies of a revoked capability

**Cross-family delta:** ISA-defined, consistent across families. Deltas: PMP for RISC-V, bus capability enforcement for DMA.

## DMTF SPDM v1.4

**Extraction focus:** Authentication handshake, measurement reporting, key exchange, secure session, certificate management.

**Key compliance areas:**
- Responder must authenticate using a valid certificate chain
- Measurements must be reported accurately and completely
- Session keys must have forward secrecy
- Nonces must be fresh and unpredictable

**Cross-family delta:** Protocol consistent across families. Transport binding varies: MCTP for server/DC, PCIe DOE for device-level, custom transport for automotive.

## FIPS 140-3 (Compliance Overlay)

Overlay FIPS on top of primary standard requirements:
- Cryptographic algorithm validation (CAVP)
- Key management lifecycle
- Self-test requirements
- Physical security levels (Levels 1-4)
- Degraded operation modes

**Application:** Add FIPS clauses as additional `standard` and `standardClause` references on ComplianceResult entities. Do not create separate SecurityRequirement entities.

## ISO 21434 (Compliance Overlay)

Applicable to automotive family:
- TARA requirements
- Cybersecurity goals and claims
- Work product requirements per lifecycle phase
- Supply chain cybersecurity requirements
- Monitoring and incident response

**Application:** Lifecycle standard. Map requirements to engineering activities and work products rather than specific RTL or firmware implementations.

## Cross-Family Analysis

### Identifying Shared Requirements

Group requirements by reuse pattern:
- **Fully shared:** Same requirement, same implementation across families (e.g., DICE CDI derivation logic)
- **Shared with deltas:** Same requirement, different implementation per family (e.g., bus firewall varies by interconnect)
- **Family-specific:** Applies only to certain families (e.g., ISO 21434 only for automotive)

### Delta Categories

| Delta Category | What Varies | Example |
|---|---|---|
| Bus wrapper | Bus interface connecting security IP to SoC fabric | AXI for automotive, CXL for data center |
| Compliance regime | Which compliance overlay applies | ISO 21434 for automotive, FIPS 140-3 for compute |
| Power domain | Power management interactions with security | Automotive has power-gated security domains |
| Verification approach | Different verification strategies per family | Formal for server, simulation for client |
| Evidence format | Different compliance evidence artifacts | ISO 21434 work products vs. FIPS test reports |

### Reuse Assessment Levels

| Reuse Level | Meaning | Action |
|---|---|---|
| **High** | Same RTL module, same verification, same compliance evidence | Reference shared evidence; no per-family work |
| **Medium** | Same RTL but different integration; needs per-family verification | Share RTL verification; add integration checks per family |
| **Low** | Same concept but fundamentally different implementation | Independent compliance tracking per family |
