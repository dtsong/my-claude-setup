# Entity Schema — SoC Security Skills Suite

Defines the typed entities used as inter-skill contracts and the document envelope format for persistence. All skills in the pipeline produce and consume these entities.

## Overview

The data model has two layers:

1. **Typed Entities** — Runtime contracts passed between skills. Each entity type has a defined structure that downstream skills can validate and consume.
2. **Document Envelopes** — Persistence wrappers that add YAML frontmatter metadata to entity collections for disk storage, cross-session retrieval, and human readability.

---

## Common Fields

All entities share these fields:

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | Unique identifier. Format: `{PREFIX}-{YYYY}-{NNN}` (e.g., `SR-2026-001`, `TF-2026-042`) |
| `confidenceTier` | enum | Yes | One of: `GROUNDED`, `INFERRED`, `SPECULATIVE`, `ABSENT` |
| `verificationStatus` | enum | Yes | One of: `llm-assessed`, `human-verified`, `tool-verified` |
| `sourceGrounding` | enum | Yes | One of: `user-provided`, `embedded-reference`, `training-knowledge` |

### Confidence Tiers

| Tier | Meaning | Downstream Behavior |
|------|---------|---------------------|
| `GROUNDED` | Directly supported by cited spec section or user-provided evidence | Passes to all downstream skills automatically |
| `INFERRED` | Logically derived from requirements but not explicitly stated | Passes with caveat annotation |
| `SPECULATIVE` | Plausible but not grounded in provided context | Blocks pending human acknowledgment before entering Compliance Pipeline or Executive Brief |
| `ABSENT` | Known attack category where no analysis was performed | Flagged as coverage gap in all downstream outputs |

### Verification Status

| Status | Meaning |
|--------|---------|
| `llm-assessed` | Initial assessment by the LLM; requires human review |
| `human-verified` | Reviewed and confirmed by a domain expert |
| `tool-verified` | Validated by automated tooling (simulation, formal verification, lint) |

### Source Grounding

| Source | Trust Level | Annotation |
|--------|-------------|------------|
| `user-provided` | Highest | Direct from user context (RTL, specs, architecture docs) |
| `embedded-reference` | Medium | From shared-references knowledge packs |
| `training-knowledge` | Lowest | From model training data; marked `[FROM TRAINING]` |

---

## Entity Definitions

### 1. SecurityRequirement

Represents a single security requirement extracted from a specification or derived from threat analysis.

**ID prefix:** `SR`

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | e.g., `SR-2026-001` |
| `title` | string | Yes | Short descriptive title |
| `sourceSpec` | string | Yes | Specification reference (e.g., `TDISP-1.0 Section 4.3.2`) |
| `domain` | enum | Yes | Technology domain: `confidential-ai`, `tdisp-cxl`, `supply-chain`, `secure-boot-dice`, `cheri` |
| `socFamily` | enum[] | Yes | One or more: `compute`, `automotive`, `client`, `data-center` |
| `securityProperty` | enum | Yes | `confidentiality`, `integrity`, `availability`, `authenticity`, `authorization`, `non-repudiation` |
| `implementationLayer` | enum | Yes | `rtl`, `firmware`, `software`, `protocol`, `physical` |
| `complianceStatus` | enum | Yes | `met`, `partial`, `not-met`, `not-assessed` |
| `description` | string | Yes | Full requirement description |
| `rationale` | string | No | Why this requirement exists |
| `confidenceTier` | enum | Yes | See Common Fields |
| `verificationStatus` | enum | Yes | See Common Fields |
| `sourceGrounding` | enum | Yes | See Common Fields |

**Example:**

```yaml
- id: SR-2026-001
  title: "TDISP Device Interface Isolation"
  sourceSpec: "TDISP-1.0 Section 4.3.2"
  domain: tdisp-cxl
  socFamily: [data-center, compute]
  securityProperty: authorization
  implementationLayer: rtl
  complianceStatus: not-assessed
  description: >
    The TDI shall enforce that device interface functions assigned to a
    trust domain are isolated from functions assigned to other trust domains.
    No cross-domain register access shall be permitted without explicit
    TSM authorization.
  rationale: "Prevents lateral movement between trust domains via shared device interfaces"
  confidenceTier: GROUNDED
  verificationStatus: llm-assessed
  sourceGrounding: embedded-reference
```

---

### 2. ThreatFinding

Represents an identified threat against a security boundary or component.

**ID prefix:** `TF`

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | e.g., `TF-2026-001` |
| `title` | string | Yes | Short descriptive title |
| `strideCategory` | enum | Yes | `spoofing`, `tampering`, `repudiation`, `information-disclosure`, `denial-of-service`, `elevation-of-privilege` |
| `attackVector` | string | Yes | Description of the attack path |
| `targetComponent` | string | Yes | Component or boundary under threat |
| `domain` | enum | Yes | Technology domain (same enum as SecurityRequirement) |
| `socFamily` | enum[] | Yes | Applicable SoC families |
| `severity` | enum | Yes | `critical`, `high`, `medium`, `low`, `informational` |
| `prerequisite` | string | No | Required attacker capabilities or access |
| `mitigationRequirements` | string[] | No | SecurityRequirement IDs that mitigate this threat |
| `verificationMethod` | enum | Yes | `sva-assertion`, `simulation`, `formal-proof`, `code-review`, `penetration-test`, `checklist-review` |
| `description` | string | Yes | Full threat description |
| `confidenceTier` | enum | Yes | See Common Fields |
| `verificationStatus` | enum | Yes | See Common Fields |
| `sourceGrounding` | enum | Yes | See Common Fields |

**Example:**

```yaml
- id: TF-2026-001
  title: "DMA Bypass via Malformed TLP in TDISP Handshake"
  strideCategory: elevation-of-privilege
  attackVector: >
    Attacker sends malformed TLP during TDISP LOCK_INTERFACE_REPORT
    handshake to bypass DMA isolation check in the TDISP responder FSM.
  targetComponent: "TDISP Responder State Machine"
  domain: tdisp-cxl
  socFamily: [data-center]
  severity: critical
  prerequisite: "Physical or logical access to PCIe bus"
  mitigationRequirements: [SR-2026-001, SR-2026-003]
  verificationMethod: sva-assertion
  description: >
    The TDISP responder FSM transitions from LOCK_INTERFACE_REPORT to
    DEVICE_INTERFACE_STATE without validating all TLP fields. A malformed
    TLP could cause the FSM to enter an unintended state, bypassing DMA
    isolation enforcement.
  confidenceTier: INFERRED
  verificationStatus: llm-assessed
  sourceGrounding: embedded-reference
```

---

### 3. VerificationItem

Represents a single verification checklist item generated from threat findings.

**ID prefix:** `VI`

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | e.g., `VI-2026-001` |
| `title` | string | Yes | Short descriptive title |
| `tier` | enum | Yes | `1` (mechanical), `2` (protocol), `3` (information-flow) |
| `sourceThreat` | string | Yes | ThreatFinding ID this item verifies |
| `sourceRequirement` | string | No | SecurityRequirement ID this item traces to |
| `assertionStub` | string | No | SVA assertion template (Tier 1 and 2 only) |
| `assertionStatus` | enum | No | `TEMPLATE` (needs signal customization) or `READY` (uses provided RTL signals) |
| `intentComment` | string | Yes | What this check is intended to verify |
| `doesNotCheck` | string | Yes | Explicit annotation of what this item does NOT verify |
| `description` | string | Yes | Full verification item description |
| `confidenceTier` | enum | Yes | See Common Fields |
| `verificationStatus` | enum | Yes | See Common Fields |
| `sourceGrounding` | enum | Yes | See Common Fields |

**Tier Definitions:**

| Tier | Name | Scope | Output Format |
|------|------|-------|---------------|
| 1 | Mechanical | Access control, FSM state coverage, register lock-down | SVA assertions (high confidence) |
| 2 | Protocol | DICE handshake, CXL.cache coherence, SPDM session state | SVA assertions (needs review) |
| 3 | Information Flow | Side-channel, data-dependent timing, covert channels | Natural language specification only (no SVA generated) |

**Example:**

```yaml
- id: VI-2026-001
  title: "TDISP FSM State Transition Validity"
  tier: 1
  sourceThreat: TF-2026-001
  sourceRequirement: SR-2026-001
  assertionStub: |
    // INTENT: Verify TDISP responder FSM only transitions on valid TLP
    // DOES NOT CHECK: TLP payload content validity, timing side-channels
    assert property (@(posedge clk) disable iff (!rst_n)
      (tdisp_fsm_state == LOCK_INTERFACE_REPORT) && tdisp_tlp_valid
      |-> ##[1:MAX_LATENCY] (tdisp_fsm_state == DEVICE_INTERFACE_STATE)
    ) else $error("TDISP FSM invalid transition from LOCK_INTERFACE_REPORT");
  assertionStatus: TEMPLATE
  intentComment: "Verify TDISP responder FSM only transitions to DEVICE_INTERFACE_STATE on valid TLP receipt"
  doesNotCheck: "TLP payload content validity, timing side-channels, DMA isolation enforcement post-transition"
  description: >
    Tier 1 mechanical check on the TDISP responder FSM. Verifies that the
    state transition from LOCK_INTERFACE_REPORT to DEVICE_INTERFACE_STATE
    only occurs when a valid TLP is received. Signals need customization
    to match target RTL.
  confidenceTier: INFERRED
  verificationStatus: llm-assessed
  sourceGrounding: embedded-reference
```

---

### 4. ComplianceResult

Represents the mapping of a security requirement to compliance evidence with coverage status.

**ID prefix:** `CR`

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | e.g., `CR-2026-001` |
| `requirementId` | string | Yes | SecurityRequirement ID being mapped |
| `standard` | string | Yes | Compliance standard (e.g., `FIPS 140-3`, `ISO 21434`) |
| `standardClause` | string | Yes | Specific clause or section reference |
| `coverageStatus` | enum | Yes | `covered`, `partial`, `gap`, `not-applicable` |
| `evidenceType` | enum | Yes | `sva-result`, `simulation-log`, `review-record`, `design-document`, `test-report`, `none` |
| `evidenceReference` | string | No | Path or ID of the evidence artifact |
| `gapDescription` | string | No | Description of what is missing (when `partial` or `gap`) |
| `remediationPlan` | string | No | Suggested steps to close the gap |
| `traceability` | object | Yes | Links to upstream entities |
| `traceability.requirements` | string[] | Yes | SecurityRequirement IDs |
| `traceability.threats` | string[] | No | ThreatFinding IDs |
| `traceability.verificationItems` | string[] | No | VerificationItem IDs |
| `confidenceTier` | enum | Yes | See Common Fields |
| `verificationStatus` | enum | Yes | See Common Fields |
| `sourceGrounding` | enum | Yes | See Common Fields |

**Example:**

```yaml
- id: CR-2026-001
  requirementId: SR-2026-001
  standard: "FIPS 140-3"
  standardClause: "Section 7.7 — Physical Security"
  coverageStatus: partial
  evidenceType: sva-result
  evidenceReference: "vi/VI-2026-001-result.log"
  gapDescription: >
    SVA assertion covers FSM transition validity but does not verify
    DMA isolation enforcement post-transition. Physical tamper
    resistance not assessed.
  remediationPlan: >
    1. Add Tier 2 assertion for DMA isolation post-state-transition.
    2. Commission physical security assessment for tamper resistance.
  traceability:
    requirements: [SR-2026-001]
    threats: [TF-2026-001]
    verificationItems: [VI-2026-001]
  confidenceTier: INFERRED
  verificationStatus: llm-assessed
  sourceGrounding: embedded-reference
```

---

### 5. BriefSection

Represents a 4-layer abstracted finding for executive consumption. Each section translates a technical finding through increasing levels of abstraction.

**ID prefix:** `BS`

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | e.g., `BS-2026-001` |
| `title` | string | Yes | Executive-friendly title |
| `audience` | enum | Yes | `board`, `ciso`, `program` |
| `sourceFinding` | string | Yes | ThreatFinding or ComplianceResult ID |
| `layer0_technical` | string | Yes | Raw technical finding |
| `layer1_impact` | string | Yes | Security impact statement |
| `layer2_businessRisk` | string | Yes | Business risk statement |
| `layer3_actionItem` | string | Yes | Executive action item with cost/timeline |
| `riskRating` | enum | Yes | `critical`, `high`, `medium`, `low` |
| `recommendedTimeline` | string | No | Suggested remediation timeline |
| `costEstimate` | string | No | Order-of-magnitude cost if available |
| `confidenceTier` | enum | Yes | See Common Fields |
| `verificationStatus` | enum | Yes | See Common Fields |
| `sourceGrounding` | enum | Yes | See Common Fields |

**Example:**

```yaml
- id: BS-2026-001
  title: "Memory Isolation Gap in Device Assignment"
  audience: ciso
  sourceFinding: TF-2026-001
  layer0_technical: >
    DMA bypass via malformed TLP in TDISP handshake allows unauthorized
    memory access across trust domain boundaries.
  layer1_impact: >
    Attacker with physical access to the PCIe bus can bypass memory
    isolation between trust domains, accessing data belonging to other
    tenants or security-sensitive workloads.
  layer2_businessRisk: >
    Customer data in confidential AI inference pipelines may be exposed.
    Affects multi-tenant data center deployments using TDISP-based device
    assignment. Potential regulatory exposure under data protection
    frameworks.
  layer3_actionItem: >
    Prioritize TDISP responder FSM fix in Q2 silicon respin. Estimated
    engineering cost: 2-3 engineer-weeks. Risk if deferred: potential
    customer data exposure in production deployments.
  riskRating: critical
  recommendedTimeline: "Q2 2026 silicon respin"
  costEstimate: "2-3 engineer-weeks"
  confidenceTier: INFERRED
  verificationStatus: llm-assessed
  sourceGrounding: embedded-reference
```

---

## Document Envelope Format

Every artifact persisted to disk uses the `DocumentEnvelope<T>` format — a Markdown file with YAML frontmatter wrapping a collection of typed entities.

### YAML Frontmatter Fields

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `type` | enum | Yes | `threat-model`, `compliance-matrix`, `verification-checklist`, `exec-brief` |
| `id` | string | Yes | Document identifier (e.g., `TM-2026-001`) |
| `title` | string | Yes | Human-readable document title |
| `created` | date | Yes | ISO-8601 creation date |
| `updated` | date | Yes | ISO-8601 last update date |
| `soc-family` | string[] | Yes | Applicable SoC families |
| `technology-domain` | string[] | Yes | Applicable technology domains |
| `standards` | string[] | Yes | Referenced standards with versions |
| `related-documents` | string[] | No | IDs of related documents |
| `status` | enum | Yes | `draft`, `review`, `approved`, `superseded` |
| `confidence-summary` | object | Yes | Counts of entities per confidence tier |
| `caveats` | string | Yes | Mandatory disclaimer and coverage limitations |

### Example Document Envelope

```markdown
---
type: threat-model
id: TM-2026-001
title: "TDISP Device Assignment Threat Model"
created: 2026-02-13
updated: 2026-02-13
soc-family: [data-center, compute]
technology-domain: [tdisp-cxl, confidential-ai]
standards: [TDISP-1.0, SPDM-1.4, CXL-3.1]
related-documents: [VC-2026-001, CM-2026-001]
status: draft
confidence-summary: {grounded: 12, inferred: 5, speculative: 3, absent: 2}
caveats: |
  LLM-generated draft. Items marked INFERRED or SPECULATIVE require human verification.
  NOT ANALYZED: side-channel attacks, fault injection, physical tamper.
---

# TDISP Device Assignment Threat Model

> **Caveat:** LLM-generated draft. Items marked INFERRED or SPECULATIVE require
> human verification. NOT ANALYZED: side-channel attacks, fault injection,
> physical tamper.

## Coverage Boundary

This analysis covers: TDISP responder state machine, device interface isolation,
TLP validation, DMA access control.

It does NOT cover: side-channel attacks, fault injection, debug interface security,
physical tamper resistance.

## Attack Surface Checklist

| Area | Status |
|------|--------|
| Side-channel | NOT ANALYZED |
| Fault injection | NOT ANALYZED |
| Debug interface | NOT ANALYZED |
| Key management | ANALYZED |
| Boot chain | NOT ANALYZED |
| Firmware update | NOT ANALYZED |
| Bus access control | ANALYZED |

## Confidence Summary

| Tier | Count |
|------|-------|
| GROUNDED | 12 |
| INFERRED | 5 |
| SPECULATIVE | 3 |
| ABSENT | 2 |

## Security Requirements

[SecurityRequirement entities listed here]

## Threat Findings

[ThreatFinding entities listed here]
```

### Document Type Prefixes

| Document Type | Prefix | Contains |
|---------------|--------|----------|
| Threat Model | `TM` | SecurityRequirement + ThreatFinding entities |
| Verification Checklist | `VC` | VerificationItem entities |
| Compliance Matrix | `CM` | ComplianceResult entities |
| Executive Brief | `EB` | BriefSection entities |

---

### 6. MicroarchAttackFinding

Represents an identified microarchitectural attack vector against a hardware component, including transient execution attacks, cache side-channels, and branch predictor attacks.

**ID prefix:** `MF`

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | e.g., `MF-2026-001` |
| `title` | string | Yes | Short descriptive title |
| `attackClass` | enum | Yes | `transient-execution`, `cache-side-channel`, `branch-predictor`, `tlb-attack`, `port-contention`, `prefetch-attack` |
| `microarchComponent` | enum | Yes | `cache`, `btb`, `tlb`, `store-buffer`, `port`, `prefetcher`, `fill-buffer`, `line-fill-buffer` |
| `speculativeWindowCycles` | number | No | Estimated speculative execution window in clock cycles |
| `mitigationClass` | enum | Yes | `serialization`, `partitioning`, `cleansing`, `masking`, `isolation`, `none-identified` |
| `targetComponent` | string | Yes | Component or microarchitectural structure under threat |
| `domain` | enum | Yes | Technology domain (from domain ontology) |
| `socFamily` | enum[] | Yes | Applicable SoC families |
| `severity` | enum | Yes | `critical`, `high`, `medium`, `low`, `informational` |
| `researchReference` | string | No | Paper citation or CVE reference (format per `cross-cutting/research-currency.md`) |
| `description` | string | Yes | Full attack description including microarchitectural mechanism |
| `confidenceTier` | enum | Yes | See Common Fields |
| `verificationStatus` | enum | Yes | See Common Fields |
| `sourceGrounding` | enum | Yes | See Common Fields |

**Example:**

```yaml
- id: MF-2026-001
  title: "Spectre-BTB Cross-Domain Leakage via Branch Target Injection"
  attackClass: transient-execution
  microarchComponent: btb
  speculativeWindowCycles: 120
  mitigationClass: partitioning
  targetComponent: "Branch Target Buffer shared across security domains"
  domain: confidential-ai
  socFamily: [compute, data-center]
  severity: high
  researchReference: "Kocher et al., Spectre Attacks, IEEE S&P 2019; CVE-2017-5715"
  description: >
    An attacker in one security domain can mistrain the BTB with adversarial
    branch targets, causing a victim in a different domain to speculatively
    execute attacker-chosen gadgets. This transiently accesses victim memory,
    leaving observable cache footprints extractable via Flush+Reload.
  confidenceTier: GROUNDED
  verificationStatus: llm-assessed
  sourceGrounding: embedded-reference
```

---

### 7. PhysicalSCAFinding

Represents a physical side-channel analysis finding, covering power analysis, EM analysis, fault injection, and leakage assessment results.

**ID prefix:** `PF`

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | e.g., `PF-2026-001` |
| `title` | string | Yes | Short descriptive title |
| `attackClass` | enum | Yes | `spa`, `dpa`, `cpa`, `ema`, `dema`, `voltage-glitch`, `clock-glitch`, `laser-fi`, `em-fi`, `combined` |
| `targetCryptoOp` | string | Yes | Cryptographic operation or algorithm targeted (e.g., `AES-256 key schedule`, `ECDSA signing`) |
| `leakageModel` | enum | Yes | `hamming-weight`, `hamming-distance`, `identity`, `bit-model`, `stochastic`, `none-assessed` |
| `jilScore` | object | No | JIL attack potential scoring with subtotals |
| `jilScore.elapsed` | number | No | Elapsed time score (0-19) |
| `jilScore.expertise` | number | No | Expertise score (0-8) |
| `jilScore.knowledge` | number | No | Knowledge of TOE score (0-11) |
| `jilScore.access` | number | No | Window of opportunity / access score (0-10) |
| `jilScore.equipment` | number | No | Equipment score (0-9) |
| `jilScore.total` | number | No | Total JIL score |
| `jilScore.rating` | enum | No | `basic`, `enhanced-basic`, `moderate`, `high`, `beyond-high` |
| `iso17825Status` | enum | No | `pass`, `fail`, `not-assessed`, `inconclusive` |
| `countermeasureClass` | enum | Yes | `masking`, `hiding`, `detection`, `protocol-level`, `combined`, `none-identified` |
| `severity` | enum | Yes | `critical`, `high`, `medium`, `low`, `informational` |
| `description` | string | Yes | Full finding description |
| `confidenceTier` | enum | Yes | See Common Fields |
| `verificationStatus` | enum | Yes | See Common Fields |
| `sourceGrounding` | enum | Yes | See Common Fields |

**Example:**

```yaml
- id: PF-2026-001
  title: "DPA on AES-256 Key Schedule in Crypto Engine"
  attackClass: dpa
  targetCryptoOp: "AES-256 key schedule — round key derivation"
  leakageModel: hamming-weight
  jilScore:
    elapsed: 4
    expertise: 4
    knowledge: 3
    access: 4
    equipment: 4
    total: 19
    rating: moderate
  iso17825Status: not-assessed
  countermeasureClass: masking
  severity: high
  description: >
    Differential power analysis on the AES-256 key schedule reveals
    round key bytes through Hamming-weight correlation in the SubBytes
    operation. Attack requires ~10,000 power traces with 1 GS/s sampling.
    First-order masking countermeasure recommended.
  confidenceTier: INFERRED
  verificationStatus: llm-assessed
  sourceGrounding: embedded-reference
```

---

### 8. KernelSecFinding

Represents a kernel security finding, covering memory management security, process isolation, privilege escalation paths, and HW/SW security interface issues.

**ID prefix:** `KF`

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | e.g., `KF-2026-001` |
| `title` | string | Yes | Short descriptive title |
| `kernelSubsystem` | enum | Yes | `memory-management`, `process-isolation`, `iommu-smmu`, `seccomp-bpf`, `namespaces-cgroups`, `capabilities`, `integrity-subsystem`, `landlock`, `io-uring`, `dma-protection` |
| `isolationMechanism` | string | Yes | Specific isolation mechanism involved (e.g., `KPTI`, `SMAP`, `seccomp-BPF`) |
| `privilegeLevel` | enum | Yes | `user`, `kernel`, `hypervisor`, `firmware`, `hardware` |
| `attackPrimitive` | enum | Yes | `arbitrary-read`, `arbitrary-write`, `code-execution`, `privilege-escalation`, `container-escape`, `info-leak`, `denial-of-service` |
| `hwDependency` | string | No | Hardware feature dependency (e.g., `requires MMU`, `requires IOMMU`, `requires MTE`) |
| `targetComponent` | string | Yes | Kernel subsystem or component under threat |
| `severity` | enum | Yes | `critical`, `high`, `medium`, `low`, `informational` |
| `description` | string | Yes | Full finding description |
| `confidenceTier` | enum | Yes | See Common Fields |
| `verificationStatus` | enum | Yes | See Common Fields |
| `sourceGrounding` | enum | Yes | See Common Fields |

**Example:**

```yaml
- id: KF-2026-001
  title: "IOMMU Bypass via ATS Misuse in DMA-Capable Device"
  kernelSubsystem: iommu-smmu
  isolationMechanism: "IOMMU with ATS (Address Translation Services)"
  privilegeLevel: kernel
  attackPrimitive: arbitrary-read
  hwDependency: "Requires IOMMU with ATS enabled, PCIe device with ATS capability"
  targetComponent: "IOMMU/SMMU translation table management"
  severity: critical
  description: >
    A DMA-capable device with ATS privilege can issue translated requests
    that bypass IOMMU page table checks. If the IOMMU trusts ATS-translated
    requests without validation, the device can access arbitrary physical
    memory outside its assigned domain.
  confidenceTier: GROUNDED
  verificationStatus: llm-assessed
  sourceGrounding: embedded-reference
```

---

### 9. EmergingHWFinding

Represents a security finding related to emerging hardware paradigms: post-quantum crypto implementations, chiplet/UCIe architectures, heterogeneous compute security, and AI accelerator security.

**ID prefix:** `EF`

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | e.g., `EF-2026-001` |
| `title` | string | Yes | Short descriptive title |
| `paradigm` | enum | Yes | `post-quantum`, `chiplet-ucie`, `heterogeneous-compute`, `ai-accelerator` |
| `maturityLevel` | enum | Yes | `research`, `prototype`, `early-adoption`, `mainstream`, `legacy` |
| `standardsTrack` | string | No | Relevant emerging standard (e.g., `FIPS 203`, `UCIe 1.1`, `SPDM 1.4+`) |
| `migrationRisk` | enum | Yes | `critical`, `high`, `medium`, `low`, `informational` |
| `researchReference` | string | No | Paper citation (format per `cross-cutting/research-currency.md`) |
| `targetComponent` | string | Yes | Component or architectural element under analysis |
| `severity` | enum | Yes | `critical`, `high`, `medium`, `low`, `informational` |
| `description` | string | Yes | Full finding description |
| `confidenceTier` | enum | Yes | See Common Fields |
| `verificationStatus` | enum | Yes | See Common Fields |
| `sourceGrounding` | enum | Yes | See Common Fields |

**Example:**

```yaml
- id: EF-2026-001
  title: "CRYSTALS-Kyber Side-Channel via NTT Butterfly Operations"
  paradigm: post-quantum
  maturityLevel: early-adoption
  standardsTrack: "FIPS 203 (ML-KEM)"
  migrationRisk: high
  researchReference: "Primas et al., Single-trace attacks on Kyber, CHES 2023"
  targetComponent: "ML-KEM NTT hardware accelerator"
  severity: high
  description: >
    The Number Theoretic Transform (NTT) butterfly operations in a CRYSTALS-Kyber
    hardware implementation leak coefficient values through power side-channels.
    Single-trace electromagnetic analysis can recover the secret key from one
    decapsulation operation if countermeasures are absent.
  confidenceTier: INFERRED
  verificationStatus: llm-assessed
  sourceGrounding: training-knowledge
```

---

### 10. FormalSecSpec

Represents a formal security specification in TLA+, including safety/liveness properties, security invariants, and model checking configuration.

**ID prefix:** `FS`

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | e.g., `FS-2026-001` |
| `title` | string | Yes | Short descriptive title |
| `propertyType` | enum | Yes | `safety`, `liveness`, `invariant`, `fairness`, `information-flow` |
| `tlaplusModule` | string | Yes | TLA+ module name |
| `tlaplusSpec` | string | Yes | TLA+ specification text (complete module or property fragment) |
| `modelCheckStatus` | enum | Yes | `not-checked`, `checking`, `passed`, `failed`, `state-space-exceeded` |
| `stateSpace` | object | No | Model checking state space metrics |
| `stateSpace.states` | number | No | Number of reachable states explored |
| `stateSpace.distinct` | number | No | Number of distinct states |
| `stateSpace.depth` | number | No | Maximum depth of state graph |
| `assumptions` | string[] | Yes | Explicit assumptions the spec depends on |
| `limitations` | string[] | Yes | Known limitations of the specification |
| `sourceFinding` | string | No | Upstream finding ID this spec formalizes |
| `description` | string | Yes | What the specification captures and why |
| `confidenceTier` | enum | Yes | See Common Fields |
| `verificationStatus` | enum | Yes | See Common Fields |
| `sourceGrounding` | enum | Yes | See Common Fields |

**Example:**

```yaml
- id: FS-2026-001
  title: "TDISP State Machine Safety — No Unauthorized Transitions"
  propertyType: safety
  tlaplusModule: "TDISPStateMachine"
  tlaplusSpec: |
    ---- MODULE TDISPStateMachine ----
    EXTENDS Naturals, Sequences, FiniteSets
    VARIABLES state, authenticated, ide_active

    States == {"IDLE", "CONFIG", "LOCK", "RUN", "ERROR"}

    TypeInvariant ==
      /\ state \in States
      /\ authenticated \in BOOLEAN
      /\ ide_active \in BOOLEAN

    SafeTransition ==
      /\ state = "LOCK" /\ state' = "RUN"
         => authenticated /\ ide_active
      /\ state = "IDLE" /\ state' = "RUN"
         => FALSE  \* Cannot skip directly to RUN

    Safety == [][SafeTransition]_<<state, authenticated, ide_active>>
    ====
  modelCheckStatus: not-checked
  stateSpace:
    states: null
    distinct: null
    depth: null
  assumptions:
    - "State transitions are atomic (no partial transitions)"
    - "Authentication status is reliably reported by SPDM subsystem"
    - "IDE key establishment is complete before ide_active is set"
  limitations:
    - "Does not model timing — race conditions between state checks and transitions are not captured"
    - "Does not model physical fault injection that could corrupt state registers"
    - "Simplified authentication to boolean; real SPDM handshake has multiple sub-states"
  sourceFinding: "TF-2026-001"
  description: >
    Formal specification of the TDISP state machine safety property:
    the device interface cannot transition to RUN state without completed
    authentication and active IDE stream. This captures the core isolation
    invariant that unauthorized access to device resources is prevented.
  confidenceTier: INFERRED
  verificationStatus: llm-assessed
  sourceGrounding: embedded-reference
```

---

## Document Envelope Format

Every artifact persisted to disk uses the `DocumentEnvelope<T>` format — a Markdown file with YAML frontmatter wrapping a collection of typed entities.

### YAML Frontmatter Fields

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `type` | enum | Yes | `threat-model`, `compliance-matrix`, `verification-checklist`, `exec-brief`, `microarch-attack-model`, `physical-sca-assessment`, `kernel-security-model`, `emerging-hw-assessment`, `formal-security-spec` |
| `id` | string | Yes | Document identifier (e.g., `TM-2026-001`) |
| `title` | string | Yes | Human-readable document title |
| `created` | date | Yes | ISO-8601 creation date |
| `updated` | date | Yes | ISO-8601 last update date |
| `soc-family` | string[] | Yes | Applicable SoC families |
| `technology-domain` | string[] | Yes | Applicable technology domains |
| `standards` | string[] | Yes | Referenced standards with versions |
| `related-documents` | string[] | No | IDs of related documents |
| `status` | enum | Yes | `draft`, `review`, `approved`, `superseded` |
| `confidence-summary` | object | Yes | Counts of entities per confidence tier |
| `caveats` | string | Yes | Mandatory disclaimer and coverage limitations |

### Document Type Prefixes

| Document Type | Prefix | Contains |
|---------------|--------|----------|
| Threat Model | `TM` | SecurityRequirement + ThreatFinding entities |
| Verification Checklist | `VC` | VerificationItem entities |
| Compliance Matrix | `CM` | ComplianceResult entities |
| Executive Brief | `EB` | BriefSection entities |
| Microarch Attack Model | `MA` | MicroarchAttackFinding entities |
| Physical SCA Assessment | `PA` | PhysicalSCAFinding entities |
| Kernel Security Model | `KS` | KernelSecFinding entities |
| Emerging HW Assessment | `EH` | EmergingHWFinding entities |
| Formal Security Spec | `FS` | FormalSecSpec entities |

---

## Entity Relationships

```
EXISTING PIPELINE:
SecurityRequirement ←──── references ────→ ThreatFinding
        │                                        │
        │ traces to                               │ generates
        ▼                                        ▼
ComplianceResult ←──── verifies ────── VerificationItem
        │
        │ abstracts into
        ▼
   BriefSection

ADVANCED PIPELINE (parallel, independent):
ComponentDescription ─┬─→ MicroarchAttackFinding (MF)
  or ThreatFindings   ├─→ PhysicalSCAFinding (PF)
  (from P0)           ├─→ KernelSecFinding (KF)
                      └─→ EmergingHWFinding (EF)

FORMAL PIPELINE (hub, accepts any findings):
Any findings ──────────→ FormalSecSpec (FS)

Cross-feed: A0-A3 findings can feed into P1/P2/P3 for verification/compliance/brief
```

**Flow through the existing pipeline:**

1. `threat-model-skill` produces `SecurityRequirement[]` + `ThreatFinding[]`
2. `verification-scaffold-skill` consumes threats, produces `VerificationItem[]`
3. `compliance-pipeline-skill` consumes requirements + verification items, produces `ComplianceResult[]`
4. `executive-brief-skill` consumes findings + compliance results, produces `BriefSection[]`

**Flow through the advanced pipeline:**

5. `microarch-attack-skill` consumes ComponentDescription or ThreatFindings, produces `MicroarchAttackFinding[]`
6. `physical-sca-skill` consumes ComponentDescription or ThreatFindings, produces `PhysicalSCAFinding[]`
7. `kernel-security-skill` consumes ComponentDescription or ThreatFindings, produces `KernelSecFinding[]`
8. `emerging-hw-security-skill` consumes ComponentDescription or ThreatFindings, produces `EmergingHWFinding[]`

**Flow through the formal pipeline:**

9. `tlaplus-security-skill` consumes any findings type, produces `FormalSecSpec[]`
