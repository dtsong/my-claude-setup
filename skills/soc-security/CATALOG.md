# SoC Security Skills Catalog

> A curated suite of Claude Code skills for SoC hardware security engineering. 9 skills across two pipelines plus formal verification — from threat identification and microarchitectural attack analysis through compliance mapping, executive communication, and TLA+ property specification.

---

## How to Use This Catalog

1. **Find the skill** that matches your workflow phase (see pipeline below)
2. **Install** the full suite or individual skills using [install.sh](install.sh)
3. **Skills auto-activate** when Claude detects relevant keywords in your conversation
4. **Slash commands** provide direct invocation: `/soc-security:threat-model`, `/soc-security:verify`, `/soc-security:comply`, `/soc-security:brief`, `/soc-security:pipeline`, `/soc-security:microarch`, `/soc-security:physical-sca`, `/soc-security:kernel-sec`, `/soc-security:emerging-hw`, `/soc-security:formalize`, `/soc-security:advanced-pipeline`
5. **Progressive disclosure**: Skills provide core guidance first, then reference deep-dive materials on demand
6. **Confidence-first**: All outputs are tagged with GROUNDED/INFERRED/SPECULATIVE/ABSENT confidence tiers

---

## Pipeline Architecture

Skills connect through typed entity contracts in three pipeline tracks:

```
ORIGINAL PIPELINE (P0 → P1 → P2 → P3):
threat-model-skill ──> verification-scaffold-skill ──> compliance-pipeline-skill ──> executive-brief-skill
        │                         │                              │                            │
SecurityRequirementSet    VerificationChecklist          ComplianceState             Executive Artifacts
  + ThreatFindings        (Tier 1/2/3 items)       (requirements + gaps)         (briefs, risk entries)

ADVANCED PIPELINE (A0-A3, parallel):
ComponentDescription ─┬──> microarch-attack-skill    → MicroarchAttackFindings
  or ThreatFindings   ├──> physical-sca-skill        → PhysicalSCAFindings
  (from P0)           ├──> kernel-security-skill     → KernelSecFindings
                      └──> emerging-hw-security-skill → EmergingHWFindings

FORMAL METHODS (F0, hub — accepts any findings):
Any findings ─────────> tlaplus-security-skill → FormalSecSpec

CROSS-FEED: A0-A3 findings can feed into P1/P2/P3 for verification, compliance, and executive briefing.
```

Each skill can operate standalone or as part of its pipeline. The advanced pipeline skills run in parallel on the same component description.

---

## Skills

### Threat Modeling

| Skill | Description | Status |
|-------|-------------|--------|
| [threat-model-skill](threat-model-skill/) | Structured threat identification for SoC security components using STRIDE/attack-tree methodology with spec-grounded requirements extraction | **Available** |

**Use when**: Starting security analysis of a new SoC component, extracting security requirements from specs, identifying threats against hardware security boundaries.

**Trigger keywords**: threat model, security requirements, STRIDE analysis, attack surface, threat identification

**Outputs**: `SecurityRequirementSet` + `ThreatFindings` -- requirements with spec traceability, threats with STRIDE categorization, confidence tiers

**Slash command**: `/soc-security:threat-model`

---

### Verification Scaffolding

| Skill | Description | Status |
|-------|-------------|--------|
| [verification-scaffold-skill](verification-scaffold-skill/) | Generates tiered verification checklists and SVA assertion templates from threat findings, with explicit coverage boundary annotations | **Available** |

**Use when**: Building verification plans from threat models, generating SVA assertion candidates, creating security review checklists.

**Trigger keywords**: verification checklist, SVA assertions, security verification, test plan, verification scaffold

**Outputs**: `VerificationChecklist` -- Tier 1 (mechanical checks), Tier 2 (protocol checks), Tier 3 (information flow specs)

**Verification tiers**:
- Tier 1 (Mechanical) -- Access control, FSM state coverage, register lock-down. SVA assertions with high confidence.
- Tier 2 (Protocol) -- DICE handshake, CXL.cache coherence, SPDM session state. SVA assertions needing review.
- Tier 3 (Information Flow) -- Side-channel, data-dependent timing, covert channels. Natural language specification only.

**Slash command**: `/soc-security:verify`

---

### Compliance Pipeline

| Skill | Description | Status |
|-------|-------------|--------|
| [compliance-pipeline-skill](compliance-pipeline-skill/) | Maps security requirements to compliance evidence with gap analysis, supporting FIPS 140-3, ISO 21434, and industry-specific standards | **Available** |

**Use when**: Mapping verification results to compliance requirements, identifying compliance gaps, building evidence packages for certification.

**Trigger keywords**: compliance mapping, gap analysis, FIPS 140-3, ISO 21434, compliance evidence, certification

**Outputs**: `ComplianceState` -- requirement-to-evidence mapping, coverage status, gap descriptions, traceability matrix

**3-stage pipeline**:
1. Requirements Extraction -- Structured extraction from spec text with source traceability
2. Evidence Mapping -- Map requirements to verification results, test reports, design docs
3. Gap Analysis -- Identify and categorize gaps by severity and remediation effort

**Slash command**: `/soc-security:comply`

---

### Executive Brief

| Skill | Description | Status |
|-------|-------------|--------|
| [executive-brief-skill](executive-brief-skill/) | 4-layer abstraction translator that converts technical findings into audience-calibrated executive communications (board, CISO, program level) | **Available** |

**Use when**: Communicating security findings to leadership, preparing risk register entries, creating status updates for program reviews.

**Trigger keywords**: executive brief, security summary, risk register, board update, CISO brief, status update

**Outputs**: `BriefSections` -- 4-layer translated findings (technical -> impact -> business risk -> action item)

**4-layer abstraction**:
- Layer 0: Raw technical finding
- Layer 1: Security impact statement
- Layer 2: Business risk statement
- Layer 3: Executive action item (with cost/timeline)

**Audience levels**: board, CISO, program

**Slash command**: `/soc-security:brief`

---

### Microarchitectural Attack Analysis

| Skill | Description | Status |
|-------|-------------|--------|
| [microarch-attack-skill](microarch-attack-skill/) | Systematic microarchitectural attack analysis covering transient execution (Spectre, Meltdown, MDS), cache side-channels (Prime+Probe, Flush+Reload), and branch predictor attacks with mitigation assessment | **Available** |

**Use when**: Analyzing speculative execution attack surfaces, evaluating cache side-channel resistance, assessing branch predictor security, reviewing microarchitectural mitigations.

**Trigger keywords**: Spectre, Meltdown, MDS, cache side-channel, speculative execution, transient execution, branch predictor, Prime+Probe, Flush+Reload

**Outputs**: `MicroarchAttackFindings` -- microarchitectural structure mapping, attack surface classification, attack pattern matches with paper citations, mitigation assessment with residual risk

**Slash command**: `/soc-security:microarch`

---

### Physical Side-Channel Assessment

| Skill | Description | Status |
|-------|-------------|--------|
| [physical-sca-skill](physical-sca-skill/) | Physical side-channel attack resistance assessment with JIL attack potential scoring, ISO 17825 leakage assessment, and countermeasure evaluation for cryptographic implementations | **Available** |

**Use when**: Assessing DPA/SPA resistance of crypto engines, evaluating fault injection countermeasures, scoring attack potential for certification, performing ISO 17825 leakage assessment.

**Trigger keywords**: DPA, SPA, CPA, fault injection, side-channel, JIL scoring, ISO 17825, TVLA, power analysis, EM analysis, glitching

**Outputs**: `PhysicalSCAFindings` -- leakage surface analysis, JIL attack potential scores, ISO 17825 status, countermeasure effectiveness table

**Slash command**: `/soc-security:physical-sca`

---

### Kernel Security Analysis

| Skill | Description | Status |
|-------|-------------|--------|
| [kernel-security-skill](kernel-security-skill/) | Kernel security configuration analysis and HW/SW security interface assessment covering memory protection, process isolation, privilege escalation paths, and kernel integrity | **Available** |

**Use when**: Reviewing kernel hardening configuration, analyzing isolation boundaries (IOMMU, seccomp-BPF, namespaces), identifying privilege escalation paths, assessing kernel attack surface reduction.

**Trigger keywords**: kernel security, KASLR, IOMMU, seccomp, privilege escalation, kernel hardening, SMAP, SMEP, MTE, container escape, io_uring

**Outputs**: `KernelSecFindings` -- kernel configuration analysis, isolation boundary map, attack surface enumeration, privilege escalation path analysis

**Slash command**: `/soc-security:kernel-sec`

---

### Emerging Hardware Security

| Skill | Description | Status |
|-------|-------------|--------|
| [emerging-hw-security-skill](emerging-hw-security-skill/) | Security assessment for emerging hardware paradigms — post-quantum crypto (FIPS 203/204/205), chiplet/UCIe, heterogeneous compute (CPU+GPU+NPU), and AI accelerator security | **Available** |

**Use when**: Assessing PQC hardware readiness, reviewing chiplet/UCIe security architecture, analyzing heterogeneous compute trust boundaries, evaluating AI accelerator security.

**Trigger keywords**: PQC, post-quantum, FIPS 203, ML-KEM, chiplet, UCIe, heterogeneous compute, NPU, AI accelerator, model confidentiality

**Outputs**: `EmergingHWFindings` -- paradigm-specific threat assessment, architecture security review, maturity assessment, migration risk analysis

**Slash command**: `/soc-security:emerging-hw`

---

### TLA+ Formal Security Specification

| Skill | Description | Status |
|-------|-------------|--------|
| [tlaplus-security-skill](tlaplus-security-skill/) | TLA+ formal specification of security properties — translates findings from any upstream skill into precise mathematical specifications with model checking guidance | **Available** |

**Use when**: Formalizing security properties from threat models or attack analysis, building TLA+ specifications for protocol correctness, verifying safety/liveness properties, specifying information flow properties.

**Trigger keywords**: TLA+, formal verification, safety property, liveness, model checking, TLC, security invariant, noninterference, formal specification

**Outputs**: `FormalSecSpec` -- TLA+ module with state variables, type invariants, initial state, next-state relation, security property temporal formulas, TLC configuration guidance

**Slash command**: `/soc-security:formalize`

---

## Slash Commands

| Command | Pipeline | Description |
|---------|----------|-------------|
| [`/soc-security:threat-model`](commands/threat-model.md) | Original | Start structured threat modeling for a SoC component |
| [`/soc-security:verify`](commands/verify.md) | Original | Generate tiered verification checklists and SVA templates |
| [`/soc-security:comply`](commands/comply.md) | Original | Run compliance mapping and gap analysis |
| [`/soc-security:brief`](commands/brief.md) | Original | Generate audience-adapted executive briefs |
| [`/soc-security:pipeline`](commands/pipeline.md) | Original | Run all 4 original pipeline stages |
| [`/soc-security:microarch`](commands/microarch.md) | Advanced | Run microarchitectural attack analysis |
| [`/soc-security:physical-sca`](commands/physical-sca.md) | Advanced | Run physical side-channel assessment |
| [`/soc-security:kernel-sec`](commands/kernel-sec.md) | Advanced | Run kernel security analysis |
| [`/soc-security:emerging-hw`](commands/emerging-hw.md) | Advanced | Run emerging HW security assessment |
| [`/soc-security:formalize`](commands/formalize.md) | Formal | Formalize security properties in TLA+ |
| [`/soc-security:advanced-pipeline`](commands/advanced-pipeline.md) | Advanced+Formal | Run A0-A3 + F0 in sequence with review checkpoints |

---

## Shared References

| Resource | Description | Referenced By |
|----------|-------------|---------------|
| [domain-ontology/](shared-references/soc-security/domain-ontology/) | 14 security properties, 9 technology domains, SoC family definitions, formal methods | All skills |
| [entity-schema.md](shared-references/soc-security/entity-schema.md) | 10 typed entity definitions and DocumentEnvelope format | All skills |
| [standards-registry/](shared-references/soc-security/standards-registry/) | Spec requirement extracts (DICE, TDISP, CXL, CHERI, SPDM, ISO 17825, FIPS 203-205, UCIe 1.1) | threat-model, compliance-pipeline, physical-sca, emerging-hw |
| [threat-catalog/](shared-references/soc-security/threat-catalog/) | Attack surface taxonomy — physical, firmware, interface, architectural, microarchitectural, kernel | threat-model, verification-scaffold, microarch-attack, kernel-security |
| [verification-patterns/](shared-references/soc-security/verification-patterns/) | SVA templates, security review checklists, microarch review, SCA review | verification-scaffold, microarch-attack, physical-sca |
| [cross-cutting/](shared-references/soc-security/cross-cutting/) | SoC family profiles, RoT chain, executive communication guide, research currency | All skills |
| [glossary.md](shared-references/soc-security/glossary.md) | Single source of truth for SoC security terminology (~140 terms) | All skills |

---

## Skill Sizing

### Original Pipeline

| Skill | Core Lines | Reference Lines | Total Lines | File Count |
|-------|------------|-----------------|-------------|------------|
| threat-model-skill | 1,199 | 1,053 | 2,252 | 3 |
| verification-scaffold-skill | 1,067 | 1,073 | 2,140 | 3 |
| compliance-pipeline-skill | 963 | 555 | 1,518 | 3 |
| executive-brief-skill | 827 | 667 | 1,494 | 3 |

### Advanced Pipeline + Formal Methods

| Skill | Core Lines | Reference Lines | Total Lines | File Count |
|-------|------------|-----------------|-------------|------------|
| microarch-attack-skill | ~500 | ~650 | ~1,150 | 3 |
| physical-sca-skill | ~500 | ~600 | ~1,100 | 3 |
| kernel-security-skill | ~500 | ~600 | ~1,100 | 3 |
| emerging-hw-security-skill | ~500 | ~600 | ~1,100 | 3 |
| tlaplus-security-skill | ~500 | ~600 | ~1,100 | 3 |

### Totals

| Component | Total Lines | File Count |
|-----------|-------------|------------|
| Original pipeline skills | 7,404 | 12 |
| Advanced + formal skills | ~5,550 | 15 |
| Shared references | ~7,500 | 35 |
| **Suite total** | **~20,450** | **62** |

Progressive disclosure ratio: ~35% core / ~65% references (target: ~35% / ~65%).

---

## Role-Based Presets

Install only the skills relevant to your role:

| Role | Command | Skills |
|------|---------|--------|
| Full Suite | `./install.sh --role full-suite` | All 9 skills |
| SoC Pipeline | `./install.sh --role soc-pipeline` | Original 4 skills (P0-P3) |
| Advanced Analyst | `./install.sh --role advanced-analyst` | Advanced 4 skills (A0-A3) |
| Microarch Specialist | `./install.sh --role microarch-specialist` | microarch-attack-skill |
| Physical Security | `./install.sh --role physical-security` | physical-sca-skill |
| Kernel Analyst | `./install.sh --role kernel-analyst` | kernel-security-skill |
| Emerging HW | `./install.sh --role emerging-hw` | emerging-hw-security-skill |
| Formal Methods | `./install.sh --role formal-methods` | tlaplus-security-skill |
| Threat Analyst | `./install.sh --role threat-analyst` | threat-model-skill, verification-scaffold-skill |
| Compliance Engineer | `./install.sh --role compliance-engineer` | compliance-pipeline-skill |
| Executive Communicator | `./install.sh --role executive-communicator` | executive-brief-skill |

Shared references are always installed regardless of role selection.

---

## Confidence System

All skill outputs use a 4-tier confidence system:

| Tier | Meaning | Downstream Behavior |
|------|---------|---------------------|
| **GROUNDED** | Directly supported by cited spec section or user-provided evidence | Passes to all downstream skills automatically |
| **INFERRED** | Logically derived from requirements but not explicitly stated | Passes with caveat annotation |
| **SPECULATIVE** | Plausible but not grounded in provided context | Blocks pending human acknowledgment |
| **ABSENT** | Known attack category where no analysis was performed | Flagged as coverage gap |

---

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 0.2.0 | 2026-02-13 | Advanced pipeline: 5 new skills (microarch, physical SCA, kernel, emerging HW, TLA+), 9 new shared references, 6 new slash commands, 8 new role presets |
| 0.1.0 | 2026-02-13 | Initial release: 4 skills, 26 shared references, 5 slash commands, install script |
