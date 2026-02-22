---
name: threat-model-skill
description: Use this skill when performing structured threat modeling for SoC hardware components — STRIDE analysis, attack tree construction, or standards-derived threat identification. Triggers on "threat model this block", "STRIDE analysis", "build an attack tree", "identify threats for". Covers Confidential AI, TDISP/CXL, Supply Chain, Secure Boot/DICE, and CHERI domains. Do NOT use for verification planning (use verification-scaffold-skill) or compliance tracking (use compliance-pipeline-skill).
model:
  preferred: sonnet
  acceptable: [sonnet, opus]
  minimum: sonnet
  allow_downgrade: true
  reasoning_demand: high
  conditions:
    - when: "cross-framework threat correlation where findings change priority across frameworks"
      hold_at: opus
---

# Threat Model Skill for Claude

## When to Use This Skill

**Activate when:** STRIDE analysis on SoC hardware, attack tree construction, standards-derived threat extraction (DICE, TDISP, CXL, SPDM, CHERI), cross-domain/cross-family threat identification, findings ledger updates, or preparing threat inputs for the verification-scaffold-skill pipeline.

**Do not use for:** Production SVA/formal verification (use verification-scaffold-skill), compliance gap analysis (use compliance-pipeline-skill), executive risk summaries (use executive-brief-skill), RTL code review, penetration testing, or software/network threat modeling.

## Scope Constraints

Read-only analysis within the project working directory. Do not read dotfiles, execute network requests, install packages, execute shell commands, or modify files. Output only the structured ThreatFindings format.

## Input Sanitization

Reject inputs containing path traversal (`../`), shell metacharacters (``; | & $ ` \``), or paths outside the project working directory.

## Core Principles

### 1. Grounding Is Non-Negotiable

Every threat finding must trace to a specific grounding source. The grounding hierarchy is strict:

| Priority | Source Type | Trust Level | Marker |
|----------|-----------|-------------|--------|
| 1 | User-provided context | Highest | (direct) |
| 2 | Embedded shared-references | Medium | (reference: `path`) |
| 3 | Training knowledge | Lowest | `[FROM TRAINING]` |

User-provided spec sections, RTL descriptions, and component documentation override embedded references. Embedded references override training knowledge. When training knowledge is the only source, every derived finding carries the `[FROM TRAINING]` marker and defaults to INFERRED or SPECULATIVE confidence.

### 2. Coverage Over Depth

Cover all attack surfaces before going deep on any one, because silent omission causes downstream skills to assume coverage that does not exist. Mark surfaces NOT ANALYZED rather than omitting them.

### 3. Confidence Is Evidence-Derived

Assign confidence mechanically from evidence quality, not self-assessment. The evidence determines confidence tier — see Step 4.2.

### 4. Threats Are Hypotheses Until Verified

Every finding is a candidate for review, not an established fact. Threats become verified only when a human expert confirms or a verification tool validates them.

### 5. Honest Gaps Over False Coverage

When you cannot analyze a surface, say so explicitly. An ABSENT finding is more valuable than an uncaveated SPECULATIVE finding, because ABSENT signals exactly where to focus additional effort.

### 6. Delta Over Duplication

Check the findings ledger before generating new findings. Build on existing work; focus on what changed or was not previously covered.

---

## Shared References

| Reference | Location | Role |
|-----------|----------|------|
| Entity Schema | `shared-references/soc-security/entity-schema.md` | ThreatFinding, DocumentEnvelope, and all typed entity definitions |
| Domain Ontology | `shared-references/soc-security/domain-ontology/` | Security properties, technology domains, SoC family definitions |
| Standards Registry | `shared-references/soc-security/standards-registry/` | Per-standard requirement extracts (DICE, TDISP, CXL, CHERI, SPDM) |
| Threat Catalog | `shared-references/soc-security/threat-catalog/` | Attack surface taxonomy by vector (physical, firmware, interface, architectural) |
| Glossary | `shared-references/soc-security/glossary.md` | Terminology definitions |
| Cross-Cutting | `shared-references/soc-security/cross-cutting/` | SoC family profiles, Root of Trust chain model |
| STRIDE Methodology | `references/threat-modeling-methodology-stride.md` | STRIDE category adaptations for hardware, analysis patterns, worked example |
| Attack Tree Methodology | `references/threat-modeling-methodology-attack-trees.md` | Attack tree construction, notation, cut set analysis, worked example |
| Standards Extraction | `references/threat-modeling-methodology-standards.md` | Standards-derived threat extraction, per-standard focus areas |
| Cross-Framework Integration | `references/threat-modeling-methodology-integration.md` | Multi-framework synthesis, coverage gap analysis, threat statement templates |
| Cross-Framework Synthesis Checklist | `references/cross-framework-synthesis-checklist.md` | Mandatory checklist for Phase 3 cross-framework synthesis (required at Sonnet tier) |
| Output Templates — Envelope | `references/output-templates-envelope.md` | DocumentEnvelope template, envelope rules |
| Output Templates — Entities | `references/output-templates-entities.md` | ThreatFinding entity template, attack surface checklist |
| Output Templates — Examples | `references/output-templates-examples.md` | Worked examples, coverage boundary, confidence summary, caveat block templates |

---

## Input Requirements

**Required:** (1) Component Description — name, architecture, security boundary, interfaces; (2) Scope Declaration — technology domain(s), SoC family, spec sections with versions, target attack surfaces; (3) Prior Context (if available) — previous threat model IDs, known requirements, mitigations, RTL module names.

**Optional:** Framework preference, adversary model, severity threshold, target audience.

Validate inputs using checklist (`[x]`=present, `[!]`=missing required, `[?]`=missing optional). Request missing required inputs with "X because Y" rationale. Offer to proceed with partial input at lower confidence if the engineer prefers.

---

## Progress Tracking

Copy this checklist and update as you complete each phase:
```
Progress:
- [ ] Phase 1: Context Loading & Prior Art Check
- [ ] Phase 2: Attack Surface Enumeration
- [ ] Phase 3: Threat Identification (Framework-Driven)
- [ ] Phase 4: Threat Assessment & Confidence Assignment
- [ ] Phase 5: Output Assembly & Ledger Update
```

> **Recovery note:** If context has been compacted and you've lost prior step details, check the progress checklist above. Resume from the last unchecked item. Re-read the relevant reference file for that phase.

## The Threat Modeling Process

Every engagement follows five phases in sequence. Announce phase transitions explicitly so the engineer can track progress.

```
Phase 1: Context Loading & Prior Art Check
Phase 2: Attack Surface Enumeration
Phase 3: Threat Identification (Framework-Driven)
Phase 4: Threat Assessment & Confidence Assignment
Phase 5: Output Assembly & Ledger Update
```

---

### Phase 1: Context Loading & Prior Art Check

#### Step 1.1: Load Domain Context

Based on the specified technology domain(s), load relevant shared references:

| Technology Domain | References to Load |
|-------------------|-------------------|
| Confidential AI | `threat-catalog/architectural-attacks.md` (isolation, attestation), `standards-registry/dice/`, `standards-registry/spdm/` |
| TDISP/CXL | `threat-catalog/interface-attacks.md` (PCIe/CXL bypass, DMA), `standards-registry/tdisp/`, `standards-registry/cxl/` |
| Supply Chain | `threat-catalog/firmware-attacks.md` (supply chain injection), `standards-registry/spdm/` |
| Secure Boot/DICE | `threat-catalog/firmware-attacks.md` (boot chain, rollback), `standards-registry/dice/` |
| CHERI | `threat-catalog/architectural-attacks.md` (capability bypass, compartment escape), `standards-registry/cheri/` |

Always load: `domain-ontology/security-properties.md`, `domain-ontology/technology-domains.md`, `cross-cutting/root-of-trust-chain.md`, and SoC family profile if specified.

#### Step 1.2: Check Findings Ledger

Scan for entries matching the component, domain, or SoC family. If prior findings exist, report what was previously ANALYZED vs. NOT ANALYZED vs. ABSENT, assess recency (>6 months needs re-evaluation; >12 months baseline only), and reference prior IDs for lineage tracking. If none exist, note this establishes the baseline.

#### Step 1.3: Confirm Scope

Present the analysis scope (component, domains, family, boundary, specs, frameworks, planned attack surface coverage, prior findings referenced) for engineer confirmation. Wait for confirmation before proceeding.

---

### Phase 2: Attack Surface Enumeration

#### Step 2.1: Map Component Interfaces

Enumerate all interfaces: external (cross trust boundary) and internal, data flows with protection status, control flows, and stored assets (keys, secrets, credentials with access control mechanisms).

#### Step 2.2: Map to Standard Attack Surface Checklist

Assess applicability of each standard attack surface (side-channel, fault injection, debug interface, key management, boot chain, firmware update, bus access control) with rationale and relevant interfaces.

#### Step 2.3: Load Domain-Specific Attack Surfaces

Load domain-specific threat profiles from `shared-references/soc-security/threat-catalog/` based on the specified technology domain. Present the complete attack surface inventory to the engineer before proceeding.

---

### Phase 3: Threat Identification (Framework-Driven)

Apply one or more frameworks as selected by the engineer. If no preference, apply all three — they identify different threat classes.

#### Framework 1: STRIDE Analysis (Hardware-Adapted)

Apply STRIDE to each interface from Phase 2. For HW-adapted category definitions and domain-specific threat prompts, load `references/threat-modeling-methodology-stride.md`.

For each interface, systematically evaluate all six categories (Spoofing, Tampering, Repudiation, Information Disclosure, Denial of Service, Elevation of Privilege) using the hardware-adapted analysis patterns in the methodology reference. Produce preliminary ThreatFinding entities per the entity schema.

#### Framework 2: Attack Tree Construction

Use attack trees when the threat scenario involves multiple steps, the engineer wants feasibility analysis, or cross-domain threats require tracing chains across boundaries.

**Construction process:**
1. Define the root goal — specific attacker objective
2. Decompose into sub-goals using AND/OR nodes
3. Identify leaf actions with: attack vector, required access, estimated difficulty
4. Assess feasibility per leaf: Difficulty (Low/Medium/High), Access (Remote/Local-Logical/Local-Physical/Invasive), Detectability (Stealthy/Detectable/Obvious)
5. Identify minimal cut sets — smallest set of mitigations preventing the root goal

For detailed methodology, notation, and worked examples, load `references/threat-modeling-methodology-attack-trees.md`. Format output per the entity schema and output templates reference.

#### Framework 3: Standards-Derived Threat Extraction

Identify threats by negating security requirements from relevant specifications. Each SHALL/MUST implies a threat where the requirement is violated.

**Extraction process:**
1. Identify relevant spec sections based on component and domain
2. Extract explicit (SHALL/MUST) and implicit (SHOULD) requirements with security properties
3. Derive threats via requirement negation: "What happens if [requirement] is NOT met?"
4. Cross-reference with STRIDE and attack tree findings — confirm coverage, add unique findings, strengthen confidence

For per-standard extraction guides, load `references/threat-modeling-methodology-standards.md`.

#### Cross-Framework Synthesis

Load `references/cross-framework-synthesis-checklist.md` and work through each section before proceeding to Phase 4: de-duplicate (merge findings from multiple frameworks), gap check (surfaces covered by one framework but not others), coverage assessment (map to attack surface checklist), and cross-reference related threats.

---

### Phase 4: Threat Assessment & Confidence Assignment

#### Step 4.1: Apply the Retrieve-Reason-Render Pipeline

For every threat finding:

- **Retrieve:** Cite the exact spec section, catalog entry, or user-provided context. Mark `[FROM TRAINING]` if grounded in training knowledge only. Mark ABSENT if no grounding exists.
- **Reason:** Document the reasoning chain explicitly — the engineer must be able to follow the logic from evidence to threat. Note where reasoning relies on inference vs. direct evidence.
- **Render:** Transform to ThreatFinding entity format per `shared-references/soc-security/entity-schema.md`.

#### Step 4.2: Assign Confidence Tiers

| Tier | Criteria | Example |
|------|----------|---------|
| **GROUNDED** | Directly supported by a cited spec section or user-provided evidence | Spec says "SHALL authenticate before granting access" — unauthenticated access threat is GROUNDED |
| **INFERRED** | Logically derived from requirements but not explicitly stated; requires inference steps | Key management weakness enabling encryption bypass is INFERRED from encryption requirement |
| **SPECULATIVE** | Plausible but not grounded in provided context; based on training data | "GPU side-channel timing attack" without specific spec or evidence |
| **ABSENT** | Known attack category where no analysis was performed | Side-channel not analyzed because no power model provided |

When in doubt between two tiers, assign the lower tier. You do not override these rules — if you believe a finding deserves a different confidence, note reasoning in `assessmentNotes` but report the rules' output as official.

#### Step 4.3: Assess Threat Severity

| Severity | Criteria |
|----------|----------|
| **CRITICAL** | Breaks Root of Trust, enables persistent compromise, or defeats primary security property. Recovery requires silicon respin. |
| **HIGH** | Breaks a security boundary or enables unauthorized access to protected assets. May be mitigatable in FW/SW. |
| **MEDIUM** | Weakens a security mechanism under specific conditions. Mitigatable through configuration or operational controls. |
| **LOW** | Minor weakness with limited exploitability. Defense-in-depth recommendation. |
| **INFORMATIONAL** | Design observation, not a direct threat. May inform future analysis. |

Severity and confidence are independent — a CRITICAL/SPECULATIVE finding has a very different risk profile than CRITICAL/GROUNDED.

#### Step 4.4: Cross-Family Reuse Assessment

For each finding, assess cross-family applicability: which SoC families it applies to, family-specific deltas (bus wrapper, compliance regime, power domain), and reuse confidence (High/Medium/Low) with rationale.

Threats to core security blocks (crypto engines, boot ROM, DICE layers, fuse controllers) typically reuse across families. Threats to bus integration, power topology, or compliance regime typically do not.

---

### Phase 5: Render & Ledger Update

#### Step 5.1: Assemble the DocumentEnvelope

Package all findings in DocumentEnvelope format per `references/output-templates-envelope.md`. Include: type, id, title, dates, soc-family, technology-domain, standards, related-documents, status (always `draft`), confidence-summary counts, and caveats specific to this analysis.

#### Step 5.2: Produce Mandatory Elements

Every threat model output must include these four elements. For full templates, load `references/output-templates-examples.md`.

1. **Caveat Block** — Scope statement, what was/was not analyzed, grounding quality summary
2. **Attack Surface Checklist** — All 7 surfaces marked ANALYZED or NOT ANALYZED with finding counts
3. **Coverage Boundary** — Explicit lists of what was/was not covered, unexamined interfaces, unconsulted specs
4. **Confidence Summary** — Tier counts, percentages, and narrative assessment of confidence quality

#### Step 5.3: Format ThreatFinding Entities

Render each finding as a ThreatFinding entity per `shared-references/soc-security/entity-schema.md`. Required fields: id, title, strideCategory, attackVector, targetComponent, domain, socFamily, severity, verificationMethod, description (use "attacker with [access] can [action] the [target] by [method], resulting in [impact]" format), confidenceTier, verificationStatus (`llm-assessed`), sourceGrounding. Extended fields: groundingReference, reasoningChain, assessmentNotes, suggestedMitigation, attackSurface, crossFamilyReuse, relatedFindings, standardsReferences, framework. For full template with all fields, load `references/output-templates-entities.md`.

#### Step 5.4: Ledger Update & Downstream Handoff

Prepare ledger entries for CRITICAL/HIGH or novel findings; present to engineer before appending. Ensure every finding includes `verificationMethod` for verification-scaffold-skill and standards references for compliance-pipeline-skill traceability.

---

## Interaction Patterns

Start with a brief orientation listing the 5 phases, then begin input validation. Announce each phase transition with findings count and next action. Present findings inline with confidence at the point of discovery:

> **[TF-001] Unauthenticated DMA Access via TDISP Handshake Race**
> An attacker with local physical access can initiate DMA transfers before the TDISP handshake completes, bypassing device isolation.
> **Severity:** HIGH | **Confidence:** GROUNDED | **Source:** TDISP 1.0 Section 4.3.2
> **Attack Surface:** Bus access control | **STRIDE:** Elevation of Privilege

Accept engineer overrides (severity, confidence, scope, findings) without resistance; document all overrides with rationale. When analysis hits gaps, report what is missing and offer: (1) provide missing info, (2) mark ABSENT (recommended), (3) proceed with SPECULATIVE findings.

---

## Quality Standards

1. Every finding has a confidence tier (mechanical rules) and grounding source with markers
2. Attack surface checklist complete — every surface marked ANALYZED or NOT ANALYZED
3. Coverage boundary explicit; confidence summary counts match actual findings
4. Caveat block specific to this analysis, not generic boilerplate
5. Cross-family reuse assessed for every multi-family finding
6. Severity and confidence are independent assessments
7. Retrieve-Reason-Render pipeline visible — evidence to reasoning to output is traceable
8. ABSENT findings present for unanalyzed surfaces, because silent omission causes downstream skills to assume coverage
9. Good: specific threat statements (access+action+target+method+impact), realistic confidence distribution, spec section references, honest ABSENT findings. Bad: missing tiers/grounding, generic "may be vulnerable" statements, all-GROUNDED distributions, unmarked training knowledge.

---

## Worked Example: Condensed Threat Model Flow

**Component:** TDISP Device Assignment Module
**Technology Domain:** TDISP/CXL
**SoC Family:** Data Center
**Spec References:** TDISP 1.0, CXL 3.1 Section 11, SPDM 1.4

### Phase 1 Output (abbreviated)

- Loaded: `threat-catalog/interface-attacks.md`, `standards-registry/tdisp/`, `standards-registry/cxl/`
- Prior findings: FINDING-2025-017 (DMA isolation in TDISP, HIGH/GROUNDED) — will build on this
- Scope confirmed: STRIDE + standards-derived analysis, all 7 attack surfaces

### Phase 2 Output (abbreviated)

**Interfaces identified:** 6 external (PCIe TLP, CXL.io, SPDM, IDE key channel, host configuration, device BAR), 3 internal (register file, FSM state, key store)

**Attack surface applicability:**
| Surface | Applicable | Rationale |
|---------|-----------|-----------|
| Side-channel | Partial | Timing on SPDM handshake; power analysis out of scope without model |
| Fault injection | Yes | FSM state corruption during assignment |
| Debug interface | Yes | JTAG access to assignment state |
| Key management | Yes | IDE key derivation and storage |
| Boot chain | No | Not part of device assignment module |
| Firmware update | No | Module is hardware-only |
| Bus access control | Yes | Core function of the module |

### Phase 3 Output (one finding abbreviated)

**[TF-TM-2026-001-003] TDISP State Machine Desynchronization**
- Category: Tampering (STRIDE-T)
- Threat: An attacker with PCIe fabric access can inject out-of-order TDISP messages to desynchronize the assignment state machine, potentially leaving a device in an inconsistent security state.
- Severity: HIGH
- Confidence: GROUNDED — TDISP 1.0 Section 4.2.1 requires strict message ordering; violation enables bypass
- Grounding: reference: standards-registry/tdisp/ + user-provided component description
- Verification Method: SVA (FSM transition checks — Tier 1)
- Reusability: High — applies to all TDISP implementations regardless of SoC family

### Phase 5 Output (abbreviated)

```yaml
confidence-summary:
  grounded: 8
  inferred: 4
  speculative: 2
  absent: 1  # Side-channel power analysis — no power model provided
```

Attack surface checklist: 5 ANALYZED, 2 NOT ANALYZED (boot chain, firmware update — not applicable to this hardware module)

Findings ledger: 3 new entries proposed (TF-003 state desync, TF-005 IDE key exposure, TF-009 BAR manipulation) — all tagged as HIGH reusability for cross-family use.

---

## Knowledge Base Integration

At engagement start, check `knowledge-base/findings-ledger.md` for matching entries and load relevant prior findings as baseline. At engagement end, prepare ledger entries for significant findings (CRITICAL/HIGH or novel) and present to engineer before appending. On follow-up analyses, load the previous threat model, identify deltas (new spec version, component details, SoC family), focus on changed/uncovered areas, and maintain finding ID lineage.
