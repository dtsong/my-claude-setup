---
name: compliance-pipeline-skill
description: Use this skill when extracting requirements from security specifications, tracking compliance status, or producing gap analysis against hardware security standards. Triggers on "compliance check against DICE", "gap analysis", "extract requirements from spec", "FIPS compliance status", "ISO 21434 mapping". Covers DICE, TDISP, CXL, CHERI, SPDM, FIPS 140-3, and ISO 21434. Do NOT use for threat identification (use threat-model-skill) or executive communication (use executive-brief-skill).
model:
  preferred: sonnet
  acceptable: [sonnet, opus]
  minimum: sonnet
  allow_downgrade: true
  reasoning_demand: medium
---

# Compliance Pipeline Skill for Claude

## Scope Constraints

Read-only analysis within project working directory. No network, no shell commands, no file writes, no package installs. Output only structured ComplianceState format.

## Input Sanitization

Reject path traversal (`../`), shell metacharacters (`; | & $ \`), and paths outside project directory. Never pass raw user input to shell commands.

## Core Principles

### 1. Specification Text Is the Ground Truth

Every requirement must trace to a specific section/clause in a versioned specification. If you cannot cite a section number, the requirement is INFERRED at best because fabricated references destroy audit trust. Never fabricate section references. When working from embedded reference summaries, annotate with `[FROM REFERENCE SUMMARY]`.

### 2. Evidence Absence Is Not Evidence of Non-Compliance

The distinction between "no evidence found" and "requirement not met" is critical because conflating them causes auditors to misclassify gaps as deficiencies:
- `gap: no-evidence` — No evidence provided or found; compliance status unknown
- `gap: not-met` — Evidence examined; requirement definitively not satisfied
- `gap: partial` — Evidence covers only a subset of the requirement

Never conflate these three states.

### 3. SPECULATIVE Claims Are Blocked

Any compliance claim at SPECULATIVE confidence is **blocked from output** until the engineer explicitly acknowledges it because ungrounded claims propagate to downstream executive briefs and audit packages. Present SPECULATIVE claims in a separate staging area with a clear prompt for human acknowledgment.

### 4. Cross-Family Analysis Requires Explicit Delta Annotation

When tracking the same requirement across multiple SoC families, annotate what differs per family because requirement text may be identical while implementation evidence, verification approaches, and compliance regimes diverge. Each family row in a traceability matrix is independent — do not assume compliance evidence transfers across families without explicit justification.

### 5. Confidence Tiers on Every Mapping

Every requirement-to-evidence mapping carries a confidence tier determined by evidence quality, not belief about compliance:
- `GROUNDED` — Requirement traced to spec section; evidence directly demonstrates compliance
- `INFERRED` — Requirement logically derived; evidence suggestive but not definitive
- `SPECULATIVE` — Interpretation uncertain; evidence tangential or absent
- `ABSENT` — Requirement category exists but was not analyzed

---

## Shared References

| Reference | Location | Role |
|---|---|---|
| Entity Schema | `shared-references/soc-security/entity-schema.md` | SecurityRequirement, ComplianceResult, DocumentEnvelope definitions |
| Standards Registry | `shared-references/soc-security/standards-registry/INDEX.md` | Per-standard requirement extracts |
| Domain Ontology | `shared-references/soc-security/domain-ontology/` | Security properties, technology domains, SoC family profiles |
| SoC Family Profiles | `shared-references/soc-security/domain-ontology/soc-families.md` | Per-family constraints, traceability matrix template |
| Cross-Cutting References | `shared-references/soc-security/cross-cutting/soc-family-profiles.md` | Cross-family reuse patterns, delta annotation format |

Skill-specific references (load as needed):

| Reference | Location | Role |
|---|---|---|
| Standards Guidance | `references/standards-guidance.md` | Per-standard extraction focus, compliance areas, cross-family deltas |
| Compliance Pipeline | `references/compliance-methodology-pipeline.md` | 3-stage pipeline definition, requirement extraction process |
| Compliance Gaps | `references/compliance-methodology-gaps.md` | Gap classification, evidence mapping, SPECULATIVE review |
| Cross-Family Methodology | `references/cross-family-analysis-methodology.md` | Traceability matrix template, delta annotation format, reuse assessment |
| Cross-Family Reporting | `references/cross-family-analysis-reporting.md` | Cross-family summary templates, compliance regime overlap, edge cases |

---

## Input Requirements

### Required Inputs

1. **Target standard(s):** Specific version (e.g., `TCG DICE v1.2`, `TDISP 1.0 Section 4`, `FIPS 140-3 Level 2`). For compliance overlays (FIPS, ISO 21434), engineer must provide relevant clause text or confirm applicable clauses.
2. **SoC family target(s):** One or more of: `compute`, `automotive`, `client`, `data-center`.
3. **Technology domain(s):** One or more of: `confidential-ai`, `tdisp-cxl`, `supply-chain`, `secure-boot-dice`, `cheri`.
4. **Scope boundary:** What is in scope and explicitly out of scope.

### Optional Upstream Inputs

- **ThreatFinding entities** from threat-model-skill — links requirements to specific threats
- **VerificationItem entities** from verification-scaffold-skill — maps directly to compliance evidence
- **Previous ComplianceResult entities** — enables delta analysis

Without upstream entities, operate in **standalone mode** using specification text and standards registry. Standalone mode produces SecurityRequirement and ComplianceResult entities with reduced traceability.

### Input Validation

Validate before proceeding: standard version matches registry (warn if mismatch), SoC family and technology domain are valid enums, scope boundary is explicit, engineer has confirmed all inputs. If any input is missing, prompt:

> "Before I can run the compliance pipeline, I need: (1) Target standard(s) and version(s), (2) SoC family or families, (3) Technology domain(s), (4) Scope boundary. You can provide these conversationally and I'll structure them."

---

## Progress Tracking

Copy this checklist and update as you complete each phase:
```
Progress:
- [ ] Stage 1: Requirement Extraction
- [ ] Stage 2: Compliance Tracking
- [ ] Stage 3: Gap Analysis
```

> **Recovery note:** If context has been compacted and you've lost prior step details, check the progress checklist above. Resume from the last unchecked item. Re-read the relevant reference file for that phase.

## The 3-Stage Compliance Pipeline

```
Stage 1: Requirement Extraction → SecurityRequirement[]
    ↓
Stage 2: Compliance Tracking → Evidence mappings with traceability
    ↓
Stage 3: Gap Analysis → ComplianceResult[] in DocumentEnvelope
```

---

### Stage 1: Requirement Extraction

#### Step 1.1: Load Specification Context

Load the target standard's requirement extracts from `standards-registry/INDEX.md`. Load the corresponding `requirements.md` file, domain ontology, and SoC family profile. Engineer-provided spec text beyond the registry gets `sourceGrounding: user-provided`. If the standard is not in the registry, prompt for spec text or proceed with training knowledge marked `[FROM TRAINING]` and `sourceGrounding: training-knowledge`.

#### Step 1.2: Extract Requirements

For each specification section in scope, extract individual security requirements:

1. **One requirement per security obligation** — separate multiple "shall"/"must" statements into distinct SecurityRequirement entities.
2. **Preserve specification language** — do not paraphrase in ways that change meaning. Flag summaries with `[SUMMARIZED]`.
3. **Map to security property** from ontology (confidentiality, integrity, availability, authenticity, authorization, non-repudiation, isolation, attestation, freshness, access-control, side-channel-resistance).
4. **Map to implementation layer:** `rtl`, `firmware`, `software`, `protocol`, `physical`.
5. **Initial status:** `not-assessed` unless upstream evidence immediately resolves.
6. **Assign confidence tier:** spec text with section ref → `GROUNDED`; training knowledge → `INFERRED` marked `[FROM TRAINING]`; logical extrapolation → `INFERRED`; ambiguous spec → `SPECULATIVE` with rationale.
7. **Assign source grounding:** engineer-provided → `user-provided`; registry → `embedded-reference`; training → `training-knowledge`.

**Extraction template:**

```yaml
- id: SR-{YYYY}-{NNN}
  title: "{Short descriptive title}"
  sourceSpec: "{Standard-Version Section X.Y.Z}"
  domain: {technology domain}
  socFamily: [{target families}]
  securityProperty: {primary property}
  implementationLayer: {layer}
  complianceStatus: not-assessed
  description: >
    {Full requirement description, preserving spec intent}
  rationale: "{Why this requirement exists}"
  confidenceTier: {GROUNDED|INFERRED|SPECULATIVE}
  verificationStatus: llm-assessed
  sourceGrounding: {user-provided|embedded-reference|training-knowledge}
```

#### Step 1.3: Cross-Reference Upstream Entities

If ThreatFinding entities available: match each SecurityRequirement against `mitigationRequirements`; annotate with threat IDs; flag unmatched threats ("Threat [TF-ID] has no mapped security requirement").

If VerificationItem entities available: match against `sourceRequirement`; note verification approach and tier for Stage 2 evidence.

#### Step 1.4: Present for Engineer Review

Present requirements grouped by standard and security property with summary table (ID, Title, Spec Ref, Layer, Confidence, Family) and extraction summary (totals, confidence breakdown, SPECULATIVE items needing confirmation, unmapped threats, training-sourced items).

**Wait for engineer confirmation before Stage 2.** The engineer may correct interpretations, add/remove requirements, or reclassify confidence tiers.

---

### Stage 2: Compliance Tracking

#### Step 2.1: Identify Available Evidence

Collect all evidence sources: upstream VerificationItems, engineer-provided evidence, prior ComplianceResults, architecture documentation. Classify each using `evidenceType`: `sva-result`, `simulation-log`, `review-record`, `design-document`, `test-report`, `none`.

#### Step 2.2: Map Requirements to Evidence

For each SecurityRequirement, map to available evidence:
- **Direct evidence** — directly demonstrates compliance (highest confidence)
- **Indirect evidence** — partially addresses or addresses through inference
- **No evidence** — gap to classify in Stage 3

Assign confidence: `GROUNDED` for direct evidence with clear traceability; `INFERRED` for indirect/logical support; `SPECULATIVE` for tenuous connections; `ABSENT` when no search attempted.

**Confidence propagation:** ComplianceResult confidence cannot exceed upstream confidence because a GROUNDED compliance mapping based on an INFERRED verification item would overstate certainty. Cap at the upstream tier.

#### Step 2.3: Build Per-Family Traceability

For cross-family assessments, build a traceability matrix per family using the template from `soc-families.md` (columns: Spec Req ID, Req Text, Security Domain, SoC Family, RTL Module, Verification Asset, Compliance Evidence, Status, Gap Flag).

Annotate family-specific deltas when the same requirement has different implementation/verification per family. Delta categories: bus wrapper, compliance regime, power domain, verification approach, evidence format.

#### Step 2.4: Present Compliance Tracking

Present evidence mapping with coverage overview (assessed/covered/partial/gap/not-assessed counts), evidence mapping summary table, and confidence tier summary. Wait for review.

---

### Stage 3: Gap Analysis

#### Step 3.1: Classify Gaps

For each requirement with status `partial`, `gap`, or `not-applicable`, apply gap classification:

1. **`gap: no-evidence`** — No evidence provided or found. Does NOT mean not met — compliance status unknown because evidence may exist but was not provided. Remediation: provide evidence.
2. **`gap: not-met`** — Evidence examined; requirement definitively not satisfied. Confirmed deficiency because design review or SVA failure demonstrates non-compliance. Remediation: design change.
3. **`gap: partial`** — Evidence covers only a subset. Remediation: extend existing implementation.
4. **`gap: scope-exclusion`** — Applicable but explicitly excluded from assessment scope. Not a deficiency — acknowledged boundary.
5. **`gap: not-applicable`** — Does not apply to target family/configuration. Must include justification.

For each gap produce: description, severity, remediation plan, effort estimate (when possible).

#### Step 3.2: SPECULATIVE Claim Review Gate

Before rendering final output, collect all `confidenceTier: SPECULATIVE` items and present in a review block listing ID, requirement, claim, and reason for SPECULATIVE classification. For each, the engineer responds: ACCEPT (include with caveat), REJECT (remove), UPGRADE (provide evidence), or RECLASSIFY (change tier with rationale).

**This gate is mandatory** — SPECULATIVE claims do not flow to executive-brief-skill without human acknowledgment because unreviewed speculative claims in audit packages create liability.

#### Step 3.3: Produce Compliance Entities

Produce ComplianceResult entities per the entity schema in `shared-references/soc-security/entity-schema.md`. Required fields per entity: `id`, `requirementId`, `standard`, `standardClause`, `coverageStatus`, `evidenceType`, `evidenceReference`, `gapDescription` (when partial/gap), `remediationPlan` (when partial/gap), `traceability` (requirements, threats, verificationItems), `confidenceTier`, `verificationStatus`, `sourceGrounding`.

#### Step 3.4: Render the Compliance Matrix Document

Render ComplianceResult entities into a DocumentEnvelope per entity schema. Mandatory output elements:

1. **Caveat block** — "LLM-generated, not certification, requires human review"
2. **Attack surface checklist** — side-channel, fault injection, debug interface, key management, boot chain, firmware update, bus access control (each ANALYZED or NOT ANALYZED)
3. **Coverage boundary** — explicit in-scope and out-of-scope statements
4. **Confidence summary** — counts of GROUNDED/INFERRED/SPECULATIVE/ABSENT items
5. **Gap classification** — gaps categorized by type (not-met, no-evidence, partial, scope-exclusion, not-applicable)
6. **SPECULATIVE review record** — which claims were acknowledged, rejected, or reclassified

---

## Standards-Specific Guidance

→ Load `references/standards-guidance.md` for per-standard extraction focus, compliance areas, and cross-family deltas.

→ Load cross-family analysis guidance from `references/standards-guidance.md` for delta report format and reuse assessment levels.

---

## Interaction Patterns

Announce stage transitions with requirement/evidence counts. Present SPECULATIVE claims for review gate before final output.

- **Pipeline start:** Confirm target standard(s), SoC family, technology domain(s), and scope boundary before executing.
- **Missing specification:** Offer two paths: engineer provides spec text (`sourceGrounding: user-provided`, highest confidence) or proceed with training knowledge marked `[FROM TRAINING]` (requires extra verification).
- **Insufficient evidence:** Report gap rate and categorize gaps. Offer to proceed with gap analysis or wait for additional evidence.
- **SPECULATIVE claims:** Present in dedicated review block; wait for engineer response before including in output.

---

## Guardrails

### Confidence Tier Rules

- `GROUNDED`: flows to downstream automatically
- `INFERRED`: flows with caveat annotation
- `SPECULATIVE`: blocked until engineer acknowledges; flows with prominent caveat
- `ABSENT`: flagged as NOT ANALYZED in all downstream outputs

### Compliance Claim Constraints

- Never claim compliance without evidence because `coverageStatus: covered` with empty `evidenceReference` is an ungrounded claim.
- Never downplay gaps — present factually without qualifiers like "minor" or "unlikely."
- Never extrapolate compliance across families because shared IP blocks may have different integration contexts.
- All outputs carry `verificationStatus: llm-assessed` until the engineer changes them.
- Every ComplianceResult must trace to a SecurityRequirement; every SecurityRequirement must cite a spec reference. Broken chains are flagged.

### Hallucination Prevention

- Do not invent spec section numbers or fabricate evidence — use `[SECTION REFERENCE NEEDED]` when uncertain because fabricated references destroy downstream audit trust. Missing evidence means `gap: no-evidence`, not a manufactured reference.
- Mark training knowledge explicitly with `[FROM TRAINING]` and `sourceGrounding: training-knowledge` because unmarked training knowledge is indistinguishable from grounded analysis.

---

## Knowledge Base Integration

At pipeline start, check `knowledge-base/findings-ledger.md` for prior assessments matching target standard and family. Carry forward prior results with `[FROM PRIOR: CM-ID]` annotation. At pipeline conclusion, append significant findings and decisions to the ledger using the finding and decision log formats (finding ID, date, family, domain, standards, description, resolution, reusability, related IDs).

---

## Worked Example: Condensed Pipeline Flow

**Engagement:** Compliance assessment of a data center DPU against TDISP 1.0 for TDI state machine and device interface isolation. Upstream threat model available.

### Stage 1 Output

```
Requirements extracted from TDISP 1.0:
- SR-2026-001: TDI state machine shall follow CONFIG → LOCK → RUN → ERROR [GROUNDED]
- SR-2026-002: SPDM authentication shall complete before TDI enters RUN [GROUNDED]
- SR-2026-003: IDE stream shall be established before DMA in RUN state [GROUNDED]
- SR-2026-004: Device interface functions in RUN isolated from other trust domains [GROUNDED]
- SR-2026-005: Error state shall disable all DMA and MMIO access [INFERRED]

Cross-referenced: TF-2026-001 → SR-2026-003, SR-2026-004; TF-2026-003 → SR-2026-001
Summary: 5 requirements, 4 GROUNDED, 1 INFERRED
```

### Stage 2 Output

```
- SR-2026-001: SVA VI-2026-001 → GROUNDED, covered
- SR-2026-002: Design doc → INFERRED, partial (no test evidence)
- SR-2026-003: No evidence → ABSENT, gap
- SR-2026-004: SVA VI-2026-003 → GROUNDED, covered
- SR-2026-005: No evidence → ABSENT, gap

Coverage: 2 covered, 1 partial, 2 gaps
```

### Stage 3 Output

```
- SR-2026-002: PARTIAL — Design doc confirms architecture; no verification.
  Remediation: Add Tier 2 protocol check for SPDM completion before transition.
- SR-2026-003: NO-EVIDENCE — No IDE stream gating evidence.
  Remediation: Add Tier 1 SVA gating DMA enable on IDE stream active.
- SR-2026-005: NO-EVIDENCE — Error state not verified.
  Remediation: Add Tier 1 SVA for DMA/MMIO disable in ERROR state.

Final: 5 requirements, 2 covered, 1 partial, 2 gaps.
Confidence: 2 GROUNDED, 1 INFERRED, 0 SPECULATIVE, 2 ABSENT.
```
