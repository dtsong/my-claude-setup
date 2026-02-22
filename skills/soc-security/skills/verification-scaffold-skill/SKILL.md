---
name: verification-scaffold-skill
description: Use this skill when generating verification artifacts from threat findings — SVA assertion templates, security review checklists, or tiered verification plans. Triggers on "generate assertions for these threats", "verification checklist", "SVA template", "map threats to verification". Expects upstream ThreatFinding input. Do NOT use for threat identification (use threat-model-skill) or compliance gap analysis (use compliance-pipeline-skill).
model:
  preferred: sonnet
  acceptable: [sonnet, opus]
  minimum: sonnet
  allow_downgrade: true
  reasoning_demand: medium
---

# Verification Scaffold Skill for Claude

## When to Use This Skill

**Activate when:** generating verification checklists from threat findings, creating SVA assertion templates, building security review checklists, planning verification coverage, mapping threats to verification tiers, producing artifacts for security review boards, creating Tier 1 assertion templates.

**Do not use for:** production-ready SVA (templates only, not production IP), formal verification setup, RTL code review (v2 roadmap), threat identification (threat-model-skill), compliance gap analysis (compliance-pipeline-skill), executive communication (executive-brief-skill), functional verification beyond security.

## Scope Constraints

Read files ONLY within project working directory. No home directory dotfiles, external services, shell commands, or file modifications. Output SVA templates as text only in the VerificationChecklist format.

## Input Sanitization

Reject path traversal (`../`), shell metacharacters, paths outside project directory. RTL signal names: alphanumeric, underscores, brackets only.

## Core Principles

### 1. Scaffolds, Not Solutions

Every artifact is a starting point. SVA templates require signal-level customization. NL properties require formalization. Spec references require contextual interpretation. The scaffold saves time; it does not replace expertise.

### 2. Honest Annotation Over False Precision

Every assertion includes two mandatory annotations:
- `// INTENT:` — What this assertion checks
- `// DOES NOT CHECK:` — What it explicitly does NOT verify

These exist because a template that appears comprehensive but silently omits key scenarios is more dangerous than one that declares its limitations. False coverage is worse than known gaps.

### 3. Tier Discipline

| Tier | Type | Confidence | When to Use | What to Produce |
|------|------|-----------|-------------|-----------------|
| **Tier 1** | Mechanical / Structural | HIGH | Access control, FSM transitions, register locks, address range checks | SVA assertion templates |
| **Tier 2** | Protocol / Behavioral | MEDIUM | DICE key derivation, CXL protocol sequences, TDISP handshake, SPDM flows | Natural-language property descriptions |
| **Tier 3** | Specification-Only | REFERENCE | Information flow, side-channel resistance, architectural isolation | NL spec descriptions, NO SVA |

Attempting SVA for Tier 3 properties produces false confidence because these require specialized formal methods, physical measurement, or architectural review. The skill refuses to generate SVA for Tier 3.

### 4. Confidence Propagation

Verification items inherit confidence from their upstream ThreatFinding. A SPECULATIVE threat cannot produce a GROUNDED verification item.

```
ThreatFinding.confidenceTier → VerificationItem.upstreamConfidence
VerificationItem.verificationConfidence = min(upstreamConfidence, tierConfidence)
```

Where tierConfidence is: Tier 1 = HIGH, Tier 2 = MEDIUM, Tier 3 = REFERENCE.

A GROUNDED threat verified by a Tier 2 property gets MEDIUM overall confidence. A SPECULATIVE threat verified by a Tier 1 assertion gets SPECULATIVE overall confidence (upstream caps it).

### 5. Template vs. Ready

- `[TEMPLATE]` — Placeholder signal names, requires design-specific customization
- `[READY]` — Actual RTL signal names provided by engineer, ready for syntax review

Most will be `[TEMPLATE]` because the skill typically lacks RTL access. `[READY]` only when engineer provides signal names, module hierarchy, and clock/reset info.

### 6. Never "Correct" — Always "Candidate"

Every assertion is framed as: "Candidate assertion for review. Verify against your RTL before use." This framing is not optional — it appears in caveat blocks, annotations, and handoff notes.

---

## References

| Reference | Location | Role |
|-----------|----------|------|
| Entity Schema | `shared-references/soc-security/entity-schema.md` | VerificationItem, DocumentEnvelope, typed entity definitions |
| Verification Patterns | `shared-references/soc-security/verification-patterns/` | SVA templates and checklist templates |
| Threat Catalog | `shared-references/soc-security/threat-catalog/` | Threat context for verification mapping |
| Domain Ontology | `shared-references/soc-security/domain-ontology/` | Security property definitions |
| Glossary | `shared-references/soc-security/glossary.md` | Terminology consistency |

**Load skill-specific references as needed:**

| Reference | Location | Role |
|-----------|----------|------|
| Verification Overview | `references/verification-methodology-overview.md` | 3-tier model rationale, tier boundary rules |
| Tier 1 Methodology | `references/verification-methodology-tier1.md` | Tier 1 criteria, property categories, worked example |
| Tier 2–3 Methodology | `references/verification-methodology-tier2-tier3.md` | Tier 2/3 criteria, property categories, worked examples |
| Confidence Propagation | `references/verification-methodology-confidence.md` | Tier promotion/demotion, confidence chain rules |
| SVA Pattern Library | `references/sva-pattern-library.md` | 7 standard SVA patterns + domain-specific Tier 2 patterns |
| SVA Syntax Guide | `references/sva-authoring-guide-syntax.md` | SVA template syntax, signal naming conventions |
| SVA Annotations Guide | `references/sva-authoring-guide-annotations.md` | Annotation requirements, coverage boundary format |
| SVA Patterns Guide | `references/sva-authoring-guide-patterns.md` | Worked examples, domain-specific patterns, anti-patterns |

---

## Input Requirements

**Required:** (1) ThreatFindings from threat-model-skill — id, severity, confidenceTier, attackSurface, verificationMethod per finding, plus DocumentEnvelope with attack surface checklist and confidence summary. (2) Verification Scope — which threats (all/specific IDs/filtered), target tier(s), output format (checklist/templates/both).

**Optional (improve quality):** (3) RTL Signal Information — enables `[READY]` assertions: module hierarchy, clock/reset, security-critical signals, address ranges. (4) Existing Verification Assets — prevents duplication. (5) Design Constraints — clock domains, reset architecture, tool constraints.

### Input Validation

```
[x/!/?] ThreatFindings envelope present with valid confidence summary
[x/!/?] At least one ThreatFinding entity with verificationMethod field
[x/!/?] Attack surface checklist present (for coverage mapping)
[x/!/?] RTL signal information available (improves template specificity)
[x/!/?] Existing verification assets listed (prevents duplication)

Legend: [x] = present, [!] = missing (required), [?] = missing (optional)
```

If ThreatFindings missing: request threat-model-skill first or provide threat descriptions manually. Without ThreatFindings, the skill cannot map threats to tiers, propagate confidence, or generate targeted templates.

---

## Progress Tracking

Copy this checklist and update as you complete each phase:
```
Progress:
- [ ] Phase 1: Input Analysis & Tier Assignment
- [ ] Phase 2: Tier 1 — SVA Assertion Template Generation
- [ ] Phase 3: Tier 2 — Natural-Language Property Description
- [ ] Phase 4: Tier 3 — Specification-Only Descriptions
- [ ] Phase 5: Output Assembly & Coverage Mapping
```

> **Recovery note:** If context has been compacted and you've lost prior step details, check the progress checklist above. Resume from the last unchecked item. Re-read the relevant reference file for that phase.

## The Verification Scaffold Process

Phase 1: Tier Assignment -> Phase 2: Tier 1 SVA -> Phase 3: Tier 2 NL -> Phase 4: Tier 3 Spec -> Phase 5: Output Assembly

---

### Phase 1: Input Analysis & Tier Assignment

Validate ThreatFindings. Per finding: note confidenceTier (propagates), verificationMethod (informs tier), severity (priority).

#### Tier Assignment Tables

**Tier 1 — Mechanical / Structural (SVA Templates)**

| Property Type | SVA Pattern | Example |
|--------------|-------------|---------|
| Access control | Signal-level gate | "Only master X writes register Y in state Z" |
| FSM transition | State transition | "No LOCKED->ACTIVE without authentication" |
| Register lock | Write protection | "Config register not writable after lock" |
| Address range | Bounds check | "DMA address within [base, base+size)" |
| One-hot encoding | Encoding check | "FSM state maintains one-hot" |
| Mutual exclusion | Concurrent access | "Key storage: no simultaneous read+write" |
| Timeout | Bounded liveness | "Handshake completes within N cycles" |

**Tier 2 — Protocol / Behavioral (NL Properties)**

| Property Type | Example |
|--------------|---------|
| DICE key derivation | "Layer N key from Layer N-1 measurement before Layer N+1 operation" |
| CXL protocol | "Snoop response within timeout respecting coherence state" |
| TDISP handshake | "Full DISCOVER->LOCK->RUN before data transfer" |
| SPDM authentication | "Mutual verification before measurement report trusted" |
| Boot sequence | "Each stage measures next before transferring control" |

**Tier 3 — Specification-Only (No SVA)**

| Property Type | Why No SVA | Output |
|--------------|-----------|--------|
| Information flow | Requires info flow analysis tools | Spec + tool recommendation |
| Side-channel | Requires physical measurement | Spec + test methodology |
| Architectural isolation | System-level, beyond module scope | Spec + review checklist |
| Cryptographic strength | Mathematical, not RTL checkable | Spec + certification ref |
| Supply chain integrity | Process verification required | Spec + process checklist |

**Assignment Rules:**
1. `verificationMethod` = "SVA" -> Tier 1
2. "simulation" + behavioral -> Tier 2
3. "review"/"formal-analysis" -> Tier 2 or 3 by property type
4. "test" + physical measurement -> Tier 3
5. Information flow or side-channel -> always Tier 3 because these cannot be expressed as signal-level assertions
6. When uncertain, assign higher tier — under-promising is safer

#### Tier Assignment Plan

```
Verification Scaffold Plan
===========================
Source: [TM-ID] — [N] ThreatFindings consumed
Tier 1 (SVA): [N] — [IDs]  |  Tier 2 (NL): [N] — [IDs]
Tier 3 (Spec): [N] — [IDs]  |  Not Verifiable: [N] — [IDs + reason]
RTL Signals: [AVAILABLE/NOT] — Assertions: [READY/TEMPLATE]
Priority: CRITICAL -> HIGH -> MEDIUM -> LOW
```

Wait for engineer confirmation before proceeding.

---

### Phase 2: Tier 1 — SVA Assertion Template Generation

Refer to `references/sva-authoring-guide-syntax.md` and `references/sva-authoring-guide-annotations.md` for authoring rules.

#### Step 2.1: Pattern Selection

| Security Property | Pattern Category | Key Construct |
|-------------------|-----------------|---------------|
| Access control | Implication | `grant \|-> permitted_master` |
| FSM transition | Sequence + property | `state == S1 ##1 state == S2 \|-> guard` |
| Register lock | Stability | `$rose(lock) \|-> $stable(reg)[*]` |
| Address range | Range check | `valid \|-> (addr >= base) && (addr < base+size)` |
| One-hot | Invariant | `$onehot(state_reg)` |
| Mutual exclusion | Never concurrent | `not (op_a && op_b)` |
| Timeout | Bounded liveness | `req \|-> ##[1:MAX] ack` |
| Reset | After reset | `$fell(rst_n) \|=> ##1 (state == IDLE)` |

#### Step 2.2: Assertion Template Structure

```systemverilog
// =============================================================================
// Verification Item: [VI-TM-YYYY-NNN-MMM]
// Source Threat: [TF-TM-YYYY-NNN-XXX] — [threat title]
// Tier: 1 | Status: [TEMPLATE/READY] | Confidence: [upstream] -> [computed]
// =============================================================================
// INTENT: [specific description]
// DOES NOT CHECK: [specific omissions]
// CANDIDATE FOR REVIEW: Verify against your RTL before use.

module sva_[name] (input logic <clk>, <rst_n>, <signals...>);
  property p_[name];
    @(posedge <clk>) disable iff (!<rst_n>)
    <antecedent> |-> <consequent>;
  endproperty
  a_[name]: assert property (p_[name])
    else $error("[VI-ID] FAIL: [message]");
  c_[name]_trigger: cover property (@(posedge <clk>) <antecedent>);
endmodule
```

#### Step 2.3: Mandatory Annotations

Every assertion MUST include `// INTENT:` (what is checked and why) and `// DOES NOT CHECK:` (specific omissions). See pattern library for examples.

#### Step 2.4: SVA Pattern Library

-> Load `references/sva-pattern-library.md` for the 7 standard SVA patterns (access control gate, FSM transition guard, register lock, address range, one-hot, mutual exclusion, handshake timeout).

---

### Phase 3: Tier 2 — Natural-Language Property Description

For each Tier 2 finding, produce:

```markdown
### [VI-TM-YYYY-NNN-MMM] — [Property Title]
**Source:** [TF-ID] | **Tier:** 2 | **Confidence:** [upstream] -> MEDIUM

**Property Statement:** [temporal NL: "Before X, Y must have completed" / "While S, P holds" / "If E, within N cycles R occurs"]
**Verification Approach:** [simulation / constrained random / protocol checker / formal / review]
**Checks:** [2-3 sentences]  **Does NOT Check:** [2-3 sentences]
**Test Scenarios:** 1. Normal operation 2. Attack scenario 3. Edge case
**Formalization Notes:** [SVA feasibility + what info needed]
```

-> Load `references/sva-pattern-library.md` for domain-specific Tier 2 patterns (DICE layer ordering, TDISP state machine, CXL IDE key rotation, SPDM authentication).

---

### Phase 4: Tier 3 — Specification-Only Descriptions

For each Tier 3 finding, produce:

```markdown
### [VI-TM-YYYY-NNN-MMM] — [Property Title]
**Source:** [TF-ID] | **Tier:** 3 | **Confidence:** REFERENCE
**NO SVA — RATIONALE:** [specific reason SVA cannot express this]
**Property:** [spec description with section reference]
**Methodology:** [specific method, tool, expertise needed]
**Spec Reference:** [standard, version, section, quoted requirement]
**Review Checklist:** [3-5 items]
```

**Tier 3 Categories:**

| Category | Why No SVA | Approach |
|----------|-----------|----------|
| Information flow | Data provenance across modules | Caisson, SecVerilog, GLIFT |
| Side-channel | Physical phenomena, not functional RTL | Power/EM analysis, timing |
| Architectural isolation | SoC-wide, beyond module scope | System-level formal or review |
| Cryptographic | Mathematical, not RTL checkable | FIPS 140-3, Common Criteria |

---

### Phase 5: Render & Coverage Mapping

#### DocumentEnvelope

```yaml
type: verification-checklist
id: "VC-[YYYY]-[NNN]"
title: "Verification Scaffold — [Component] [Domain(s)]"
created/updated: "[YYYY-MM-DD]"
soc-family: ["[family]"]
technology-domain: ["[domain]"]
standards: ["[standard]"]
related-documents: ["[TM-YYYY-NNN]"]
status: "draft"
confidence-summary: { grounded: N, inferred: N, speculative: N, absent: N }
caveats: |
  LLM-generated scaffold. All assertions CANDIDATES FOR REVIEW.
  [TEMPLATE] requires signal customization. [READY] requires correctness review.
  Tier 3: NO SVA. NOT VERIFIED: [list gaps]
```

#### Mandatory Elements

**Caveat block:** LLM-generated draft notice, critical limitations ([TEMPLATE] won't compile, [READY] not formally verified, Tier 2 needs formalization, Tier 3 no artifacts), per-tier counts, specific coverage gaps.

**Coverage mapping:** Threat-to-VI traceability table (Threat ID, Severity, Confidence, VI ID, Tier, Status), coverage-by-attack-surface summary, explicit verification gaps with rationale.

**Confidence summary:** Per-tier counts with upstream confidence distribution, percentage breakdown, propagation assessment narrative.

#### VerificationItem Entity Format

Per entity schema at `shared-references/soc-security/entity-schema.md`. See worked example for structure.

---

## Interaction Patterns

**Starting:** Announce the 5-phase process (tier assignment, SVA templates, NL properties, spec references, coverage mapping), then begin analyzing threat findings.

**Phase transitions:** Announce tier assignments confirmed, count of items generated, and what comes next.

**RTL signals provided mid-session:** Update affected assertions from [TEMPLATE] to [READY] with explicit signal substitution list. Note that [READY] still requires review because signal substitution does not guarantee correctness.

**Finding cannot be mapped:** Explain why, offer options (provide more context, accept as gap, assign to Tier 3 as minimum), recommend Tier 3 because at minimum the threat gets documented with a review checklist.

---

## Quality Standards

1. Every Tier 1 assertion has `// INTENT:` and `// DOES NOT CHECK:` — no exceptions
2. Every assertion marked `[TEMPLATE]` or `[READY]` — none unmarked
3. No SVA for Tier 3 — skill refuses
4. Confidence propagated correctly — no VI exceeds source threat confidence
5. Coverage mapping complete — every ThreatFinding in traceability table
6. Gaps documented with rationale
7. Caveat block tailored, not boilerplate
8. Assertions syntactically plausible SVA
9. Annotations specific per assertion, not copy-pasted
10. Tier 2 includes normal + attack test scenarios

**Good:** assertions specific to threat, DOES NOT CHECK lists specific omissions, Tier 2 uses temporal language, Tier 3 explains why no SVA and what instead.
**Bad:** missing annotations, SVA for Tier 3, all [READY] without RTL, missing coverage mapping, no gaps documented.

---

## Worked Example: TDISP Device Assignment

**Input:** TM-2026-001 — TDISP Device Assignment Module Threat Model (8 findings)

### Phase 1 Output

```
Tier Assignment:
  Tier 1 (SVA): 4 findings
    TF-003 (FSM desync, CRITICAL/GROUNDED) -> FSM transition guard
    TF-005 (BAR manipulation, CRITICAL/GROUNDED) -> Address range check
    TF-006 (Register lock bypass, HIGH/GROUNDED) -> Register lock
    TF-008 (Concurrent access, MEDIUM/INFERRED) -> Mutual exclusion

  Tier 2 (NL Property): 2 findings
    TF-001 (SPDM auth bypass, HIGH/GROUNDED) -> Authentication sequence
    TF-004 (IDE key exposure, HIGH/GROUNDED) -> Key exchange protocol

  Tier 3 (Spec Only): 2 findings
    TF-002 (Timing side-channel, MEDIUM/SPECULATIVE) -> Timing analysis
    TF-007 (Cross-device info flow, HIGH/INFERRED) -> Information flow analysis
```

### Phase 2 Output (one assertion shown)

```systemverilog
// =============================================================================
// VI-VC-2026-001-001
// Source: TF-TM-2026-001-003 — TDISP State Machine Desynchronization
// Tier: 1 (Mechanical/Structural) | Status: [TEMPLATE] | Confidence: GROUNDED -> HIGH
// =============================================================================
// INTENT: Checks that the TDISP assignment FSM cannot transition from
//         LOCKED to DATA_TRANSFER without authentication_complete being
//         asserted in the immediately preceding cycle. This enforces the
//         TDISP 1.0 Section 4.2.1 requirement that authentication must
//         complete before data transfer begins.
//
// DOES NOT CHECK:
//   - Whether authentication_complete was legitimately derived from
//     a successful SPDM exchange (only checks the signal, not the protocol)
//   - Glitch-based state corruption that bypasses the FSM transition logic
//   - Behavior during or immediately after reset
//   - Transitions to states other than DATA_TRANSFER
//   - The correctness of the LOCKED state itself

property p_tdisp_locked_to_transfer_guard;
  @(posedge <clk>) disable iff (!<rst_n>)
  (<tdisp_state> == LOCKED) ##1 (<tdisp_state> == DATA_TRANSFER) |->
    $past(<authentication_complete>);
endproperty

a_tdisp_locked_to_transfer: assert property (p_tdisp_locked_to_transfer_guard)
  else $error("[VI-001] LOCKED->DATA_TRANSFER without authentication");

c_tdisp_locked_to_transfer_trigger: cover property (
  @(posedge <clk>) (<tdisp_state> == LOCKED) ##1 (<tdisp_state> == DATA_TRANSFER)
);
```

### Phase 5 Output (coverage mapping)

| Threat | Severity | VI | Tier | Status |
|--------|----------|-----|------|--------|
| TF-003 | CRITICAL | VI-001 | 1 | TEMPLATE |
| TF-005 | CRITICAL | VI-002 | 1 | TEMPLATE |
| TF-001 | HIGH | VI-005 | 2 | NL Property |
| TF-002 | MEDIUM | VI-007 | 3 | Spec Only |

Verification gaps: 0 threats without any coverage. 2 threats at Tier 3 only (timing side-channel, information flow) — recommended for specialized tool-based analysis.

---

## Knowledge Base Integration

When generating scaffolds for a previously analyzed component: check for existing VerificationChecklist documents, reuse effective assertion patterns (customize signals), reference prior verification coverage, and focus new scaffold on threats not covered by existing verification.

When upstream ThreatFinding has `crossFamilyReuse` information: generate base template once, note family-specific deltas in annotations, create variant templates if differences are significant, document which signals change across families in placeholder descriptions.

**Downstream handoff:** compliance-pipeline-skill (verification items as compliance evidence), executive-brief-skill (coverage statistics for executive reporting), engineer's verification environment (assertion templates for testbench integration).
