# Output Templates — ThreatFinding Entity and Attack Surface Checklist

## Table of Contents

- [ThreatFinding Entity Template](#1-threatfinding-entity-template)
- [Required vs Optional Fields](#required-vs-optional-fields)
- [Attack Surface Checklist Template](#3-attack-surface-checklist-template)
- [Checklist Rules](#checklist-rules)
- [Example Completed Checklist](#example-completed-checklist)

---

## 1. ThreatFinding Entity Template

Each identified threat produces one ThreatFinding.

```yaml
ThreatFinding:
  # === Identity ===
  id: "TF-[TM-ID]-[NNN]"          # Example: TF-TM-2026-001-003
  title: "[Concise threat title — max 80 characters]"

  # === Threat Description ===
  threatStatement: |
    An attacker with [access level] can [action] the [target]
    by [method], resulting in [impact].
  description: |
    [2-4 sentences providing additional context beyond the threat statement.
    Include relevant technical details about the attack mechanism, prerequisites,
    and scope of impact. Reference specific interfaces or components by name.]

  # === Classification ===
  strideCategory: "[S|T|R|I|D|E]"  # null if not from STRIDE framework
  attackVector: "[physical|firmware|interface|architectural]"
  attackSurface: "[side-channel|fault-injection|debug-interface|key-management|boot-chain|firmware-update|bus-access-control|other]"
  technologyDomain: "[confidential-ai|tdisp-cxl|supply-chain|secure-boot-dice|cheri]"
  socFamily: "[compute|automotive|client|data-center|all]"

  # === Affected Components ===
  affectedInterfaces:
    - "[interface name 1]"
    - "[interface name 2]"
  affectedAssets:
    - "[asset name 1]"
    - "[asset name 2]"

  # === Assessment ===
  severity: "[CRITICAL|HIGH|MEDIUM|LOW|INFORMATIONAL]"
  confidenceTier: "[GROUNDED|INFERRED|SPECULATIVE|ABSENT]"
  verificationStatus: "llm-assessed"  # Always llm-assessed for new findings

  # === Grounding ===
  sourceGrounding: "[user-provided|embedded-reference|training-knowledge]"
  groundingReference: "[Specific reference — spec section, catalog entry path, or 'FROM TRAINING']"
  reasoningChain: |
    1. [Evidence/fact]: [source]
    2. [Logical step]: [reasoning]
    3. [Conclusion]: [how this leads to the threat]

  # === Assessment Notes ===
  assessmentNotes: |
    [Any additional context about confidence assignment, severity rationale,
    or caveats specific to this finding. Include notes about why the
    confidence tier was assigned if it might seem unexpected.]

  # === Mitigation & Verification ===
  suggestedMitigation: |
    [High-level mitigation direction. NOT a detailed design — the engineer
    determines the implementation. Example: "Implement state machine lock
    that prevents data transfer until assignment handshake completes."]
  verificationMethod: "[SVA|simulation|review|test|formal-analysis]"
  verificationNotes: |
    [Specific guidance for the verification-scaffold-skill. What should
    the verification check? What signals or properties are relevant?]

  # === Cross-Family Reuse ===
  crossFamilyReuse:
    applicable:
      - "[family 1]"
      - "[family 2]"
    deltas: |
      [Family-specific differences that affect this threat.
      Example: "Automotive: AXI bus instead of PCIe — same logical threat
      but different physical interface. Access control mechanism differs."]
    confidence: "[High|Medium|Low]"

  # === Relationships ===
  relatedFindings:
    - "[ID of related ThreatFinding]"
  standardsReferences:
    - standard: "[standard name]"
      version: "[version number]"
      section: "[section number]"
      requirement: "[brief requirement text or summary]"
  priorFindings:
    - "[ID of prior finding this builds on or supersedes]"
  attackTreeNodes:
    - "[ID of attack tree node, if this finding appears in an attack tree]"

  # === Framework Source ===
  framework: "[stride|attack-tree|standards-derived|combined]"
```

### Required vs. Optional Fields

| Field | Required? | Notes |
|-------|----------|-------|
| id | Required | Unique within the document |
| title | Required | Concise, max 80 characters |
| threatStatement | Required | Standard format with access, action, target, method, impact |
| description | Required | Additional context beyond the threat statement |
| strideCategory | Required if STRIDE was used | null for non-STRIDE findings |
| attackVector | Required | One of the 4 standard vectors |
| attackSurface | Required | One of the 7 standard surfaces or "other" |
| technologyDomain | Required | One of the 5 technology domains |
| socFamily | Required | Specific family or "all" |
| affectedInterfaces | Required | At least one interface |
| severity | Required | One of the 5 levels |
| confidenceTier | Required | One of the 4 tiers |
| verificationStatus | Required | Always "llm-assessed" for new findings |
| sourceGrounding | Required | One of the 3 grounding levels |
| groundingReference | Required | Specific reference |
| reasoningChain | Required | Step-by-step derivation |
| suggestedMitigation | Optional | High-level direction only |
| verificationMethod | Required | One of the verification methods |
| crossFamilyReuse | Required if multiple families in scope | Reuse assessment |
| relatedFindings | Optional | Links to related threats |
| standardsReferences | Required if standards-derived | Spec citations |
| framework | Required | Source framework(s) |

---

## 3. Attack Surface Checklist Template

This checklist is **mandatory** on every threat model output. No exceptions.

```markdown
## Attack Surface Coverage

| # | Attack Surface | Status | Finding Count | Notes |
|---|---------------|--------|---------------|-------|
| 1 | Side-channel | [ANALYZED / NOT ANALYZED] | [N or N/A] | [Brief justification] |
| 2 | Fault injection | [ANALYZED / NOT ANALYZED] | [N or N/A] | [Brief justification] |
| 3 | Debug interface | [ANALYZED / NOT ANALYZED] | [N or N/A] | [Brief justification] |
| 4 | Key management | [ANALYZED / NOT ANALYZED] | [N or N/A] | [Brief justification] |
| 5 | Boot chain | [ANALYZED / NOT ANALYZED] | [N or N/A] | [Brief justification] |
| 6 | Firmware update | [ANALYZED / NOT ANALYZED] | [N or N/A] | [Brief justification] |
| 7 | Bus access control | [ANALYZED / NOT ANALYZED] | [N or N/A] | [Brief justification] |
```

### Checklist Rules

1. **All 7 surfaces must be present.** No surface may be omitted from the checklist.
2. **NOT ANALYZED requires justification.** Acceptable reasons:
   - "Not applicable to this component" (e.g., boot chain for a bus controller)
   - "Insufficient input to analyze" (e.g., no power model for side-channel)
   - "Out of scope per engineer direction"
   - "Covered in separate threat model [TM-ID]"
3. **ANALYZED requires at least one finding or an explicit "No threats identified" note.**
4. **Finding count must be accurate.** Count only ThreatFinding entities mapped to this surface.
5. **Notes should be concise** (one sentence) explaining the analysis status.

### Example Completed Checklist

```markdown
## Attack Surface Coverage

| # | Attack Surface | Status | Finding Count | Notes |
|---|---------------|--------|---------------|-------|
| 1 | Side-channel | NOT ANALYZED | N/A | No power model provided; timing analysis included under interface threats |
| 2 | Fault injection | ANALYZED | 2 | FSM glitching and clock manipulation assessed |
| 3 | Debug interface | ANALYZED | 3 | JTAG and DFT access paths analyzed |
| 4 | Key management | ANALYZED | 4 | IDE key establishment, storage, and rotation assessed |
| 5 | Boot chain | NOT ANALYZED | N/A | Not applicable — component is a bus controller, not a boot path element |
| 6 | Firmware update | NOT ANALYZED | N/A | Component is hardware-only, no firmware |
| 7 | Bus access control | ANALYZED | 6 | Primary focus — PCIe/CXL access control analyzed comprehensively |
```
