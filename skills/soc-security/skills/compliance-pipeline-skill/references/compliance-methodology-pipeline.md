# Compliance Methodology — Pipeline Definition and Requirement Extraction

## Table of Contents

- [Stage 1: Requirement Extraction](#stage-1-requirement-extraction--detailed-process)
- [Extraction Decision Tree](#extraction-decision-tree)
- [Normative Language Mapping](#normative-language-mapping)
- [Spec Section Reference Format](#spec-section-reference-format)
- [Security Property Assignment Rules](#security-property-assignment-rules)
- [Implementation Layer Assignment Rules](#implementation-layer-assignment-rules)
- [ID Assignment](#id-assignment)

---

## Stage 1: Requirement Extraction — Detailed Process

### Extraction Decision Tree

For each specification paragraph or clause in scope:

```
Does the paragraph contain a normative obligation ("shall", "must", "required")?
  YES → Extract as SecurityRequirement
    → Does it contain multiple obligations?
       YES → Extract each as a separate requirement
       NO  → Extract as a single requirement
  NO → Does it contain a recommendation ("should", "recommended")?
    YES → Extract as SecurityRequirement with note: [RECOMMENDATION, not mandatory]
    NO  → Does it define a security-relevant behavior or property?
      YES → Extract as SecurityRequirement with confidenceTier: INFERRED
      NO  → Skip — not a security requirement
```

### Normative Language Mapping

| Spec Language | Obligation Level | Compliance Status If Not Met |
|---|---|---|
| "shall" / "must" / "is required to" | Mandatory | `not-met` |
| "shall not" / "must not" | Prohibition (mandatory) | `not-met` |
| "should" / "is recommended" | Recommended | `partial` (not a hard failure) |
| "may" / "can" / "is permitted to" | Optional | `not-applicable` (unless explicitly chosen) |
| "is" / "are" (descriptive) | Informative | Not extracted as requirement |

### Spec Section Reference Format

All spec references must follow this format for consistency:

```
{Standard}-{Version} Section {X.Y.Z}
```

Examples:
- `TDISP-1.0 Section 4.3.2`
- `DICE-v1.2 Section 6.1`
- `CXL-3.1 Section 11.4.1`
- `SPDM-v1.4 Section 10.5`
- `CHERI-v9 Section 3.2.1`

For compliance overlays:
- `FIPS-140-3 Section 7.7`
- `ISO-21434 Clause 9.4`

When the exact section is uncertain:
- `TDISP-1.0 Section 4.x [SECTION REFERENCE NEEDED]`

### Security Property Assignment Rules

Each requirement maps to one primary security property. Use this decision guide:

| If the requirement is about... | Primary Property |
|---|---|
| Preventing data disclosure to unauthorized entities | Confidentiality |
| Detecting unauthorized modification | Integrity |
| Verifying identity of device, firmware, or peer | Authenticity |
| Ensuring timely access to resources | Availability |
| Enforcing separation between security domains | Isolation |
| Providing verifiable evidence of platform state | Attestation |
| Preventing denial of past actions | Non-Repudiation |
| Ensuring recency (not replayed) | Freshness |
| Restricting operations based on identity/capability | Access Control |
| Mitigating physical side-channel leakage | Side-Channel Resistance |

When a requirement spans multiple properties (e.g., "encrypted and integrity-protected link"), map to the primary property and note the secondary in the `rationale` field.

### Implementation Layer Assignment Rules

| If the requirement is implemented in... | Layer |
|---|---|
| Digital logic, state machines, hardware blocks | `rtl` |
| Boot firmware, security monitor, HSM firmware | `firmware` |
| OS drivers, user-space services, management software | `software` |
| Protocol handshakes, session management, message formats | `protocol` |
| Physical countermeasures, tamper resistance, lab testing | `physical` |

### ID Assignment

SecurityRequirement IDs follow the pattern `SR-{YYYY}-{NNN}` where:
- `YYYY` is the assessment year
- `NNN` is a sequential number within the assessment, starting at 001
- IDs are assigned in extraction order within each standard
- IDs are stable within an assessment — do not renumber after extraction
