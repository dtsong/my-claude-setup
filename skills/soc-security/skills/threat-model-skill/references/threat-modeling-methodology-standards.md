# Threat Modeling Methodology — Standards-Derived Threat Extraction

## Contents

- [Purpose](#purpose)
- [Quick Reference](#quick-reference)
- [Background](#background)
- [Extraction Process](#extraction-process)
  - [Step 1: Identify Relevant Sections](#step-1-identify-relevant-sections)
  - [Step 2: Extract Requirements](#step-2-extract-requirements)
  - [Step 3: Negate Requirements to Derive Threats](#step-3-negate-requirements-to-derive-threats)
  - [Step 4: Classify and Cross-Reference](#step-4-classify-and-cross-reference)
- [Per-Standard Extraction Focus Areas](#per-standard-extraction-focus-areas)
  - [TDISP 1.0](#tdisp-10)
  - [DICE](#dice)
  - [CXL 3.1](#cxl-31)
  - [SPDM 1.4](#spdm-14)
  - [CHERI ISA](#cheri-isa)
- [Extraction Quality Checks](#extraction-quality-checks)

## Purpose

Methodology for extracting threats by negating security requirements from specifications. Includes per-standard extraction guides and cross-framework integration.

**Primary consumer:** threat-model-skill (Phase 3 threat identification, Framework 3)

---

## Quick Reference

| Methodology | Use When | Output | Typical Scope |
|---|---|---|---|
| Standards-Derived Extraction | Mapping spec requirements to threats for compliance traceability | Requirement-threat pairs with direct spec grounding | Per-standard analysis |

---

## Background

Security specifications contain explicit and implicit security requirements. Each requirement implies a threat: the condition where the requirement is violated. Standards-derived threat extraction systematically transforms specification requirements into threat findings, providing GROUNDED confidence for explicit requirements.

---

## Extraction Process

### Step 1: Identify Relevant Sections

| Standard | Relevant Sections | Focus |
|----------|-------------------|-------|
| TDISP 1.0 | Section 4 (Device Assignment), Section 5 (Key Management) | State machine, isolation, key establishment |
| CXL 3.1 | Section 11 (Security), Section 14 (IDE) | Fabric security, integrity/data encryption |
| DICE | Section 5 (Layered Architecture), Section 6 (Certificate Chain) | Measurement, key derivation, attestation |
| SPDM 1.4 | Section 10 (Authentication), Section 11 (Measurement) | Device authentication, firmware measurement |
| CHERI ISA | Chapter 3 (Capability Model), Chapter 5 (Exceptions) | Capability integrity, monotonicity, exception handling |

### Step 2: Extract Requirements

| Keyword | Requirement Strength | Confidence for Derived Threat |
|---------|---------------------|-------------------------------|
| SHALL / MUST | Mandatory | GROUNDED |
| SHALL NOT / MUST NOT | Mandatory prohibition | GROUNDED |
| SHOULD / RECOMMENDED | Advisory | INFERRED |
| MAY / OPTIONAL | Permitted behavior | INFERRED at most |

### Step 3: Negate Requirements to Derive Threats

**Template:**
```
Requirement: "[Standard] [Section]: [Quoted requirement]"
Negation: "If [requirement is not met], then..."
Threat: "[Specific consequence of the negation]"
```

**Worked examples:**

1. **TDISP 1.0 Section 4.3.2:** "The DSM SHALL verify that the TDI is in the LOCKED state before allowing data transfer."
   - Threat: "Data transfers may occur to/from a TDI that has not completed its security handshake."
   - Confidence: GROUNDED

2. **DICE Section 5.2:** "Each DICE layer SHOULD derive its key material using a one-way function that includes the measurement of the next layer."
   - Threat: "A compromised layer's key material could be valid regardless of subsequent layers' integrity."
   - Confidence: INFERRED

3. **CXL 3.1 Section 11.4:** "The IDE key SHALL be rotated at intervals not exceeding [configured maximum]."
   - Threat: "Extended window for key recovery attacks if keys are not rotated."
   - Confidence: GROUNDED

### Step 4: Classify and Cross-Reference

For each standards-derived threat: (1) Assign STRIDE category. (2) Assign attack vector. (3) Check for existing findings from other frameworks — if duplicate, link; if new, add. (4) Identify verification method: SHALL on state machines -> SVA (Tier 1); SHALL on protocols -> NL properties (Tier 2); SHALL on information flow -> Specification only (Tier 3).

---

## Per-Standard Extraction Focus Areas

### TDISP 1.0

| Section | Security Focus | Common Threats |
|---------|---------------|----------------|
| 4.1 | Device Discovery | Spoofing, unauthorized enumeration |
| 4.2 | State Machine | State desynchronization, race conditions |
| 4.3 | Assignment | Unauthorized DMA, BAR manipulation |
| 4.4 | BAR Management | Out-of-range access, BAR reconfiguration |
| 5.1 | Key Establishment | Key interception, downgrade, replay |
| 5.2 | Key Storage | Key extraction, unauthorized read |

### DICE

| Section | Security Focus | Common Threats |
|---------|---------------|----------------|
| 5.1 | Layer Architecture | Layer bypass, measurement tampering |
| 5.2 | Key Derivation | Key prediction, derivation weakness |
| 5.3 | Attestation | Certificate forgery, chain manipulation |
| 6.1 | Anti-Rollback | Counter manipulation, overflow |
| 6.2 | Recovery | Recovery bypass, persistent compromise |

### CXL 3.1

| Section | Security Focus | Common Threats |
|---------|---------------|----------------|
| 11.1 | Fabric Security | Cross-port access, fabric manipulation |
| 11.2 | Device Auth | Authentication bypass, replay |
| 14.1 | IDE Architecture | Key compromise, stream manipulation |
| 14.2 | IDE Key Management | Rotation failure, key exposure |
| 14.3 | IDE Integrity | Integrity bypass, MAC forgery |

### SPDM 1.4

| Section | Security Focus | Common Threats |
|---------|---------------|----------------|
| 10.1 | Challenge-Response | Replay, man-in-the-middle |
| 10.2 | Certificate Chain | Expired certs, revocation bypass |
| 11.1 | Measurement Reporting | Measurement spoofing, TOCTOU |
| 11.2 | Measurement Freshness | Replay of stale measurements |

### CHERI ISA

| Section | Security Focus | Common Threats |
|---------|---------------|----------------|
| 3.1 | Capability Model | Forgery, uninitialized use |
| 3.2 | Monotonicity | Amplification, escalation |
| 3.3 | Bounds Checking | Out-of-bounds access |
| 5.1 | Exception Handling | Exception-based escalation |
| 5.2 | Compartmentalization | Compartment escape, IPC abuse |

---

## Extraction Quality Checks

1. Every SHALL/MUST requirement in scope has a derived threat — none silently skipped
2. SHOULD requirements included but marked INFERRED
3. Each derived threat has a specific consequence, not just "requirement violated"
4. Cross-referencing complete — every standards-derived threat checked against STRIDE findings
5. Verification method assigned per threat
6. Spec versions recorded — threats may change between versions
