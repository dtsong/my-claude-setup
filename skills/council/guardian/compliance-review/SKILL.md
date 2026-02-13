---
name: "Compliance Review"
department: "guardian"
description: "[Council] GDPR/privacy compliance review for proposed features and data flows. Used during council/academy deliberation only."
version: 1
triggers:
  - "GDPR"
  - "CCPA"
  - "privacy"
  - "PII"
  - "compliance"
  - "consent"
  - "regulation"
  - "data protection"
  - "lawful basis"
  - "right to erasure"
---

# Compliance Review

## Purpose
Assess proposed features and data flows against applicable privacy regulations, identify compliance gaps, and produce actionable remediation plans.

## Inputs
- Feature description or proposal being analyzed
- Data elements collected, processed, or stored
- User-facing consent flows and privacy notices
- Third-party integrations and data sharing arrangements
- Target jurisdictions and applicable regulations

## Process

### Step 1: Identify Applicable Regulations
Determine which regulatory frameworks apply based on user base, data types, and jurisdictions. Map each regulation to its key obligations:

- **GDPR** (EU/EEA): Lawful basis, consent, right to access/erasure/portability, DPIAs, breach notification
- **CCPA/CPRA** (California): Right to know, right to delete, right to opt-out, data sale restrictions
- **HIPAA** (US health): PHI safeguards, minimum necessary standard, BAAs
- **SOC2**: Security, availability, processing integrity, confidentiality, privacy trust principles
- **PCI-DSS**: Cardholder data protection, network segmentation, access controls

### Step 2: Map Data Flows for PII
Trace every data element through its lifecycle. For each element, document:

- **Collection point**: Where and how is it gathered? (form, API, third-party sync)
- **Lawful basis**: What legal ground justifies processing? (consent, contract, legitimate interest)
- **Storage location**: Where does it live? (database, cache, logs, backups, third-party)
- **Processing purposes**: What is it used for? (core feature, analytics, marketing, ML training)
- **Sharing**: Who else receives it? (sub-processors, analytics vendors, ad networks)
- **Retention**: How long is it kept? (active use, archival, legal hold)

### Step 3: Assess Consent Mechanisms
Evaluate whether consent collection meets regulatory standards:

- Is consent freely given, specific, informed, and unambiguous?
- Are consent purposes granular (not bundled)?
- Can users withdraw consent as easily as they gave it?
- Is consent recorded with timestamp, version, and scope?
- Are pre-checked boxes or dark patterns avoided?
- Is there a mechanism for parental consent if minors are in scope?

### Step 4: Evaluate Data Retention Policies
For each data category, assess:

- Is there a defined retention period with documented justification?
- Does the retention period align with the lawful basis? (consent-based data must be deletable)
- Are automated deletion/anonymization processes in place?
- Do backups respect retention limits, or do they create shadow copies?
- Are legal hold requirements accounted for without overriding general deletion?

### Step 5: Check Right-to-Deletion Compliance
Verify that data subject rights are technically implementable:

- Can all PII for a given user be located across all systems?
- Does deletion cascade to backups, caches, logs, and third-party systems?
- Is soft-delete distinguished from hard-delete, and is hard-delete available?
- Can deletion be completed within regulatory timeframes (e.g., 30 days for GDPR)?
- Are there documented exceptions (legal obligations, legitimate interest overrides)?

### Step 6: Design Audit Trail Requirements
Specify what must be logged for compliance evidence:

- Consent events (granted, modified, withdrawn) with full context
- Data access events (who accessed what PII, when, for what purpose)
- Deletion/anonymization events (request received, processing, confirmation)
- Breach-related events (detection, assessment, notification timeline)
- Policy changes (consent text updates, retention policy modifications)

## Output Format

### Regulatory Applicability Matrix
| Regulation | Applies? | Key Obligations | Current Status |
|---|---|---|---|
| GDPR | Yes/No/Partial | [Obligations] | Compliant / Gap / Unknown |
| CCPA | Yes/No/Partial | [Obligations] | Compliant / Gap / Unknown |
| ... | ... | ... | ... |

### Data Flow Map
```
[User] → [Collection Point] → [Processing Service] → [Data Store]
                                      ↓
                              [Third-Party / Sub-processor]

PII Elements: [list]
Lawful Basis: [basis per element]
Retention: [period per element]
```

### Compliance Gap Analysis
| Area | Requirement | Current State | Gap | Severity | Remediation |
|---|---|---|---|---|---|
| Consent | Granular opt-in | Bundled consent | Non-compliant | Mandatory | Split consent by purpose |
| Retention | Defined periods | No expiry set | Non-compliant | Mandatory | Implement TTL per data category |
| ... | ... | ... | ... | ... | ... |

### Severity Key
- **Mandatory**: Regulatory requirement — must fix before launch or risk enforcement action
- **Strongly Recommended**: Best practice that significantly reduces risk — fix in current sprint
- **Advisory**: Improvement that strengthens posture — schedule for next iteration

## Quality Checks
- [ ] All applicable regulations are identified with specific articles/sections referenced
- [ ] Every PII element has a documented lawful basis for processing
- [ ] Consent mechanisms meet the "freely given, specific, informed, unambiguous" standard
- [ ] Data retention periods are defined and justified for every data category
- [ ] Right-to-deletion path covers all storage locations including backups and caches
- [ ] Third-party data sharing is documented with DPA/contractual coverage
- [ ] Audit trail requirements cover consent, access, deletion, and breach events
- [ ] Gap analysis includes specific, actionable remediation for every finding

## Evolution Notes
<!-- Observations appended after each use -->
