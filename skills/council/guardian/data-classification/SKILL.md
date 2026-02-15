---
name: data-classification
department: "guardian"
description: "Use when classifying data elements by sensitivity tier and defining per-tier handling requirements. Covers data inventory, sensitivity classification, PII flow mapping, encryption and masking specifications, and cross-boundary transfer documentation. Do not use for regulatory gap analysis (use compliance-review) or audit logging design (use audit-trail-design)."
version: 1
triggers:
  - "data classification"
  - "PII"
  - "sensitive"
  - "confidential"
  - "public"
  - "internal"
  - "restricted"
  - "data handling"
  - "encryption"
  - "masking"
---

# Data Classification

## Purpose
Classify data elements by sensitivity tier, define handling requirements for each tier, and map PII flows to ensure appropriate protections are applied throughout the data lifecycle.

## Scope Constraints
Reads data models, schemas, and architecture documentation for classification analysis. Does not modify schemas, apply encryption, or access production data stores directly.

## Inputs
- Data model or schema being analyzed
- Data elements and their sources (user input, system generated, third-party)
- Storage and processing architecture
- Integration points and data sharing arrangements
- Applicable regulatory context (from compliance review if available)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Inventory data elements
- [ ] Step 2: Classify by sensitivity tier
- [ ] Step 3: Map PII flows
- [ ] Step 4: Define handling requirements per tier
- [ ] Step 5: Identify cross-boundary data transfers
- [ ] Step 6: Specify encryption and masking requirements

### Step 1: Inventory Data Elements
Catalog every data element in scope. For each element, document:

- **Name and description**: What is the field and what does it represent?
- **Source**: User-provided, system-generated, derived, or third-party
- **Format**: Free text, structured (email, phone), numeric, binary, etc.
- **Volume**: Approximate record count and growth rate
- **Current protections**: Encryption at rest/transit, access controls, masking

### Step 2: Classify by Sensitivity Tier
Assign each data element to a sensitivity tier:

- **Public**: Information intended for public access. No PII. No competitive sensitivity. Example: marketing copy, public API docs, open-source code.
- **Internal**: Not public, but low impact if disclosed. Non-identifying operational data. Example: internal project names, non-sensitive configs, aggregated metrics.
- **Confidential**: Business-sensitive or indirect PII. Disclosure causes material harm. Example: email addresses, IP addresses, financial reports, API keys, internal strategies.
- **Restricted**: Direct PII, protected health information, payment data, credentials. Disclosure triggers regulatory obligations. Example: SSN, medical records, credit card numbers, passwords, biometric data.

### Step 3: Map PII Flows
For each PII element, trace the complete data flow:

- **Collection**: Where does it enter the system? What consent covers it?
- **Transit**: How does it move between services? Is it encrypted in transit?
- **Processing**: Which services touch it? Is the access minimized to what's necessary?
- **Storage**: Where is it persisted? Is it encrypted at rest? Is it in the right geography?
- **Sharing**: Does it leave the system boundary? Under what contractual protections?
- **Deletion**: How is it removed? Does deletion cascade to all copies?

### Step 4: Define Handling Requirements Per Tier
Specify the minimum controls required for each sensitivity tier:

- **Access control**: Who can read/write/delete? What authentication is required?
- **Encryption**: At rest, in transit, application-level? Key management approach?
- **Masking/redaction**: In logs, error messages, API responses, UI displays?
- **Retention**: Maximum retention period, automated expiry mechanism?
- **Audit**: What access events must be logged? What level of detail?
- **Backup/recovery**: Backup frequency, encryption of backups, geographic constraints?

### Step 5: Identify Cross-Boundary Data Transfers
Document every case where data moves across trust boundaries:

- Internal service to external API (analytics, payment processors, email services)
- Production to non-production environments (test data, staging copies)
- Geographic transfers (EU to US, cross-region replication)
- Employee access (admin tools, support dashboards, database queries)
- For each transfer: document the justification, contractual protections (DPA, SCCs), and technical safeguards

### Step 6: Specify Encryption and Masking Requirements
Define specific technical controls for each data element:

- **Encryption at rest**: AES-256 for Restricted, AES-128 minimum for Confidential
- **Encryption in transit**: TLS 1.2+ for all tiers, mTLS for Restricted inter-service
- **Application-level encryption**: Field-level encryption for Restricted elements in shared databases
- **Log masking**: Restricted fields never appear in logs; Confidential fields are masked/truncated
- **Display masking**: SSN shows last 4 only, credit cards show last 4 only, emails partially masked in admin views
- **Test data**: Restricted and Confidential data must be synthesized or anonymized for non-production

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what system is being analyzed, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Output Format

### Data Classification Matrix
| Data Element | Source | Sensitivity Tier | PII? | Regulatory Scope | Owner |
|---|---|---|---|---|---|
| Email address | User input | Confidential | Yes | GDPR, CCPA | User Service |
| Session token | System | Restricted | No | SOC2 | Auth Service |
| Page views | System | Internal | No | — | Analytics |
| ... | ... | ... | ... | ... | ... |

### Handling Requirements Table
| Tier | Access Control | Encryption (Rest) | Encryption (Transit) | Log Masking | Retention | Audit Level |
|---|---|---|---|---|---|---|
| Public | Open | Optional | TLS 1.2+ | None | Unlimited | None |
| Internal | Role-based | Optional | TLS 1.2+ | None | 2 years | Read-only |
| Confidential | Role-based + MFA | AES-128+ | TLS 1.2+ | Masked | Defined per type | Read/Write |
| Restricted | Need-to-know + MFA | AES-256 | TLS 1.2+ / mTLS | Never logged | Minimum viable | Full (who/what/when) |

### PII Flow Diagram
```
[User Input] ──TLS──▶ [API Gateway] ──mTLS──▶ [User Service]
                                                    │
                                              [Encrypted DB]
                                                    │
                                    ┌───────────────┼───────────────┐
                                    ▼               ▼               ▼
                              [Analytics]     [Email SaaS]    [Backup Store]
                              (anonymized)    (DPA in place)  (AES-256)
```

## Handoff

- Hand off regulatory gap analysis to compliance-review if classification reveals unaddressed regulatory obligations.
- Hand off audit logging requirements to audit-trail-design for access event logging on Confidential and Restricted data.

## Quality Checks
- [ ] Every data element in scope is inventoried and classified
- [ ] All PII elements are identified and mapped through their full lifecycle
- [ ] Handling requirements are defined for every sensitivity tier
- [ ] Cross-boundary data transfers are documented with justification and protections
- [ ] Encryption requirements are specific (algorithm, key size) not generic
- [ ] Log masking rules prevent Restricted data from appearing in any log output
- [ ] Test/staging environments have no production Restricted or Confidential data
- [ ] Classification matrix identifies an owner for each data element

## Evolution Notes
<!-- Observations appended after each use -->
