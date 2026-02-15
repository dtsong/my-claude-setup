---
name: audit-trail-design
department: "guardian"
description: "Use when designing audit logging systems for accountability and compliance evidence. Covers event catalogs, log schemas, retention policies, immutability requirements, and compliance reporting. Do not use for regulatory gap analysis (use compliance-review) or data sensitivity classification (use data-classification)."
version: 1
triggers:
  - "audit"
  - "logging"
  - "trail"
  - "accountability"
  - "traceability"
  - "compliance reporting"
  - "forensic"
  - "immutable log"
  - "SOC2"
---

# Audit Trail Design

## Purpose
Design audit logging systems that provide accountability, traceability, and compliance evidence. Produce event catalogs, log schemas, and retention policies that satisfy regulatory requirements and support forensic investigation.

## Scope Constraints
Reads system architecture, regulatory requirements, and data classification outputs for audit design. Does not implement logging infrastructure or access production log stores.

## Inputs
- System architecture and services to be audited
- Regulatory requirements (from compliance review if available)
- Data classification (which data elements are Confidential/Restricted)
- User roles and access control model
- Existing logging infrastructure and constraints

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Identify auditable events
- [ ] Step 2: Define log schema
- [ ] Step 3: Specify retention policies
- [ ] Step 4: Design immutability requirements
- [ ] Step 5: Plan access controls for audit data
- [ ] Step 6: Define compliance reporting

### Step 1: Identify Auditable Events
Catalog every event that must be recorded for compliance, security, or operational accountability:

- **Authentication events**: Login success/failure, logout, session creation/expiry, MFA challenges, password changes
- **Authorization events**: Permission grants/revocations, role changes, access denied events
- **Data access events**: Read access to Restricted/Confidential data, bulk exports, API queries returning PII
- **Data mutation events**: Create/update/delete of sensitive records, schema migrations, bulk operations
- **Consent events**: Consent granted/modified/withdrawn, privacy preference changes
- **Administrative events**: Configuration changes, feature flag toggles, deployment events, user account management
- **Compliance events**: Data subject requests (access, erasure, portability), breach detection, regulatory submissions

### Step 2: Define Log Schema
Design a consistent schema that answers who/what/when/where/why for every event:

- **who**: Actor identity (user ID, service account, API key ID). Never log credentials or tokens.
- **what**: Event type (enum), action performed, resource affected (type + ID), before/after state for mutations
- **when**: Timestamp in UTC (ISO 8601), with millisecond precision. Clock synchronization requirements.
- **where**: Service name, instance ID, request ID (correlation), source IP (masked per policy), geographic region
- **why**: Business context — the operation that triggered the event, request path, feature context
- **outcome**: Success/failure, error code if applicable, affected record count

### Step 3: Specify Retention Policies
Define retention based on regulatory and business requirements:

- **Regulatory minimums**: HIPAA (6 years), SOC2 (1 year), PCI-DSS (1 year), financial regulations (5-7 years)
- **Tiered retention**: Hot storage (fast query, 90 days) -> Warm storage (indexed, 1 year) -> Cold storage (archived, regulatory maximum)
- **Deletion policy**: Audit logs of deleted user data must be retained for compliance even after user data deletion
- **Cost modeling**: Estimate storage costs per tier and growth rate

### Step 4: Design Immutability Requirements
Ensure audit records cannot be tampered with after creation:

- **Write-once storage**: Append-only log stores, WORM storage for compliance
- **Integrity verification**: Hash chaining or Merkle trees to detect tampering or gaps
- **Separation of duties**: Audit log administrators cannot modify log contents
- **Tamper evidence**: If a record is modified or deleted, the system must detect and alert

### Step 5: Plan Access Controls for Audit Data
Define who can access audit records and under what circumstances:

- **Read access**: Security team (full), compliance officers (filtered), engineering (operational only, no PII)
- **Export controls**: Bulk export requires approval, exports are themselves audited
- **PII in audit logs**: Mask or encrypt PII fields; provide decryption only for authorized investigations
- **Cross-team access**: Support/customer success may need filtered views — define scope limits

### Step 6: Define Compliance Reporting
Specify the reports and dashboards that audit data must support:

- **Regulatory reports**: Data subject access requests, breach timeline reconstruction, consent audit trail
- **Operational dashboards**: Failed authentication trends, unusual access patterns, bulk export monitoring
- **Periodic evidence**: SOC2 control evidence, HIPAA access review reports, PCI-DSS log review evidence
- **Alerting**: Real-time alerts for high-severity events (mass data export, privilege escalation, repeated auth failures)

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what system is being analyzed, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Output Format

### Event Catalog
| Event Category | Event Type | Trigger | Data Captured | Retention Tier |
|---|---|---|---|---|
| Authentication | login_success | User login | user_id, timestamp, IP, method | Hot 90d → Cold 1y |
| Authentication | login_failure | Failed login | attempted_user, timestamp, IP, reason | Hot 90d → Cold 1y |
| Data Access | pii_read | PII field accessed | user_id, accessor_id, field, purpose | Hot 90d → Cold 7y |
| Consent | consent_granted | User gives consent | user_id, purpose, scope, version, timestamp | Hot 90d → Cold 7y |
| ... | ... | ... | ... | ... |

### Log Schema
```json
{
  "event_id": "uuid-v4",
  "event_type": "enum(event_catalog)",
  "timestamp": "2024-01-15T10:30:00.000Z",
  "actor": {
    "type": "user|service|system",
    "id": "user_123",
    "ip": "192.168.x.x",
    "session_id": "sess_abc"
  },
  "resource": {
    "type": "user|record|config",
    "id": "res_456",
    "field": "email"
  },
  "action": "read|create|update|delete|grant|revoke",
  "outcome": "success|failure",
  "context": {
    "service": "user-service",
    "request_id": "req_789",
    "region": "us-east-1"
  },
  "metadata": {}
}
```

### Retention Policy
| Tier | Storage Type | Duration | Query SLA | Cost Model |
|---|---|---|---|---|
| Hot | Primary database / search index | 90 days | < 1s | $$$  |
| Warm | Indexed archive | 1 year | < 30s | $$ |
| Cold | Object storage (compressed) | Regulatory max (up to 7y) | Minutes | $ |

### Access Control Matrix
| Role | Read Events | Search PII Fields | Export | Admin |
|---|---|---|---|---|
| Security Team | All | Yes | With approval | No |
| Compliance Officer | All | Yes (masked) | With approval | No |
| Engineering | Operational only | No | No | No |
| Audit Log Admin | Metadata only | No | No | Yes (config, not content) |

## Handoff

- Hand off regulatory compliance gaps discovered during audit design to compliance-review for full gap analysis.
- Hand off data sensitivity questions to data-classification if audit events contain unclassified data elements.

## Quality Checks
- [ ] Every auditable event category is represented in the event catalog
- [ ] Log schema captures who/what/when/where/why for every event type
- [ ] Retention policies reference specific regulatory requirements with durations
- [ ] Immutability controls prevent tampering and detect gaps in the audit trail
- [ ] PII within audit logs is masked or encrypted with controlled decryption
- [ ] Access control matrix defines least-privilege access for every role
- [ ] Compliance reporting covers all required regulatory evidence outputs
- [ ] Alerting is defined for high-severity events requiring real-time response

## Evolution Notes
<!-- Observations appended after each use -->
