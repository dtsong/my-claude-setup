---
name: "Audit Trail Design"
department: "guardian"
description: "Audit logging design with event catalogs, log schemas, and retention policies"
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

## Inputs
- System architecture and services to be audited
- Regulatory requirements (from compliance review if available)
- Data classification (which data elements are Confidential/Restricted)
- User roles and access control model
- Existing logging infrastructure and constraints

## Process

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
Define how long audit records must be retained based on regulatory and business requirements:

- **Regulatory minimums**: GDPR (no specific minimum, but must demonstrate compliance), HIPAA (6 years), SOC2 (1 year), PCI-DSS (1 year), financial regulations (5-7 years)
- **Operational needs**: Active query window (30-90 days in hot storage), archival period (cold storage)
- **Tiered retention**: Hot storage (fast query, 90 days) → Warm storage (indexed, 1 year) → Cold storage (archived, regulatory maximum)
- **Deletion policy**: Audit logs of deleted user data must be retained for compliance even after user data deletion (log the deletion, don't delete the log)
- **Cost modeling**: Estimate storage costs per tier and growth rate to inform retention decisions

### Step 4: Design Immutability Requirements
Ensure audit records cannot be tampered with after creation:

- **Write-once storage**: Append-only log stores, WORM (Write Once Read Many) storage for compliance
- **Integrity verification**: Hash chaining or Merkle trees to detect tampering or gaps
- **Separation of duties**: Audit log administrators cannot modify log contents; different IAM roles for write vs. admin
- **Tamper evidence**: If a record is modified or deleted, the system must detect and alert
- **Backup integrity**: Audit log backups must have independent integrity verification

### Step 5: Plan Access Controls for Audit Data
Define who can access audit records and under what circumstances:

- **Read access**: Security team (full access), compliance officers (filtered views), engineering (operational logs only, no PII fields)
- **Search/query access**: Define which fields are searchable, which require elevated permissions
- **Export controls**: Bulk export requires approval, exports are themselves audited
- **PII in audit logs**: Mask or encrypt PII fields within audit records; provide decryption only for authorized investigations
- **Cross-team access**: Support/customer success may need filtered audit views for user-facing inquiries — define scope limits

### Step 6: Define Compliance Reporting
Specify the reports and dashboards that audit data must support:

- **Regulatory reports**: Data subject access requests (all events for a given user), breach timeline reconstruction, consent audit trail
- **Operational dashboards**: Failed authentication trends, unusual access patterns, bulk data export monitoring
- **Periodic compliance evidence**: SOC2 control evidence generation, HIPAA access review reports, PCI-DSS log review evidence
- **Ad-hoc investigation**: Query capabilities for forensic analysis — filter by user, time range, event type, resource, outcome
- **Alerting**: Real-time alerts for high-severity events (mass data export, privilege escalation, repeated auth failures)

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
