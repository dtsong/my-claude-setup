---
name: threat-model
department: "skeptic"
description: "Use when applying STRIDE threat modeling to identify security risks in proposed features. Covers trust boundary mapping, data flow analysis, threat rating, mitigation proposals, and residual risk documentation. Do not use for failure scenario discovery (use failure-mode-analysis) or boundary value testing (use edge-case-enumeration)."
version: 1
triggers:
  - "security"
  - "authentication"
  - "authorization"
  - "auth"
  - "threat"
  - "attack"
  - "vulnerability"
  - "XSS"
  - "injection"
  - "CSRF"
  - "token"
  - "permission"
  - "encryption"
---

# Threat Model

## Purpose
Apply STRIDE threat modeling to identify security risks in proposed features and produce mitigation recommendations.

## Scope Constraints

Analyzes feature proposals, architecture diagrams, and authentication/authorization flows for security threats. Does not execute exploits, modify code, or access production systems. Limited to design-time threat identification and mitigation planning.

## Inputs
- Feature description or proposal being analyzed
- System architecture context (services, data stores, external dependencies)
- Authentication/authorization flows involved
- Data sensitivity classification

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Step 1: Define Trust Boundaries
Identify what's inside the trust boundary, what's outside, and where boundaries are crossed. Map out the system perimeter, internal service boundaries, and client/server boundaries.

### Step 2: Enumerate Data Flows
Trace each data flow: user input → processing → storage → output. Identify each hop, transformation, and boundary crossing. Note where data changes trust level.

### Step 3: Apply STRIDE Per Data Flow
For each data flow, analyze all six threat categories:

- **Spoofing**: Can someone impersonate a legitimate user or service?
- **Tampering**: Can data be modified in transit or at rest?
- **Repudiation**: Can actions be denied without an audit trail?
- **Information Disclosure**: Can sensitive data leak through errors, logs, or APIs?
- **Denial of Service**: Can the system be overwhelmed or made unavailable?
- **Elevation of Privilege**: Can a user gain unauthorized access to resources?

### Step 4: Rate Each Threat
Use Likelihood x Impact to assign a Risk Score:
- **Critical**: Likely + Severe impact (data breach, full compromise)
- **High**: Likely + Moderate impact, or Possible + Severe impact
- **Medium**: Possible + Moderate impact
- **Low**: Unlikely + Minor impact

### Step 5: Propose Mitigations
For all High+ threats, propose specific, actionable mitigations. Not "add security" — instead "validate JWT signature on every API route using middleware X" or "add rate limiting of 100 req/min per IP on /api/auth endpoints."

### Step 6: Identify Residual Risks
Document what remains after mitigations are applied. Note accepted risks and their justification.

### Progress Checklist
- [ ] Step 1: Trust boundaries defined
- [ ] Step 2: Data flows enumerated
- [ ] Step 3: STRIDE analysis applied per data flow
- [ ] Step 4: Threats rated by likelihood x impact
- [ ] Step 5: Mitigations proposed for High+ threats
- [ ] Step 6: Residual risks documented

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what system is being analyzed, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Output Format

### Trust Boundary Diagram
```
┌─────────────────────────────┐
│  Trust Boundary: [Name]     │
│                             │
│  [Internal Components]      │
│                             │
└──────────┬──────────────────┘
           │ [Data Flow]
           ▼
  [External Component]
```

### Threat Table

| STRIDE Category | Threat Description | Risk Rating | Mitigation | Status |
|---|---|---|---|---|
| Spoofing | [Description] | High | [Specific mitigation] | Open |
| ... | ... | ... | ... | ... |

### Residual Risk Summary
- [Risk]: [Why it's accepted] — [Monitoring approach]

## Handoff

- Hand off to failure-mode-analysis if infrastructure failure scenarios are identified during threat modeling.
- Hand off to architect/codebase-context if architectural vulnerabilities require structural remediation.

## Quality Checks
- [ ] Every data flow has full STRIDE analysis
- [ ] All High+ threats have specific, actionable mitigations
- [ ] Mitigations reference concrete implementation approaches
- [ ] Auth flows are fully covered (login, session, token refresh, logout)
- [ ] Third-party integrations are analyzed for trust boundary crossings
- [ ] Residual risks are documented with justification

## Evolution Notes
<!-- Observations appended after each use -->
