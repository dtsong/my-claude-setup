# Knowledge Base

The knowledge base is an append-only repository of findings and decisions accumulated across analysis sessions. It enables cross-session learning and prevents redundant analysis.

## Structure

```
knowledge-base/
├── findings-ledger.md    # Append-only log of significant security findings
├── decision-log.md       # Security architecture decisions with rationale
└── README.md             # This file
```

## Files

### findings-ledger.md

Significant security findings discovered during threat modeling, verification, and compliance analysis. Each entry captures:

- **What** was found (finding description)
- **Where** it applies (SoC family, technology domain, standards)
- **What was done** (resolution)
- **How reusable** it is (High/Medium/Low with rationale)
- **What it connects to** (related findings, documents)

Entries are append-only. Never modify or delete existing entries. If a finding is superseded, add a new entry referencing the old one.

### decision-log.md

Architecture and security design decisions with full rationale. Each entry captures:

- **Context** that prompted the decision
- **What was decided**
- **Alternatives considered** and why they were rejected
- **Consequences** of the decision

Decisions can be marked `superseded` when replaced by a new decision, but the original entry is preserved for auditability.

## Cross-Session Workflow

### At Session Start

1. Check `findings-ledger.md` for prior findings relevant to the current SoC family and technology domain.
2. Check `decision-log.md` for prior decisions that constrain the current analysis.
3. Reference relevant entries by ID in your analysis outputs.

### During Analysis

- When a prior finding informs the current threat model, cite it: "Per FINDING-2026-001, the TDISP responder FSM requires..."
- When a prior decision constrains a verification approach, reference it: "Per DECISION-2026-001, we use two-tier verification for..."

### At Session End

- Append new significant findings to `findings-ledger.md`.
- Append new architecture decisions to `decision-log.md`.
- Not every observation needs an entry — record findings and decisions that would save effort or prevent mistakes in future sessions.

## Entry Format Quick Reference

### Finding

```
## [FINDING-YYYY-NNN] — Title
- Date: YYYY-MM-DD
- SoC Family: [compute|automotive|client|data-center]
- Technology Domain: [confidential-ai|tdisp-cxl|supply-chain|secure-boot-dice|cheri]
- Standards: [spec refs]
- Finding: [description]
- Resolution: [action taken]
- Reusability: [High|Medium|Low] — [rationale]
- Related: [finding IDs, document IDs]
```

### Decision

```
## [DECISION-YYYY-NNN] — Title
- Date: YYYY-MM-DD
- Status: [proposed|accepted|superseded|deprecated]
- SoC Family: [families]
- Technology Domain: [domains]
- Context: [what prompted this decision]
- Decision: [what was decided]
- Alternatives Considered:
  1. [alternative] — [why rejected]
- Consequences: [implications]
- Related: [IDs]
```

## ID Conventions

| Prefix | Entity |
|--------|--------|
| `FINDING-YYYY-NNN` | Knowledge base finding |
| `DECISION-YYYY-NNN` | Architecture decision |
| `SR-YYYY-NNN` | SecurityRequirement |
| `TF-YYYY-NNN` | ThreatFinding |
| `VI-YYYY-NNN` | VerificationItem |
| `CR-YYYY-NNN` | ComplianceResult |
| `BS-YYYY-NNN` | BriefSection |
| `TM-YYYY-NNN` | Threat Model document |
| `VC-YYYY-NNN` | Verification Checklist document |
| `CM-YYYY-NNN` | Compliance Matrix document |
| `EB-YYYY-NNN` | Executive Brief document |
