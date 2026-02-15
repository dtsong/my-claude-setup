---
name: adr-template
department: "chronicler"
description: "Use when recording significant architectural or design decisions that affect the system. Covers decision framing, context documentation, options analysis with tradeoff evaluation, consequence mapping, and review trigger definition. Do not use for documentation strategy planning (use documentation-plan) or release changelog creation (use changelog-design)."
version: 1
triggers:
  - "ADR"
  - "decision"
  - "architecture decision"
  - "rationale"
  - "decision record"
  - "design decision"
  - "tradeoff"
---

# ADR Template

## Purpose

Create Architecture Decision Records that capture the context, options considered, decision rationale, and consequences of significant technical choices. Produces structured ADR documents that serve as the institutional memory of the project.

## Scope Constraints

Reads existing ADRs, system context, and stakeholder input to produce a structured decision record. Does not implement the chosen option or modify system architecture.

## Inputs

- The architectural question or decision being made
- Current system context and constraints
- Stakeholder concerns and priorities
- Related previous decisions (existing ADRs)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Identify the decision to record
- [ ] Step 2: Describe context
- [ ] Step 3: Enumerate options considered
- [ ] Step 4: Evaluate each option
- [ ] Step 5: Document the decision
- [ ] Step 6: Specify consequences
- [ ] Step 7: Define review triggers

### Step 1: Identify the Decision to Record

Clearly frame the architectural question:
- What specific question was (or needs to be) resolved?
- Why is this decision significant enough to record? (Costly to change, cross-cutting impact, team disagreement)
- What is the scope of this decision? (Single service, full system, team process)
- Assign a sequential ADR number and descriptive title

### Step 2: Describe Context

Document the forces at play:
- What is the current state of the system relevant to this decision?
- What constraints exist? (Technical: language, framework, infrastructure. Business: timeline, budget, team size)
- What requirements drive this decision? (Functional, non-functional, compliance)
- What assumptions are being made?
- Reference related ADRs that provide context or are affected by this decision

### Step 3: Enumerate Options Considered

List at least 2-3 alternatives, including "do nothing":
- **Option A: [Name]** — Brief description of the approach
- **Option B: [Name]** — Brief description of the approach
- **Option C: Do nothing / Status quo** — What happens if no change is made
- For each option, provide enough detail for a reader to understand the approach without external context

### Step 4: Evaluate Each Option

Analyze tradeoffs systematically:
- **Pros**: What does this option do well? Alignment with principles, simplicity, performance
- **Cons**: What are the downsides? Complexity, risk, learning curve, migration effort
- **Risks**: What could go wrong? Scaling issues, vendor lock-in, maintenance burden
- **Effort**: Rough implementation effort (T-shirt size: S/M/L/XL)
- **Alignment**: How well does this option align with architectural principles and team capabilities?

### Step 5: Document the Decision

State the chosen option and core rationale:
- Which option was selected?
- What was the primary reason for choosing it? (Not "it's the best" — the specific tradeoff that tipped the balance)
- Was this decision unanimous or contentious? Note dissenting opinions if applicable
- What conditions would make this the wrong decision? (Helps future readers know when to revisit)

### Step 6: Specify Consequences

Detail what follows from this decision:
- **What becomes easier**: Capabilities enabled, patterns simplified, workflows improved
- **What becomes harder**: Constraints introduced, options foreclosed, complexity added
- **New constraints**: What must all future development respect because of this decision?
- **Technical debt accepted**: What shortcuts or imperfections are knowingly accepted?
- **Follow-up work**: What tasks, migrations, or changes are needed to implement this decision?

### Step 7: Define Review Triggers

Specify when this decision should be revisited:
- **Scale thresholds**: "Revisit if traffic exceeds X or data grows beyond Y"
- **Technology changes**: "Revisit if [framework/service] releases [capability]"
- **Team changes**: "Revisit if team grows beyond N engineers or splits into multiple teams"
- **Time-based**: "Review after 12 months regardless of other triggers"
- **Pain indicators**: "Revisit if [specific friction point] becomes a recurring issue"

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what system is being analyzed, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Output Format

```markdown
# ADR-[NNN]: [Descriptive Title]

**Status**: [Proposed | Accepted | Deprecated | Superseded by ADR-NNN]
**Date**: [YYYY-MM-DD]
**Deciders**: [Who was involved in the decision]

## Context

[What is the situation? What forces are at play? What constraints exist?]

[Reference related ADRs: ADR-NNN, ADR-NNN]

## Decision

We will [chosen approach].

[Core rationale — the specific tradeoff that decided it.]

## Consequences

### What becomes easier
- [Consequence 1]
- [Consequence 2]

### What becomes harder
- [Consequence 1]
- [Consequence 2]

### Technical debt accepted
- [Debt item and why it's acceptable for now]

## Alternatives Considered

### Option A: [Name]
[Description]
- **Pros**: [list]
- **Cons**: [list]
- **Why not**: [specific reason this was rejected]

### Option B: [Name]
[Description]
- **Pros**: [list]
- **Cons**: [list]
- **Why not**: [specific reason this was rejected]

### Option C: Do Nothing
[What happens if we don't act]
- **Pros**: No effort, no risk of change
- **Cons**: [specific problems that persist or worsen]
- **Why not**: [why inaction is unacceptable]

## Review Triggers

- [ ] [Scale threshold]: Revisit if [condition]
- [ ] [Technology change]: Revisit if [condition]
- [ ] [Team change]: Revisit if [condition]
- [ ] [Time-based]: Review by [date]
```

## Handoff

- Hand off to documentation-plan if the ADR reveals gaps in project documentation strategy or onboarding materials.
- Hand off to changelog-design if the decision introduces breaking changes that require consumer communication and migration guides.

## Quality Checks

- [ ] Decision is framed as a clear architectural question with defined scope
- [ ] Context captures constraints, assumptions, and related decisions
- [ ] At least 3 options are evaluated including "do nothing"
- [ ] Each option has pros, cons, risks, and effort assessed
- [ ] Decision rationale explains the specific tradeoff, not just "it's better"
- [ ] Consequences cover both what becomes easier and harder
- [ ] Review triggers define concrete conditions for revisiting the decision
- [ ] ADR is self-contained — a reader can understand it without external context

## Evolution Notes
<!-- Observations appended after each use -->
