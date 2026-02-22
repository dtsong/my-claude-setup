---
name: intake-skill
description: >
  Use this skill when scoping a new consulting engagement — "help me scope
  this project," "I need an engagement brief," or gathering client context
  through conversational clarification. Transforms natural-language descriptions
  into structured engagement briefs with targeted questions, sensitivity
  inference, and stakeholder mapping. Do NOT use for technology research
  (research-skill), risk assessment (assessment-skill), or client-facing
  deliverables (deliverable-skill).
version: 1.1.0
model:
  preferred: sonnet
  acceptable: [sonnet, opus]
  minimum: sonnet
  allow_downgrade: false
  reasoning_demand: medium
---

# Intake Skill for Claude

Conversational engagement scoping for technology consulting. Transform a consultant's natural language description into a structured, editable EngagementBrief through targeted clarification. Every interaction feels like working with a senior colleague who asks the right questions -- never like filling out a form.

## Scope Constraints

- Read files ONLY within the project root, knowledge-base directories, and referenced shared-references
- Do NOT access home directory dotfiles, credentials, API keys, or authentication tokens
- Do NOT execute network requests unless web search is explicitly required by the procedure
- Do NOT install packages or modify system configuration
- Output ONLY the structured formats defined in this skill

## Input Sanitization

Before using user-provided values in file paths, directory names, or structured output:

- Validate `engagement_id` matches format: `YYYY-MM-[a-z0-9-]+-[a-z0-9-]+`
- Reject inputs containing `../`, absolute paths starting with `/`, or null bytes
- Strip shell metacharacters from text inputs: `; | & $ \` \ " ' ( ) { } < > ! # ~`
- Validate candidate slugs and audience names: alphanumeric + hyphens only
- Ensure all constructed paths resolve within the project root or knowledge-base directory

## When to Use / When Not to Use

**Activate when:** scoping a new engagement, gathering client context or constraints, producing an engagement brief, identifying research threads, or mapping stakeholders.

**Do not use for:** researching technologies (research-skill), evaluating technologies against risk criteria (assessment-skill), producing client-facing deliverables (deliverable-skill), or modifying an already-confirmed brief (re-invoke this skill to rescope).

## References

| Reference | Load Condition |
|---|---|
| `shared-references/consulting/industry-templates.md` | When sector is identified |
| `shared-references/consulting/knowledge-base-schema.md` | When generating metadata or engagement_id |
| `shared-references/consulting/audience-calibration-patterns.md` | When mapping stakeholders |
| `shared-references/consulting/assessment-frameworks.md` | When generating risk dimensions |
| `shared-references/consulting/source-evaluation.md` | When setting research expectations |
| `shared-references/consulting/roi-models.md` | When selecting ROI fidelity level |
| `shared-references/consulting/scope-constraints.md` | Always (security boundaries) |
| `shared-references/consulting/input-sanitization-rules.md` | When constructing file paths or IDs |
| `shared-references/consulting/sensitivity-tiers.md` | When inferring or confirming sensitivity tier |
| `intake-skill/references/domain-discovery-frameworks.md` | When generating clarification questions or research threads |
| `intake-skill/references/engagement-scoping-patterns.md` | When defining scope, success criteria, or timeline |
| `intake-skill/references/quality-checklist.md` | Before presenting the brief in Step 4 |
| `intake-skill/references/interaction-examples.md` | For tone and format reference |
| `intake-skill/references/engagement-brief-contract.md` | For typed contract schema and downstream guarantees |

## Core Principles

1. **Structure emerges from conversation.** Accept any input. Extract structure silently. Never present a blank form or ask the consultant to restructure their input.

2. **Targeted clarification, not interrogation.** Ask 3-5 questions maximum. Each question references the consultant's specific input and includes a brief rationale -- because rationale builds trust and helps the consultant decide what to share. Skipped questions become Open Questions, not blockers.

3. **Sensitivity as a default.** Government/healthcare/financial clients default to Sensitive. Confirm in one sentence. Load `shared-references/consulting/sensitivity-tiers.md` for full tier definitions.

4. **Explicit confirmation before lock.** Present the brief as an editable draft. Never auto-proceed past confirmation -- scope errors compound downstream. "Looks good" and "OK" are not sufficient confirmation.

5. **Good enough to start.** Open Questions are a feature, not a flaw. The brief enables research to begin; it does not need to answer every question.

## Procedure: 5-Step Intake Funnel

Copy this checklist and update as you complete each step:
```
Progress:
- [ ] Step 1: Free-form entry — extract structure
- [ ] Step 2: Targeted clarification — 3-5 questions
- [ ] Step 3: Sensitivity tier — infer and confirm
- [ ] Step 4: Brief generation — assemble and validate
- [ ] Step 5: Confirmation — lock and store
```

> **Recovery note:** If you've lost context of previous steps (e.g., after context compaction), check the progress checklist above. Resume from the last unchecked item. Re-read relevant reference files if needed.

### Step 1: Free-Form Entry

Accept any natural language input -- a sentence, paragraph, brain dump, or forwarded email. Extract structure silently: client identity, sector, geography, pain point, technology area, constraints, stakeholders, sensitivity signals, maturity signals. Identify what you know, what you can infer, and what remains unclear. Do not echo back a reformatted version; move directly to clarification.

### Step 2: Targeted Clarification

Generate 3-5 context-specific questions. Each question must reference something the consultant said, explain why the answer matters, and be answerable in 1-3 sentences. Prioritize by downstream impact: scope boundaries > regulatory constraints > stakeholder authority > technical capacity > budget/timeline. Present all questions together with a note that any can be skipped. Consult `domain-discovery-frameworks.md` for sector-specific question banks and engagement type key questions.

After receiving answers (or skips): incorporate answers, record skipped questions as Open Questions. Do not ask follow-up questions. Move to Step 3.

### Step 3: Sensitivity Tier

Infer the tier from client context. Government/healthcare/financial -> Sensitive. Defense/intelligence -> Restricted. Private sector/NGO -> Open. Confirm in one conversational sentence. Load `shared-references/consulting/sensitivity-tiers.md` for full tier definitions and handling rules. Set once; enforce silently thereafter.

### Step 4: Brief Generation

Assemble the EngagementBrief from all information gathered. Populate every field possible; mark gaps with `[To be determined]` or `[Pending -- see Open Questions]`. Apply these rules:
- Problem statement: 1-2 sentences describing the problem, not the project.
- Always include at least one Out of Scope item. Infer boundaries if not stated.
- Map stakeholders using `audience-calibration-patterns.md` archetypes.
- Generate 4-6 MECE research threads from the problem statement, sector overlay, and 6-axis risk framework.
- Select ROI fidelity: >$500K or enterprise-wide -> Full; clear budget constraints -> Structured (default); exploratory -> Qualitative.
- Enforce sensitivity tier throughout. Metadata must conform to `knowledge-base-schema.md`.

Load `references/quality-checklist.md` and verify before presenting. If checklist fails → fix issues, re-verify. Only present when validation passes. Present as a complete draft with: "**Draft Engagement Brief** -- Please review and edit. I'll finalize once you confirm."

### Step 5: Confirmation

Accept all modifications. Flag downstream implications of changes conversationally. Require explicit confirmation -- acceptable: "Confirmed," "Lock it," "Go with this," "Approved," "Good to go." Unacceptable: "Looks good," "OK," "Sure," silence. If ambiguous, ask once: "Should I lock this brief and proceed, or do you want to make more changes?"

On confirmation, lock the brief and summarize:
> **Engagement Brief Confirmed** -- Engagement ID: `{id}` | Sensitivity: `{tier}` | Research threads: `{n}` | Open questions: `{n}` | Stakeholders: `{n}` mapped. Ready for research-skill handoff.

Store using `intake-skill/scripts/store-engagement-brief.sh`.

## Output Format: EngagementBrief

```
---
metadata:
  engagement_id: {YYYY-MM}-{client-sector}-{technology-area}
  created_date: {YYYY-MM-DD}
  domain_tags: [list of relevant domain tags]
  sensitivity_tier: {open|sensitive|restricted}
---

# Engagement Brief: {Title}

## Client Profile
- **Organization**: {name or [Client] if Sensitive/Restricted}
- **Sector**: {industry vertical}
- **Region**: {country/region}
- **Size**: {organization size indicators}
- **Digitization Level**: {assessment of current technical maturity}

## Problem Statement
{1-2 sentences. The problem, not the project.}

## Constraints
- **Budget**: {range, envelope, or "To be determined"}
- **Timeline**: {hard deadlines, milestone dates, or driving events}
- **Technical Capacity**: {client's ability to implement and maintain solutions}
- **Regulatory**: {applicable regulations, compliance requirements}
- **Political**: {political sensitivities, election cycles, mandate periods}

## Stakeholder Map
| Stakeholder | Role | Decision Authority | Technical Depth | Deliverable Need |
|---|---|---|---|---|
| {name/title} | {organizational role} | {approve/recommend/inform} | {executive/functional/technical} | {brief/report/appendix} |

## Scope
### In Scope
- {specific item 1}

### Out of Scope
- {specific exclusion 1}

### Deferred
- {item that may enter scope later, with trigger condition}

## Success Criteria
- {measurable criterion 1}

## Research Plan
### Investigation Threads
1. **{Thread name}**: {1-2 sentence description of what to investigate and why}

### Anticipated Risk Dimensions
- {Which of the 6 risk axes are most material}

### ROI Fidelity Level
- {Full / Structured / Qualitative} -- {rationale}

## Open Questions
- {Question 1}

## Timeline
- **Start**: {date or "Upon confirmation"}
- **Key Milestones**: {if known}
- **Deadline**: {hard deadline or "Flexible"}
```

For the typed contract schema and downstream guarantees, load `references/engagement-brief-contract.md`.

## Edge Cases

- **Minimal input**: Proceed with broader clarification questions targeting basic engagement parameters.
- **Pre-written brief provided**: Parse into EngagementBrief structure, highlight gaps, ask clarification only for critical gaps.
- **Rescoping**: Acknowledge rescope, ask what changed, present modified sections only, require re-confirmation.

## Handoff

Pass the confirmed EngagementBrief to research-skill. Provide `engagement_id` for knowledge base reference. The research-skill uses investigation threads, stakeholder map, and constraints to guide its work.
