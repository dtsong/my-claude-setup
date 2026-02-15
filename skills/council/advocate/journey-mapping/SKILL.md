---
name: journey-mapping
department: "advocate"
description: "Use when mapping complete user journeys through multi-step flows, onboarding sequences, or feature workflows. Covers entry points, happy paths, alternate paths, error states, friction analysis, and delight opportunities. Do not use for individual component interaction specs (use interaction-design)."
version: 1
triggers:
  - "user flow"
  - "journey"
  - "onboarding"
  - "experience"
  - "workflow"
  - "entry point"
  - "happy path"
  - "user story"
  - "persona"
---

# Journey Mapping

## Purpose

Map complete user journeys with entry points, states, emotions, and decision points to ensure features serve real user needs.

## Scope Constraints

Reads feature descriptions, user stories, and existing screen documentation for journey analysis. Does not modify files or execute code. Does not access user analytics data or production systems directly.

## Inputs

- Feature description or user story
- Target user persona (or enough context to infer one)
- Existing screens/views if modifying an existing flow
- Any known constraints (platform, auth requirements, data dependencies)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Identify the user persona
- [ ] Step 2: Define entry points
- [ ] Step 3: Map the happy path
- [ ] Step 4: Map alternate paths
- [ ] Step 5: Map error and edge paths
- [ ] Step 6: Identify friction points
- [ ] Step 7: Design delight moments

### Step 1: Identify the User Persona

- Who is this for?
- What is their context (new user, power user, admin)?
- What job are they hiring this feature to do?
- What is their emotional state when they arrive (frustrated, curious, task-focused)?

### Step 2: Define Entry Points

How does the user discover or arrive at this feature:
- Direct navigation (sidebar, menu)
- Deep link / URL
- Notification or alert
- Search result
- Redirect from another flow
- First-time onboarding prompt

### Step 3: Map the Happy Path

Walk through step by step:

| Step | Screen/View | User Action | System Response | User Emotion | Notes |
|------|-------------|-------------|-----------------|--------------|-------|
| 1 | ... | ... | ... | ... | ... |

For each step capture:
- What does the user see?
- What action do they take?
- What feedback do they receive?
- What emotion do they feel? (confident, confused, delighted, anxious, neutral)

### Step 4: Map Alternate Paths

- **First-time user vs returning user** — different onboarding needs, remembered preferences
- **Power user shortcuts** — keyboard shortcuts, bulk actions, saved presets
- **Mobile vs desktop** — layout differences, touch vs pointer, reduced screen real estate

### Step 5: Map Error and Edge Paths

- What happens when something fails (API error, validation failure)?
- Empty states (no data yet) — what does the user see and do?
- Permission denied — clear messaging and recovery path
- Network failure mid-flow — data preservation, retry strategy
- Timeout or slow response — loading states, skeleton screens

### Step 6: Identify Friction Points

Where users might:
- Hesitate (unclear next action)
- Get confused (ambiguous UI, unexpected behavior)
- Abandon (too many steps, too much required input)
- Make errors (easy to misclick, unclear consequences)

### Step 7: Design Delight Moments

Where can we exceed expectations:
- Instant feedback (optimistic updates, real-time validation)
- Smart defaults (pre-filled from context, remembered preferences)
- Progressive disclosure (show basics first, reveal complexity on demand)
- Micro-interactions (subtle animations that confirm actions)
- Shortcuts (auto-complete, recent items, suggested actions)

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what feature is being mapped, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Output Format

### Journey Map Table

| Step | Screen/View | User Action | System Response | User Emotion | Notes |
|------|-------------|-------------|-----------------|--------------|-------|
| ... | ... | ... | ... | ... | ... |

### Entry Point Diagram

```
[Entry Point A] ──→ [Step 1] ──→ [Step 2] ──→ ...
[Entry Point B] ──→ [Step 1]
                        ↓
                   [Error Path] ──→ [Recovery]
```

### Friction and Delight Annotations

- **Friction:** [Step X] — [description of friction and mitigation]
- **Delight:** [Step Y] — [description of delight opportunity]

## Handoff

- Hand off to interaction-design if component-level interaction specs are needed for UI elements identified in the journey.
- Hand off to craftsman/pattern-analysis if implementation patterns are needed for the mapped user flows.

## Quality Checks

- [ ] Every step has an emotion annotation
- [ ] Error paths are mapped for each step that can fail
- [ ] Empty states are designed (not just "no data")
- [ ] Mobile path is considered
- [ ] Entry points cover all discovery methods
- [ ] First-time vs returning user differences noted
- [ ] Friction points have mitigation strategies
- [ ] At least one delight moment identified

## Evolution Notes
<!-- Observations appended after each use -->
