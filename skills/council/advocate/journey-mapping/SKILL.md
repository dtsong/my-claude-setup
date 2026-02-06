---
name: "Journey Mapping"
department: "advocate"
description: "Map complete user journeys with entry points, states, emotions, and decision points"
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

## Inputs

- Feature description or user story
- Target user persona (or enough context to infer one)
- Existing screens/views if modifying an existing flow
- Any known constraints (platform, auth requirements, data dependencies)

## Process

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
