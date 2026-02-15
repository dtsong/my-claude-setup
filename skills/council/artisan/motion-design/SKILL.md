---
name: motion-design
department: "artisan"
description: "Use when designing the motion language for a feature or system. Covers transition specs, micro-interaction definitions, choreography principles, performance constraints, and reduced-motion alternatives. Do not use for visual design critique (use visual-audit) or design token architecture (use design-system-architecture)."
version: 1
triggers:
  - "animation"
  - "transition"
  - "motion"
  - "easing"
  - "micro-interaction"
  - "reduced-motion"
  - "choreography"
  - "loading"
  - "skeleton"
---

# Motion Design

## Purpose

Design the motion language for a feature or system, including transition specs, micro-interaction definitions, choreography principles, and reduced-motion alternatives.

## Scope Constraints

Reads existing animation code, CSS transitions, and motion specifications for analysis. Does not modify source files or execute animations. Does not generate production animation code directly.

## Inputs

- Feature or component requiring motion design
- Existing animation patterns in the project (if any)
- Performance constraints (target FPS, device capabilities)
- Accessibility requirements (prefers-reduced-motion support)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Identify motion opportunities
- [ ] Step 2: Define motion principles
- [ ] Step 3: Spec each animation
- [ ] Step 4: Design choreography
- [ ] Step 5: Reduced-motion alternatives
- [ ] Step 6: Performance considerations

### Step 1: Identify Motion Opportunities

Catalog where motion adds meaning:
- **State transitions:** Loading to loaded, collapsed to expanded, hidden to visible
- **Navigation transitions:** Screen push/pop, modal present/dismiss, tab switch
- **Feedback responses:** Button press, form submission, error shake, success check
- **Attention guidance:** New item appears, notification badge, scroll-to-target
- **Data changes:** List reorder, item add/remove, value count-up

### Step 2: Define Motion Principles

Establish the motion language for this project:
- **Duration scale:** Micro (100ms), short (200ms), medium (300ms), long (500ms)
- **Easing curves:** Enter (ease-out), exit (ease-in), standard (ease-in-out)
- **Stagger:** Delay between sequential items (50-100ms per item, max 5 items)
- **Distance:** How far elements travel relative to their size

### Step 3: Spec Each Animation

For each motion opportunity, define:
- **Property:** What changes (opacity, transform, height, color)
- **Duration:** How long (from the duration scale)
- **Easing:** Which curve (from the easing set)
- **Delay:** When it starts relative to the trigger
- **Direction:** Where it moves from/to

### Step 4: Design Choreography

For multi-element transitions:
- **Entrance order:** What appears first, second, third
- **Stagger timing:** Delay between each element
- **Shared elements:** Elements that morph between states
- **Exit choreography:** Reverse of entrance, or distinct exit pattern

### Step 5: Reduced-Motion Alternatives

For every animation, define the prefers-reduced-motion alternative:
- **Instant transitions:** Replace motion with opacity crossfade
- **Remove parallax:** Static positioning instead
- **Simplify choreography:** Single fade-in instead of staggered entrance
- **Keep functional animation:** Loading spinners stay (they communicate state)

### Step 6: Performance Considerations

Verify motion feasibility:
- **Composite-only properties:** Prefer transform and opacity (GPU-accelerated)
- **Avoid layout thrash:** Don't animate width, height, top, left
- **will-change hints:** Add for elements that will animate
- **60fps budget:** Each frame must complete in <16.6ms

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what feature is being designed, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Output Format

```markdown
# Motion Design Specification

## Motion Principles
| Property | Value | Usage |
|----------|-------|-------|
| Duration (micro) | 100ms | Hover, focus |
| Duration (short) | 200ms | Expand, collapse |
| Duration (medium) | 300ms | Page transitions |
| Ease (enter) | cubic-bezier(0, 0, 0.2, 1) | Elements appearing |
| Ease (exit) | cubic-bezier(0.4, 0, 1, 1) | Elements leaving |
| Stagger | 50ms | List items |

## Animation Specs

### [Component/Interaction Name]
**Trigger:** [User action or state change]
**Property:** [What changes]
**From → To:** [Start value → End value]
**Duration:** [From scale]
**Easing:** [From set]
**Reduced motion:** [Alternative]

## Choreography
### [Transition Name]
1. [Element] fades in at 0ms (200ms, ease-out)
2. [Element] slides up at 50ms (200ms, ease-out)
3. [Element] fades in at 100ms (200ms, ease-out)

## Reduced Motion Summary
| Animation | Full Motion | Reduced Motion |
|-----------|------------|----------------|
| Page enter | Slide + fade | Instant fade |
| List stagger | Staggered slide-up | Single fade |
| Loading | Spinner | Spinner (kept) |
```

## Handoff

- Hand off to visual-audit if motion design reveals visual hierarchy issues needing interface-level critique.
- Hand off to design-system-architecture if animation tokens (durations, easings) need integration into the design token system.

## Quality Checks

- [ ] Every animation has a purpose (communicates state change, guides attention, or provides feedback)
- [ ] Duration and easing values come from the defined scale, not arbitrary values
- [ ] Every animation has a prefers-reduced-motion alternative
- [ ] Animations use composite-only properties (transform, opacity) where possible
- [ ] Stagger timing doesn't exceed 5 items (cap the stagger, fade the rest)
- [ ] No animation exceeds 500ms (users perceive delays >400ms as laggy)

## Evolution Notes
<!-- Observations appended after each use -->
