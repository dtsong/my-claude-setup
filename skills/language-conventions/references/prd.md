---
type: project-convention
topic: product requirements document
last_updated: 2026-02-10
token_estimate: ~1200
---

# PRD Template Guide

## Purpose

- Structured requirements that AI agents can execute against
- Quality gates provide copy-pasteable verification commands
- User stories with checkboxed acceptance criteria for progress tracking
- Bridges the gap between product thinking and implementation

## Template

```markdown
# PRD: <Feature Name>

## Overview
<2-3 sentence description of the feature and its purpose. Include the problem
being solved and who benefits.>

## Goals
- <Measurable goal 1 (e.g., "Reduce page load time to < 200ms p99")>
- <Measurable goal 2 (e.g., "> 95% accuracy on classification")>
- <Measurable goal 3 (e.g., "Support 1000 concurrent users")>

## Non-Goals
- <Explicit exclusion 1> -- <brief rationale>
- <Explicit exclusion 2> -- <brief rationale>
- <Explicit exclusion 3> -- <brief rationale>

## Quality Gates

All of these must pass before the feature is considered complete:

- `<test command>` -- All tests pass
- `<lint command>` -- Linting passes
- `<typecheck command>` -- Type checking passes
- `<build command>` -- Build succeeds
- <Manual verification criteria if applicable>

---

## User Stories

### US-001: <Story Title>

**Description:** As a <role>, I want <capability> so that <benefit>.
**Agent:** <Suggested agent/team (optional)>

**Acceptance Criteria:**

- [ ] <Specific, testable criterion>
- [ ] <Specific, testable criterion>
- [ ] <Specific, testable criterion>
- [ ] Tests for <specific behavior>

---

### US-002: <Story Title>

**Description:** As a <role>, I want <capability> so that <benefit>.

**Acceptance Criteria:**

- [ ] <Specific, testable criterion>
- [ ] <Specific, testable criterion>
- [ ] Tests for <specific behavior>

---

### US-003: <Story Title>

**Description:** As a <role>, I want <capability> so that <benefit>.

**Acceptance Criteria:**

- [ ] <Specific, testable criterion>
- [ ] <Specific, testable criterion>
- [ ] Tests for <specific behavior>
```

## Writing Tips

### Goals
- Must be **measurable** -- include numbers, thresholds, or percentages
- Good: "> 95% classification accuracy", "< 200ms p99 latency"
- Bad: "Improve performance", "Make it faster"

### Non-Goals
- As important as goals -- they prevent scope creep
- Include the rationale so future readers understand why
- Good: "Mobile app -- web-first for initial launch, mobile Phase 2"
- Bad: "Out of scope" (no rationale)

### Quality Gates
- Must be **copy-pasteable terminal commands**
- Include both automated checks and manual verification
- Run these before marking any story as complete

### User Stories
- Each story should be **independently implementable**
- Keep stories small enough for one agent or one coding session
- Number sequentially (US-001, US-002) for easy reference in discussions
- Acceptance criteria use checkboxes for progress tracking during implementation

### Acceptance Criteria
- Must be **specific and testable** -- not vague or subjective
- Include a "Tests for..." criterion to ensure test coverage
- Good: "API returns 404 when resource not found"
- Bad: "Error handling works correctly"

## Anti-Patterns

| Anti-Pattern | Problem | Fix |
|-------------|---------|-----|
| Vague goals | Can't verify completion | Add measurable metrics |
| Missing non-goals | Scope creep | Explicitly list exclusions with rationale |
| No quality gate commands | Not enforceable | Add copy-pasteable terminal commands |
| Coupled stories | Can't implement independently | Break into smaller, independent stories |
| Subjective criteria | Can't verify objectively | Rewrite with specific, testable conditions |
| Too many stories | Overwhelming scope | Split into multiple PRDs by phase |
