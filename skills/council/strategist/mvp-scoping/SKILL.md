---
name: "MVP Scoping"
department: "strategist"
description: "[Council] MoSCoW prioritization and value-effort matrix for defining minimum viable scope. Used during council/academy deliberation only."
version: 1
triggers:
  - "MVP"
  - "scope"
  - "priority"
  - "phase"
  - "launch"
  - "v1"
  - "minimum viable"
  - "cut scope"
  - "roadmap"
---

# MVP Scoping

## Purpose

Define the smallest viable scope that delivers maximum learning and value, using MoSCoW prioritization and value-effort analysis to draw a clear MVP cut line.

## Inputs

- Full list of proposed features and capabilities
- Target users and their primary jobs-to-be-done
- Timeline or launch constraints
- Team capacity (number of developers, available time)
- Key assumptions to validate
- Business goals or success criteria

## Process

### Step 1: Enumerate All Proposed Features

- List every feature, capability, and requirement mentioned
- Break large features into independently shippable increments
- Include both functional features and non-functional requirements (performance, security, accessibility)
- Note the source of each request (user research, stakeholder, assumption, competitive parity)

### Step 2: Apply MoSCoW Classification

For each feature, classify:
- **Must have** — Without this, the product doesn't work or solve the core problem. Launch blocker.
- **Should have** — Important but the product is usable without it. Ship soon after launch.
- **Could have** — Nice to have, improves experience but not essential. Include if time permits.
- **Won't have (this time)** — Explicitly out of scope for this phase. Documented for future.

Decision test: "If we launched without this, would users still get value from the core use case?"

### Step 3: Estimate Effort for Each Feature

Use T-shirt sizing:
- **XS** — Less than half a day. Trivial change, well-understood.
- **S** — Half day to one day. Small feature, low complexity.
- **M** — Two to three days. Moderate complexity, some unknowns.
- **L** — One week. Significant feature, multiple components.
- **XL** — Two or more weeks. Large feature, many unknowns, high complexity.

Flag any estimates with high uncertainty for spike/prototype first.

### Step 4: Estimate Value/Impact for Each Feature

Rate each feature:
- **High** — Directly enables the core use case or removes a major friction point. Users would choose this product because of it.
- **Medium** — Improves the experience meaningfully. Users would notice if it were missing.
- **Low** — Polish or convenience. Users wouldn't choose or reject the product based on this.

Include rationale for each rating tied to user needs or business goals.

### Step 5: Plot Value-Effort Matrix

Arrange features into four quadrants:

```
  High Value │
             │  Strategic Bets    Quick Wins
             │  (High value,      (High value,
             │   High effort)      Low effort)
  ───────────┼──────────────────────────────
             │  Avoid             Fill-ins
             │  (Low value,       (Low value,
             │   High effort)      Low effort)
             │
             └──────────────────────────────
               High Effort ←──→ Low Effort
```

- **Quick Wins** (high value, low effort) — Do first
- **Strategic Bets** (high value, high effort) — Plan carefully, consider phasing
- **Fill-ins** (low value, low effort) — Include if time permits
- **Avoid** (low value, high effort) — Cut from MVP

### Step 6: Define the MVP Cut Line

- Start with all Must Haves (these are non-negotiable)
- Add Quick Wins (high value, low effort)
- Evaluate Strategic Bets for phased inclusion (can the first phase be smaller?)
- Total the effort and compare against available capacity
- Adjust until the MVP fits within timeline constraints
- Everything below the cut line becomes v1.1 or v2

### Step 7: Plan Phased Roadmap

- **v1 (MVP):** [Features above the cut line] — [Timeline]
- **v1.1 (Fast Follow):** [Should haves and remaining quick wins] — [Timeline]
- **v2 (Next Major):** [Strategic bets and could haves] — [Timeline]
- **Future:** [Won't haves and speculative features] — No timeline

Include milestones and key decision points between phases.

## Output Format

### MoSCoW Table

| Feature | MoSCoW | Effort | Value | Quadrant | Phase |
|---------|--------|--------|-------|----------|-------|
| ... | Must | S | High | Quick Win | v1 |
| ... | Should | M | Medium | Fill-in | v1.1 |
| ... | Could | XL | High | Strategic Bet | v2 |
| ... | Won't | L | Low | Avoid | Future |

### Value-Effort Matrix

```
[Visual diagram with features plotted in quadrants]
```

### MVP Feature Set (v1)

- [ ] Feature A (Must, S)
- [ ] Feature B (Must, M)
- [ ] Feature C (Should, XS) — Quick Win
- **Total estimated effort:** [sum]
- **MVP cut line rationale:** [why these features and not others]

### Phase Roadmap

| Phase | Features | Effort | Milestone | Decision Point |
|-------|----------|--------|-----------|----------------|
| v1 | ... | ... | Launch | Validate core assumption |
| v1.1 | ... | ... | ... | Review user feedback |
| v2 | ... | ... | ... | Evaluate expansion |

## Quality Checks

- [ ] All proposed features enumerated (nothing forgotten)
- [ ] MoSCoW classification justified with user-need rationale
- [ ] Effort estimates use consistent T-shirt sizing
- [ ] Value ratings tied to specific user needs or business goals
- [ ] Value-effort matrix plotted with all features
- [ ] MVP cut line is explicitly defined and justified
- [ ] Phased roadmap includes milestones and decision points
- [ ] Won't-haves are documented (not just deleted)

## Evolution Notes
<!-- Observations appended after each use -->
