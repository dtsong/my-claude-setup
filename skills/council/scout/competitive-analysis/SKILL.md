---
name: "competitive-analysis"
department: "scout"
description: "Use when designing features that exist in competing products or analyzing prior art in the market. Covers feature mapping, UX evaluation, technical trade-off assessment, and differentiation opportunity identification. Do not use for evaluating individual libraries (use library-evaluation) or assessing technology maturity (use technology-radar)."
version: 1
triggers:
  - "competitive"
  - "alternative"
  - "comparison"
  - "prior art"
  - "competitor"
  - "benchmark"
  - "market research"
---

# Competitive Analysis

## Purpose

Map the landscape of competing products and prior art to identify proven patterns, differentiation opportunities, and lessons learned before building.

## Scope Constraints

- Analyzes products and services at the feature and UX level, not individual code libraries.
- Focuses on identifying patterns, gaps, and differentiation — not producing marketing materials.
- Does not perform deep technical benchmarking; flag performance concerns for handoff.

## Inputs

- Feature or product area to analyze
- Known competitors or similar products (or let the process discover them)
- Target user segment
- Specific aspects to compare (if any focus areas are known)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Step 1: Identify Competing Products or Prior Art

- Direct competitors (same problem, same audience)
- Indirect competitors (different approach to the same underlying need)
- Prior art in adjacent domains (similar interaction patterns in different contexts)
- Open source alternatives
- Note market positioning of each (enterprise vs indie, free vs paid, general vs niche)

### Step 2: Map Feature Sets

For each competitor, catalog:
- Core features (what they do well)
- Secondary features (nice-to-haves they include)
- Missing features (notable gaps)
- Unique features (things only they offer)
- Recent additions (direction they're heading)

### Step 3: Evaluate UX and Interaction Approaches

For each competitor:
- Onboarding flow (how new users get started)
- Primary interaction model (how users accomplish the core task)
- Information architecture (how content and features are organized)
- Visual design language (aesthetic, density, tone)
- Notable UX innovations or frustrations

### Step 4: Assess Technical Architecture Trade-offs

Where visible or inferable:
- Client-side vs server-side rendering approach
- Real-time vs polling vs static data
- Offline support and data sync strategy
- API design philosophy (REST, GraphQL, RPC)
- Performance characteristics (load time, responsiveness)

### Step 5: Identify Gaps and Differentiation Opportunities

- Features competitors lack that users request (check forums, reviews, feature requests)
- UX frustrations users report across competitors
- Underserved user segments
- Technical advantages your stack enables
- Pricing or access model gaps

### Step 6: Synthesize Lessons Learned

- What patterns are proven across multiple competitors (safe to adopt)?
- What approaches have competitors tried and abandoned (learn from their mistakes)?
- What is table stakes vs differentiating in this space?
- What would users switch for?

### Progress Checklist

- [ ] Step 1: Competitors identified
- [ ] Step 2: Feature sets mapped
- [ ] Step 3: UX approaches evaluated
- [ ] Step 4: Technical trade-offs assessed
- [ ] Step 5: Gaps and opportunities identified
- [ ] Step 6: Lessons synthesized

> **Compaction resilience:** If context was compacted, re-read this SKILL.md and check the Progress Checklist for completed steps before continuing.

## Handoff

- If technical architecture concerns surface during competitor assessment, recommend loading architect/system-design for deeper analysis.
- If user research gaps are identified, recommend loading advocate/user-story for user-centered exploration.

## Output Format

### Feature Comparison Matrix

| Feature | Our Product | Competitor A | Competitor B | Competitor C |
|---------|-------------|-------------|-------------|-------------|
| Feature 1 | ... | ... | ... | ... |
| Feature 2 | ... | ... | ... | ... |
| ... | ... | ... | ... | ... |

### UX Approach Summary

| Aspect | Competitor A | Competitor B | Competitor C |
|--------|-------------|-------------|-------------|
| Onboarding | ... | ... | ... |
| Core interaction | ... | ... | ... |
| Information architecture | ... | ... | ... |
| Visual style | ... | ... | ... |

### Differentiation Opportunities

1. **[Opportunity]** — [Description and rationale]
2. **[Opportunity]** — [Description and rationale]
3. **[Opportunity]** — [Description and rationale]

### Lessons from Prior Art

- **Adopt:** [Pattern] — proven across [competitors], users expect it
- **Avoid:** [Pattern] — [competitor] tried this and [outcome]
- **Innovate:** [Area] — no competitor has solved this well yet

## Quality Checks

- [ ] At least 3 competitors or prior art examples analyzed
- [ ] Feature sets mapped comprehensively (not just top-level)
- [ ] UX approaches evaluated with specific observations
- [ ] Technical trade-offs assessed where inferable
- [ ] User pain points sourced from real feedback (reviews, forums)
- [ ] Differentiation opportunities are actionable
- [ ] Table stakes vs differentiators clearly distinguished
- [ ] Lessons include both what to adopt and what to avoid

## Evolution Notes
<!-- Observations appended after each use -->
