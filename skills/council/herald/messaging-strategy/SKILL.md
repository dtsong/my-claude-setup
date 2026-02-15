---
name: messaging-strategy
department: "herald"
description: "Use when developing product messaging frameworks including value propositions, feature naming, microcopy guidelines, and CTA strategy. Covers voice and tone definition, conversion copy, and upgrade prompt language. Do not use for pricing architecture or paywall placement (use monetization-design) or onboarding funnels and referral systems (use growth-engineering)."
version: 1
triggers:
  - "copy"
  - "messaging"
  - "CTA"
  - "value proposition"
  - "landing page"
  - "feature naming"
  - "microcopy"
  - "upgrade prompt"
  - "onboarding text"
---

# Messaging Strategy

## Purpose

Develop the product messaging framework, including value propositions, feature naming conventions, microcopy guidelines, and call-to-action strategy.

## Scope Constraints

Analyzes product positioning, audience segments, and conversion copy needs. Does not implement UI changes, modify production content, or access user analytics data directly.

## Inputs

- Product description and key features
- Target audience segments
- Competitive positioning
- Existing brand voice guidelines (if any)
- Key conversion points requiring messaging

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Value proposition defined
- [ ] Step 2: Voice and tone established
- [ ] Step 3: Features and concepts named
- [ ] Step 4: Key conversion copy written
- [ ] Step 5: Microcopy guidelines developed
- [ ] Step 6: Upgrade and paywall copy created

### Step 1: Define Value Proposition

Articulate the core value proposition:
- **One-sentence pitch:** "We help [audience] [achieve outcome] by [mechanism]"
- **Before/after framing:** What's the user's life like before vs after?
- **Unique differentiator:** Why this product over alternatives?
- **Proof points:** Numbers, testimonials, or social proof that back the claim

### Step 2: Establish Voice and Tone

Define how the product speaks:
- **Voice attributes:** (e.g., "confident but not arrogant, helpful but not patronizing")
- **Tone spectrum:** How tone shifts by context (error messages are empathetic, success messages are celebratory, upgrade prompts are enthusiastic but not pushy)
- **Words we use / don't use:** Terminology guidelines

### Step 3: Name Features and Concepts

For each feature or concept that needs a name:
- **Descriptive option:** Says what it does ("Quick Share," "Smart Search")
- **Metaphorical option:** Evokes a concept ("Workspace," "Blueprint," "Spotlight")
- **Evaluation criteria:** Memorable, scannable, not confused with existing terms, works internationally
- **Recommendation:** One name with rationale

### Step 4: Write Key Conversion Copy

For each major conversion point:
- **CTA text:** Action-oriented, benefit-focused ("Start free trial" not "Subscribe")
- **Supporting text:** 1 line that addresses the main objection
- **Social proof:** Nearby proof point ("Join 10,000+ teams")
- **Urgency (if appropriate):** Scarcity or time-sensitivity (use sparingly and honestly)

### Step 5: Develop Microcopy Guidelines

For in-app text:
- **Empty states:** Helpful and actionable, not just "No items found"
- **Error messages:** What happened + what to do next, in human language
- **Loading states:** Set expectations ("Analyzing your data..." not just a spinner)
- **Success states:** Confirm the action and suggest next step
- **Placeholder text:** Helpful examples, not lorem ipsum

### Step 6: Create Upgrade and Paywall Copy

For monetization touchpoints:
- **Feature gate message:** What they're missing + what they'll get
- **Trial prompt:** Low-commitment language ("Try free for 14 days, cancel anytime")
- **Pricing page headlines:** Benefit-oriented tier names
- **Cancellation flow copy:** Empathetic, not guilt-tripping

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what product is being analyzed, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Output Format

```markdown
# Messaging Strategy

## Value Proposition
**One-liner:** [Pitch]
**Before → After:** [Transformation]
**Differentiator:** [Why us]

## Voice and Tone
**Voice:** [3-4 attributes]
**Tone by context:**
| Context | Tone | Example |
|---------|------|---------|
| Onboarding | Welcoming, guiding | "Welcome! Let's set up your workspace." |
| Error | Empathetic, helpful | "Something went wrong. Here's what to try." |
| Upgrade | Enthusiastic, honest | "Unlock unlimited projects — try free for 14 days." |
| Success | Celebratory, brief | "Done! Your changes are live." |

## Feature Names
| Feature | Recommended Name | Rationale |
|---------|-----------------|-----------|
| [Feature] | [Name] | [Why this name works] |

## Key Copy
### [Conversion Point]
**CTA:** [Button text]
**Supporting:** [One-line sub-text]
**Proof:** [Social proof element]

## Microcopy Guidelines
| State | Pattern | Example |
|-------|---------|---------|
| Empty | Action-oriented | "No projects yet. Create your first one →" |
| Error | What happened + what to do | "Couldn't save. Check your connection and try again." |
| Loading | Set expectations | "Generating your report..." |
| Success | Confirm + next step | "Saved! Share it with your team →" |
```

## Handoff

- Hand off to monetization-design if pricing tier structure or paywall placement decisions surface during messaging work.
- Hand off to growth-engineering if onboarding flow optimization or referral system design needs emerge from conversion copy analysis.

## Quality Checks

- [ ] Value proposition passes the "so what?" test (clear benefit, not just feature description)
- [ ] Feature names are tested for clarity (would a new user understand this?)
- [ ] CTA copy is action-oriented and benefit-focused (not just "Submit" or "Continue")
- [ ] Error messages explain what happened AND what to do next
- [ ] Upgrade copy focuses on what they'll get, not what they're missing
- [ ] Voice and tone guidelines include examples for at least 4 contexts

## Evolution Notes
<!-- Observations appended after each use -->
