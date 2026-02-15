---
name: growth-engineering
department: "herald"
description: "Use when designing growth infrastructure including onboarding funnels, referral mechanics, A/B test instrumentation, and re-engagement loops. Covers activation metrics, funnel mapping, and experimentation design. Do not use for pricing or paywall architecture (use monetization-design) or product copy and naming (use messaging-strategy)."
version: 1
triggers:
  - "onboarding"
  - "activation"
  - "referral"
  - "viral"
  - "A/B test"
  - "funnel"
  - "retention"
  - "churn"
  - "engagement"
  - "sign up"
---

# Growth Engineering

## Purpose

Design the growth engineering infrastructure for a product feature, including onboarding funnel optimization, referral system mechanics, and A/B test instrumentation.

## Scope Constraints

Analyzes product flows, conversion metrics, and experimentation architecture. Does not implement code, modify production systems, or access user data directly.

## Inputs

- Product feature being designed
- Current onboarding flow (if exists)
- Target activation metric ("aha moment")
- User acquisition channels
- Existing analytics infrastructure

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Activation metric defined
- [ ] Step 2: Onboarding funnel mapped
- [ ] Step 3: Onboarding flow designed
- [ ] Step 4: Referral mechanics designed
- [ ] Step 5: A/B test infrastructure instrumented
- [ ] Step 6: Re-engagement loops designed

### Step 1: Define the Activation Metric

Identify the "aha moment" — the action that correlates with long-term retention:
- What specific action indicates the user has gotten value?
- How quickly should a new user reach this action? (target: under 60 seconds for simple products, under 5 minutes for complex ones)
- What's the current activation rate? What's the target?

### Step 2: Map the Onboarding Funnel

Trace the path from first visit to activation:
- **Entry point -> Sign up -> First action -> Aha moment -> Habit formation**
- For each step, measure: conversion rate, drop-off reason, time spent
- Identify the highest-drop-off step (this is your bottleneck)
- Design interventions for the bottleneck step

### Step 3: Design Onboarding Flow

For the onboarding experience:
- **Progressive profiling:** Collect only what's needed now, ask for more later
- **Value before effort:** Show the user what they'll get before asking them to work
- **Checklist pattern:** Visual progress indicator for multi-step onboarding
- **Skip option:** Never trap users in onboarding — always allow skipping
- **Contextual education:** Teach features at the moment of need, not upfront

### Step 4: Design Referral Mechanics

If referral/viral growth is relevant:
- **Incentive structure:** What does the referrer get? What does the invitee get?
- **Share surface:** Where in the product does sharing feel natural (not forced)?
- **Link mechanics:** Deep link to personalized onboarding, attribution tracking
- **K-factor modeling:** Users x invites-per-user x conversion-rate = viral coefficient

### Step 5: Instrument A/B Test Infrastructure

Design the experimentation layer:
- **Feature flag system:** How are experiments gated (LaunchDarkly, Statsig, custom)?
- **Assignment:** How are users bucketed (user ID hash, session-based, geo-based)?
- **Event tracking:** What events must fire for each experiment variant?
- **Statistical rigor:** Sample size calculation, significance threshold, duration estimate

### Step 6: Design Re-engagement Loops

For users who don't activate or who churn:
- **Trigger events:** What signals indicate a user is at risk?
- **Re-engagement channels:** Email, push notification, in-app message
- **Timing:** How soon after drop-off, and how many touchpoints?
- **Content:** What value reminder or incentive brings them back?

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what product is being analyzed, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Output Format

```markdown
# Growth Engineering Plan

## Activation Metric
**"Aha moment":** [Specific action]
**Target time-to-activation:** [X minutes]
**Current rate:** [X%] → **Target rate:** [Y%]

## Onboarding Funnel
| Step | Action | Current Conversion | Target | Intervention |
|------|--------|-------------------|--------|-------------|
| 1 | Landing page visit | — | — | — |
| 2 | Sign up | 12% | 18% | Simplify form |
| 3 | First [action] | 65% | 80% | Guided walkthrough |
| 4 | Aha moment | 40% | 60% | Reduce steps to value |

## Referral System
**Incentive:** [Referrer gets X, invitee gets Y]
**Share surfaces:** [Where in the product]
**Target K-factor:** [X.XX]
**Attribution:** [Link structure and tracking]

## A/B Test Plan
| Experiment | Hypothesis | Metric | Variants | Sample Size | Duration |
|-----------|-----------|--------|----------|-------------|----------|
| Onboarding V2 | Reducing steps increases activation by 20% | Activation rate | 2 | 5,000 | 2 weeks |

## Re-engagement
| Trigger | Channel | Timing | Content |
|---------|---------|--------|---------|
| No login 3 days | Email | Day 3 | Value reminder |
| Incomplete onboarding | Push | Day 1 | Resume prompt |
```

## Handoff

- Hand off to monetization-design if paywall placement or pricing tier decisions surface during growth analysis.
- Hand off to strategist/analytics-design if analytics instrumentation gaps are identified during funnel mapping.

## Quality Checks

- [ ] Activation metric is specific, measurable, and correlated with retention
- [ ] Onboarding funnel has conversion rates (actual or estimated) for each step
- [ ] Referral incentives are balanced (not so generous they attract fraud, not so stingy they don't motivate)
- [ ] A/B tests have statistical rigor (sample size, significance threshold, duration)
- [ ] Re-engagement has defined triggers, timing, and content — not just "send emails"
- [ ] The skip option is available at every onboarding step

## Evolution Notes
<!-- Observations appended after each use -->
