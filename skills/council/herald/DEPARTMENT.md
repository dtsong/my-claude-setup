---
name: "Herald Department"
executive: "Herald"
color: "Bronze"
description: "Growth, monetization, onboarding, retention"
---

# Herald Department — Bronze Lens

The Herald's department of focused skills for growth engineering, monetization architecture, and product messaging strategy.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [growth-engineering](growth-engineering/SKILL.md) | Onboarding funnels, referral systems, A/B test infrastructure | default | `onboarding`, `activation`, `referral`, `viral`, `A/B test`, `funnel`, `retention`, `churn`, `engagement` |
| [monetization-design](monetization-design/SKILL.md) | Pricing tiers, subscription architecture, paywall strategy | default | `pricing`, `subscription`, `freemium`, `paywall`, `billing`, `revenue`, `monetization`, `trial`, `upsell` |
| [messaging-strategy](messaging-strategy/SKILL.md) | Product copy, value propositions, feature naming | default | `copy`, `messaging`, `CTA`, `value proposition`, `landing page`, `feature naming`, `microcopy`, `upgrade prompt` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Onboarding flow, activation metric, funnel optimization, referral system, A/B test design | growth-engineering | High |
| Pricing tiers, subscription architecture, paywall placement, billing integration, freemium model | monetization-design | High |
| Product copy, value proposition, feature naming, CTA strategy, microcopy guidelines | messaging-strategy | High |
| Retention strategy, churn reduction, re-engagement loops | growth-engineering | Medium |
| Upgrade prompt copy, cancellation flow messaging, paywall copy | messaging-strategy | Medium |

## Load Directive

Load one specialist skill at a time using the Skill tool. Read the classification logic table to select the appropriate specialist, then invoke the skill. Do not pre-load multiple specialists simultaneously.

## Handoff Protocol

When the specialist skill output reveals issues in another department's domain:
1. Complete the current skill's output format.
2. Note the cross-domain findings in the output.
3. Recommend loading the appropriate department and skill (e.g., "Hand off analytics instrumentation needs to strategist/analytics-design for measurement planning").
