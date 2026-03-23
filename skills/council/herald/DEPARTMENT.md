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

## Shared Directives

Load Directive, Handoff Protocol, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
