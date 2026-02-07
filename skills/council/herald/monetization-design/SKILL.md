---
name: "Monetization Design"
department: "herald"
description: "Pricing tiers, subscription architecture, and paywall strategy"
version: 1
triggers:
  - "pricing"
  - "subscription"
  - "freemium"
  - "paywall"
  - "billing"
  - "revenue"
  - "monetization"
  - "trial"
  - "upsell"
  - "plan"
---

# Monetization Design

## Purpose

Design the monetization architecture for a product, including pricing tier structure, paywall placement strategy, subscription infrastructure, and upgrade flow design.

## Inputs

- Product feature set (what exists, what's being built)
- Target user segments and willingness-to-pay estimates
- Competitive pricing landscape
- Existing billing infrastructure (Stripe, RevenueCat, etc.)
- App Store / Play Store requirements for in-app purchases

## Process

### Step 1: Define Value Metrics

Identify what users pay for:
- **Usage-based:** API calls, storage, messages, seats
- **Feature-based:** Advanced features, integrations, priority support
- **Outcome-based:** Projects, exports, reports generated
- Choose the metric that scales with the value the user receives

### Step 2: Design Tier Structure

Create a pricing ladder:
- **Free tier:** Generous enough to create habit and demonstrate value
- **Pro tier:** For power users and small teams — the "sweet spot"
- **Enterprise tier:** For organizations — custom pricing, SSO, audit logs
- Apply anchoring: the Pro tier should look like a great deal compared to Enterprise
- Apply decoy effect if appropriate: a tier that makes the target tier look better

### Step 3: Design Paywall Placement

Determine where paywalls appear:
- **Feature gating:** Advanced features locked behind upgrade
- **Usage limits:** Free tier gets N units/month, Pro gets unlimited
- **Soft paywalls:** Show the feature, let them try it, then gate on save/export
- **Hard paywalls:** Block access entirely until upgrade
- **Rule:** Paywalls should appear when users want *more*, not when they want *basic*

### Step 4: Design Upgrade Flow

Create the conversion experience:
- **Trigger moment:** User hits a limit or discovers a locked feature
- **Value presentation:** Show what they'll get (not just what they're paying)
- **Pricing page:** Clear comparison table, recommended tier highlighted
- **Checkout flow:** Minimize steps — ideally 1-2 clicks from trigger to purchase
- **Trial option:** 7-14 day free trial with full access, credit card optional vs required

### Step 5: Design Subscription Infrastructure

Technical architecture:
- **Payment provider:** Stripe, RevenueCat, Paddle, or platform-native (App Store, Play Store)
- **Entitlement system:** How the app checks what the user has access to
- **Webhook handling:** Subscription created, renewed, cancelled, payment failed
- **Grace period:** What happens when payment fails (dunning flow)
- **Platform compliance:** App Store requirements for subscription management

### Step 6: Design Retention Mechanics

Reduce subscription churn:
- **Cancellation flow:** Ask why, offer alternatives (pause, downgrade, discount)
- **Win-back offers:** Discount email after cancellation
- **Annual discount:** Incentivize annual plans (typically 20% discount)
- **Usage reinforcement:** Show users the value they've received ("You saved 10 hours this month")

## Output Format

```markdown
# Monetization Architecture

## Value Metric
**Primary metric:** [What users pay for]
**Scaling:** [How it grows with usage]

## Tier Structure
| | Free | Pro ($X/mo) | Enterprise |
|---|------|------------|------------|
| [Feature 1] | Limited | Unlimited | Unlimited |
| [Feature 2] | No | Yes | Yes |
| [Feature 3] | No | No | Yes |
| Support | Community | Email | Dedicated |

## Paywall Map
| Feature/Limit | Type | Trigger | User Experience |
|--------------|------|---------|-----------------|
| [Feature] | Soft | Usage limit hit | Show result, gate export |
| [Feature] | Hard | Feature tap | Upgrade modal with trial |

## Upgrade Flow
1. User hits [trigger]
2. [Inline upgrade prompt / modal / pricing page]
3. [Plan selection with trial option]
4. [Checkout — X steps]
5. [Success confirmation + unlock]

## Subscription Infrastructure
**Provider:** [Stripe / RevenueCat / etc.]
**Entitlement check:** [How the app verifies access]
**Dunning flow:** [What happens on payment failure]

## Retention Strategy
| Churn Signal | Intervention | Timing |
|-------------|-------------|--------|
| Cancellation initiated | Exit survey + discount offer | Immediate |
| Payment failed | Dunning email sequence | Day 1, 3, 7 |
```

## Quality Checks

- [ ] Free tier is generous enough to demonstrate value and create habit
- [ ] Paywall placement occurs at "want more" moments, not "need basic" moments
- [ ] Upgrade flow is 2 clicks or fewer from trigger to checkout
- [ ] Subscription infrastructure handles renewal, cancellation, and payment failure
- [ ] App Store / Play Store subscription requirements are met (if applicable)
- [ ] Retention mechanics include cancellation flow and win-back strategy

## Evolution Notes
<!-- Observations appended after each use -->
