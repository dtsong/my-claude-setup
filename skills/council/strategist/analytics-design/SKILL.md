---
name: analytics-design
department: "strategist"
description: "Use when planning measurement strategy for a feature or product area. Covers metrics hierarchy design, event taxonomy, funnel instrumentation, A/B test framework, and data pipeline planning. Do not use for feature prioritization scoring (use impact-estimation) or MVP scope definition (use mvp-scoping)."
version: 1
triggers:
  - "analytics"
  - "telemetry"
  - "tracking"
  - "A/B test"
  - "funnel"
  - "metric"
  - "experiment"
  - "instrumentation"
---

# Analytics Design

## Purpose

Design a comprehensive measurement strategy including metrics hierarchy, event taxonomy, funnel instrumentation, and A/B test framework to ensure features can be evaluated with data.

## Scope Constraints

Produces measurement plans, event schemas, and experimentation frameworks as documentation artifacts. Does not implement tracking code, configure analytics platforms, or access production data. All outputs are design specifications for engineering implementation.

## Inputs

- Feature or product area to instrument
- Business goals and key questions to answer
- Existing analytics infrastructure (tools, event patterns, naming conventions)
- Privacy requirements and data retention policies
- Target user segments for experimentation

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Metrics hierarchy defined
- [ ] Step 2: Event taxonomy designed
- [ ] Step 3: Event properties specified
- [ ] Step 4: Funnel instrumentation planned
- [ ] Step 5: A/B test framework designed
- [ ] Step 6: Success criteria defined
- [ ] Step 7: Data pipeline planned

### Step 1: Define Key Metrics Hierarchy

Build a three-tier metrics structure:
- **North Star Metric:** The single metric that best captures the value delivered to users (e.g., weekly active users completing core action)
- **Leading Indicators:** Metrics that predict movement in the North Star (e.g., activation rate, feature adoption, session frequency)
- **Guardrail Metrics:** Metrics that must NOT degrade (e.g., page load time, error rate, unsubscribe rate, support ticket volume)

For each metric, define:
- Precise definition (what counts, what doesn't)
- Data source and calculation method
- Current baseline (if known)
- Target threshold

### Step 2: Design Event Taxonomy

Establish a consistent naming convention:
- **Category:** Feature area (e.g., `editor`, `dashboard`, `onboarding`)
- **Action:** User action or system event (e.g., `clicked`, `viewed`, `completed`, `errored`)
- **Label:** Specific element or variant (e.g., `save_button`, `sidebar_nav`, `dark_mode`)
- **Value:** Numeric value if applicable (e.g., duration, count, score)

Naming rules:
- Use snake_case for all event names
- Format: `category.action.label` (e.g., `editor.clicked.save_button`)
- Keep consistent across platforms (web, mobile, API)
- Version events when schema changes (`v2.editor.clicked.save_button`)

### Step 3: Specify Event Properties

For each trackable interaction, define:

| Event Name | Properties | Type | Required | Description |
|------------|-----------|------|----------|-------------|
| `feature.action.label` | user_id | string | yes | Anonymous user identifier |
| | session_id | string | yes | Current session |
| | timestamp | ISO 8601 | yes | Event time |
| | [custom props] | ... | ... | Feature-specific data |

Include:
- Common properties (present on every event)
- Feature-specific properties
- Context properties (page, referrer, device, viewport)

### Step 4: Plan Funnel Instrumentation

For each key user flow:
- Define funnel stages (each stage = a specific event)
- Identify drop-off measurement points between stages
- Design recovery tracking (users who drop off then return)
- Plan cohort segmentation (new vs returning, plan type, entry source)

```
[Stage 1: View] → [Stage 2: Engage] → [Stage 3: Convert] → [Stage 4: Retain]
     100%              65%                  30%                  20%
         ↓ 35% drop        ↓ 35% drop          ↓ 10% drop
    [Exit survey?]    [Tooltip help?]      [Follow-up email?]
```

### Step 5: Design A/B Test Framework

For each planned experiment:
- **Experiment name:** Descriptive, following convention (e.g., `onboarding_v2_simplified_flow`)
- **Hypothesis:** "If we [change], then [metric] will [improve/decrease] because [reason]"
- **Variants:** Control (A) and treatment(s) (B, C...)
- **Allocation:** Percentage split per variant (typically 50/50 for two variants)
- **Sample size:** Calculate minimum detectable effect (MDE) with 80% power, 95% significance
- **Duration:** Estimated time to reach sample size based on traffic
- **Guardrails:** Metrics to monitor for negative effects during the test

### Step 6: Define Success Criteria

For each experiment:
- **Primary metric:** The one metric that determines success
- **Minimum detectable effect:** The smallest improvement worth shipping (e.g., +5% conversion)
- **Statistical significance threshold:** Typically p < 0.05
- **Practical significance:** Is the effect size meaningful even if statistically significant?
- **Decision framework:**
  - Significant positive result → Ship to 100%
  - Significant negative result → Revert and analyze
  - No significant result → Extend test or abandon
  - Mixed results (primary up, guardrail down) → Investigate and decide

### Step 7: Plan Data Pipeline and Storage

- **Collection method:** Client-side SDK, server-side events, or hybrid
- **Transport:** Real-time streaming vs batch upload
- **Storage:** Analytics warehouse, time-series database, or SaaS platform
- **Retention:** How long to keep raw events vs aggregated data
- **Access:** Who can query the data, dashboards to create
- **Privacy:** PII handling, consent tracking, GDPR/CCPA compliance

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct the feature area and measurement goals, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Output Format

### Metrics Hierarchy

```
North Star: [Metric Name]
  ├── Leading: [Indicator 1]
  ├── Leading: [Indicator 2]
  ├── Leading: [Indicator 3]
  ├── Guardrail: [Metric A] (must not decrease)
  └── Guardrail: [Metric B] (must stay below threshold)
```

### Event Catalog

| Event Name | Description | Properties | Trigger |
|------------|-------------|-----------|---------|
| `category.action.label` | ... | `{prop1, prop2, ...}` | User clicks X |
| ... | ... | ... | ... |

### Funnel Diagram

```
[Stage 1] ──→ [Stage 2] ──→ [Stage 3] ──→ [Stage 4]
  100%           ___%           ___%           ___%
```

### A/B Test Plan

| Experiment | Hypothesis | Variants | Sample Size | Duration | Primary Metric |
|------------|-----------|----------|-------------|----------|----------------|
| ... | If..., then... | A/B | ... | ... weeks | ... |

## Handoff

- Hand off to impact-estimation if analytics findings reveal features that need RICE scoring for prioritization.
- Hand off to mvp-scoping if measurement design surfaces scope questions about which features to instrument first.

## Quality Checks

- [ ] North star metric is clearly defined with calculation method
- [ ] Event taxonomy follows consistent naming convention
- [ ] All key user interactions have corresponding events
- [ ] Funnels have defined stages with drop-off measurement
- [ ] A/B tests have hypotheses, sample size calculations, and duration estimates
- [ ] Success criteria include both statistical and practical significance
- [ ] Privacy and data retention requirements addressed
- [ ] Guardrail metrics defined for each experiment

## Evolution Notes
<!-- Observations appended after each use -->
