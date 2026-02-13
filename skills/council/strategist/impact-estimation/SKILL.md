---
name: "Impact Estimation"
department: "strategist"
description: "[Council] RICE scoring framework for evidence-based feature prioritization. Used during council/academy deliberation only."
version: 1
triggers:
  - "impact"
  - "effort"
  - "ROI"
  - "value"
  - "metric"
  - "KPI"
  - "prioritize"
  - "RICE"
  - "scoring"
---

# Impact Estimation

## Purpose

Apply RICE scoring to prioritize features and initiatives based on quantified reach, impact, confidence, and effort, replacing gut-feel prioritization with a repeatable framework.

## Inputs

- List of features or initiatives to prioritize
- User base size and segmentation (for Reach estimation)
- Available team capacity (for Effort calibration)
- Business goals and success metrics
- Any existing data (usage analytics, user research, market data)

## Process

### Step 1: Define RICE Criteria

Calibrate the scoring dimensions for this project:
- **Reach:** How many users or customers will this affect per quarter? Use real numbers where possible (e.g., "500 active users" not "many users"). For internal tools, count affected team members.
- **Impact:** How much will each affected user benefit?
  - 3 = Massive (transforms their workflow, solves a critical pain point)
  - 2 = High (significant improvement, removes notable friction)
  - 1 = Medium (noticeable improvement, nice to have)
  - 0.5 = Low (minor improvement, slight convenience)
  - 0.25 = Minimal (barely noticeable, edge case benefit)
- **Confidence:** How sure are we about Reach and Impact estimates?
  - 100% = High confidence (backed by data, user research, or direct requests)
  - 80% = Medium confidence (strong signals but some assumptions)
  - 50% = Low confidence (educated guess, limited data)
  - 20% = Moonshot (speculative, unvalidated assumption)
- **Effort:** Person-months of work (including design, development, testing, deployment). Use 0.5 as minimum for small tasks.

### Step 2: Score Each Feature on All 4 Dimensions

For each feature/initiative, provide:
- Reach number with source/rationale
- Impact score with justification
- Confidence percentage with evidence basis
- Effort estimate with scope description

Be honest about confidence — inflated confidence undermines the entire framework.

### Step 3: Calculate RICE Score

Formula: **RICE = (Reach x Impact x Confidence) / Effort**

- Higher scores indicate higher priority
- Calculate for every feature to enable direct comparison
- Show the math for transparency

### Step 4: Rank Features by RICE Score

- Sort all features by RICE score descending
- Group into tiers:
  - **Tier 1:** Top quartile — prioritize immediately
  - **Tier 2:** Second quartile — plan for next cycle
  - **Tier 3:** Third quartile — consider if capacity allows
  - **Tier 4:** Bottom quartile — deprioritize or reconsider

### Step 5: Identify Quick Wins vs Strategic Bets

Classify by effort and score:
- **Quick Wins:** High RICE score + Low effort (< 1 person-month). Do these first.
- **Strategic Bets:** High RICE score + High effort (> 2 person-months). Plan carefully, consider phasing.
- **Low-Hanging Fruit:** Medium RICE score + Very low effort (< 0.5 person-month). Fill gaps in sprints.
- **Money Pits:** Low RICE score + High effort. Avoid or fundamentally rethink.

### Step 6: Define Success Metrics and KPIs

For each prioritized feature, define:
- **Primary metric:** The one number that indicates success
- **Leading indicators:** Early signals that predict the primary metric
- **Guardrail metrics:** Things that should NOT get worse (e.g., performance, error rate)
- **Measurement method:** How and when you'll measure
- **Target:** Specific number or threshold for success

## Output Format

### RICE Scoring Table

| Feature | Reach | Impact | Confidence | Effort | RICE Score | Tier |
|---------|-------|--------|------------|--------|------------|------|
| Feature A | 1000 | 3 | 80% | 2 | 1200 | 1 |
| Feature B | 500 | 2 | 100% | 0.5 | 2000 | 1 |
| Feature C | 200 | 1 | 50% | 3 | 33 | 3 |
| ... | ... | ... | ... | ... | ... | ... |

### Priority-Ranked Feature List

1. **Feature B** (RICE: 2000) — Quick Win
2. **Feature A** (RICE: 1200) — Strategic Bet
3. ...

### Quick Wins vs Strategic Bets

| Category | Features | Combined Effort | Expected Impact |
|----------|----------|-----------------|-----------------|
| Quick Wins | Feature B, ... | ... person-months | ... |
| Strategic Bets | Feature A, ... | ... person-months | ... |
| Low-Hanging Fruit | ... | ... | ... |
| Money Pits | Feature C, ... | ... | Deprioritize |

### Success Metrics per Feature

| Feature | Primary Metric | Target | Leading Indicator | Guardrail |
|---------|---------------|--------|-------------------|-----------|
| Feature A | ... | ... | ... | ... |
| Feature B | ... | ... | ... | ... |

## Quality Checks

- [ ] Reach estimates use real numbers (not vague qualifiers)
- [ ] Impact scores include justification for each rating
- [ ] Confidence percentages are honest (not all 80%)
- [ ] Effort estimates account for design, dev, testing, and deployment
- [ ] RICE math is shown and correct
- [ ] Features are ranked and tiered by score
- [ ] Quick wins vs strategic bets are clearly classified
- [ ] Success metrics are defined with specific targets

## Evolution Notes
<!-- Observations appended after each use -->
