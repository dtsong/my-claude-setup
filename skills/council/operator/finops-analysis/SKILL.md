---
name: finops-analysis
department: "operator"
description: "Use when analyzing cloud cost attribution, reserved capacity planning, right-sizing, spot/preemptible usage, unit economics, or cost anomaly detection. Covers FinOps practices for ongoing cost governance. Do not use for one-time infrastructure cost modeling (use cost-analysis) or deployment strategy (use deployment-plan)."
version: 1
triggers:
  - "FinOps"
  - "cloud cost"
  - "cost optimization"
  - "unit economics"
  - "reserved instances"
  - "right-sizing"
  - "spot instances"
  - "cost anomaly"
  - "cost attribution"
  - "preemptible"
---

# FinOps Analysis

## Purpose

Analyze cloud spending through a FinOps lens: attribute costs to teams and products, plan reserved capacity, identify right-sizing opportunities, evaluate spot/preemptible usage, calculate unit economics, and detect cost anomalies. Produces actionable recommendations for ongoing cost governance.

## Scope Constraints

Reads cloud billing data, usage reports, and resource inventories for analysis. Does not modify infrastructure, provision resources, or access billing APIs directly.

## Inputs

- Cloud billing reports or cost explorer exports
- Resource inventory (instances, storage, services by team/product)
- Current reservation and savings plan commitments
- Business metrics for unit economics (users, transactions, requests)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Map cost attribution
- [ ] Step 2: Analyze reserved capacity
- [ ] Step 3: Identify right-sizing opportunities
- [ ] Step 4: Evaluate spot/preemptible usage
- [ ] Step 5: Calculate unit economics
- [ ] Step 6: Detect cost anomalies and set guardrails

### Step 1: Map Cost Attribution

Attribute costs to owners:
- Tag coverage audit -- identify untagged resources and enforce tagging policy
- Break down spend by team, product, environment, and service
- Identify shared costs and define allocation model (proportional, fixed, or equal split)
- Separate controllable spend from fixed platform costs

### Step 2: Analyze Reserved Capacity

Evaluate commitment-based discounts:
- Inventory current reservations and savings plans with expiry dates
- Calculate current coverage ratio (reserved vs on-demand hours)
- Identify stable baseline workloads suitable for 1-year or 3-year commitments
- Model savings for Reserved Instances, Savings Plans, and Committed Use Discounts
- Flag over-committed reservations with low utilization

### Step 3: Identify Right-Sizing Opportunities

Find over-provisioned resources:
- Compare actual CPU/memory/IOPS utilization against provisioned capacity
- Flag instances running below 30% average utilization
- Recommend downsizing or family migration for underutilized resources
- Identify idle resources (zero traffic for >7 days) for termination

### Step 4: Evaluate Spot/Preemptible Usage

Assess interruptible compute opportunities:
- Identify fault-tolerant workloads (batch, CI/CD, dev/test, data processing)
- Calculate potential savings vs on-demand pricing
- Recommend diversified instance pools to reduce interruption risk
- Define fallback strategy for spot capacity unavailability

### Step 5: Calculate Unit Economics

Tie infrastructure cost to business value:
- Cost per user, cost per transaction, cost per API call
- Marginal cost of the next 1K users or 1M requests
- Gross margin impact of infrastructure spend
- Trend unit costs over time -- flag efficiency degradation

### Step 6: Detect Cost Anomalies and Set Guardrails

Establish ongoing cost governance:
- Define anomaly detection thresholds (e.g., >20% day-over-day spike)
- Set per-team or per-service budget caps with alert escalation
- Create cost review cadence (weekly anomaly triage, monthly deep dive)
- Define showback/chargeback reporting for stakeholders

> **Compaction resilience**: If context was lost, re-read Inputs to reconstruct scope, check Progress Checklist for completed steps, resume from earliest incomplete step.

## Output Format

```markdown
# FinOps Analysis: [Scope]

## Cost Attribution

| Team/Product | Monthly Spend | % of Total | Top Cost Driver |
|-------------|--------------|------------|-----------------|
| [team] | $X | Y% | [service] |

## Reservation & Right-Sizing

| Action | Resource | Current Cost | Projected Cost | Savings |
|--------|----------|-------------|----------------|---------|
| Reserve | [resource] | $X | $X | $X/mo |
| Right-size | [resource] | $X | $X | $X/mo |
| Spot migrate | [workload] | $X | $X | $X/mo |

## Unit Economics

| Metric | Current | 90-Day Trend | Target |
|--------|---------|-------------|--------|
| Cost/user | $X | +/-Y% | $X |
| Cost/1K requests | $X | +/-Y% | $X |

## Anomaly Guardrails

| Guardrail | Threshold | Action |
|-----------|-----------|--------|
| Daily spike | >20% | Alert on-call |
| Monthly budget | >90% | Escalate to lead |
```

## Handoff

- Hand off to cost-analysis if a full infrastructure cost model from scratch is needed.
- Hand off to observability-design if anomaly detection requires integration with existing monitoring stack.

## Quality Checks

- [ ] Cost attribution covers >90% of total spend (minimal untagged resources)
- [ ] Reserved capacity analysis includes coverage ratio and expiry timeline
- [ ] Right-sizing recommendations cite actual utilization data
- [ ] Spot/preemptible evaluation identifies eligible workloads with fallback plan
- [ ] Unit economics tie cost to at least two business metrics
- [ ] Anomaly guardrails define thresholds and escalation paths

## Evolution Notes
<!-- Observations appended after each use -->
