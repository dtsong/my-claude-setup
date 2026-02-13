---
name: "Cost Analysis"
department: "operator"
description: "[Council] Infrastructure cost modeling, scaling projections, and optimization recommendations. Used during council/academy deliberation only."
version: 1
triggers:
  - "cost"
  - "pricing"
  - "budget"
  - "compute"
  - "scaling"
  - "infrastructure cost"
  - "optimization"
  - "reserved instances"
---

# Cost Analysis

## Purpose

Model infrastructure costs at current and projected scale, identify optimization opportunities, and establish cost monitoring with budget alerting. Produces a cost breakdown that enables informed architecture and scaling decisions.

## Inputs

- Current infrastructure inventory (services, providers, tiers)
- Current usage metrics (requests/day, storage volume, compute hours)
- Growth projections or scaling targets
- Budget constraints or cost reduction goals

## Process

### Step 1: Inventory Infrastructure Components

Catalog all cost-bearing components:
- **Compute**: Application servers, serverless functions, background workers, build runners
- **Storage**: Object storage, block storage, database storage, backup storage
- **Database**: Managed database instances, read replicas, connection poolers
- **CDN**: Bandwidth, edge compute, cache storage
- **Third-party services**: Auth providers, email/SMS, payment processing, analytics, error tracking
- **DNS and networking**: Domain registration, DNS queries, load balancers, NAT gateways, data transfer
- **Email**: Transactional email, marketing email, inbound processing

### Step 2: Estimate Per-Unit Costs at Current Scale

For each component, calculate:
- **Monthly base cost**: Fixed costs regardless of usage (reserved instances, minimum tiers)
- **Variable cost**: Per-request, per-GB, per-user marginal costs
- **Cost per user**: Total infrastructure cost divided by active users
- **Cost per request**: Total infrastructure cost divided by total requests
- Document pricing tier thresholds and current utilization against limits

### Step 3: Model Cost Projections at Scale

Project costs at growth milestones:
- **2x scale**: Which components scale linearly vs step-function? Where do tier upgrades hit?
- **5x scale**: Which pricing tiers break? Where do volume discounts apply?
- **10x scale**: What architectural changes become necessary? Which components become dominant costs?
- Identify cost cliffs — points where a small usage increase triggers a large cost jump

### Step 4: Identify Optimization Opportunities

Evaluate cost reduction strategies:
- **Right-sizing**: Over-provisioned instances, unused reserved capacity, oversized database tiers
- **Reserved/committed use**: Savings from 1-year or 3-year commitments on stable workloads
- **Spot/preemptible instances**: Suitable workloads for interruptible compute (batch jobs, builds)
- **Caching to reduce compute**: CDN caching, application-level caching, database query caching
- **Query optimization**: Slow queries consuming excess database resources, missing indexes
- **Architecture changes**: Serverless for bursty workloads, edge compute for latency, static generation

### Step 5: Design Cost Monitoring and Alerting

Establish ongoing cost visibility:
- **Budget thresholds**: Alert at 50%, 75%, 90%, 100% of monthly budget
- **Anomaly detection**: Unexpected cost spikes from runaway processes, misconfigured auto-scaling, or attacks
- **Cost-per-user trending**: Track unit economics over time to catch efficiency degradation
- **Tag-based allocation**: Cost attribution by service, team, environment, feature
- **Review dashboard**: Real-time cost breakdown accessible to engineering and leadership

### Step 6: Plan Budget Allocation and Review Cadence

Define the financial process:
- **Budget allocation**: Per-service or per-team budget breakdown
- **Review cadence**: Monthly cost review meetings, quarterly budget adjustments
- **Cost ownership**: Which team owns which infrastructure costs
- **Approval process**: Threshold for new infrastructure spending requiring approval
- **Cost-benefit framework**: How to evaluate infrastructure investments against engineering time

## Output Format

```markdown
# Cost Analysis: [Project/Service Name]

## Infrastructure Cost Table

| Component | Provider | Tier | Monthly Cost | Cost Driver | Notes |
|-----------|----------|------|-------------|-------------|-------|
| App Server | [provider] | [tier] | $X | requests | ... |
| Database | [provider] | [tier] | $X | storage + queries | ... |
| CDN | [provider] | [tier] | $X | bandwidth | ... |
| **Total** | | | **$X** | | |

**Cost per user**: $X/month | **Cost per 1K requests**: $X

## Scaling Projections

| Component | Current | 2x | 5x | 10x |
|-----------|---------|-----|-----|------|
| Compute | $X | $X | $X | $X |
| Database | $X | $X | $X | $X |
| Storage | $X | $X | $X | $X |
| **Total** | **$X** | **$X** | **$X** | **$X** |

## Optimization Recommendations

| Optimization | Estimated Savings | Effort | Risk | Priority |
|-------------|-------------------|--------|------|----------|
| [description] | $X/month (Y%) | Low/Med/High | Low/Med/High | P1/P2/P3 |

## Budget Alert Thresholds

| Threshold | Monthly Amount | Action |
|-----------|---------------|--------|
| 50% | $X | Review dashboard |
| 75% | $X | Investigate anomalies |
| 90% | $X | Escalate to lead |
| 100% | $X | Freeze non-critical spending |
```

## Quality Checks

- [ ] All cost-bearing infrastructure components are inventoried
- [ ] Per-unit costs (per user, per request) are calculated for current scale
- [ ] Scaling projections identify cost cliffs and tier boundaries
- [ ] Optimization recommendations include estimated savings and effort
- [ ] Cost monitoring covers budget alerts and anomaly detection
- [ ] Budget review cadence and cost ownership are defined
- [ ] Third-party service costs are included (not just cloud infrastructure)
- [ ] Cost projections account for both linear and step-function scaling

## Evolution Notes
<!-- Observations appended after each use -->
