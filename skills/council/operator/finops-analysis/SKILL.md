---
name: finops-analysis
department: "operator"
description: "Use when analyzing cloud spending, cost attribution, or unit economics. Covers cost allocation tagging, reserved capacity planning, right-sizing, spot/preemptible usage, cost anomaly detection, and showback/chargeback models. Do not use for general infrastructure cost modeling (use cost-analysis) or deployment strategy (use deployment-plan)."
version: 1
triggers:
  - "FinOps"
  - "cloud cost"
  - "cost optimization"
  - "unit economics"
  - "reserved instances"
  - "right-sizing"
  - "cost attribution"
  - "cost anomaly"
  - "spot instances"
  - "savings plan"
---

# FinOps Analysis

## Purpose

Evaluate cloud spending efficiency and produce actionable recommendations for cost optimization across compute, storage, network, and managed services. Align cloud costs with business value through unit economics and cost attribution.

## Scope Constraints

Reads cloud billing data, resource configurations, and usage metrics for cost analysis. Does not modify infrastructure or execute provisioning commands. Does not access financial systems beyond cloud cost APIs.

## Inputs

- Cloud provider(s) in scope (AWS, GCP, Azure, multi-cloud)
- Current monthly spend breakdown or billing export
- Application architecture overview (compute, storage, databases, networking)
- Business metrics for unit economics (users, transactions, requests)
- Any existing cost optimization efforts or commitments

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Map cost allocation and tagging
- [ ] Step 2: Analyze compute right-sizing
- [ ] Step 3: Evaluate commitment-based discounts
- [ ] Step 4: Assess spot/preemptible opportunities
- [ ] Step 5: Calculate unit economics
- [ ] Step 6: Detect cost anomalies and waste

### Step 1: Map Cost Allocation and Tagging

- Inventory all cloud accounts, projects, and resource groups.
- Verify tagging strategy covers: team, environment, service, cost center.
- Identify untagged or mis-tagged resources.
- Map spend to business units or product features for showback/chargeback.
- Flag shared resources that need allocation rules (e.g., shared databases, networking).

### Step 2: Analyze Compute Right-Sizing

- Review CPU and memory utilization for compute instances over 14+ days.
- Identify over-provisioned instances (avg utilization <30%).
- Identify under-provisioned instances causing performance degradation.
- Recommend instance family changes for better price-performance.
- Check auto-scaling configurations for appropriate min/max/target settings.

### Step 3: Evaluate Commitment-Based Discounts

- Inventory existing Reserved Instances, Savings Plans, or Committed Use Discounts.
- Calculate current commitment coverage rate vs on-demand spend.
- Identify stable workloads suitable for 1-year or 3-year commitments.
- Model savings for different commitment levels (50%, 75%, 90% coverage).
- Flag commitments nearing expiration that need renewal decisions.

### Step 4: Assess Spot/Preemptible Opportunities

- Identify fault-tolerant workloads suitable for spot/preemptible (batch, CI/CD, dev/test).
- Review interruption history for target instance types.
- Recommend spot fleet diversification strategy (multiple instance types/AZs).
- Estimate savings vs on-demand for candidate workloads.
- Verify graceful interruption handling is implemented.

### Step 5: Calculate Unit Economics

- Define cost-per-unit metrics (cost per user, per transaction, per API call, per GB stored).
- Calculate current unit economics from billing and business metrics.
- Identify services with disproportionate cost-per-unit.
- Project unit economics at 2x and 5x current scale.
- Flag services where cost scales faster than revenue.

### Step 6: Detect Cost Anomalies and Waste

- Identify idle resources (unattached volumes, unused IPs, stopped instances with attached storage).
- Flag data transfer costs from suboptimal architecture (cross-region, cross-AZ).
- Check for over-provisioned managed services (database tiers, cache sizes).
- Review storage lifecycle policies (S3 tiers, snapshot retention).
- Set up anomaly detection thresholds for daily/weekly spend alerts.

> **Compaction resilience**: If context was lost, re-read the Inputs section to identify the analysis scope, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Output Format

### Cost Optimization Summary

| Category | Current Spend | Optimized Spend | Savings | Effort |
|----------|--------------|-----------------|---------|--------|
| Right-sizing | $X/mo | $Y/mo | Z% | Low/Med/High |
| Commitments | ... | ... | ... | ... |
| Spot/Preemptible | ... | ... | ... | ... |
| Waste elimination | ... | ... | ... | ... |

### Unit Economics

| Metric | Current | At 2x Scale | At 5x Scale |
|--------|---------|-------------|-------------|
| Cost per user | ... | ... | ... |
| Cost per transaction | ... | ... | ... |

## Handoff

- Hand off to cost-analysis for detailed infrastructure cost modeling of new architectures.
- Hand off to deployment-plan if cost optimization requires migration or redeployment.

## Quality Checks

- [ ] All cloud accounts and resource groups inventoried
- [ ] Tagging gaps identified with remediation plan
- [ ] Right-sizing recommendations backed by 14+ day utilization data
- [ ] Commitment coverage modeled at multiple levels
- [ ] Spot candidates verified for fault tolerance
- [ ] Unit economics calculated with current business metrics
- [ ] Idle resources and waste identified with estimated savings
- [ ] Total savings opportunity quantified with effort estimates

## Evolution Notes
<!-- Observations appended after each use -->
