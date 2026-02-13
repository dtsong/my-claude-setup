---
name: "Load Modeling"
department: "tuner"
description: "[Council] Capacity planning with traffic projections, scaling triggers, and cost-at-scale modeling. Used during council/academy deliberation only."
version: 1
triggers:
  - "load"
  - "scale"
  - "capacity"
  - "throughput"
  - "concurrent"
  - "benchmark"
  - "traffic"
  - "scaling"
---

# Load Modeling

## Purpose

Model application load patterns and plan capacity to handle current and projected traffic. Produces a load model with growth projections, scaling trigger definitions, a benchmark plan for critical paths, and cost-at-scale estimates.

## Inputs

- Current traffic data (requests/sec, concurrent users, peak vs average)
- Application architecture (services, databases, queues, external dependencies)
- Growth projections or business targets (user growth rate, launch events, seasonal spikes)
- Current infrastructure (instance types, database tier, CDN, serverless limits)
- SLA requirements (uptime target, max acceptable latency, error rate budget)

## Process

### Step 1: Estimate User Load Patterns

Model the traffic shape:
- Average concurrent users and requests per second
- Peak-to-average ratio (daily peaks, weekly patterns, seasonal spikes)
- Growth trajectory — linear, exponential, or event-driven (launches, campaigns)
- Geographic distribution and timezone effects on peak timing
- Read vs write ratio across the application

### Step 2: Model Request Distribution Across Endpoints

Map traffic to specific system paths:
- Identify the top 10 endpoints by request volume
- Classify endpoints: read-heavy, write-heavy, compute-heavy, I/O-heavy
- Estimate per-endpoint resource cost (CPU time, memory, DB queries, external calls)
- Identify fan-out patterns (one user request triggers N downstream calls)
- Map dependency chains — which downstream services does each endpoint touch?

### Step 3: Identify Resource Bottlenecks at Scale

For each resource type, model where saturation occurs:
- **Database** — connection pool exhaustion, query throughput ceiling, storage growth
- **Application servers** — CPU saturation, memory pressure, thread/process limits
- **Network** — bandwidth limits, connection limits, DNS resolution latency
- **External services** — rate limits, timeout thresholds, quota exhaustion
- **Queues/workers** — queue depth growth, processing lag, dead letter accumulation

### Step 4: Define Horizontal and Vertical Scaling Triggers

Set thresholds that trigger scaling actions:
- CPU utilization threshold for auto-scaling (e.g., scale out at 70% sustained for 3 min)
- Memory utilization threshold
- Request queue depth or response latency threshold
- Database connection pool utilization threshold
- Define scale-up and scale-down policies (cooldown periods, min/max instances)
- Document manual scaling triggers for known events (launches, sales)

### Step 5: Design Benchmark Suite for Critical Paths

Define load tests that validate capacity:
- Identify the 5-10 most critical user journeys to benchmark
- Define load profiles: ramp-up, sustained, spike, soak (long-running)
- Specify success criteria per benchmark (p95 latency, error rate, throughput)
- Plan for realistic test data volume and variety
- Define the baseline benchmark to run before and after changes

### Step 6: Plan Capacity Thresholds and Alerts

Design the monitoring and alerting layer:
- Define warning thresholds (approaching limits) vs critical thresholds (at limits)
- Map each threshold to an alert channel and response playbook
- Set up dashboard panels for real-time capacity visibility
- Plan capacity review cadence (weekly, monthly, quarterly)
- Define runbook actions for each alert scenario

### Step 7: Model Cost-at-Scale Projections

Estimate infrastructure cost as traffic grows:
- Current monthly infrastructure cost breakdown
- Cost per additional 1,000 concurrent users (compute, database, bandwidth, CDN)
- Identify cost cliffs (tier upgrades, reserved instance thresholds)
- Model 3-month, 6-month, and 12-month cost projections
- Identify cost optimization opportunities (reserved instances, spot/preemptible, caching ROI)

## Output Format

```markdown
# Load Model: [Application Name]

## Traffic Profile

| Metric | Current | 3-Month | 6-Month | 12-Month |
|--------|---------|---------|---------|----------|
| Concurrent Users | ... | ... | ... | ... |
| Requests/sec (avg) | ... | ... | ... | ... |
| Requests/sec (peak) | ... | ... | ... | ... |
| Peak:Average Ratio | ... | ... | ... | ... |
| Daily Data Growth | ... | ... | ... | ... |

## Endpoint Heat Map

| Endpoint | Req/sec | Type | Resource Cost | Bottleneck Risk |
|----------|---------|------|--------------|----------------|
| ...      | ...     | ...  | ...          | ...            |

## Scaling Trigger Table

| Resource | Warning Threshold | Critical Threshold | Scale Action | Cooldown |
|----------|------------------|-------------------|-------------|----------|
| CPU      | ...              | ...               | ...         | ...      |
| Memory   | ...              | ...               | ...         | ...      |
| DB Connections | ...        | ...               | ...         | ...      |
| Queue Depth | ...           | ...               | ...         | ...      |

## Bottleneck Analysis

| Resource | Current Utilization | Saturation Point | Time to Saturation | Mitigation |
|----------|-------------------|-----------------|-------------------|-----------|
| ...      | ...               | ...             | ...               | ...       |

## Benchmark Plan

| Journey | Load Profile | Success Criteria (p95) | Tool |
|---------|-------------|----------------------|------|
| ...     | ...         | ...                  | ...  |

## Cost Projections

| Component | Current/mo | +3mo | +6mo | +12mo |
|-----------|-----------|------|------|-------|
| Compute   | ...       | ...  | ...  | ...   |
| Database  | ...       | ...  | ...  | ...   |
| CDN/Bandwidth | ...   | ...  | ...  | ...   |
| **Total** | ...       | ...  | ...  | ...   |

## Capacity Budget

| Resource | Current Headroom | Scaling Ceiling | Action Required By |
|----------|-----------------|----------------|-------------------|
| ...      | ...             | ...            | ...               |
```

## Quality Checks

- [ ] Traffic model includes peak, average, and growth projections
- [ ] All critical endpoints are mapped with resource cost estimates
- [ ] Bottleneck analysis covers database, compute, network, and external dependencies
- [ ] Scaling triggers have specific numeric thresholds, not vague descriptions
- [ ] Benchmark plan covers the critical user journeys with defined success criteria
- [ ] Cost projections include at least 3 time horizons
- [ ] Alerts map to specific response playbooks
- [ ] Model accounts for both organic growth and planned events (launches, campaigns)

## Evolution Notes
<!-- Observations appended after each use -->
