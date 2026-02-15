---
name: observability-design
department: "operator"
description: "Use when designing monitoring, alerting, logging, tracing, and SLI/SLO strategies for services or systems. Covers metric collection, structured logging, distributed tracing, dashboard design, and error budget management. Do not use for deployment pipeline design (use deployment-plan) or infrastructure cost modeling (use cost-analysis)."
version: 1
triggers:
  - "monitoring"
  - "alerting"
  - "logging"
  - "observability"
  - "Sentry"
  - "metrics"
  - "tracing"
  - "dashboard"
  - "SLO"
---

# Observability Design

## Purpose

Design a comprehensive observability strategy covering metrics, logging, tracing, alerting, and SLI/SLO definitions. Produces a monitoring architecture that enables rapid incident detection, diagnosis, and resolution.

## Scope Constraints

Reads system architecture documentation, existing monitoring configurations, and service definitions for observability analysis. Does not modify files, deploy monitoring agents, or access production telemetry data directly.

## Inputs

- System architecture (services, databases, APIs, third-party dependencies)
- Current monitoring setup (existing tools, dashboards, alerts)
- Reliability requirements (SLA commitments, uptime targets)
- Team structure (on-call rotation, escalation paths)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Define observability pillars
- [ ] Step 2: Design metric collection
- [ ] Step 3: Define alert thresholds and escalation
- [ ] Step 4: Plan structured logging
- [ ] Step 5: Design distributed tracing
- [ ] Step 6: Specify dashboard requirements
- [ ] Step 7: Define SLIs/SLOs

### Step 1: Define Observability Pillars

Establish the three pillars for this system:
- **Metrics**: What to measure — request rate, error rate, latency, saturation, business KPIs
- **Logs**: What to record — request lifecycle, state changes, errors, audit events
- **Traces**: What to follow — cross-service request flows, database queries, external API calls
- Map each pillar to specific use cases: debugging, alerting, capacity planning, business intelligence

### Step 2: Design Metric Collection

Define the metric taxonomy:
- **Application metrics**: Request count, error count, latency histograms, queue depth, cache hit rate
- **Infrastructure metrics**: CPU, memory, disk I/O, network throughput, connection pool utilization
- **Business metrics**: Sign-ups, conversions, revenue events, feature adoption rates
- **Custom instrumentation**: Counters (events), gauges (current values), histograms (distributions)
- Specify metric naming conventions, label/tag strategy, and cardinality limits

### Step 3: Define Alert Thresholds and Escalation

Design the alerting strategy:
- **Warning alerts**: Early indicators — elevated error rate, latency creep, resource approaching limits
- **Critical alerts**: Immediate action required — service down, error rate spike, SLO burn rate exceeded
- **Escalation paths**: Primary on-call → secondary → engineering lead → incident commander
- **Runbook links**: Every alert includes a link to its diagnosis and remediation runbook
- **Alert fatigue prevention**: Grouping, deduplication, silence windows, alert quality reviews

### Step 4: Plan Structured Logging

Design the logging architecture:
- **Log levels**: DEBUG (development only), INFO (normal operations), WARN (unexpected but handled), ERROR (requires attention)
- **Structured fields**: timestamp, service, request_id, user_id, action, duration_ms, status
- **Correlation IDs**: Request ID propagation across services for distributed request tracing
- **PII redaction**: Identify sensitive fields, implement automatic redaction/masking
- **Log aggregation**: Collection, indexing, retention periods, search capabilities

### Step 5: Design Distributed Tracing

Plan request flow visibility:
- **Span naming conventions**: `service.operation` format, consistent across services
- **Context propagation**: How trace context passes between services (headers, message metadata)
- **Sampling strategy**: Head-based vs tail-based sampling, sampling rate by endpoint or error status
- **Trace enrichment**: Adding business context (user tier, feature flag state) to spans
- **Critical paths**: Which request flows must always be traced (payments, auth, data mutations)

### Step 6: Specify Dashboard Requirements

Define dashboard hierarchy:
- **Operational dashboards**: Service health overview, real-time traffic, error rates, latency percentiles
- **Business dashboards**: User activity, feature adoption, conversion funnels, revenue metrics
- **SLO dashboards**: Error budget remaining, burn rate, SLO compliance history
- **Incident dashboards**: Pre-built investigation views for common failure modes
- Specify dashboard layout, refresh intervals, time range defaults, and access controls

### Step 7: Define SLIs/SLOs

Establish reliability targets:
- **Availability SLI**: Successful requests / total requests (define "successful")
- **Latency SLI**: Proportion of requests faster than threshold (p50, p95, p99 targets)
- **Error rate SLI**: Proportion of requests without errors (define "error")
- **SLO targets**: e.g., 99.9% availability, p95 latency < 200ms, error rate < 0.1%
- **Error budgets**: Calculate error budget from SLO, define burn rate alerts (fast burn, slow burn)
- **SLO review cadence**: Weekly error budget check, monthly SLO review, quarterly target adjustment

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what system is being analyzed, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Output Format

```markdown
# Observability Design: [Service/Feature Name]

## Observability Architecture

```
[Application] → [Metrics Agent] → [Metrics Store] → [Dashboards]
     ↓                                                    ↓
[Structured Logs] → [Log Aggregator] → [Log Search]  [Alerts] → [On-call]
     ↓
[Trace SDK] → [Trace Collector] → [Trace UI]
```

## Metric Catalog

| Metric Name | Type | Labels | Description | Alert Threshold |
|-------------|------|--------|-------------|-----------------|
| http_requests_total | counter | method, path, status | Request count | N/A |
| http_request_duration_ms | histogram | method, path | Request latency | p95 > 500ms |
| ... | ... | ... | ... | ... |

## Alert Catalog

| Alert Name | Severity | Condition | Duration | Runbook |
|------------|----------|-----------|----------|---------|
| HighErrorRate | critical | error_rate > 5% | 5m | [link] |
| LatencyDegraded | warning | p95 > 500ms | 10m | [link] |
| ... | ... | ... | ... | ... |

## Logging Schema

```json
{
  "timestamp": "ISO8601",
  "level": "INFO",
  "service": "api",
  "request_id": "uuid",
  "user_id": "string (optional)",
  "action": "string",
  "duration_ms": "number",
  "status": "number",
  "message": "string"
}
```

## SLI/SLO Definitions

| SLI | Measurement | SLO Target | Error Budget (30d) |
|-----|-------------|------------|-------------------|
| Availability | successful requests / total | 99.9% | 43.2 min downtime |
| Latency | requests < 200ms / total | 99.0% | 432 min slow |
| Error Rate | non-error requests / total | 99.9% | 0.1% errors |

## Dashboard Specifications

| Dashboard | Audience | Key Panels | Refresh |
|-----------|----------|------------|---------|
| Service Health | On-call | Traffic, errors, latency, saturation | 30s |
| SLO Status | Engineering | Error budget, burn rate, compliance | 5m |
| Business Metrics | Product | Adoption, conversions, revenue | 1h |
```

## Handoff

- Hand off to deployment-plan if observability findings reveal deployment pipeline gaps (e.g., missing health checks, no canary metrics integration).
- Hand off to cost-analysis if telemetry storage, metric cardinality, or log retention volumes raise infrastructure cost concerns.

## Quality Checks

- [ ] All three observability pillars (metrics, logs, traces) are covered
- [ ] Every alert has a defined severity, threshold, and linked runbook
- [ ] Structured logging schema includes correlation IDs for distributed tracing
- [ ] PII fields are identified with redaction strategy
- [ ] SLIs are measurable and SLO targets are realistic for the service tier
- [ ] Error budgets are calculated with burn rate alert thresholds
- [ ] Dashboard hierarchy covers operational, business, and SLO views
- [ ] Sampling strategy balances trace coverage with storage costs

## Evolution Notes
<!-- Observations appended after each use -->
