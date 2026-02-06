---
name: "Failure Mode Analysis"
department: "skeptic"
description: "Systematic failure scenario discovery and resilience mitigations"
version: 1
triggers:
  - "failure"
  - "error"
  - "crash"
  - "downtime"
  - "resilience"
  - "availability"
  - "recovery"
  - "rollback"
  - "degradation"
  - "timeout"
  - "retry"
---

# Failure Mode Analysis

## Purpose
Systematically identify failure scenarios for proposed features and design mitigations that maintain system resilience.

## Inputs
- Feature or infrastructure change being analyzed
- System architecture (services, databases, APIs, third-party dependencies)
- Current reliability requirements (SLA/SLO targets)
- Existing monitoring and alerting setup

## Process

### Step 1: List System Components
Enumerate all components involved: services, databases, APIs, third-party dependencies, caches, queues, CDNs, DNS, and any shared infrastructure.

### Step 2: Enumerate Failure Modes Per Component
For each component, systematically consider:

- **Network failures**: Timeout, DNS resolution failure, TLS handshake failure, connection reset, packet loss
- **Data failures**: Corruption, inconsistency between stores, migration errors, schema drift, encoding issues
- **Resource exhaustion**: Memory leak, CPU saturation, connection pool exhaustion, disk full, file descriptor limits
- **Dependency failures**: Third-party API down, rate limited, schema change, authentication revoked, region outage
- **State failures**: Race conditions, stale cache serving wrong data, split-brain in distributed systems, phantom reads

### Step 3: Assess Cascade Potential
Map the failure tree: if component X fails, what else breaks? Identify single points of failure and shared dependencies. Determine blast radius for each failure mode.

### Step 4: Design Mitigations
For each failure mode, define:

- **Graceful degradation**: What functionality survives? What's the user experience during failure?
- **Retry strategy**: Exponential backoff with jitter, circuit breaker thresholds, max retry limits
- **Fallback behavior**: Cached data, default values, error states, read-only mode
- **Recovery procedure**: Automatic vs manual recovery, estimated time to recovery, data reconciliation steps

### Step 5: Define Monitoring Signals
For each failure mode, specify the metric, log pattern, or alert that detects it. Include detection latency — how quickly will you know?

### Step 6: Plan Rollback Strategy
Define rollback approach: feature flags for instant disable, database rollback scripts, deployment rollback procedure, data cleanup if needed.

## Output Format

### Failure Mode Table

| Component | Failure Mode | Severity | Cascade Risk | Mitigation | Monitoring Signal |
|---|---|---|---|---|---|
| [Component] | [What fails] | Critical/High/Medium/Low | [What else breaks] | [Specific mitigation] | [Metric/alert] |

### Cascade Diagram
```
[Component A fails]
  ├── [Component B] — degraded (uses cached data)
  ├── [Component C] — down (hard dependency)
  │   └── [Component D] — down (depends on C)
  └── [Component E] — unaffected (independent)
```

### Rollback Checklist
- [ ] Feature flag to disable: [flag name]
- [ ] Database rollback: [migration name / script]
- [ ] Deployment rollback: [procedure]
- [ ] Data cleanup: [steps if needed]
- [ ] Communication: [who to notify]

## Quality Checks
- [ ] Every external dependency has failure analysis
- [ ] Cascade paths are fully mapped with blast radius
- [ ] Mitigations don't introduce new failure modes
- [ ] Monitoring covers detection of each identified failure
- [ ] Rollback strategy is defined and tested
- [ ] Recovery time estimates are documented

## Evolution Notes
<!-- Observations appended after each use -->
