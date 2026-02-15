---
name: deployment-plan
department: "operator"
description: "Use when designing deployment strategies including environment progression, CI/CD pipelines, zero-downtime releases, rollback procedures, and feature flag management. Covers blue-green, rolling, and canary deployment patterns with database migration coordination. Do not use for monitoring or alerting design (use observability-design) or infrastructure cost modeling (use cost-analysis)."
version: 1
triggers:
  - "deploy"
  - "rollback"
  - "release"
  - "staging"
  - "production"
  - "CI/CD"
  - "pipeline"
  - "blue-green"
  - "canary"
---

# Deployment Plan

## Purpose

Design a complete deployment strategy covering environment progression, pipeline stages, zero-downtime releases, rollback procedures, and feature flag management. Produces actionable deployment runbooks and pipeline configurations.

## Scope Constraints

Reads infrastructure configurations, CI/CD definitions, and deployment documentation for strategy analysis. Does not modify files, execute deployments, or access production credentials directly.

## Inputs

- Feature or service being deployed
- Current infrastructure (hosting provider, container orchestration, CI/CD tooling)
- Existing deployment process (if any)
- Availability requirements (SLA/SLO targets, maintenance window constraints)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Define deployment environments
- [ ] Step 2: Design deployment pipeline
- [ ] Step 3: Plan zero-downtime strategy
- [ ] Step 4: Define rollback procedures
- [ ] Step 5: Design feature flag strategy
- [ ] Step 6: Specify health checks
- [ ] Step 7: Plan database migration coordination

### Step 1: Define Deployment Environments

Map the environment progression and configuration strategy:
- **Environment chain**: dev → staging → production (add preview/QA if needed)
- **Environment-specific configs**: Feature flags, API endpoints, database connections, third-party service keys
- **Environment parity**: What differs between environments and why — minimize drift
- **Access controls**: Who can deploy to which environment, approval requirements

### Step 2: Design Deployment Pipeline

Define the build-test-deploy stages:
- **Build stage**: Compilation, dependency resolution, asset bundling, Docker image creation
- **Test stage**: Unit tests, integration tests, E2E smoke tests, security scans
- **Deploy stages**: Per-environment deployment steps with promotion gates
- **Approval gates**: Automatic promotion vs manual approval between environments
- **Artifact management**: Image tagging strategy, artifact retention policy

### Step 3: Plan Zero-Downtime Strategy

Select and design the deployment strategy:
- **Blue-green**: Two identical environments, instant traffic switch, simple rollback
- **Rolling update**: Gradual instance replacement, reduced resource overhead, longer rollout
- **Canary**: Progressive traffic shifting (1% → 10% → 50% → 100%), metric-gated promotion
- **Feature flags**: Deploy dark, enable progressively, decouple deploy from release
- Choose strategy based on risk tolerance, infrastructure capabilities, and rollback speed requirements

### Step 4: Define Rollback Procedures

Plan for every failure scenario:
- **Automated rollback triggers**: Health check failures, error rate spikes, latency thresholds
- **Manual rollback steps**: Exact commands or UI steps to revert to previous version
- **Data rollback considerations**: Can database changes be reversed? Forward-fix vs rollback
- **Rollback testing**: How and when rollback procedures are verified
- **Communication protocol**: Who is notified during rollback, status page updates

### Step 5: Design Feature Flag Strategy

Plan feature flag lifecycle:
- **Flag types**: Release flags (temporary), ops flags (kill switches), experiment flags (A/B), permission flags (entitlements)
- **Flag lifecycle**: Creation → testing → rollout → full-release → cleanup
- **Cleanup schedule**: Maximum flag age, review cadence, stale flag detection
- **Flag management**: Tooling choice, naming conventions, flag ownership

### Step 6: Specify Health Checks

Define verification at every stage:
- **Readiness probes**: Is the new version ready to receive traffic? Dependency checks, warmup completion
- **Liveness probes**: Is the running instance healthy? Memory, deadlock detection, heartbeat
- **Smoke tests**: Post-deploy verification of critical paths — login, core API, key user flows
- **Synthetic monitoring**: Continuous external checks simulating user behavior

### Step 7: Plan Database Migration Coordination

Coordinate schema changes with deployments:
- **Migration ordering**: Run migrations before deploy (expand), after deploy (contract), or both (expand-contract pattern)
- **Backward-compatible migrations**: Additive changes only during rollout — no column drops, no renames
- **Rollback scripts**: Reverse migration for every forward migration
- **Data backfill**: Strategy for populating new columns or transforming existing data
- **Migration testing**: Run against production-like data volume before deploying

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what system is being analyzed, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Output Format

```markdown
# Deployment Plan: [Feature/Service Name]

## Environment Matrix

| Environment | Purpose | URL | Deploy Method | Approval |
|-------------|---------|-----|---------------|----------|
| dev         | Development testing | ... | Auto on merge to dev | None |
| staging     | Pre-production validation | ... | Auto on merge to main | None |
| production  | Live traffic | ... | Promotion from staging | Manual |

## Pipeline Diagram

```
[commit] → [build] → [test] → [deploy:dev] → [deploy:staging] → [approve] → [deploy:prod]
                                                                      ↓
                                                              [smoke tests]
```

## Deployment Strategy

**Method**: [Blue-green / Rolling / Canary / Feature flag]

[Strategy-specific details: traffic percentages, timing, promotion criteria]

## Rollback Checklist

- [ ] Trigger: [condition that initiates rollback]
- [ ] Command: [exact rollback command or procedure]
- [ ] Verify: [how to confirm rollback succeeded]
- [ ] Database: [migration rollback steps if applicable]
- [ ] Notify: [who to inform and how]

## Feature Flag Plan

| Flag Name | Type | Default | Rollout Plan | Cleanup Date |
|-----------|------|---------|--------------|--------------|
| ... | release | off | 1% → 10% → 100% | [date] |

## Health Checks

| Check | Type | Endpoint/Method | Interval | Failure Threshold |
|-------|------|-----------------|----------|-------------------|
| Readiness | probe | /health/ready | 5s | 3 consecutive |
| Liveness | probe | /health/live | 10s | 5 consecutive |
| Smoke | post-deploy | [test suite] | on deploy | any failure |

## Database Migration Plan

| Migration | Type | Reversible | Run When | Dependencies |
|-----------|------|------------|----------|--------------|
| ... | expand | yes | pre-deploy | none |
```

## Handoff

- Hand off to observability-design if deployment health monitoring or SLO-based deployment gating needs are identified.
- Hand off to cost-analysis if deployment strategy choices have significant infrastructure cost implications (e.g., blue-green doubling compute).

## Quality Checks

- [ ] Every environment has defined configuration and access controls
- [ ] Pipeline includes automated tests before each promotion
- [ ] Zero-downtime strategy is specified with rollback speed estimate
- [ ] Rollback procedures are documented with exact commands
- [ ] Feature flags have defined lifecycle and cleanup dates
- [ ] Health checks cover readiness, liveness, and post-deploy smoke tests
- [ ] Database migrations are backward-compatible during rollout
- [ ] Communication plan covers both deploy and rollback scenarios

## Evolution Notes
<!-- Observations appended after each use -->
