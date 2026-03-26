---
name: distributed-patterns
department: "architect"
description: "Use when designing distributed systems or evaluating distributed architecture patterns. Covers CAP theorem trade-offs, consensus protocols (Raft, Paxos), saga orchestration, CRDTs, event sourcing, partition handling, distributed transactions, and failure detectors. Do not use for general API design (use api-design) or database schema design (use schema-design)."
version: 1
triggers:
  - "distributed"
  - "consensus"
  - "partition"
  - "saga"
  - "CRDT"
  - "event sourcing"
  - "microservices"
  - "distributed transactions"
  - "Raft"
  - "Paxos"
  - "CAP theorem"
---

# Distributed Patterns

## Purpose

Evaluate distributed system design decisions and recommend appropriate patterns for consistency, availability, partition tolerance, and failure handling. Ensure designs account for the fundamental constraints of distributed computing.

## Scope Constraints

Analyzes architecture documents, system diagrams, and code for distributed system patterns. Does not modify files or execute code. Does not benchmark or load-test distributed systems.

## Inputs

- System architecture overview (services, data stores, communication patterns)
- Consistency requirements (strong, eventual, causal)
- Availability and latency SLAs
- Expected failure modes and partition scenarios
- Current distributed patterns in use, if any

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Classify CAP trade-offs
- [ ] Step 2: Evaluate consistency patterns
- [ ] Step 3: Design failure handling
- [ ] Step 4: Review data synchronization
- [ ] Step 5: Assess transaction patterns
- [ ] Step 6: Validate operational readiness

### Step 1: Classify CAP Trade-offs

- Identify each service's position on the CAP spectrum.
- Map which data requires strong consistency vs eventual consistency.
- Document partition behavior: does the system favor CP or AP per data domain?
- Flag services that implicitly assume no partitions (single-region, no failover).
- Verify the design explicitly acknowledges CAP trade-offs rather than ignoring them.

### Step 2: Evaluate Consistency Patterns

- Identify consensus requirements (leader election, distributed locks, config agreement).
- Recommend consensus protocol fit: Raft for simplicity, Paxos/Multi-Paxos for flexibility, ZAB for ordered broadcast.
- Evaluate CRDT suitability for conflict-free replicated data (counters, sets, registers, maps).
- Check event sourcing applicability: append-only event log, projection rebuilds, event versioning.
- Verify causal ordering where needed (vector clocks, hybrid logical clocks).

### Step 3: Design Failure Handling

- Enumerate failure detector strategy (heartbeats, phi-accrual, swim protocol).
- Define timeout budgets per service call (connect, read, total).
- Specify circuit breaker configuration (threshold, half-open behavior, fallback).
- Plan for partial failure: which operations can proceed with degraded service?
- Document split-brain prevention strategy for stateful services.

### Step 4: Review Data Synchronization

- Map data replication topology (single-leader, multi-leader, leaderless).
- Identify read-after-write consistency requirements and implementation.
- Check for anti-entropy mechanisms (Merkle trees, read repair, hinted handoff).
- Verify conflict resolution strategy for concurrent writes (last-writer-wins, merge functions, manual).
- Assess replication lag tolerance per data domain.

### Step 5: Assess Transaction Patterns

- Identify cross-service transaction requirements.
- Evaluate saga pattern fit: orchestration (central coordinator) vs choreography (event-driven).
- Define compensating transactions for each saga step.
- Check idempotency guarantees for all saga participants.
- Verify at-least-once delivery with deduplication for message-driven flows.
- Flag any use of distributed locks or two-phase commit — justify or replace.

### Step 6: Validate Operational Readiness

- Verify distributed tracing spans cross service boundaries (trace ID propagation).
- Check that partition/failover scenarios have runbooks.
- Confirm chaos engineering tests cover: network partition, node failure, clock skew.
- Validate that the system degrades gracefully under partial failure.

> **Validation gate**: Revisit this analysis after 5+ sessions to verify patterns held up under real-world usage and evolution.

> **Compaction resilience**: If context was lost, re-read the Inputs section to identify the system under analysis, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Output Format

### Pattern Selection Matrix

| Concern | Pattern | Rationale | Trade-off |
|---------|---------|-----------|-----------|
| Consistency | Raft / CRDT / Event sourcing | ... | ... |
| Failure handling | Circuit breaker + phi-accrual | ... | ... |
| Transactions | Saga (orchestration) | ... | ... |
| Replication | Single-leader with read replicas | ... | ... |

### Failure Scenario Table

| Scenario | Impact | Mitigation | Recovery Time |
|----------|--------|------------|---------------|
| Network partition between A and B | ... | ... | ... |
| Leader node failure | ... | ... | ... |

## Handoff

- Hand off to api-design for service boundary API contracts.
- Hand off to operator/deployment-plan for multi-region deployment topology.
- Hand off to prover/formal-spec if consensus protocol correctness needs formal verification.

## Quality Checks

- [ ] CAP trade-offs explicitly documented per data domain
- [ ] Consensus protocol selection justified with requirements
- [ ] Failure detectors and timeout budgets specified
- [ ] Saga compensating transactions defined for each step
- [ ] Idempotency and deduplication verified for message-driven flows
- [ ] Replication strategy and conflict resolution documented
- [ ] Distributed tracing confirmed across service boundaries
- [ ] Chaos engineering scenarios identified

## Evolution Notes
<!-- Observations appended after each use -->
