---
name: "distributed-patterns"
department: "architect"
description: "Use when designing distributed systems requiring coordination across nodes. Covers CAP theorem trade-offs, consensus protocols (Raft, Paxos), saga orchestration, CRDTs, event sourcing, partition handling, distributed transactions, and failure detectors. Do not use for single-node database design (use schema-design) or API contract design (use api-design)."
version: 1
triggers:
  - "distributed"
  - "consensus"
  - "partition"
  - "saga"
  - "CRDT"
  - "event sourcing"
  - "microservices"
  - "CAP theorem"
  - "Raft"
  - "Paxos"
  - "eventual consistency"
---

# Distributed Patterns

## Purpose

Design distributed system architectures with explicit consistency, availability, and partition-tolerance trade-offs. Produces architecture decisions, coordination protocols, and failure-handling strategies for multi-node systems.

## Scope Constraints

- Produces architecture patterns and coordination strategies only; does not implement services.
- Covers consensus, sagas, CRDTs, event sourcing, partition handling, distributed transactions, and failure detection.
- Does not design database schemas or API contracts -- hand off to schema-design or api-design.

## Inputs

- System requirements (throughput, latency, consistency needs)
- Current architecture (monolith, microservices, hybrid)
- Data ownership boundaries (which services own which data)
- Failure tolerance requirements (RPO, RTO, availability targets)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
<!-- Track completion across compaction boundaries -->
- [ ] Step 1: Map System Boundaries
- [ ] Step 2: Classify Consistency Requirements
- [ ] Step 3: Select Coordination Patterns
- [ ] Step 4: Design Failure Handling
- [ ] Step 5: Define Data Flow
- [ ] Step 6: Validate Trade-offs

### Step 1: Map System Boundaries

Identify services, their data ownership, and communication paths. List all cross-boundary operations that require coordination.

### Step 2: Classify Consistency Requirements

For each cross-boundary operation, determine: strong consistency (CP), availability-first (AP), or tunable consistency. Apply CAP theorem reasoning to justify each choice.

### Step 3: Select Coordination Patterns

Match each operation to a pattern:
- **Strong consistency**: consensus protocol (Raft/Paxos), distributed transactions (2PC/3PC)
- **Eventual consistency**: CRDTs, event sourcing with projections, async replication
- **Multi-step workflows**: saga orchestration (choreography vs orchestration), compensating transactions
- **Conflict resolution**: last-writer-wins, merge functions, operational transforms

### Step 4: Design Failure Handling

For each coordination pattern, specify:
- Failure detector strategy (heartbeat interval, phi-accrual, gossip)
- Partition behavior (reject writes, accept and reconcile, read-only mode)
- Recovery procedure (replay log, snapshot restore, manual intervention)
- Timeout and retry policies (idempotency keys, exponential backoff, circuit breakers)

### Step 5: Define Data Flow

Map the event/message flow for each distributed operation. Specify message ordering guarantees, delivery semantics (at-least-once, exactly-once), and dead-letter handling.

### Step 6: Validate Trade-offs

Review each pattern choice against requirements. Confirm that consistency/availability trade-offs are acceptable. Identify operational complexity costs.

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what system is being analyzed, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

> **Validation gate**: After 5+ sessions using this skill, if outputs are consistently insufficient for the problem domain, escalate to a full distributed-systems agent.

## Handoff

- If the design reveals database schema needs, recommend loading architect/schema-design.
- If the design requires API contracts between services, recommend loading architect/api-design.
- If the design introduces security boundaries, recommend loading guardian/data-classification.

## Output Format

```markdown
# Distributed Architecture: [System Name]

## System Boundaries
| Service | Owns | Communicates With |
|---------|------|-------------------|
| ...     | ...  | ...               |

## Consistency Decisions
| Operation | Pattern | CAP Choice | Justification |
|-----------|---------|------------|---------------|
| ...       | ...     | CP / AP    | ...           |

## Coordination Protocols
### [Operation Name]
- **Pattern**: [saga / consensus / CRDT / event sourcing]
- **Flow**: [step-by-step sequence]
- **Failure mode**: [what happens on partition/timeout]
- **Recovery**: [compensating action or replay strategy]

## Failure Handling
| Component | Detector | Partition Behavior | Recovery |
|-----------|----------|--------------------|----------|
| ...       | ...      | ...                | ...      |
```

## Quality Checks

- [ ] Every cross-boundary operation has an explicit consistency choice with CAP justification
- [ ] Failure modes are specified for each coordination pattern
- [ ] Recovery procedures exist for every failure mode
- [ ] Message delivery semantics are defined (at-least-once, exactly-once)
- [ ] Idempotency strategy is specified for retry-able operations
- [ ] Operational complexity is acknowledged and justified

## Evolution Notes
<!-- Observations appended after each use -->
