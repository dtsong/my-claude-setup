---
name: "Pipeline Design"
department: "alchemist"
description: "[Council] Design data pipelines with ETL/ELT, orchestration, batch vs streaming, and data quality. Used during council/academy deliberation only."
version: 1
triggers:
  - "pipeline"
  - "ETL"
  - "ELT"
  - "orchestration"
  - "Airflow"
  - "Dagster"
  - "Prefect"
  - "dbt"
  - "batch"
  - "streaming"
  - "Kafka"
  - "ingestion"
  - "transformation"
  - "lineage"
  - "data quality"
---

# Pipeline Design

## Purpose

Design data pipelines that reliably move, transform, and deliver data from source systems to consumption layers. Covers ETL vs ELT pattern selection, orchestration tool choice, batch vs streaming trade-offs, idempotency guarantees, data quality checkpoints, and lineage tracking.

## Inputs

- Source systems and their data formats (databases, APIs, event streams, files)
- Destination systems (warehouse, lake, feature store, BI tool)
- Data volume and velocity (rows/day, events/second, payload size)
- Freshness requirements (real-time, near-real-time, hourly, daily)
- Existing infrastructure (cloud provider, orchestration tools, current pipelines)
- Team size and expertise (SQL-heavy? Python-heavy? Platform team available?)

## Process

### Step 1: Map Source-to-Destination Flows

Document every data flow:
- Source system, extraction method (CDC, API poll, event subscription, file drop)
- Transformation requirements (cleaning, joining, aggregating, enriching)
- Destination system and loading pattern (append, upsert, full refresh)
- Data volume per flow (rows/batch, events/second)

Produce a flow diagram showing all sources, transformations, and destinations.

### Step 2: Choose ETL vs ELT Pattern

Evaluate the trade-offs:
- **ETL (Extract-Transform-Load):** Transform before loading. Best when: destination has limited compute, transformations reduce data volume significantly, or sensitive data must be filtered before landing.
- **ELT (Extract-Load-Transform):** Load raw first, transform in-warehouse. Best when: destination has powerful compute (BigQuery, Snowflake, Databricks), you want raw data preserved for auditability, or transformation logic changes frequently.

Document the chosen pattern per flow and the reasoning.

### Step 3: Select Batch vs Streaming

For each flow, determine the processing mode:
- **Batch:** Scheduled intervals (hourly, daily). Simple, cost-effective, good tooling. Best when freshness SLA is minutes-to-hours.
- **Micro-batch:** Frequent small batches (every 1-5 minutes). Compromise between batch simplicity and near-real-time freshness.
- **Streaming:** Continuous processing (Kafka, Kinesis, Flink). Best when freshness SLA is seconds and data arrives as an event stream.

Document latency requirements, cost implications, and complexity trade-offs for the chosen mode.

### Step 4: Design for Idempotency

Ensure every pipeline step is safe to re-run:
- Use merge/upsert patterns instead of blind inserts
- Partition data by time to enable clean backfills without full re-processing
- Use deterministic IDs (content-based hashing) or natural keys for deduplication
- Document the idempotency strategy for each pipeline step: "If this step runs twice for the same input, what happens?"

### Step 5: Define Data Quality Checkpoints

Insert quality gates between pipeline stages:
- **Source validation:** Schema conformance, null rates, row count thresholds
- **Transformation validation:** Referential integrity, business rule assertions, duplicate detection
- **Destination validation:** Row count reconciliation (source vs destination), freshness checks, metric drift alerts

For each checkpoint, define: what is checked, what threshold triggers a failure, and what happens on failure (halt pipeline, alert, quarantine bad records).

### Step 6: Plan Lineage and Observability

Design data lineage tracking:
- Column-level lineage from source to destination
- Transformation dependency graph (which tables feed which downstream models)
- Pipeline execution metadata (start time, end time, rows processed, errors)
- Alerting on SLA breaches, data quality failures, and pipeline errors

Specify tooling: dbt lineage, OpenLineage, Datahub, or custom metadata tables.

### Step 7: Select Orchestration Tool

Choose the orchestration layer based on team and requirements:
- **dbt** — SQL-centric transformations, built-in lineage, great for ELT. Best for analytics engineering teams.
- **Airflow** — General-purpose DAG orchestration, large ecosystem, battle-tested. Best for complex multi-system pipelines.
- **Dagster** — Software-defined assets, strong typing, built-in observability. Best for teams wanting modern DX and asset-centric thinking.
- **Prefect** — Python-native, dynamic workflows, lightweight. Best for Python-heavy teams with simpler orchestration needs.

Document the choice, alternatives considered, and migration path if the team outgrows the tool.

## Output Format

```markdown
# Pipeline Design: [Project/Domain Name]

## Flow Diagram

```
[ASCII diagram showing sources → transformations → destinations]
```

## Flow Inventory

| Flow | Source | Extraction | Transform | Load Pattern | Volume | Freshness SLA |
|------|--------|-----------|-----------|-------------|--------|---------------|
| ...  | ...    | ...       | ...       | ...         | ...    | ...           |

## Architecture Decisions

| Decision | Chosen | Alternatives | Rationale |
|----------|--------|-------------|-----------|
| ETL vs ELT | ... | ... | ... |
| Batch vs Streaming | ... | ... | ... |
| Orchestration tool | ... | ... | ... |

## Idempotency Strategy

| Pipeline Step | Idempotency Method | Re-run Behavior |
|---------------|-------------------|-----------------|
| ...           | ...               | ...             |

## Data Quality Checkpoints

| Stage | Check | Threshold | On Failure |
|-------|-------|-----------|------------|
| Source | ... | ... | ... |
| Transform | ... | ... | ... |
| Destination | ... | ... | ... |

## Lineage and Observability

| Capability | Tool/Method | Coverage |
|-----------|-------------|----------|
| Column lineage | ... | ... |
| Pipeline metrics | ... | ... |
| Alerting | ... | ... |

## Orchestration Design

| DAG/Pipeline | Schedule | Dependencies | SLA |
|-------------|----------|-------------|-----|
| ...         | ...      | ...         | ... |
```

## Quality Checks

- [ ] Every source-to-destination flow is documented with volume and freshness SLA
- [ ] ETL vs ELT decision is justified per flow, not assumed globally
- [ ] Batch vs streaming choice is driven by freshness requirements, not preference
- [ ] Every pipeline step has an idempotency strategy documented
- [ ] Data quality checkpoints exist between each pipeline stage
- [ ] Failure handling is specified for each checkpoint (halt, alert, quarantine)
- [ ] Lineage tracking covers column-level provenance for critical fields
- [ ] Orchestration tool selection considers team expertise and existing infrastructure
- [ ] Backfill strategy is documented — how to reprocess historical data safely

## Evolution Notes
<!-- Observations appended after each use -->
