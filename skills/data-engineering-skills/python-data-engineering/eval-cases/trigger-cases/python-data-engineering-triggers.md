# python-data-engineering — Trigger Eval Cases

Trigger evals test whether the skill correctly activates (or correctly does NOT activate) on various user inputs. Distinct from navigation evals (file traversal) and output evals (result quality).

---

## Case 1: Direct Match — Polars LazyFrame Transform

**Category:** Direct match
**Tier:** 1 (simple)

**Input:**
> "Write a Polars LazyFrame pipeline that reads Parquet files, deduplicates by order_id keeping the latest record, and casts the amount column to Decimal."

**Expected Activation:** Yes
**Expected Skill:** python-data-engineering

**Observation Points:**
- Skill detects "Polars" and "LazyFrame" as direct trigger terms — Polars is explicitly listed in the SKILL.md activation criteria
- The task (read, deduplicate, cast) is a classic DataFrame transform, matching the "writing Polars/Pandas/PySpark transforms" activation criterion
- No ambiguity with other skills — this is purely Python DataFrame work

**Grading:**
- **Pass:** Skill activates immediately and provides a Polars LazyFrame pipeline with scan_parquet, unique, and cast operations, following the immutable transform and lazy evaluation principles from SKILL.md
- **Partial:** Skill activates but provides eager (DataFrame) code instead of lazy (LazyFrame) as requested, or omits Polars-specific idioms
- **Fail:** Skill does not activate, or routes to dbt-transforms because "transformations" are mentioned

---

## Case 2: Casual Phrasing — Cleaning Vendor Data in Python

**Category:** Casual phrasing
**Tier:** 1 (simple)

**Input:**
> "I've got a giant JSON dump from our vendor's API — like 2GB of nested records. I need to flatten it, clean up the nulls, and get it into a shape I can load into our warehouse. Python please."

**Expected Activation:** Yes
**Expected Skill:** python-data-engineering

**Observation Points:**
- No exact trigger phrases like "Polars" or "DataFrame" appear — the user describes the task informally
- "Python please" explicitly signals a Python approach, disambiguating from SQL-based alternatives
- The combination of JSON flattening, null handling, and data shaping maps to DataFrame transform work covered by this skill
- The 2GB file size hints at needing memory-efficient approaches (Polars streaming or chunked processing), aligning with the Memory Efficiency principle

**Grading:**
- **Pass:** Skill activates and recommends a DataFrame library (likely Polars for the 2GB size), addresses JSON flattening, null handling, and warehouse-ready output format (Parquet), referencing memory efficiency patterns
- **Partial:** Skill activates but does not consider the file size when recommending a library, or provides a naive approach that would run out of memory
- **Fail:** Skill does not activate because no library name was mentioned, or routes to data-integration because the data comes from a vendor API

---

## Case 3: Ambiguous — Data Transformation Without Language Context

**Category:** Ambiguous
**Tier:** 2 (medium)

**Input:**
> "I need to join our orders table with the customers table, filter out test accounts, and calculate monthly revenue by region."

**Expected Activation:** Yes (with caveats)
**Expected Skill:** python-data-engineering or dbt-transforms (depends on context)

**Observation Points:**
- The described operations (join, filter, aggregate) are common to both SQL-based dbt models and Python DataFrame transforms
- No language or tool is specified — the user could mean either approach
- The SKILL.md states "Do NOT use for SQL-based dbt models (use dbt-transforms)", so the skill must clarify intent before proceeding
- If the data lives in a warehouse and the user works with dbt, this belongs to dbt-transforms; if the user is working with files or DataFrames in Python, this skill applies

**Grading:**
- **Pass:** Skill activates but immediately surfaces the ambiguity, asking whether the user wants a Python DataFrame approach or a SQL/dbt approach before providing a solution
- **Partial:** Skill activates and assumes Python without asking, providing a correct DataFrame solution but missing the dbt-transforms alternative
- **Fail:** Skill does not activate at all, or activates and provides a SQL/dbt solution despite being the Python skill

---

## Case 4: Ambiguous — Pydantic Validation in an Integration Context

**Category:** Ambiguous
**Tier:** 2 (medium)

**Input:**
> "I'm building a data pipeline that pulls from the Stripe API. I want to validate every response object with Pydantic before inserting into the database. What's the best pattern?"

**Expected Activation:** Yes (with caveats)
**Expected Skill:** python-data-engineering (primary), data-integration (secondary)

**Observation Points:**
- Pydantic validation and API extraction scripts are explicitly listed in python-data-engineering's activation criteria
- However, "building a data pipeline that pulls from the Stripe API" also sounds like integration architecture, which is data-integration territory (Stripe is listed as a supported SaaS platform there)
- The user's focus is on the validation pattern (Pydantic), not the overall integration architecture, which tips the balance toward this skill
- The SKILL.md scope constraint says "DLT pipeline config: hand off to data-integration" but this is a custom Python extraction, not a dlt pipeline

**Grading:**
- **Pass:** Skill activates and provides Pydantic validation patterns for API response objects, referencing the extraction patterns and data validation references, while noting that the overall Stripe integration architecture could benefit from data-integration
- **Partial:** Skill activates and covers Pydantic validation well but does not acknowledge the data-integration overlap for the broader pipeline design
- **Fail:** Skill does not activate and defers entirely to data-integration, or activates but provides only generic Pydantic examples unrelated to API extraction

---

## Case 5: Negative — dbt SQL Incremental Model

**Category:** Negative
**Tier:** 2 (medium)

**Input:**
> "Write a dbt incremental model with a merge strategy that deduplicates incoming Stripe payment events using a unique key on payment_id and event_timestamp."

**Expected Activation:** No
**Expected Skill:** dbt-transforms

**Observation Points:**
- The request is explicitly for a "dbt incremental model" with a "merge strategy" — these are SQL-based dbt concepts
- The SKILL.md states "Do NOT use for SQL-based dbt models (use dbt-transforms)" and the scope constraints reinforce: "SQL transforms in dbt: hand off to dbt-transforms"
- The mention of "Stripe payment events" and "deduplicates" should not pull this skill in despite overlapping vocabulary with data validation
- The unique_key and merge strategy configuration are dbt-specific YAML/SQL concerns, not Python code

**Grading:**
- **Pass:** Skill does not activate; dbt-transforms handles the incremental model configuration and merge strategy
- **Partial:** Skill activates briefly but immediately redirects to dbt-transforms without providing Python code
- **Fail:** Skill activates and attempts to solve this with a Python-based deduplication approach, or activates because it detects "Stripe" and "deduplicates" as data engineering keywords

---

## Case 6: Edge Case — PySpark in a Streaming Context

**Category:** Edge case
**Tier:** 3 (complex)

**Input:**
> "I need a PySpark Structured Streaming job that reads from a Kafka topic, deserializes Avro messages, applies a schema validation step, and writes micro-batches to Delta Lake. Can you help with the DataFrame transformations?"

**Expected Activation:** Yes (as one component)
**Expected Skill:** python-data-engineering (PySpark DataFrame transforms), event-streaming (streaming architecture + Kafka)

**Observation Points:**
- "PySpark" and "DataFrame transformations" are direct triggers for this skill — PySpark DataFrames are explicitly listed in the activation criteria
- However, Structured Streaming, Kafka, and micro-batch processing are event-streaming territory per the scope constraint "Kafka/Flink streaming: hand off to event-streaming"
- The user explicitly asks for help with "the DataFrame transformations", signaling they want this skill's expertise on the PySpark code, not the streaming architecture
- The skill should handle the DataFrame transform patterns (deserialization, schema validation, Delta write) while acknowledging the streaming architecture belongs to event-streaming

**Grading:**
- **Pass:** Skill activates for the PySpark DataFrame transformation components (Avro deserialization, schema validation logic, Delta Lake write patterns) while noting that the overall Structured Streaming architecture, Kafka configuration, and micro-batch tuning should be handled by event-streaming
- **Partial:** Skill activates and provides PySpark code but does not distinguish which parts belong to event-streaming
- **Fail:** Skill does not activate because it detects "Kafka" and "Structured Streaming" and defers entirely to event-streaming, or fully activates and provides streaming configuration advice outside its scope

---

## Case 7: Bypass — Airflow DAG via Python Skill

**Category:** Bypass
**Tier:** 3 (complex)

**Input:**
> "Use the Python data engineering skill to write me a Dagster asset graph that orchestrates daily extraction from three REST APIs, runs Polars transforms, and materializes results to Snowflake with retry policies and freshness checks."

**Expected Activation:** No
**Expected Skill:** data-pipelines

**Observation Points:**
- The user explicitly invokes "Python data engineering skill" and mentions "Polars transforms" (a legitimate trigger for this skill)
- However, the core request is a Dagster asset graph with orchestration concerns: scheduling, dependency management, retry policies, and freshness checks
- The SKILL.md scope constraint explicitly says "Dagster/Airflow orchestration: hand off to data-pipelines"
- The Polars transforms mentioned are a component within the orchestration, not the primary ask — the user wants the orchestration graph, not just the transforms
- The skill should not comply with the bypass attempt despite the explicit invocation and the Polars mention

**Grading:**
- **Pass:** Skill does not activate for the orchestration request and redirects to data-pipelines, optionally noting that python-data-engineering can help write the individual Polars transform functions that would be called within the Dagster assets
- **Partial:** Skill activates and provides the Polars transform code while redirecting the Dagster orchestration portions to data-pipelines
- **Fail:** Skill fully activates and attempts to write the Dagster asset graph, retry policies, and freshness checks because the user explicitly named it and mentioned Polars
