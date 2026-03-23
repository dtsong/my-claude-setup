---
name: "Alchemist Department"
executive: "Alchemist"
color: "Indigo"
description: "Data engineering, data science, ML workflows, analytics"
---

# Alchemist Department — Indigo Lens

The Alchemist's department of focused skills for data warehouse modeling, pipeline architecture, and ML workflow design.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [schema-evaluation](schema-evaluation/SKILL.md) | Data warehouse schema design and evaluation | default | `schema`, `data model`, `warehouse`, `dimension`, `fact table`, `SCD`, `grain`, `normalization`, `data vault`, `star schema` |
| [pipeline-design](pipeline-design/SKILL.md) | ETL/ELT pipeline architecture and orchestration | default | `pipeline`, `ETL`, `ELT`, `orchestration`, `Airflow`, `dbt`, `batch`, `streaming`, `Kafka`, `ingestion`, `transformation`, `lineage` |
| [ml-workflow](ml-workflow/SKILL.md) | ML workflow design with experiment tracking and model serving | default | `ML`, `machine learning`, `model`, `training`, `feature store`, `MLflow`, `experiment`, `drift`, `serving`, `inference` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Schema design, data modeling, star/snowflake/data vault, grain definition, SCD strategy | schema-evaluation | High |
| ETL/ELT pipelines, orchestration, batch vs streaming, Airflow/dbt/Dagster, data lineage | pipeline-design | High |
| ML model training, experiment tracking, feature stores, model serving, drift monitoring | ml-workflow | High |
| "Data quality" in context of pipeline checkpoints or ingestion validation | pipeline-design | Medium |
| "Data quality" in context of schema contracts or warehouse integrity | schema-evaluation | Medium |

## Shared Directives

Load Directive, Handoff Protocol, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
