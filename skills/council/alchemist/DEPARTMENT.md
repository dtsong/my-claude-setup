---
name: "Alchemist Department"
executive: "Alchemist"
color: "Indigo"
description: "Data engineering, data science, ML workflows, analytics"
---

# Alchemist Department — Indigo Lens

The Alchemist's department of focused skills for data warehouse modeling, pipeline architecture, and ML workflow design.

## Skills

| Skill | Purpose | Triggers |
|-------|---------|----------|
| [schema-evaluation](schema-evaluation/SKILL.md) | Data warehouse schema design and evaluation | `schema`, `data model`, `warehouse`, `dimension`, `fact table`, `SCD`, `grain`, `normalization`, `data vault`, `star schema` |
| [pipeline-design](pipeline-design/SKILL.md) | ETL/ELT pipeline architecture and orchestration | `pipeline`, `ETL`, `ELT`, `orchestration`, `Airflow`, `dbt`, `batch`, `streaming`, `Kafka`, `ingestion`, `transformation`, `lineage` |
| [ml-workflow](ml-workflow/SKILL.md) | ML workflow design with experiment tracking and model serving | `ML`, `machine learning`, `model`, `training`, `feature store`, `MLflow`, `experiment`, `drift`, `serving`, `inference` |

## When This Department Activates

The Alchemist activates when data engineering, data science, or analytics concerns are raised. Any mention of schemas, pipelines, warehousing, ML workflows, data quality, or BI tools triggers inclusion.

## Department Philosophy

Model the grain first, validate quality before use, and keep pipelines idempotent. Prefer SQL where SQL suffices — complexity should be earned. Separate storage from compute, and always trace data lineage from source to serving layer.
