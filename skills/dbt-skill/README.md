# dbt Skill for Claude

[![Claude Skill](https://img.shields.io/badge/Claude-Skill-5865F2)](https://docs.claude.ai/docs/agent-skills)
[![dbt](https://img.shields.io/badge/dbt-1.5+-FF694B)](https://www.getdbt.com/)
[![Snowflake](https://img.shields.io/badge/Snowflake-supported-29B5E8)](https://www.snowflake.com/)
[![BigQuery](https://img.shields.io/badge/BigQuery-supported-4285F4)](https://cloud.google.com/bigquery)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)

Comprehensive dbt (data build tool) skill for Claude Code. Get instant guidance on project structure, modeling methodology, testing strategies, CI/CD workflows, and production-ready analytics engineering.

## What This Skill Provides

**Project Structure & Modeling**
- Medallion + Kimball methodology (staging → intermediate → marts)
- Naming conventions and SQL style guide
- Materialization decision matrices
- Source configuration with freshness monitoring

**Testing & Quality**
- Testing pyramid: schema, generic, singular, and unit tests
- dbt-expectations and dbt-utils integration
- Layer-specific testing strategies
- Data quality metrics and observability

**CI/CD & Deployment**
- GitHub Actions workflows (Snowflake + BigQuery)
- Slim CI with `state:modified+`
- Blue/green deployment patterns
- SQLFluff linting integration

**Performance & Scale**
- Incremental strategies: microbatch (1.9+), merge, delete+insert, insert_overwrite
- Snowflake tuning: cluster keys, transient tables, Dynamic Tables
- BigQuery tuning: partitioning, clustering, slot management
- Cost monitoring and optimization

**Advanced Capabilities**
- Jinja macros and warehouse-adaptive patterns
- Essential packages (dbt-utils, dbt-expectations, Elementary)
- Semantic Layer and MetricFlow
- Model contracts, versions, and access controls
- dbt Mesh for multi-project architectures

## Installation

### Claude Code

```bash
# Clone to Claude skills directory
git clone https://github.com/danielsong/dbt-skill ~/.claude/skills/dbt-skill
```

### Verify Installation

After installation, try:
```
"Create a dbt project with staging and marts layers for a Snowflake warehouse"
```

Claude will automatically use the skill when working with dbt.

## Quick Start Examples

**Create a project structure:**
> "Set up a dbt project with staging and marts layers for our Stripe and Shopify data"

**Choose a materialization:**
> "Should I use incremental or table materialization for my 500M row events table?"

**Write tests:**
> "Add comprehensive tests to my fct_orders model"

**Set up CI/CD:**
> "Create a GitHub Actions workflow for dbt with Slim CI on Snowflake"

**Optimize performance:**
> "My incremental model is slow on BigQuery — help me optimize it"

## Skill Structure

The skill uses **progressive disclosure** — the core file covers essentials, reference files provide depth:

```
skills/dbt-skill/
├── SKILL.md                              # Core skill — project structure, modeling,
│                                         #   conventions, materializations, commands
└── references/
    ├── testing-quality.md                # 1️⃣  Testing & Quality Strategy
    ├── ci-cd-deployment.md               # 2️⃣  CI/CD & Deployment
    ├── jinja-macros-packages.md          # 3️⃣  Jinja, Macros & Packages
    ├── incremental-performance.md        # 4️⃣  Incremental Models & Performance
    ├── data-quality-observability.md     # 5️⃣  Data Quality & Observability
    └── semantic-layer-governance.md      # 6️⃣  Semantic Layer & Governance
```

### Learning Path

The reference files follow a deliberate progression:

1. **Testing & Quality** — Foundation: validate your models work correctly
2. **CI/CD & Deployment** — Feedback loop: automate build, test, deploy
3. **Jinja, Macros & Packages** — DRY: reduce duplication, leverage ecosystem
4. **Incremental Models & Performance** — Scale: handle growing data volumes
5. **Data Quality & Observability** — Production: monitor and alert on issues
6. **Semantic Layer & Governance** — Enterprise: centralize metrics and access control

## Warehouse Support

| Feature | Snowflake | BigQuery |
|---------|-----------|----------|
| All materializations | Yes | Yes |
| Incremental strategies | merge, delete+insert, microbatch, append | merge, insert_overwrite, microbatch, append |
| Partitioning guidance | Automatic micro-partitions | Manual partition_by config |
| Clustering guidance | Yes | Yes |
| CI/CD templates | Yes | Yes |
| Cost optimization | Credits-based | Bytes-scanned / Slots |
| Dynamic Tables | Yes | N/A |

## Requirements

- **Claude Code** or other Claude environment supporting skills
- **dbt Core** 1.5+ or **dbt Cloud**
- **Snowflake** or **BigQuery** warehouse (primary targets)
- Other warehouses (Redshift, Databricks, Postgres) work with dbt but receive less specific guidance in this skill

## Contributing

Contributions welcome! When submitting changes:

1. Follow the imperative voice style ("Use X", not "You should consider X")
2. Include both Snowflake and BigQuery examples where relevant
3. Use practical e-commerce domain examples (orders, payments, customers)
4. Keep the core SKILL.md under ~500 lines
5. Reference files should be self-contained with TOC and back-links

## License

Apache 2.0 — see [LICENSE](../../LICENSE) for full terms.

**Copyright 2026 Daniel Song**
