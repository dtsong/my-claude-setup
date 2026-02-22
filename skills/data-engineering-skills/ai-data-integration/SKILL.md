---
name: ai-data-integration
description: "Use this skill when connecting AI or LLMs to data platforms. Covers MCP servers for warehouses, natural-language-to-SQL, embeddings for data discovery, LLM-powered enrichment, and AI agent data access patterns. Common phrases: \"text-to-SQL\", \"MCP server for Snowflake\", \"LLM data enrichment\", \"AI agent access\". Do NOT use for general data integration (use data-integration) or dbt modeling (use dbt-transforms)."
model:
  preferred: sonnet
  acceptable: [sonnet, opus]
  minimum: sonnet
  allow_downgrade: false
  reasoning_demand: medium
  conditions:
    - when: "designing novel security tier taxonomy from scratch"
      hold_at: opus
version: 1.0.0
---

# AI Data Integration Skill for Claude

Expert guidance for integrating AI/LLM capabilities with data engineering systems. Covers MCP server patterns for warehouses, NL-to-SQL generation, LLM-powered data transformations, and embeddings for data discovery. Security tiers are deeply integrated -- not bolted on.

**Not an ML/MLOps skill.** Covers how AI agents *interact with* data platforms, not model training or deployment.

## When to Use

**Activate when:** building MCP servers for warehouse data, implementing NL-to-SQL interfaces, using LLMs for data enrichment/classification/extraction in pipelines, building embeddings for catalog search or semantic matching, designing AI agent access with security guardrails, evaluating when AI adds value vs traditional approaches.

**Don't use for:** ML model training/experiment tracking, general prompt engineering, chatbots/conversational AI, dbt/DLT/orchestration (use domain skills), Python DataFrame transforms without LLM involvement (`python-data-engineering`).

## Scope Constraints

- This skill generates *integration patterns*, not production-ready applications.
- All code examples assume read-only warehouse access unless explicitly stated.
- Security guidance covers AI-specific concerns only -- see [Security & Compliance Patterns](../shared-references/data-engineering/security-compliance-patterns.md) for the full framework.
- Cost estimates are approximate and vary by provider and model version.

## Model Routing

| reasoning_demand | preferred | acceptable | minimum |
|-----------------|-----------|------------|---------|
| medium | Sonnet | Sonnet, Opus | Sonnet |

Condition: designing novel security tier taxonomy from scratch → hold at Opus.

## Core Principles

### 1. Progressive Trust

Never start with full data access. Graduate through trust levels (see Maturity Model below).

### 2. Least Privilege

AI agents get minimum data access required: read-only connections, scoped to specific schemas/tables, row-limited queries, cost-capped, and audit-logged with the originating prompt.

### 3. Cost Awareness

LLM calls have real cost in data pipelines. Rule of thumb: if calling an LLM per-row on millions of rows, batch, cache, or use traditional approaches instead. See reference files for cost tables.

### 4. Human-in-the-Loop

AI-generated SQL and transforms need review in regulated environments:
- **Tier 1**: Auto-execute against dev/staging with logging
- **Tier 2**: Generate for human review, execute after approval
- **Tier 3**: Generate code only, human handles all execution

### 5. Determinism Where Possible

For reproducible pipelines: cache LLM results, use structured output (JSON mode), implement fallback logic for invalid output, log all inputs/outputs.

---

## AI-Data Integration Maturity Model

| Level | Name | AI Can Access | AI Can Do | Security Tier |
|-------|------|---------------|-----------|---------------|
| **0** | Code Generation | Nothing -- generates code offline | Write SQL, Python, YAML, configs | Tier 3 (Air-Gapped) |
| **1** | Metadata Aware | Schemas, column types, row counts, stats | Generate context-aware SQL using real schema | Tier 2-3 |
| **2** | Sample Access | Representative data samples (10-100 rows) | Understand data patterns, suggest transforms | Tier 1-2 |
| **3** | Guarded Execution | Read-only query results (with limits) | Run NL-to-SQL, explore data, answer questions | Tier 1 |

**Most organizations operate at Level 0-1.** Level 2-3 requires explicit security review and approval.

---

## MCP Server Patterns for Data

Build an MCP server for your warehouse to give AI agents structured, controlled access.

### Tool Design Principles

| Principle | Implementation |
|-----------|---------------|
| **Least privilege** | Separate tools for metadata vs data access |
| **Input validation** | Prevent SQL injection via parameterized queries or allowlists |
| **Output limiting** | Always enforce row limits; truncate large results |
| **Audit logging** | Log every invocation: who (agent), what (tool + params), when, result summary |
| **Graceful degradation** | Return helpful errors; never expose stack traces or connection strings |
| **Progressive disclosure** | Offer metadata tools first; gate data access behind explicit config |

For MCP server code examples (Snowflake, BigQuery, multi-warehouse, connection pooling, context management), see [MCP Data Patterns Reference](references/mcp-data-patterns.md).

---

## NL-to-SQL Patterns

NL-to-SQL translates user questions into warehouse queries -- the most common AI-data integration pattern. Key success factors: provide accurate schema context to the LLM, validate generated SQL before execution, enforce LIMIT clauses and schema allowlists, cache results for repeated questions.

For implementation patterns (schema context strategies, few-shot examples, query validation with sqlglot, caching, evaluation metrics, error recovery), see [NL-to-SQL Patterns Reference](references/nl-to-sql-patterns.md).

---

## LLM-Powered Transformations

Use LLMs for transforms difficult with traditional code: classification of free-text, entity extraction from unstructured text, enrichment with world knowledge, and data quality assessment.

| Use LLM When | Use Traditional Code When |
|--------------|--------------------------|
| Classifying free-text into categories | Categories map to simple rules or keywords |
| Extracting entities from unstructured text | Data has consistent structure (regex works) |
| Enriching records with world knowledge | Enrichment comes from a lookup table or API |
| Assessing data quality of text fields | Quality checks are numeric/null/format-based |
| Resolving ambiguous entity matches | Exact or fuzzy string matching suffices |

For batch processing patterns (classification, entity extraction, structured output, caching, cost monitoring), see [LLM Transform Patterns Reference](references/llm-transform-patterns.md).

---

## Embeddings for Data Discovery

Use embeddings to make your data platform searchable by meaning, not keywords.

| Use Case | Description |
|----------|-------------|
| **Data catalog search** | "Find tables related to customer churn" -- discover by semantic meaning |
| **Column matching** | Match columns across systems by meaning: `cust_id` = `customer_identifier` |
| **Documentation search** | RAG over dbt docs, data dictionaries, runbooks |
| **Query suggestion** | Find similar past queries to reuse validated SQL |

For embedding pipelines (vector stores, chunking, catalog embedding, RAG over documentation, semantic column matching), see [Embeddings Pipelines Reference](references/embeddings-pipelines.md).

---

## Input Sanitization

User-provided text becomes SQL in NL-to-SQL and MCP server patterns. Treat all user input as untrusted.

| Control | Implementation |
|---------|---------------|
| **Parameterized queries** | Never interpolate user input into SQL strings. Use bind parameters for all user-supplied values. |
| **Schema allowlists** | Restrict queryable schemas/tables to an explicit allowlist. Reject queries referencing non-allowed objects. |
| **Query type restriction** | Parse generated SQL with sqlglot or similar. Allow only SELECT statements — reject INSERT, UPDATE, DELETE, DDL, and COPY. |
| **Input length limits** | Cap user prompt length (e.g., 1,000 chars). Reject inputs that embed SQL fragments or escape sequences. |
| **Output sanitization** | Return query results only. Never expose connection strings, internal errors, or stack traces to the user. |

Apply these controls at the MCP tool boundary and the NL-to-SQL execution boundary. See [NL-to-SQL Patterns Reference](references/nl-to-sql-patterns.md) for query validation implementation.

---

## Security Posture

**This is the highest-risk skill in the suite** -- AI accessing production data requires careful guardrails. See [Security & Compliance Patterns](../shared-references/data-engineering/security-compliance-patterns.md) for the full framework.

**Credentials required**: LLM API keys, warehouse connections (read-only), vector database access. Configure via environment variables. Use separate credentials for AI access vs human access.

### Capabilities by Security Tier

| Capability | Tier 1 (Cloud-Native) | Tier 2 (Regulated) | Tier 3 (Air-Gapped) |
|------------|----------------------|--------------------|--------------------|
| Code generation (Level 0) | Yes | Yes | Yes |
| Metadata access (Level 1) | Yes (dev/staging) | Schema only, human approval | No -- provide manually |
| Sample data (Level 2) | Yes (dev, 10-100 rows) | Synthetic/anonymized only | No data access |
| Query execution (Level 3) | Dev/staging with guardrails | No | No |
| NL-to-SQL | Generate and execute (dev) | Generate for review | Generate for review |
| LLM enrichment | Process dev data | Process anonymized data | Generate code only |
| MCP server | Dev/staging | Metadata-only tools | Not deployed |
| Embeddings | Embed metadata + data | Metadata only | Documentation only |

### AI-Specific Credential Rules

1. **Separate service accounts** -- AI agents use a different warehouse account than human users
2. **Read-only roles** -- no INSERT/UPDATE/DELETE/DDL permissions
3. **Schema scoping** -- AI roles access approved schemas only (`STAGING`, `MARTS` -- never `RAW` or `PII`)
4. **Query logging** -- all AI-initiated queries logged with originating prompt for audit
5. **Cost controls** -- warehouse-level credit limits and query timeout for AI service accounts
6. **API key isolation** -- LLM API keys for pipelines separate from application keys
7. **Rotation** -- rotate AI credentials on shorter cycles than human accounts

For the AI query audit trail schema, see [MCP Data Patterns Reference](references/mcp-data-patterns.md).

---

## Reference Files

- [MCP Data Patterns](references/mcp-data-patterns.md) -- MCP server architecture, multi-warehouse support, connection pooling, context management, audit trail
- [NL-to-SQL Patterns](references/nl-to-sql-patterns.md) -- Schema context strategies, few-shot examples, query validation, caching, evaluation
- [Embeddings Pipelines](references/embeddings-pipelines.md) -- Vector stores, chunking, catalog embedding, RAG over documentation
- [LLM Transform Patterns](references/llm-transform-patterns.md) -- Batch processing, entity extraction, classification, structured output, cost optimization
