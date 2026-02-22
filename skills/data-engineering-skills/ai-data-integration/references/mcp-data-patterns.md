## Contents

- [Architecture Overview](#architecture-overview)
- [Snowflake MCP Server](#snowflake-mcp-server)
- [Multi-Warehouse Routing](#multi-warehouse-routing)
- [Context Management](#context-management)
  - [Tool Selection by Maturity Level](#tool-selection-by-maturity-level)
- [AI Query Audit Trail](#ai-query-audit-trail)

---

# MCP Data Patterns Reference

> MCP server architecture for warehouse and data platform integration. Part of the [AI Data Integration Skill](../SKILL.md).

---

## Architecture Overview

```
┌──────────────┐     MCP Protocol     ┌──────────────────┐     SQL      ┌───────────┐
│  AI Agent    │ ◄──────────────────► │  MCP Data Server  │ ◄──────────► │ Warehouse │
│  (Claude)    │    Tools + Results    │  (Guardrails)     │   Read-Only  │ (Snowflake│
└──────────────┘                      └──────────────────┘              │  BigQuery) │
                                             │                          └───────────┘
                                             │ Audit Log
                                             ▼
                                      ┌──────────────┐
                                      │ audit.ai_log │
                                      └──────────────┘
```

---

## Snowflake MCP Server

```python
from mcp.server import Server
from mcp.types import Tool, TextContent
import snowflake.connector
import os, hashlib

# ── Credential boundary ──────────────────────────────────────────────
# export SNOWFLAKE_ACCOUNT, SNOWFLAKE_USER, SNOWFLAKE_ROLE
# export SNOWFLAKE_PRIVATE_KEY_PATH, SNOWFLAKE_WAREHOUSE
# Use a dedicated AI_READER role with read-only access to approved schemas.
# ─────────────────────────────────────────────────────────────────────

class WarehouseConfig:
    MAX_ROWS = 1000
    QUERY_TIMEOUT_SECONDS = 30
    ALLOWED_SCHEMAS = ["STAGING", "MARTS", "REFERENCE"]
    BLOCKED_PATTERNS = ["PII", "AUDIT", "ADMIN", "PASSWORD", "SECRET"]

app = Server("snowflake-mcp")

def get_connection():
    return snowflake.connector.connect(
        account=os.environ["SNOWFLAKE_ACCOUNT"],
        user=os.environ["SNOWFLAKE_USER"],
        private_key_file_path=os.environ["SNOWFLAKE_PRIVATE_KEY_PATH"],
        warehouse=os.environ.get("SNOWFLAKE_WAREHOUSE", "AI_READER_WH"),
        role=os.environ.get("SNOWFLAKE_ROLE", "AI_READER"),
        database=os.environ.get("SNOWFLAKE_DATABASE", "ANALYTICS"),
    )

@app.tool()
async def list_schemas() -> list[TextContent]:
    """List database schemas available to the AI reader role."""
    conn = get_connection()
    cursor = conn.cursor()
    cursor.execute("SHOW SCHEMAS IN DATABASE")
    schemas = [row[1] for row in cursor.fetchall()
               if row[1].upper() in WarehouseConfig.ALLOWED_SCHEMAS]
    conn.close()
    return [TextContent(type="text", text="\n".join(schemas))]

@app.tool()
async def describe_table(schema_name: str, table_name: str) -> list[TextContent]:
    """Describe columns, types, and comments for a table."""
    schema, table = schema_name.upper(), table_name.upper()
    if schema not in WarehouseConfig.ALLOWED_SCHEMAS:
        return [TextContent(type="text", text=f"Schema '{schema}' is not accessible")]
    conn = get_connection()
    cursor = conn.cursor()
    cursor.execute(f"""
        SELECT column_name, data_type, is_nullable, comment
        FROM information_schema.columns
        WHERE table_schema = '{schema}' AND table_name = '{table}'
        ORDER BY ordinal_position
    """)
    rows = cursor.fetchall()
    conn.close()
    lines = [f"{name:<30} {dtype:<20} {nullable:<10} {comment or ''}"
             for name, dtype, nullable, comment in rows]
    return [TextContent(type="text", text=f"Table: {schema}.{table}\n" + "\n".join(lines))]

@app.tool()
async def run_query(sql: str) -> list[TextContent]:
    """Execute a read-only SQL query with guardrails."""
    is_valid, reason = validate_query(sql)
    if not is_valid:
        return [TextContent(type="text", text=f"Query rejected: {reason}")]
    conn = get_connection()
    cursor = conn.cursor()
    try:
        cursor.execute(f"ALTER SESSION SET STATEMENT_TIMEOUT_IN_SECONDS = {WarehouseConfig.QUERY_TIMEOUT_SECONDS}")
        cursor.execute(sql)
        columns = [desc[0] for desc in cursor.description]
        rows = cursor.fetchall()
        header = "| " + " | ".join(columns) + " |"
        separator = "| " + " | ".join(["---"] * len(columns)) + " |"
        data_rows = ["| " + " | ".join(str(v) for v in row) + " |" for row in rows]
        return [TextContent(type="text", text="\n".join([header, separator] + data_rows))]
    except Exception as e:
        return [TextContent(type="text", text=f"Query error: {str(e)}")]
    finally:
        conn.close()

def validate_query(sql: str) -> tuple[bool, str]:
    sql_upper = sql.strip().upper()
    if not sql_upper.startswith("SELECT"):
        return False, "Only SELECT statements are allowed"
    blocked = ["INSERT", "UPDATE", "DELETE", "DROP", "CREATE", "ALTER", "TRUNCATE", "GRANT", "REVOKE"]
    for kw in blocked:
        if f" {kw} " in f" {sql_upper} ":
            return False, f"Blocked keyword: {kw}"
    if "LIMIT" not in sql_upper:
        return False, "Query must include a LIMIT clause"
    for pattern in WarehouseConfig.BLOCKED_PATTERNS:
        if pattern in sql_upper:
            return False, f"Query references blocked pattern: {pattern}"
    return True, "Valid"
```

---

## Multi-Warehouse Routing

For organizations with multiple warehouses, use a unified MCP server that routes to the appropriate backend:

```python
WAREHOUSES = {
    "snowflake_analytics": SnowflakeBackend(database="ANALYTICS"),
    "bigquery_marketing": BigQueryBackend(dataset="marketing"),
    "duckdb_local": DuckDBBackend(path="local.duckdb"),
}

@app.tool()
async def query(warehouse: str, sql: str) -> list[TextContent]:
    if warehouse not in WAREHOUSES:
        return [TextContent(type="text", text=f"Unknown warehouse: {warehouse}")]
    return await WAREHOUSES[warehouse].execute(sql)
```

---

## Context Management

Manage schema context carefully -- LLMs have limited context windows:

```python
def build_focused_context(question: str, all_tables: list[dict], max_tables: int = 10) -> str:
    scored_tables = score_table_relevance(question, all_tables)[:max_tables]
    context_parts = []
    for table in scored_tables:
        cols = [f"  {c['name']} {c['type']}" + (f" -- {c['comment']}" if c.get('comment') else "")
                for c in table["columns"][:20]]
        context_parts.append(f"-- {table['schema']}.{table['name']}\n" + "\n".join(cols))
    return "\n\n".join(context_parts)
```

### Tool Selection by Maturity Level

```python
TOOLS_BY_LEVEL = {
    0: [],                                                        # Code gen only
    1: ["list_schemas", "list_tables", "describe_table"],         # Metadata
    2: ["list_schemas", "list_tables", "describe_table", "sample_table"],  # + samples
    3: ["list_schemas", "list_tables", "describe_table", "sample_table", "run_query"],  # + queries
}
```

---

## AI Query Audit Trail

```sql
CREATE TABLE IF NOT EXISTS audit.ai_query_log (
    query_id STRING DEFAULT UUID_STRING(),
    agent_id STRING,           -- Which AI agent/MCP server
    prompt_hash STRING,        -- SHA-256 of the originating prompt
    generated_sql STRING,
    execution_status STRING,   -- 'approved', 'rejected', 'executed', 'failed'
    result_row_count INTEGER,
    execution_time_ms INTEGER,
    warehouse_credits_used FLOAT,
    reviewed_by STRING,        -- Human reviewer (Tier 2)
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP()
);
```
