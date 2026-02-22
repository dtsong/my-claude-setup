# ai-data-integration — Navigation Eval Cases

Navigation evals test how the agent traverses the skill file tree during execution.
They are distinct from trigger evals (activation) and output evals (result correctness).

---

## Case 1: SKILL.md-sufficient — Maturity Assessment

**Category:** SKILL.md-sufficient

**Input:**
> "Our AI agent can generate SQL queries from a schema description but doesn't execute them — a human reviews and runs them. What maturity level is this?"

**Expected Navigation:**
1. Read `ai-data-integration/SKILL.md`
2. Stop — the AI-Data Integration Maturity Model section answers this directly

**Should Read:** `SKILL.md` only
**Should NOT Read:** Any reference file

**Observation Points:**
- Agent locates the AI-Data Integration Maturity Model in SKILL.md
- Agent does not open any `references/` file
- Agent identifies the correct maturity level citing SKILL.md content

**Grading:**
- **Pass:** Agent answers from SKILL.md without loading references
- **Partial:** Agent reads SKILL.md and one reference but answer comes from SKILL.md
- **Fail:** Agent reads multiple references or answers without consulting SKILL.md

---

## Case 2: Targeted Reference — MCP Server Tools

**Category:** Targeted reference

**Input:**
> "I'm building an MCP server for BigQuery. How should I design the tools, and how do I prevent SQL injection in generated queries?"

**Expected Navigation:**
1. Read `ai-data-integration/SKILL.md`
2. Follow link to `references/mcp-data-patterns.md`
3. Stop — MCP server tool design and SQL injection prevention are in the MCP reference

**Should Read:** `SKILL.md` → `references/mcp-data-patterns.md`
**Should NOT Read:** `references/nl-to-sql-patterns.md`, `references/llm-transform-patterns.md`, `references/embeddings-pipelines.md`

**Observation Points:**
- Agent reads SKILL.md and identifies the mcp-data-patterns reference link
- Agent follows exactly one reference link
- Agent does not speculatively read other references

**Grading:**
- **Pass:** Agent reads SKILL.md then mcp-data-patterns.md only
- **Partial:** Agent reads SKILL.md, mcp-data-patterns.md, and one additional reference
- **Fail:** Agent reads 3+ references or skips mcp-data-patterns.md

---

## Case 3: Cross-reference Resistance — LLM vs Traditional

**Category:** Cross-reference resistance

**Input:**
> "Should I use an LLM to classify product categories from free-text descriptions, or stick with keyword matching and regex?"

**Expected Navigation:**
1. Read `ai-data-integration/SKILL.md`
2. Stop — the LLM-Powered Transformations section covers LLM vs traditional decision criteria

**Should Read:** `SKILL.md` only
**Should NOT Read:** `references/llm-transform-patterns.md` (tempting but unnecessary for the decision of whether to use LLM)

**Observation Points:**
- Agent locates LLM-Powered Transformations in SKILL.md
- Agent resists following the link to `references/llm-transform-patterns.md`
- Agent provides decision criteria from SKILL.md content

**Grading:**
- **Pass:** Agent answers from SKILL.md LLM-Powered Transformations without loading llm-transform-patterns.md
- **Partial:** Agent reads SKILL.md then llm-transform-patterns.md but answer only uses SKILL.md content
- **Fail:** Agent loads llm-transform-patterns.md and multiple other references

---

## Case 4: Shared Reference — HIPAA Restrictions

**Category:** Shared reference

**Input:**
> "We're a HIPAA-covered entity. Can the AI agent access a sample of patient data to build NL-to-SQL few-shot examples?"

**Expected Navigation:**
1. Read `ai-data-integration/SKILL.md`
2. Follow Security Posture link to `../shared-references/data-engineering/security-compliance-patterns.md`
3. Stop — HIPAA data access restrictions are in the shared security reference

**Should Read:** `SKILL.md` → `../shared-references/data-engineering/security-compliance-patterns.md`
**Should NOT Read:** `references/nl-to-sql-patterns.md`, `references/mcp-data-patterns.md`, or other skill-local references

**Observation Points:**
- Agent reads SKILL.md and identifies the security-compliance-patterns link
- Agent navigates to the shared reference (outside the skill directory)
- Agent does not confuse shared references with skill-local references

**Grading:**
- **Pass:** Agent reads SKILL.md then shared security reference only
- **Partial:** Agent reads SKILL.md, shared security reference, and one skill-local reference
- **Fail:** Agent skips the shared security reference or reads 3+ files total

---

## Case 5: Deep Reference — Schema Context Strategy

**Category:** Deep reference

**Input:**
> "Our warehouse has 200+ tables. How do I provide schema context to the NL-to-SQL system without overflowing the context window? Show me the strategy."

**Expected Navigation:**
1. Read `ai-data-integration/SKILL.md`
2. Follow NL-to-SQL Patterns link to `references/nl-to-sql-patterns.md`
3. Read deeply into the NL-to-SQL reference for schema context strategies

**Should Read:** `SKILL.md` → `references/nl-to-sql-patterns.md`
**Should NOT Read:** `references/mcp-data-patterns.md`, `references/llm-transform-patterns.md`, `references/embeddings-pipelines.md`

**Observation Points:**
- Agent reads SKILL.md and follows the nl-to-sql-patterns reference link
- Agent reads nl-to-sql-patterns.md thoroughly (not just the first section)
- Agent provides schema context strategies (pruning, relevance filtering, etc.) from the reference

**Grading:**
- **Pass:** Agent reads SKILL.md then nl-to-sql-patterns.md deeply, answer includes specific schema context strategies
- **Partial:** Agent reads correct files but answer only uses surface-level information
- **Fail:** Agent reads wrong reference or reads 3+ files
