# python-data-engineering — Navigation Eval Cases

Navigation evals test how the agent traverses the skill file tree during execution.
They are distinct from trigger evals (activation) and output evals (result correctness).

---

## Case 1: SKILL.md-sufficient — Library Selection

**Category:** SKILL.md-sufficient

**Input:**
> "I need to process a 500GB Parquet dataset on a single machine with minimal memory usage. Which DataFrame library should I use?"

**Expected Navigation:**
1. Read `python-data-engineering/SKILL.md`
2. Stop — the DataFrame Library Decision Matrix section answers this directly

**Should Read:** `SKILL.md` only
**Should NOT Read:** Any reference file

**Observation Points:**
- Agent locates the DataFrame Library Decision Matrix in SKILL.md
- Agent does not open any `references/` file
- Agent provides a library recommendation (Polars lazy, DuckDB, etc.) citing SKILL.md content

**Grading:**
- **Pass:** Agent answers from SKILL.md without loading references
- **Partial:** Agent reads SKILL.md and one reference but answer comes from SKILL.md
- **Fail:** Agent reads multiple references or answers without consulting SKILL.md

---

## Case 2: Targeted Reference — Polars LazyFrame

**Category:** Targeted reference

**Input:**
> "Explain how Polars LazyFrame query optimization works. Show me the execution plan and optimization passes."

**Expected Navigation:**
1. Read `python-data-engineering/SKILL.md`
2. Follow link to `references/polars-patterns.md`
3. Stop — LazyFrame optimization details are in the Polars reference

**Should Read:** `SKILL.md` → `references/polars-patterns.md`
**Should NOT Read:** `references/pandas-patterns.md`, `references/pyspark-patterns.md`, `references/data-validation-patterns.md`, `references/extraction-patterns.md`

**Observation Points:**
- Agent reads SKILL.md and identifies the polars-patterns reference link
- Agent follows exactly one reference link
- Agent does not speculatively read other DataFrame library references

**Grading:**
- **Pass:** Agent reads SKILL.md then polars-patterns.md only
- **Partial:** Agent reads SKILL.md, polars-patterns.md, and one additional reference
- **Fail:** Agent reads 3+ references or skips polars-patterns.md

---

## Case 3: Cross-reference Resistance — Pydantic Validation

**Category:** Cross-reference resistance

**Input:**
> "I want to validate API responses with Pydantic before loading them into my pipeline. What's the basic pattern?"

**Expected Navigation:**
1. Read `python-data-engineering/SKILL.md`
2. Stop — the Data Validation section and Type Safety First principle cover basic Pydantic usage

**Should Read:** `SKILL.md` only
**Should NOT Read:** `references/data-validation-patterns.md` (tempting but unnecessary for basic Pydantic validation pattern)

**Observation Points:**
- Agent locates Data Validation and Type Safety First sections in SKILL.md
- Agent resists following the link to `references/data-validation-patterns.md`
- Agent provides basic Pydantic model pattern from SKILL.md content

**Grading:**
- **Pass:** Agent answers from SKILL.md without loading data-validation-patterns.md
- **Partial:** Agent reads SKILL.md then data-validation-patterns.md but answer only uses SKILL.md content
- **Fail:** Agent loads data-validation-patterns.md and multiple other references

---

## Case 4: Shared Reference — API Credentials

**Category:** Shared reference

**Input:**
> "What's the best practice for API key management in Python extraction scripts across dev and production environments?"

**Expected Navigation:**
1. Read `python-data-engineering/SKILL.md`
2. Follow Security link to `../shared-references/data-engineering/security-compliance-patterns.md`
3. Stop — credential management patterns are in the shared security reference

**Should Read:** `SKILL.md` → `../shared-references/data-engineering/security-compliance-patterns.md`
**Should NOT Read:** `references/extraction-patterns.md`, `references/polars-patterns.md`, or other skill-local references

**Observation Points:**
- Agent reads SKILL.md and identifies the security-compliance-patterns link
- Agent navigates to the shared reference (outside the skill directory)
- Agent does not confuse shared references with skill-local references

**Grading:**
- **Pass:** Agent reads SKILL.md then shared security reference only
- **Partial:** Agent reads SKILL.md, shared security reference, and one skill-local reference
- **Fail:** Agent skips the shared security reference or reads 3+ files total

---

## Case 5: Deep Reference — Async Extraction

**Category:** Deep reference

**Input:**
> "I need to extract from 1000 API endpoints in parallel with rate limiting using async httpx. Show me the full pattern."

**Expected Navigation:**
1. Read `python-data-engineering/SKILL.md`
2. Follow API Extraction link to `references/extraction-patterns.md`
3. Read deeply into the extraction reference for async patterns

**Should Read:** `SKILL.md` → `references/extraction-patterns.md`
**Should NOT Read:** `references/polars-patterns.md`, `references/pandas-patterns.md`, `references/pyspark-patterns.md`, `references/data-validation-patterns.md`

**Observation Points:**
- Agent reads SKILL.md and follows the extraction-patterns reference link
- Agent reads extraction-patterns.md thoroughly (not just the first section)
- Agent provides async httpx patterns with rate limiting from the reference

**Grading:**
- **Pass:** Agent reads SKILL.md then extraction-patterns.md deeply, answer includes specific async httpx code
- **Partial:** Agent reads correct files but answer only uses surface-level information
- **Fail:** Agent reads wrong reference or reads 3+ files
