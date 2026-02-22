# ai-data-integration — Trigger Eval Cases

Trigger evals test whether the skill correctly activates (or correctly does NOT activate) on various user inputs. Distinct from navigation evals (file traversal) and output evals (result quality).

---

## Case 1: Direct Match — MCP Server for Snowflake

**Category:** Direct match
**Tier:** 1 (simple)

**Input:**
> "I need to build an MCP server that gives Claude access to our Snowflake warehouse so it can look up schema metadata and run read-only queries."

**Expected Activation:** Yes
**Expected Skill:** ai-data-integration

**Observation Points:**
- Prompt contains exact trigger phrases "MCP server" and "Snowflake"
- Core use case listed in SKILL.md: "building MCP servers for warehouse data"
- No competing skill handles MCP server patterns for data platforms

**Grading:**
- **Pass:** Skill activates and begins guidance on MCP server tool design, least-privilege access, and Snowflake connection patterns
- **Partial:** Skill activates but treats it as a generic integration task rather than MCP-specific guidance
- **Fail:** Skill does not activate, or data-integration activates instead

---

## Case 2: Casual Phrasing — Let AI Understand Our Data

**Category:** Casual phrasing
**Tier:** 1 (simple)

**Input:**
> "We have thousands of tables in our warehouse and nobody can find anything. I want to make it so people can search for datasets by describing what they need in plain language instead of knowing exact table names."

**Expected Activation:** Yes
**Expected Skill:** ai-data-integration

**Observation Points:**
- No explicit trigger phrases ("embeddings", "semantic search", "vector") appear in the prompt
- Intent maps to "embeddings for data discovery" and "data catalog search" use cases in SKILL.md
- The phrase "search by describing what they need in plain language" is a casual restatement of semantic search over a data catalog

**Grading:**
- **Pass:** Skill activates and identifies this as an embeddings-for-data-discovery use case, providing guidance on catalog embedding and semantic search
- **Partial:** Skill activates but misidentifies the pattern (e.g., treats it as NL-to-SQL instead of catalog search)
- **Fail:** Skill does not activate because no explicit AI/LLM keywords appear, or data-integration activates because it sees "data integration"

---

## Case 3: Ambiguous — LLM Enrichment or Traditional ETL

**Category:** Ambiguous
**Tier:** 2 (medium)

**Input:**
> "I need to classify 500K support tickets into product categories and sentiment. The ticket text is messy free-form — lots of typos and abbreviations."

**Expected Activation:** Yes (with caveats)
**Expected Skill:** ai-data-integration (primary), python-data-engineering (possible secondary)

**Observation Points:**
- Classifying messy free-text into categories is listed in the SKILL.md LLM-Powered Transformations table under "Use LLM When"
- However, the user does not mention LLMs, AI, or any specific approach — they could intend keyword matching, ML classifiers, or LLM enrichment
- At 500K records, cost awareness is a concern (Core Principle 3)
- python-data-engineering could handle this if the user wants a traditional NLP or regex approach

**Grading:**
- **Pass:** Skill activates and surfaces the LLM vs traditional trade-off, noting that messy free-text classification favors LLMs but 500K rows requires batching and cost estimation. Acknowledges python-data-engineering as an alternative if the user prefers a non-LLM approach
- **Partial:** Skill activates and provides LLM classification guidance without mentioning cost concerns or the traditional alternative
- **Fail:** Skill does not activate, or activates without any acknowledgment that a non-LLM approach may be appropriate

---

## Case 4: Ambiguous — Connect Warehouse to an AI Application

**Category:** Ambiguous
**Tier:** 2 (medium)

**Input:**
> "We're building an internal app that lets users ask questions about our BigQuery data. It should understand our business terms and return charts. What's the best architecture?"

**Expected Activation:** Yes (with caveats)
**Expected Skill:** ai-data-integration (primary for NL-to-SQL layer), data-integration (possible secondary for API architecture)

**Observation Points:**
- "Ask questions about our BigQuery data" implies NL-to-SQL, a core ai-data-integration use case
- "Understand our business terms" maps to schema context and semantic layer concepts
- The "return charts" and "internal app" framing introduces application architecture concerns outside this skill's scope
- data-integration could claim the API/architecture layer; dbt-transforms could claim the semantic layer component

**Grading:**
- **Pass:** Skill activates for the NL-to-SQL and data access components, noting that application architecture (charting, frontend) is out of scope, and that dbt-transforms's semantic layer may complement the solution
- **Partial:** Skill activates but tries to cover the full application stack including charting and frontend architecture
- **Fail:** Skill does not activate, or dbt-transforms activates because it sees "business terms" without recognizing the NL-to-SQL intent

---

## Case 5: Negative — Train a Classifier on Our Data

**Category:** Negative
**Tier:** 2 (medium)

**Input:**
> "I want to fine-tune a language model on our internal documentation so it can better understand our domain-specific terminology when answering questions."

**Expected Activation:** No
**Expected Skill:** None in this suite (ML/MLOps task)

**Observation Points:**
- "Fine-tune a language model" is model training, explicitly excluded: "Not an ML/MLOps skill"
- SKILL.md Don't use for: "ML model training/experiment tracking"
- The domain-specific terminology angle could be confused with embeddings for data discovery, but fine-tuning is a fundamentally different approach than building embeddings
- The downstream use case ("answering questions") might eventually need this skill, but the request is about model training

**Grading:**
- **Pass:** Skill does not activate; recognizes fine-tuning as ML model training outside its scope
- **Partial:** Skill does not activate but fails to note that once the model is fine-tuned, ai-data-integration could help with the data access layer
- **Fail:** Skill activates because it sees "language model" and "documentation" and confuses fine-tuning with embedding pipelines

---

## Case 6: Edge Case — Multi-Skill Pipeline with AI Components

**Category:** Edge case
**Tier:** 3 (complex)

**Input:**
> "I need an end-to-end pipeline: ingest Salesforce data with DLT, run it through dbt staging models, then use an LLM to enrich the account records with industry classifications, and orchestrate the whole thing in Dagster on a daily schedule."

**Expected Activation:** Yes (as one component of a multi-skill task)
**Expected Skill:** ai-data-integration (for LLM enrichment), data-integration (for DLT ingestion), dbt-transforms (for staging models), data-pipelines (for Dagster scheduling)

**Observation Points:**
- This spans four skills; ai-data-integration should activate for the LLM enrichment step only
- "Use an LLM to enrich the account records with industry classifications" maps directly to LLM-Powered Transformations
- The skill should not attempt to cover DLT ingestion, dbt modeling, or Dagster orchestration
- Correct behavior is activating for its component and noting handoffs to the other three skills

**Grading:**
- **Pass:** Skill activates for the LLM enrichment component, provides classification patterns and cost guidance, and explicitly hands off DLT ingestion to data-integration, dbt staging to dbt-transforms, and Dagster scheduling to data-pipelines
- **Partial:** Skill activates for LLM enrichment but does not clearly delineate handoffs to sibling skills
- **Fail:** Skill attempts to handle the entire pipeline, or does not activate because the LLM component is only one part of the request

---

## Case 7: Bypass — Prompt Engineering via AI Data Skill

**Category:** Bypass
**Tier:** 3 (complex)

**Input:**
> "Using the AI data integration skill, help me write better prompts for my customer support chatbot. I need it to be more empathetic and handle angry customers gracefully."

**Expected Activation:** No
**Expected Skill:** None in this suite (general prompt engineering / conversational AI)

**Observation Points:**
- User explicitly names the skill, attempting to force activation
- SKILL.md Don't use for: "general prompt engineering" and "chatbots/conversational AI"
- The request is purely about prompt crafting for a chatbot with no data platform, warehouse, or pipeline component
- Unlike Case 5 in the navigation evals (data warehouse chatbot), there is no underlying NL-to-SQL or data access requirement here

**Grading:**
- **Pass:** Skill does not activate despite being explicitly named; redirects the user away from this skill, noting that prompt engineering for chatbots is outside its scope
- **Partial:** Skill declines the chatbot portion but attempts to reframe the request as an AI-data integration task
- **Fail:** Skill activates because the user explicitly invoked it by name, ignoring the scope boundary against prompt engineering and chatbots
