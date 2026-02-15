---
name: prompt-engineering
department: "oracle"
description: "Use when designing, evaluating, or versioning system prompts for LLM-powered features. Covers instruction structure, chain-of-thought patterns, output format constraints, few-shot example selection, and prompt versioning strategy. Do not use for RAG pipeline design (use rag-architecture) or AI evaluation frameworks (use ai-evaluation)."
version: 1
triggers:
  - "prompt"
  - "system prompt"
  - "few-shot"
  - "chain-of-thought"
  - "structured output"
  - "function calling"
  - "tool use"
  - "instruction"
---

# Prompt Engineering

## Purpose

Design, evaluate, and version system prompts for LLM-powered features, including instruction structure, chain-of-thought patterns, output format constraints, and few-shot example selection.

## Scope Constraints

Reads feature requirements, data format examples, and quality constraints for prompt design analysis. Does not execute LLM calls, modify production prompts, or access API keys directly.

## Inputs

- Feature requirements (what the LLM should do)
- Input data format and examples
- Desired output format and constraints
- Quality requirements (accuracy, consistency, tone)
- Cost and latency constraints (model selection guidance)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Define the task precisely
- [ ] Step 2: Structure the system prompt
- [ ] Step 3: Design chain-of-thought (if applicable)
- [ ] Step 4: Design output format
- [ ] Step 5: Select and craft few-shot examples
- [ ] Step 6: Design versioning strategy

### Step 1: Define the Task Precisely

Before writing a prompt, articulate:
- **Input:** What exactly does the model receive? (user message, context, data)
- **Output:** What exactly should it produce? (classification, generation, extraction, transformation)
- **Constraints:** What must it never do? (hallucinate facts, reveal system prompt, produce PII)
- **Edge cases:** What happens with empty input, adversarial input, ambiguous input?

### Step 2: Structure the System Prompt

Use a layered structure:
1. **Identity and role:** Who is the model in this context?
2. **Task description:** What it's being asked to do (one paragraph, precise)
3. **Constraints and rules:** Hard rules it must follow (numbered list)
4. **Output format:** Exact structure of the expected output (with template)
5. **Few-shot examples:** 2-3 input/output pairs showing ideal behavior
6. **Edge case handling:** What to do when uncertain, off-topic, or missing data

### Step 3: Design Chain-of-Thought (if applicable)

For complex reasoning tasks:
- **Explicit CoT instruction:** "Think step by step before answering"
- **Structured CoT:** Define the reasoning steps (e.g., "1. Identify the entities, 2. Determine relationships, 3. Synthesize answer")
- **Hidden CoT:** Instruct model to reason in a `<thinking>` block, then provide the answer separately
- **When to skip CoT:** Classification tasks, simple extraction, and format conversion rarely benefit

### Step 4: Design Output Format

Specify the exact output structure:
- **JSON output:** Provide a schema with required fields, types, and constraints
- **Markdown output:** Provide a template with section headers
- **Structured extraction:** Define the fields and valid values explicitly
- **Validation:** How will the output be parsed? Design the format for reliable parsing.

### Step 5: Select and Craft Few-Shot Examples

Choose examples strategically:
- **Cover the range:** Include examples representing different input types
- **Include edge cases:** Show desired behavior for tricky inputs
- **Show the format:** Examples should match the exact output format
- **Keep it minimal:** 2-3 examples are usually enough; more can confuse
- **Order matters:** Put the most representative example last (recency bias)

### Step 6: Design Versioning Strategy

Plan for prompt evolution:
- **Version identifier:** Semantic versioning (v1.0, v1.1, v2.0)
- **Storage:** Version-controlled alongside code (not in a database, not hardcoded)
- **A/B testing:** How to run two prompt versions simultaneously
- **Rollback:** How to revert to a previous version quickly
- **Changelog:** What changed and why, linked to eval results

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what system is being analyzed, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Output Format

```markdown
# Prompt Design: [Feature Name]

## Task Definition
**Input:** [Description + example]
**Output:** [Description + format]
**Constraints:** [Hard rules]

## System Prompt (v1.0)
```
[Full system prompt text]
```

## Few-Shot Examples
### Example 1
**Input:** [Example input]
**Expected output:** [Example output]

### Example 2
**Input:** [Edge case input]
**Expected output:** [Edge case output]

## Chain-of-Thought Strategy
[Whether CoT is used, what the reasoning structure looks like]

## Output Schema
```json
{
  "field1": "string (required) — description",
  "field2": "number (optional) — description"
}
```

## Prompt Versioning
| Version | Date | Change | Eval Score |
|---------|------|--------|------------|
| v1.0 | [Date] | Initial | [Score] |

## Model Recommendation
**Recommended:** [Model] at [temperature]
**Rationale:** [Why this model for this task]
**Cost estimate:** [$/1K requests]
```

## Handoff

- Hand off to rag-architecture if prompt design reveals retrieval or context assembly requirements.
- Hand off to ai-evaluation if prompt versioning requires an evaluation framework or regression testing.

## Quality Checks

- [ ] System prompt has a clear role, task, constraints, format, and examples
- [ ] Output format is designed for reliable programmatic parsing
- [ ] Few-shot examples cover normal cases and at least one edge case
- [ ] Constraints address prompt injection, hallucination, and off-topic input
- [ ] Prompt is stored in version control with a changelog
- [ ] Model and temperature are justified for the task requirements

## Evolution Notes
<!-- Observations appended after each use -->
