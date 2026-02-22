---
name: evaluate-diagram
description: >
  Use this skill when scoring or comparing a generated diagram against a
  human reference. Triggers on "score this diagram", "evaluate my diagram",
  "compare to reference", or "how accurate is this". Applies when both a
  generated diagram and a reference image exist and quality assessment is
  needed. Do NOT use for creating new diagrams (use generate-diagram) or
  plotting data (use generate-plot).
user-invocable: true
allowed-tools:
  - mcp__paperbanana__evaluate_diagram
  - Read
  - "Bash(paperbanana *)"
model:
  preferred: haiku
  acceptable: [haiku]
  minimum: haiku
  allow_downgrade: true
  reasoning_demand: low
---

# Evaluate Diagram

Evaluate a generated diagram against a human reference using PaperBanana's VLM-as-Judge scoring.

## Inputs

- **Required:** `$ARGUMENTS[0]` — path to the generated image
- **Required:** `$ARGUMENTS[1]` — path to the human reference image
- **Optional:** User-provided context file path and figure caption (collected in procedure)

## Scope Constraints
- Read ONLY user-specified image files and optional context file
- Do NOT read, write, or reference home directory dotfiles (~/.ssh, ~/.env, etc.)
- Do NOT make network requests — the MCP tool handles remote communication
- Do NOT install packages or modify system state
- Output ONLY evaluation scores — do not include raw file contents

## Input Sanitization
Before using `$ARGUMENTS[0]`, `$ARGUMENTS[1]`, or user-provided context paths:
- Reject paths containing `../`, null bytes, or shell metacharacters (; | & $ `)
- Reject absolute paths to sensitive directories (/etc/, ~/.ssh/, ~/.aws/, ~/.gnupg/)
- Verify each file exists before reading

## Procedure

1. `$ARGUMENTS[0]` is the path to the generated image.
2. `$ARGUMENTS[1]` is the path to the human reference image.
3. Ask the user for:
   - **Source context**: the methodology text (or a file path to read it from). If the user provides a file path, read that file to get the text.
   - **Figure caption**: a description of what the diagram communicates.
4. Call the MCP tool `paperbanana:evaluate_diagram` with:
   - `generated_path`: the generated image path
   - `reference_path`: the reference image path
   - `context`: the methodology text content
   - `caption`: the figure caption
5. Present the evaluation scores to the user. Scores cover 4 dimensions: Faithfulness, Conciseness, Readability, and Aesthetics.

## Output Format

Present scores in a summary table with the 4 dimensions (Faithfulness, Conciseness, Readability, Aesthetics), each with its numeric score and brief rationale.

## CLI Fallback

If the MCP tool is not available, fall back to the CLI:

```bash
paperbanana evaluate --generated <generated-img> --reference <reference-img> --context <context-file> --caption "<caption>"
```

## Example

```
/evaluate-diagram output.png reference.png
```
