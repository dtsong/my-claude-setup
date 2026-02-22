---
name: generate-plot
description: >
  Use this skill when creating a statistical plot or chart from a data file.
  Triggers on "plot this data", "make a chart", "graph this CSV", or
  "visualize these results". Applies to CSV, JSON, or tabular data needing
  bar charts, scatter plots, line graphs, or similar visualizations. Do NOT
  use for methodology diagrams from text (use generate-diagram) or diagram
  scoring (use evaluate-diagram).
user-invocable: true
allowed-tools:
  - mcp__paperbanana__generate_plot
  - Read
  - "Bash(paperbanana *)"
model:
  preferred: haiku
  acceptable: [haiku]
  minimum: haiku
  allow_downgrade: true
  reasoning_demand: low
---

# Generate Plot

Generate a publication-quality statistical plot from a data file using PaperBanana.

## Inputs

- **Required:** `$ARGUMENTS[0]` — path to the data file (CSV or JSON)
- **Optional:** `$ARGUMENTS[1]` — plot intent description (prompted if not provided)

## Scope Constraints
- Read ONLY the user-specified data file
- Do NOT read, write, or reference home directory dotfiles (~/.ssh, ~/.env, etc.)
- Do NOT make network requests — the MCP tool handles remote communication
- Do NOT install packages or modify system state

## Input Sanitization
Before using `$ARGUMENTS[0]` in file operations:
- Reject paths containing `../`, null bytes, or shell metacharacters (; | & $ `)
- Reject absolute paths to sensitive directories (/etc/, ~/.ssh/, ~/.aws/, ~/.gnupg/)
- Verify the file exists before reading

## Procedure

1. Read the file at `$ARGUMENTS[0]` to get the data content.
2. If the file is CSV, convert it to a column-keyed JSON dictionary (each key is a column name, each value is a list of values). If the file is already JSON, use the content directly.
3. If `$ARGUMENTS[1]` is provided, use it as the plot intent description. Otherwise, ask the user what kind of plot they want and what it should show.
4. Call the MCP tool `paperbanana:generate_plot` with:
   - `data_json`: the JSON-serialized data
   - `intent`: the plot description
   - `iterations`: 3 (default)
5. Present the generated plot to the user.

## Output Format

Present the generated plot with a summary of parameters used (data source, intent, iterations).

## CLI Fallback

If the MCP tool is not available, fall back to the CLI:

```bash
paperbanana plot --data <file> --intent "<intent>"
```

## Example

```
/generate-plot results.csv "Bar chart comparing model accuracy across datasets"
```
