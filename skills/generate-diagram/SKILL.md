---
name: generate-diagram
description: >
  Use this skill when creating a methodology diagram from research text.
  Triggers on "make a diagram", "visualize this methodology", "diagram this
  process", or "generate a figure from this paper". Applies to methodology
  descriptions, process flows, and research paper sections. Do NOT use for
  scoring existing diagrams (use evaluate-diagram) or plotting data from
  CSV/JSON (use generate-plot).
user-invocable: true
allowed-tools:
  - mcp__paperbanana__generate_diagram
  - Read
  - "Bash(paperbanana *)"
model:
  preferred: haiku
  acceptable: [haiku]
  minimum: haiku
  allow_downgrade: true
  reasoning_demand: low
---

# Generate Diagram

Generate a publication-quality methodology diagram from a text file using PaperBanana.

## Inputs

- **Required:** `$ARGUMENTS[0]` — path to the methodology text file
- **Optional:** `$ARGUMENTS[1]` — figure caption (prompted if not provided)

## Scope Constraints
- Read ONLY the user-specified input file and `~/Desktop/PaperBanana/` contents
- Do NOT read, write, or reference home directory dotfiles (~/.ssh, ~/.env, etc.)
- Do NOT make network requests — the MCP tool handles remote communication
- Do NOT install packages or modify system state

## Input Sanitization
Before using `$ARGUMENTS[0]` in file operations:
- Reject paths containing `../`, null bytes, or shell metacharacters (; | & $ `)
- Reject absolute paths to sensitive directories (/etc/, ~/.ssh/, ~/.aws/, ~/.gnupg/)
- Verify the file exists before reading

## Procedure

1. Read the file at `$ARGUMENTS[0]` to get the methodology text content.
2. If `$ARGUMENTS[1]` is provided, use it as the figure caption. Otherwise, ask the user for a caption describing what the diagram should communicate.
3. Call the MCP tool `paperbanana:generate_diagram` with:
   - `source_context`: the text content read from the file
   - `caption`: the figure caption
   - `iterations`: 3 (default)
4. After generation, list and read **all files** in the `~/Desktop/PaperBanana` folder (including any subfolders) to show the full iterative history — previous versions, metadata, intermediate outputs, etc.  # SECURITY: PaperBanana's designated output directory; contains only generated artifacts
5. Present the newly generated diagram **and** a summary of the folder contents so the user has full context of how the image was created and can request adjustments based on any iteration.

## Output Format

Present the generated diagram with a summary of parameters used (caption, iterations) and the full contents listing of `~/Desktop/PaperBanana/`.

## CLI Fallback

If the MCP tool is not available, fall back to the CLI:

```bash
paperbanana generate --input <file> --caption "<caption>"
```

## Example

```
/generate-diagram method.txt "Overview of our encoder-decoder architecture"
```
