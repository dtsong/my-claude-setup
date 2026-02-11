# Workspace Configuration Format

Workspaces provide pre-configured rich context for frequently-used projects. When the council/academy detects a matching workspace, this context is automatically loaded alongside the standard context scan.

## Directory Structure

```
workspaces/
  <project-name>/
    INFRASTRUCTURE_MAP.md    # Architecture, tech stack, project structure
    gap_analysis.md          # Known gaps, priorities, roadmap (optional)
    *.mermaid                # Diagrams (optional)
```

## How Workspaces Are Matched

During the Context Injection step, the engine checks:

1. Get the current workspace name (from `git remote` repo name, or directory name)
2. Look for a matching directory under `~/.claude/workspaces/<name>/`
3. If found, read `INFRASTRUCTURE_MAP.md` and include it in the PROJECT_CONTEXT block
4. If not found, fall back to standard context scan (no error)

## INFRASTRUCTURE_MAP.md Template

```markdown
# <Project Name> - Infrastructure & Project Map

## Overview
<1-2 sentence description of the project>

**Repository:** <url>
**Current Status:** <status>

## Tech Stack Summary

| Layer | Technology | Version |
|-------|------------|---------|
| ... | ... | ... |

## Project Structure

```
project-root/
├── src/           # Source code
│   ├── ...
├── ...
```

## Database Schema
<Summary of tables/models>

## Key Files
| File | Purpose |
|------|---------|
| ... | ... |

## Active Work
<Current branches, in-progress features>

## Known Gaps
<Prioritized list of issues/missing features>

## Environment Variables
<List of required env vars (no values)>

## Commands
```bash
# Development
<dev commands>
```
```

## Usage

Workspaces are automatically detected. No flags needed. The engine will:
1. Check for a workspace config matching the current project
2. If found, inject it into every agent's PROJECT_CONTEXT
3. This gives agents deep project knowledge without expensive codebase scanning

## Related Conventions

Workspaces pair well with the language and project convention references in `skills/language-conventions/references/`:

| Convention | Purpose |
|-----------|---------|
| `python.md` | Python tooling, patterns, and configs |
| `typescript.md` | TypeScript tooling, patterns, and configs |
| `terraform.md` | Terraform module structure and patterns |
| `project-claude-md.md` | CLAUDE.md template for new projects |
| `codemap.md` | How to create a CODEMAP.md |

For a full-stack workspace example, see `workspaces/_full-stack/`.

## Creating a New Workspace

1. Create a directory: `workspaces/<project-name>/`
2. Add `INFRASTRUCTURE_MAP.md` with the template above
3. Optionally add `gap_analysis.md`, diagrams, etc.
4. Run `install.sh` to ensure the symlink exists
