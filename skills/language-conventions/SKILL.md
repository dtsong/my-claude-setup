---
name: language-conventions
description: "Reference language and project conventions for Python, TypeScript, and Terraform. Triggers on: project setup, code conventions, tooling config, linter setup. Not for: runtime implementation guidance (use domain-specific skills)."
---

# Language & Project Conventions

Convention references for consistent, opinionated project setup. Each reference provides inline configs, patterns, and gotchas learned from production use.

## Language References

| Language | File | Key Topics |
|----------|------|------------|
| Python | [references/python.md](references/python.md) | uv, ruff (88-char), ty, FastAPI, SQLAlchemy async, Pydantic, pytest |
| TypeScript | [references/typescript.md](references/typescript.md) | pnpm, Vitest, Prettier, Next.js App Router, Tailwind, shadcn/ui, React Query |
| Terraform | [references/terraform.md](references/terraform.md) | GCS/S3 backend, tflint, tfsec, modules, OIDC CI/CD |

## Project References

| Topic | File | Key Topics |
|-------|------|------------|
| CLAUDE.md | [references/project-claude-md.md](references/project-claude-md.md) | Project-level AI assistant config template |
| CODEMAP | [references/codemap.md](references/codemap.md) | Token-efficient codebase navigation doc |
| Memory System | [references/memory-system.md](references/memory-system.md) | Three-layer persistent memory for AI sessions |
| PRD | [references/prd.md](references/prd.md) | Product Requirements Document template |
| Developer CLI | [references/developer-cli.md](references/developer-cli.md) | Unified CLI pattern for developer tooling |

## Usage

These references are consumed by:
- `/new-python`, `/new-typescript`, `/new-terraform` scaffolding commands
- Direct reading during code reviews and convention discussions
- Council/Academy agents for project context
