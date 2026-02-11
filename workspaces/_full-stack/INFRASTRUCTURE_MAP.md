# Full-Stack Project - Infrastructure & Project Map

> Example workspace for a multi-stack project (Python backend + TypeScript frontend + Terraform infra).
> Copy this directory, rename it to match your project, and customize.

## Overview

Full-stack web application with a FastAPI backend, Next.js frontend, and Terraform-managed infrastructure.

**Repository:** `https://github.com/<org>/<project>`
**Current Status:** Active development

## Tech Stack Summary

| Layer | Technology | Version | Convention Reference |
|-------|------------|---------|---------------------|
| Frontend | Next.js (App Router) | 14+ | [typescript.md](~/.claude/skills/language-conventions/references/typescript.md) |
| UI | Tailwind CSS + shadcn/ui | 3.4+ | [typescript.md](~/.claude/skills/language-conventions/references/typescript.md) |
| Backend | FastAPI (Python) | 0.115+ | [python.md](~/.claude/skills/language-conventions/references/python.md) |
| Database | PostgreSQL (async) | 16 | [python.md](~/.claude/skills/language-conventions/references/python.md) |
| Infrastructure | Terraform (GCP) | 1.5+ | [terraform.md](~/.claude/skills/language-conventions/references/terraform.md) |

## Project Structure

```
project-root/
├── apps/
│   ├── api/             # FastAPI backend (Python)
│   │   ├── src/         # Source code (routers, services, models, schemas)
│   │   ├── tests/       # pytest tests
│   │   └── pyproject.toml
│   └── web/             # Next.js frontend (TypeScript)
│       ├── src/         # Source code (app/, components/, lib/)
│       └── package.json
├── packages/
│   └── shared-types/    # Shared TypeScript types
├── terraform/           # Infrastructure as code
│   ├── main.tf
│   ├── modules/         # Reusable Terraform modules
│   └── environments/    # Per-environment tfvars
├── scripts/             # Developer scripts
├── docs/                # Documentation
│   ├── CODEMAP.md       # Codebase navigation
│   └── SPEC.md          # Implementation specification
├── tl                   # Developer CLI (./tl --help)
├── CLAUDE.md            # AI assistant config
└── .pre-commit-config.yaml
```

## Key Files

| File | Purpose |
|------|---------|
| `CLAUDE.md` | AI assistant project config |
| `docs/CODEMAP.md` | Token-efficient code navigation |
| `apps/api/src/main.py` | FastAPI app entry point |
| `apps/api/src/config.py` | Backend settings (pydantic-settings) |
| `apps/web/src/app/layout.tsx` | Next.js root layout |
| `terraform/main.tf` | Infrastructure resources |
| `tl` | Developer CLI entry point |

## Commands

```bash
# Development
./tl dev                    # Start full local stack
./tl check                  # Run all verification

# Backend (apps/api/)
uv run pytest --cov         # Run tests with coverage
uv run ruff check .         # Lint
uv run ty check src         # Type check

# Frontend (apps/web/)
pnpm test:coverage          # Run tests with coverage
pnpm typecheck              # Type check
pnpm build                  # Production build

# Infrastructure (terraform/)
terraform fmt -recursive    # Format
terraform validate          # Validate
terraform plan              # Plan changes
```

## Related Conventions

All language-specific patterns follow the convention references:
- **Python patterns**: `~/.claude/skills/language-conventions/references/python.md`
- **TypeScript patterns**: `~/.claude/skills/language-conventions/references/typescript.md`
- **Terraform patterns**: `~/.claude/skills/language-conventions/references/terraform.md`
- **Project setup**: `~/.claude/skills/language-conventions/references/project-claude-md.md`
