---
type: project-convention
topic: codebase navigation
last_updated: 2026-02-10
token_estimate: ~1400
---

# CODEMAP.md Guide

## Purpose

- Quick reference for code navigation without expensive codebase scanning
- Token-efficient: AI reads this instead of exploring the whole repo
- Reduces AI tool calls by 60-80% for common navigation tasks
- Target: 300-700 lines depending on project size

## Template

```markdown
# <Project Name> Codemap

> Last updated: <date>
> Purpose: Quick reference for code navigation and token-efficient context

---

## Repository Structure

```
project-root/
├── apps/
│   ├── api/            # Backend service
│   │   ├── src/        # Source code
│   │   └── tests/      # Backend tests
│   └── web/            # Frontend application
│       ├── src/        # Source code
│       └── tests/      # Frontend tests
├── packages/           # Shared packages
├── docs/               # Documentation
├── scripts/            # Developer scripts
└── infra/              # Infrastructure as code
```

---

## 1. <Layer Name> (<directory>/)

**Tech Stack:** <frameworks, libraries>

### Entry Point
- `<file>` -- <purpose>

### Core Structure
```
<directory>/
├── routers/        # API endpoints
├── services/       # Business logic
├── models/         # Database models
├── schemas/        # Request/response schemas
└── utils/          # Shared utilities
```

### Key Components

| Component | File | Purpose |
|-----------|------|---------|
| Main app | `main.py` | FastAPI app factory, middleware |
| User service | `services/user.py` | User CRUD operations |
| Auth | `services/auth.py` | JWT token handling |

### Key Algorithms

**<Algorithm Name>** (`<file>:<function>`):
```
1. Fetch input data from <source>
2. Apply <transformation>
3. Filter by <criteria>
4. Return <output format>
```

---

## 2. <Another Layer> (<directory>/)

...

---

## Quick Reference

| Find... | Look in... |
|---------|-----------|
| API endpoints | `apps/api/src/routers/` |
| Database models | `apps/api/src/models/` |
| Business logic | `apps/api/src/services/` |
| React components | `apps/web/src/components/` |
| API hooks | `apps/web/src/hooks/` |
| Shared types | `packages/shared/src/types/` |

## Common Tasks

| Task | Steps |
|------|-------|
| Add new API endpoint | 1. Create router in `routers/` 2. Add service in `services/` 3. Register router in `main.py` |
| Add new page | 1. Create route in `app/` 2. Add components in `components/` 3. Add API hook in `hooks/` |
| Add database table | 1. Create model in `models/` 2. Create migration 3. Add schema in `schemas/` |

## Development Commands

```bash
./dev test              # Run all tests
./dev lint              # Run linters
./dev typecheck         # Run type checkers
./dev dev               # Start dev server
./dev db migrate        # Run database migrations
```
```

## Writing Tips

- **Use ASCII trees** for directory structure (universally readable, no encoding issues)
- **Use tables** for component indexes (scannable at a glance)
- **Use pseudocode** for key algorithms (not full implementation)
- **Add a "Find By Concept" section** that maps questions to file locations
- **Update when architecture changes**, not every commit

## What to Include vs Exclude

| Include | Exclude |
|---------|---------|
| Directory structure overview | Individual file contents |
| Entry points and main files | Implementation details |
| Key algorithms (pseudocode) | Test file listings |
| Component relationships | Configuration values |
| Common developer tasks | Deployment procedures |
| Important constants/thresholds | Environment variables |
| Cross-cutting concerns | Generated code paths |

## Sizing Guidelines

| Project Size | Target Lines | Sections |
|-------------|-------------|----------|
| Small (< 20 files) | 100-200 | Structure + Quick Reference |
| Medium (20-100 files) | 200-400 | Full template |
| Large (100+ files) | 400-700 | Full template + subsections |

## Maintenance

- Review monthly or when major architecture changes occur
- Automate structure sections with tree commands where possible
- Keep algorithm pseudocode in sync with implementation
- Remove references to deleted files/components promptly
