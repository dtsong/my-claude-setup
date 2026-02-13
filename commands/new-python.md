# New Python Project Setup

Initialize a Python project with opinionated tooling (uv, ruff, FastAPI, pytest) and conventions.

> **`--help`**: If passed, show a one-line description and say `Run /help new-python for details.`

> For full convention details, see `~/.claude/skills/language-conventions/references/python.md`

> **Placeholders**: `<project-name>` = directory/repo name (kebab-case), `<project_name>` = Python package name (snake_case), `<db_name>` = database name. The `<project-dir>` placeholder in pre-commit config refers to the project root path.

## Stack

- **Package manager**: uv
- **Linting/formatting**: ruff (88-char, black default)
- **Type checking**: ty
- **Testing**: pytest + pytest-asyncio + pytest-cov
- **Python version**: 3.11+
- **Framework**: FastAPI (async)

## Setup Steps

1. Initialize with uv:
```bash
uv init <project-name>
cd <project-name>
```

2. Add core dependencies:
```bash
uv add fastapi "uvicorn[standard]" pydantic-settings sqlalchemy[asyncio] asyncpg httpx
```

3. Add dev dependencies:
```bash
uv add --dev pytest pytest-cov pytest-asyncio ruff ty httpx pre-commit
```

4. Configure tooling in `pyproject.toml`:
```toml
[tool.ruff]
line-length = 88
target-version = "py311"

[tool.ruff.lint]
select = ["E", "F", "I", "UP", "B", "SIM", "ASYNC", "N", "S", "C4", "PT"]
ignore = ["S101"]  # Allow assert in tests

[tool.ruff.lint.per-file-ignores]
"tests/*" = ["S105", "S106"]  # Allow hardcoded test tokens/secrets

[tool.ruff.lint.isort]
known-first-party = ["src"]

[tool.ty.environment]
python-version = "3.11"

[tool.pytest.ini_options]
asyncio_mode = "auto"
testpaths = ["tests"]
log_cli = true
log_cli_level = "INFO"

[tool.coverage.run]
source = ["src"]
branch = true

[tool.coverage.report]
exclude_lines = [
    "pragma: no cover",
    "if TYPE_CHECKING:",
]
```

5. Create `.python-version`:
```
3.11
```

6. Create `.pre-commit-config.yaml`:
```yaml
repos:
  - repo: https://github.com/pre-commit/pre-commit-hooks
    rev: v5.0.0
    hooks:
      - id: trailing-whitespace
      - id: end-of-file-fixer
      - id: check-yaml
      - id: check-json
      - id: check-added-large-files

  - repo: https://github.com/astral-sh/ruff-pre-commit
    rev: v0.9.4
    hooks:
      - id: ruff
        args: [--fix]
        types_or: [python, pyi]
      - id: ruff-format
        types_or: [python, pyi]

  - repo: local
    hooks:
      - id: ty
        name: ty (type check)
        entry: bash -c 'cd <project-name> && uv tool run ty check src'
        language: system
        types: [python]
        pass_filenames: false
```

7. Create `.gitignore`:
```
__pycache__/
*.pyc
.venv/
dist/
*.egg-info/
.pytest_cache/
.ruff_cache/
.env
```

8. Create project structure:
```
src/<project_name>/
├── __init__.py
├── py.typed
├── main.py           # FastAPI app
├── config.py         # Settings
├── db/
│   ├── __init__.py
│   └── database.py   # Async session factory
├── models/
│   └── __init__.py
├── schemas/
│   └── __init__.py
├── routers/
│   ├── __init__.py
│   └── health.py
├── services/
│   └── __init__.py
└── dependencies/
    └── __init__.py
tests/
├── __init__.py
└── conftest.py
```

9. Generate `src/<project_name>/config.py`:
```python
"""Application configuration using Pydantic settings."""

from functools import lru_cache

from pydantic_settings import BaseSettings, SettingsConfigDict


class Settings(BaseSettings):
    """Application settings loaded from environment variables."""

    model_config = SettingsConfigDict(
        env_file=".env",
        env_file_encoding="utf-8",
        extra="ignore",
    )

    environment: str = "development"
    debug: bool = False
    database_url: str = "postgresql+asyncpg://postgres:postgres@localhost:5432/<db_name>"
    cors_origins: str = "http://localhost:3000"

    @property
    def is_development(self) -> bool:
        return self.environment == "development"

    @property
    def is_production(self) -> bool:
        return self.environment == "production"


@lru_cache
def get_settings() -> Settings:
    """Get cached settings instance."""
    return Settings()
```

10. Generate `src/<project_name>/db/database.py`:
```python
"""Database connection and session management."""

from collections.abc import AsyncGenerator

from sqlalchemy.ext.asyncio import AsyncSession, async_sessionmaker, create_async_engine

from <project_name>.config import get_settings

settings = get_settings()

engine = create_async_engine(
    settings.database_url,
    echo=settings.debug,
    pool_pre_ping=True,
    pool_size=5,
    max_overflow=10,
)

async_session_factory = async_sessionmaker(
    engine,
    class_=AsyncSession,
    expire_on_commit=False,
)


async def get_db() -> AsyncGenerator[AsyncSession, None]:
    """Dependency for getting async database sessions."""
    async with async_session_factory() as session:
        try:
            yield session
        finally:
            await session.close()
```

11. Generate `src/<project_name>/main.py`:
```python
"""FastAPI application entry point."""

import logging
import sys
from collections.abc import AsyncGenerator
from contextlib import asynccontextmanager

from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware

from <project_name>.config import get_settings
from <project_name>.routers import health

settings = get_settings()

# Logging
logging.basicConfig(
    level=logging.DEBUG if settings.debug else logging.INFO,
    stream=sys.stdout,
    format="%(asctime)s %(levelname)s [%(name)s] %(message)s",
)
logger = logging.getLogger(__name__)


@asynccontextmanager
async def lifespan(app: FastAPI) -> AsyncGenerator[None, None]:
    """Handle application startup and shutdown."""
    logger.info("Starting up")
    yield
    logger.info("Shutting down")


app = FastAPI(
    title="<Project Name> API",
    version="0.0.1",
    docs_url="/docs" if settings.is_development else None,
    lifespan=lifespan,
)

app.add_middleware(
    CORSMiddleware,
    allow_origins=[o.strip() for o in settings.cors_origins.split(",") if o.strip()],
    allow_credentials=True,
    allow_methods=["GET", "POST", "PUT", "DELETE", "OPTIONS"],
    allow_headers=["Content-Type", "Authorization"],
)

app.include_router(health.router)
```

12. Generate `src/<project_name>/routers/health.py`:
```python
"""Health check endpoint."""

from fastapi import APIRouter

router = APIRouter(tags=["health"])


@router.get("/health")
async def health_check() -> dict[str, str]:
    return {"status": "healthy"}
```

13. Generate `tests/conftest.py`:
```python
"""Pytest fixtures for API tests."""

from collections.abc import AsyncGenerator
from unittest.mock import AsyncMock

import pytest
from httpx import ASGITransport, AsyncClient
from sqlalchemy.ext.asyncio import AsyncSession

from <project_name>.main import app


@pytest.fixture
async def client() -> AsyncGenerator[AsyncClient, None]:
    """Create async test client."""
    async with AsyncClient(
        transport=ASGITransport(app=app),
        base_url="http://test",
    ) as ac:
        yield ac


@pytest.fixture
def db_session() -> AsyncMock:
    """Create a mock async database session."""
    return AsyncMock(spec=AsyncSession)
```

14. Create project CLAUDE.md:
```markdown
# <Project Name>

## What This Is
<1-2 sentence description>

## Key Docs
- `/docs/CODEMAP.md` — Codebase structure and quick reference
- Convention reference: `~/.claude/skills/language-conventions/references/python.md`

## Quick Context
- Backend: FastAPI (Python)
- Database: PostgreSQL (async via SQLAlchemy + asyncpg)

## Tooling

### Python
- **uv** - Package manager (`uv sync`, `uv run`)
- **ruff** - Linting and formatting (`uv run ruff check .`, `uv run ruff format .`)
- **ty** - Type checking (`uv run ty check src`)
- **pytest** - Testing with coverage (`uv run pytest --cov`)

## Key Decisions
- <Decision 1>

## Testing
- All feature work must include unit tests
- pytest + pytest-asyncio with `asyncio_mode = "auto"`
- `AsyncMock(spec=AsyncSession)` for database mocking

## Git Workflow
- <Branch strategy>

## Current Focus
- <Current phase>
```

15. Initialize git and install pre-commit:
```bash
git init
uv run pre-commit install
git add .
git commit -m "chore: initial project setup"
```

## Verification

```bash
uv run ruff check . && uv run ruff format --check . && uv run ty check src && uv run pytest
```
