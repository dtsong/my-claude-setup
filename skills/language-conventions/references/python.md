---
language: python
stack: FastAPI + SQLAlchemy async
min_version: "3.11"
last_updated: 2026-02-10
token_estimate: ~2800
---

# Python Conventions

Opinionated Python project conventions for FastAPI + SQLAlchemy async applications.

## Tooling

| Tool | Purpose | Command |
|------|---------|---------|
| **uv** | Package manager + runner | `uv sync`, `uv run pytest` |
| **ruff** | Linting + formatting (88-char, black default) | `uv run ruff check`, `uv run ruff format` |
| **ty** | Type checking | `uv run ty check src` |
| **pytest** | Testing + coverage | `uv run pytest --cov` |

## Ruff Config

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
```

## Pre-commit Config

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
        name: ty type check
        entry: uv run ty check src
        language: system
        types: [python]
        pass_filenames: false
```

## Project Structure

```
src/<project_name>/
├── main.py              # FastAPI app init, middleware, routers
├── config.py            # Settings via pydantic-settings
├── db/
│   ├── database.py      # Async engine + session factory
│   └── base.py          # Declarative base
├── models/              # SQLAlchemy ORM models
├── schemas/             # Pydantic request/response schemas
├── routers/             # API endpoint definitions
├── services/            # Business logic
└── dependencies/        # FastAPI dependency injection
```

## FastAPI Patterns

- `Annotated[Type, Depends()]` for dependency injection
- Router prefix + tags: `APIRouter(prefix="/api/items", tags=["items"])`
- Lifespan context manager for startup/shutdown
- `HTTPException` with `status.HTTP_xxx` codes
- CORS middleware with explicit origins
- Rate limiting with slowapi
- Security headers middleware (X-Content-Type-Options, X-Frame-Options, HSTS)

```python
from contextlib import asynccontextmanager
from fastapi import FastAPI

@asynccontextmanager
async def lifespan(app: FastAPI):
    # Startup
    yield
    # Shutdown

app = FastAPI(lifespan=lifespan)
```

## SQLAlchemy Async Patterns

- `AsyncSession` with `async_sessionmaker`
- `create_async_engine` with pool_pre_ping, pool_size, max_overflow
- `Mapped[Type]` for column annotations
- `TimestampMixin` for created_at/updated_at
- JSONB columns: always `.model_dump()` Pydantic models before storage
- Async generator dependency: `async def get_db() -> AsyncGenerator[AsyncSession, None]`

```python
from sqlalchemy.ext.asyncio import AsyncSession, async_sessionmaker, create_async_engine

engine = create_async_engine(
    DATABASE_URL,
    pool_pre_ping=True,
    pool_size=5,
    max_overflow=10,
)
async_session = async_sessionmaker(engine, class_=AsyncSession, expire_on_commit=False)

async def get_db() -> AsyncGenerator[AsyncSession, None]:
    async with async_session() as session:
        yield session
```

## Pydantic Patterns

- `ConfigDict(from_attributes=True)` for ORM mode
- `BaseSettings` + `SettingsConfigDict(env_file=".env")` + `@lru_cache` for config
- `Field()` with descriptions and defaults
- Union syntax: `str | None` (not `Optional[str]`)
- Properties for computed values (e.g., `is_production`, `effective_database_url`)

```python
from pydantic_settings import BaseSettings, SettingsConfigDict
from functools import lru_cache

class Settings(BaseSettings):
    model_config = SettingsConfigDict(env_file=".env")
    database_url: str
    environment: str = "development"

    @property
    def is_production(self) -> bool:
        return self.environment == "production"

@lru_cache
def get_settings() -> Settings:
    return Settings()
```

## Testing

- `AsyncMock(spec=AsyncSession)` for mock DB sessions
- `app.dependency_overrides[get_db] = lambda: mock_session`
- `httpx.AsyncClient` with `ASGITransport(app=app)` for async test client
- Patch at import point, not definition point
- `asyncio_mode = "auto"` in pytest config
- `log_cli = true` for visible test output
- `branch = true` in coverage config

```python
from unittest.mock import AsyncMock
from sqlalchemy.ext.asyncio import AsyncSession

@pytest.fixture
def mock_session():
    session = AsyncMock(spec=AsyncSession)
    return session

@pytest.fixture
def client(mock_session):
    app.dependency_overrides[get_db] = lambda: mock_session
    with TestClient(app) as c:
        yield c
    app.dependency_overrides.clear()
```

## Pytest Config

```toml
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

## Type Hints

- Modern 3.11+: `list[str]`, `dict[str, int]`, `str | None`
- `from __future__ import annotations` not needed in 3.11+
- `TYPE_CHECKING` for circular import guards
- `from collections.abc import AsyncGenerator` (not typing)

## Logging

- Structured JSON in production (custom JSONFormatter)
- Human-readable in development (basicConfig with timestamp)
- `exc_info=True` on error-level logs
- Quiet noisy third-party loggers: `logging.getLogger("httpx").setLevel(logging.WARNING)`

```python
import logging

logger = logging.getLogger(__name__)

# Quiet noisy loggers
logging.getLogger("httpx").setLevel(logging.WARNING)
logging.getLogger("sqlalchemy.engine").setLevel(logging.WARNING)
```

## Pipeline Pattern

- `@dataclass` for pipeline results (typed, serializable)
- Dry-run mode by default for destructive operations
- `retry_commit()` for transient DB failures
- `with_timeout()` for external API calls
- Summary logging after each pipeline run

```python
@dataclass
class PipelineResult:
    processed: int = 0
    skipped: int = 0
    errors: list[str] = field(default_factory=list)

    @property
    def success(self) -> bool:
        return len(self.errors) == 0
```

## Gotchas

- Never use `importlib.reload()` in tests -- corrupts module-level globals
- Ruff N806: no PascalCase variables in functions -- use `mock_service_cls` not `MockService`
- Line limit is 88 chars (black default), not 79 or 120
- Always `.model_dump()` Pydantic models before storing in JSONB columns
- `python-multipart` required for `UploadFile` in FastAPI
- Patch at the import point (`from myapp.services import MyService` -> patch `myapp.routers.MyService`)
- `async_sessionmaker` requires `expire_on_commit=False` to avoid lazy-load errors

## Common Mistakes (WRONG → RIGHT)

### Import-point patching

```python
# WRONG — patches where the function is defined, not where it's imported
@patch("myapp.services.user_service.get_user")
def test_get_user(mock):
    ...

# RIGHT — patch at the import point in the module under test
@patch("myapp.routers.users.get_user")
def test_get_user(mock):
    ...
```

### Modern union syntax (3.11+)

```python
# WRONG — legacy Optional syntax
from typing import Optional
def get_name() -> Optional[str]:
    ...

# RIGHT — PEP 604 union syntax
def get_name() -> str | None:
    ...
```

### Ruff N806: PascalCase in functions

```python
# WRONG — ruff N806 flags PascalCase variable names in functions
def test_service():
    MockService = create_mock()

# RIGHT — use snake_case for variables, even mock classes
def test_service():
    mock_service_cls = create_mock()
```

### Async session expiry

```python
# WRONG — accessing attributes after session closes raises MissingGreenlet
async_session = async_sessionmaker(engine, class_=AsyncSession)

# RIGHT — disable expire_on_commit to safely access ORM attributes
async_session = async_sessionmaker(engine, class_=AsyncSession, expire_on_commit=False)
```
