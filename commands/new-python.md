# New Python Project Setup

Initialize a Python project with Daniel's preferred tooling.

## Stack

- **Package manager**: uv
- **Linting/formatting**: ruff
- **Type checking**: ty
- **Testing**: pytest
- **Python version**: 3.13+

## Setup Steps

1. Initialize with uv:
```bash
uv init <project-name>
cd <project-name>
```

2. Add dev dependencies:
```bash
uv add --dev pytest ruff ty
```

3. Add tooling config to `pyproject.toml`:
```toml
[tool.ruff]
line-length = 100
target-version = "py313"

[tool.ruff.lint]
select = ["E", "F", "I", "UP", "B", "SIM"]

[tool.pytest.ini_options]
testpaths = ["tests"]
```

4. Create `.python-version`:
```
3.13
```

5. Create `.pre-commit-config.yaml`:
```yaml
repos:
  - repo: https://github.com/pre-commit/pre-commit-hooks
    rev: v5.0.0
    hooks:
      - id: trailing-whitespace
      - id: end-of-file-fixer
      - id: check-yaml
      - id: check-added-large-files

  - repo: https://github.com/astral-sh/ruff-pre-commit
    rev: v0.9.4
    hooks:
      - id: ruff
        args: [--fix]
      - id: ruff-format
```

6. Create `.gitignore`:
```
__pycache__/
*.pyc
.venv/
dist/
*.egg-info/
.pytest_cache/
.ruff_cache/
```

7. Create initial structure:
```
src/<project_name>/
    __init__.py
    py.typed
tests/
    __init__.py
    test_example.py
```

8. Create project CLAUDE.md:
```markdown
# <Project Name>

## Commands
```bash
uv run pytest              # run tests
uv run ruff check .        # lint
uv run ruff format .       # format
uv run ty check src/       # typecheck
```

## Structure
src/<name>/  - source code
tests/       - pytest tests
```

9. Initialize git and install pre-commit:
```bash
git init
uv run pre-commit install
git add .
git commit -m "chore: initial project setup"
```

## Verification

Run all checks:
```bash
uv run ruff check . && uv run ruff format --check . && uv run pytest
```
