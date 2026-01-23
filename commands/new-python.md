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
uv add --dev pytest ruff
```

3. Create `pyproject.toml` ruff config:
```toml
[tool.ruff]
line-length = 100
target-version = "py313"

[tool.ruff.lint]
select = ["E", "F", "I", "UP", "B", "SIM"]
```

4. Create `.python-version`:
```
3.13
```

5. Create initial structure:
```
src/<project_name>/
    __init__.py
    py.typed
tests/
    __init__.py
    test_example.py
```

6. Create project CLAUDE.md:
```markdown
# <Project Name>

## Commands
uv run pytest           # tests
uv run ruff check .     # lint
uv run ruff format .    # format
uv run ty               # typecheck

## Structure
src/<name>/  - source code
tests/       - pytest tests
```

7. Initialize git:
```bash
git init
git add .
git commit -m "chore: initial project setup"
```

## Verification

Run all checks pass:
```bash
uv run ruff check . && uv run pytest
```
