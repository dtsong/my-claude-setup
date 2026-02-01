---
name: cicd-generation
description: Generating CI/CD pipelines (GitHub Actions) with security-first approach
---

# CI/CD Generation Skill

Generate production-ready GitHub Actions workflows.

## Core Principles

1. **Fail-fast**: Quick checks (lint, type) before slow ops (build, test)
2. **Security hardening**: OIDC auth, minimal permissions, pinned action versions
3. **Caching**: Based on detected package manager
4. **Matrix testing**: When multiple versions/platforms needed
5. **Verification-first**: Examine repo before generating workflow

## Process

### Step 1: Analyze Repository

Before generating ANY workflow, verify:

```
[ ] Language/framework detected
[ ] Package manager identified (npm, yarn, pnpm, pip, poetry, go mod)
[ ] Test command exists and verified
[ ] Lint/format commands exist
[ ] Build output/artifacts identified
[ ] Deployment target identified (if applicable)
```

### Step 2: Workflow Structure

**Standard CI workflow** (`.github/workflows/ci.yml`):

```yaml
name: CI

on:
  push:
    branches: [main]
  pull_request:
    branches: [main]

permissions:
  contents: read

jobs:
  lint:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Setup
        # Language-specific setup
      - name: Lint
        run: <lint-command>

  test:
    runs-on: ubuntu-latest
    needs: lint  # Fail-fast: lint before test
    steps:
      - uses: actions/checkout@v4
      - name: Setup
        # Language-specific setup with caching
      - name: Test
        run: <test-command>

  build:
    runs-on: ubuntu-latest
    needs: test  # Fail-fast: test before build
    steps:
      - uses: actions/checkout@v4
      - name: Setup
        # Language-specific setup
      - name: Build
        run: <build-command>
```

### Step 3: Language-Specific Patterns

**Node.js:**
```yaml
- uses: actions/setup-node@v4
  with:
    node-version: '20'
    cache: 'npm'  # or yarn, pnpm
- run: npm ci
```

**Python:**
```yaml
- uses: actions/setup-python@v5
  with:
    python-version: '3.12'
    cache: 'pip'
- run: pip install -r requirements.txt
```

**Go:**
```yaml
- uses: actions/setup-go@v5
  with:
    go-version: '1.22'
    cache: true
```

### Step 4: Security Hardening

**Required practices:**
- Pin action versions to SHA: `actions/checkout@<sha>`
- Minimal permissions block at workflow and job level
- Use OIDC for cloud deployments (no long-lived secrets)
- Never echo secrets

**OIDC example (AWS):**
```yaml
permissions:
  id-token: write
  contents: read

steps:
  - uses: aws-actions/configure-aws-credentials@v4
    with:
      role-to-assume: arn:aws:iam::ACCOUNT:role/ROLE
      aws-region: us-east-1
```

### Step 5: Matrix Testing

When multiple versions/platforms needed:

```yaml
strategy:
  fail-fast: false
  matrix:
    os: [ubuntu-latest, macos-latest]
    node: [18, 20, 22]
```

## Anti-patterns to Avoid

- `@latest` or `@v4` without SHA pinning for security-critical workflows
- `permissions: write-all`
- Storing secrets in workflow files
- Running all jobs in parallel when dependencies exist
- Missing caching for package managers
- `continue-on-error: true` hiding real failures

## Output Format

When generating a workflow, output:

1. **Analysis summary**: What was detected in repo
2. **Workflow file(s)**: Full YAML content
3. **File path**: Where to save (`.github/workflows/<name>.yml`)
4. **Setup notes**: Any required secrets or configuration
5. **Verification**: Command to test workflow locally (act, etc.)
