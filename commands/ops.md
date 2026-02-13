# /ops - Operations Control Center

Stack-wide operations dashboard. Health checks, deploys, dependency audits, and diagnostics.

> **`--help`**: If passed, show a one-line description and say `Run /help ops for details.`

## Usage

```
/ops                        # Dashboard — stack health at a glance
/ops check [target...]      # Run quality gates
/ops deploy [preview|prod]  # Deploy to hosting platform
/ops deps [update]          # Dependency audit/update
/ops perf                   # Bundle analysis + Lighthouse
/ops security               # Secret scan + dependency audit
/ops ci [--watch]           # GitHub Actions status
/ops logs [target]          # Tail production logs
```

## Instructions

Parse `$ARGUMENTS` to determine the subcommand. If no arguments, run **Dashboard** mode.

### Workspace Detection

Detect the workspace dynamically — **never hardcode paths**:

```bash
WORKSPACE="$(git rev-parse --show-toplevel 2>/dev/null || echo "")"
if [ -z "$WORKSPACE" ]; then
    echo "Not in a git repository."
    exit 1
fi
```

### Stack Detection

Auto-detect the project stack from the workspace:

```bash
# Detect package managers and languages
HAS_NODE=$(test -f "$WORKSPACE/package.json" && echo true || echo false)
HAS_PYTHON=$(test -f "$WORKSPACE/pyproject.toml" -o -f "$WORKSPACE/requirements.txt" && echo true || echo false)
HAS_TERRAFORM=$(test -d "$WORKSPACE/infra" -o -f "$WORKSPACE/main.tf" && echo true || echo false)
HAS_DOCKER=$(test -f "$WORKSPACE/Dockerfile" -o -f "$WORKSPACE/docker-compose.yml" && echo true || echo false)

# Detect monorepo structure
IS_MONOREPO=$(test -f "$WORKSPACE/pnpm-workspace.yaml" -o -d "$WORKSPACE/apps" -o -d "$WORKSPACE/packages" && echo true || echo false)

# Detect framework
HAS_NEXT=$(grep -q "next" "$WORKSPACE/package.json" 2>/dev/null && echo true || echo false)
HAS_VITE=$(grep -q "vite" "$WORKSPACE/package.json" 2>/dev/null && echo true || echo false)
```

---

## Mode: Dashboard (default — `/ops`)

Run health checks across the detected stack and display a unified status view.

### Checks to Run (in parallel, based on detected stack)

**For Node.js projects:**
```bash
BUILD=$(cd $WORKSPACE && npm run build 2>&1 && echo "PASS" || echo "FAIL")
TYPES=$(cd $WORKSPACE && npx tsc --noEmit 2>&1 && echo "PASS" || echo "FAIL")
LINT=$(cd $WORKSPACE && npm run lint 2>&1 && echo "PASS" || echo "FAIL")
TESTS=$(cd $WORKSPACE && npm test 2>&1; echo "EXIT:$?")
```

**For Python projects:**
```bash
LINT=$(cd $WORKSPACE && ruff check . 2>&1 && echo "PASS" || echo "FAIL")
FORMAT=$(cd $WORKSPACE && ruff format --check . 2>&1 && echo "PASS" || echo "FAIL")
TESTS=$(cd $WORKSPACE && pytest 2>&1; echo "EXIT:$?")
```

**For Terraform:**
```bash
TF_VALIDATE=$(cd $WORKSPACE/infra && terraform validate 2>&1 && echo "PASS" || echo "FAIL")
TF_FORMAT=$(cd $WORKSPACE/infra && terraform fmt -check 2>&1 && echo "PASS" || echo "FAIL")
```

**CI/CD status (always):**
```bash
CI_STATUS=$(cd $WORKSPACE && gh run list --limit 1 --json status,conclusion,headBranch,createdAt 2>&1)
```

### Display

```
Stack Health — <project name>

  Node.js              Build: <PASS/FAIL>  Types: <PASS/FAIL>  Lint: <PASS/FAIL>  Tests: <N/N>
  Python               Lint: <PASS/FAIL>   Format: <PASS/FAIL>  Tests: <N/N>
  Terraform            Validate: <PASS/FAIL>  Format: <PASS/FAIL>
  CI/CD (Actions)      Last: <branch> <status> (<time ago>)
```

Only show sections for detected stack components. Use PASS/FAIL indicators. If a check fails, show a brief reason below the line.

---

## Mode: Check (`/ops check [target]`)

Run quality gates for a specific target or all targets.

### `/ops check node` (or `web` or `js`)

```bash
cd $WORKSPACE

# Step 1: Lint
npm run lint

# Step 2: Type check
npx tsc --noEmit

# Step 3: Tests
npm test

# Step 4: Build
npm run build
```

Run sequentially. Stop on first failure and report which gate failed.

### `/ops check python` (or `py`)

```bash
cd $WORKSPACE

# Step 1: Lint
ruff check .

# Step 2: Format
ruff format --check .

# Step 3: Tests
pytest
```

### `/ops check terraform` (or `tf` or `infra`)

```bash
cd $WORKSPACE/infra

# Step 1: Validate
terraform validate

# Step 2: Format check
terraform fmt -check
```

### `/ops check` (no target — all)

Run checks for all detected stack components in sequence. Report per-target results.

### Display

```
Quality Gates: <target>

  [PASS] Lint
  [PASS] Types
  [PASS] Tests (42/42)
  [FAIL] Build
    Error: Module not found: 'missing-package'

  Result: 3/4 gates passed
```

---

## Mode: Deploy (`/ops deploy [target]`)

### `/ops deploy preview`

Detect the deployment platform and deploy a preview:

```bash
# Vercel
cd $WORKSPACE && vercel 2>&1

# Or Netlify
cd $WORKSPACE && netlify deploy 2>&1

# Or Docker
cd $WORKSPACE && docker build -t preview . 2>&1
```

Display the preview URL when done.

### `/ops deploy prod`

**Requires confirmation.** Ask the user: "Deploy to production? This will go live."

### Safety Checks Before Deploy

1. Run `/ops check` first — all gates must pass
2. Check for uncommitted changes — warn if dirty
3. Check CI status — warn if last run failed

---

## Mode: Deps (`/ops deps [update]`)

### Audit (`/ops deps`)

```bash
cd $WORKSPACE

# NPM audit (if Node.js project)
npm audit 2>&1
npm outdated 2>&1

# Python deps (if Python project)
pip list --outdated 2>&1

# pip-audit if available
pip-audit 2>&1
```

Display summary: N vulnerabilities, N outdated packages.

### Update (`/ops deps update`)

**Requires confirmation.** Show what will be updated, then:

```bash
cd $WORKSPACE && npm update 2>&1
```

For major version bumps, list them separately and ask about each.

---

## Mode: Perf (`/ops perf`)

Bundle analysis and performance metrics.

```bash
cd $WORKSPACE

# Bundle analysis (Next.js)
ANALYZE=true npm run build 2>&1

# Show bundle sizes
ls -lh .next/static/chunks/*.js 2>/dev/null | sort -k5 -h -r | head -10
```

Display:
- Total bundle size
- Largest chunks
- Page-specific bundles
- Recommendations for optimization

If Lighthouse CLI is available:
```bash
npx lighthouse http://localhost:3000 --output=json --quiet 2>&1
```

---

## Mode: Security (`/ops security`)

Security scanning.

```bash
cd $WORKSPACE

# Secret scan - check for leaked secrets
git secrets --scan 2>&1 || echo "git-secrets not installed"

# NPM audit (security only, if Node.js)
npm audit --audit-level=high 2>&1

# pip-audit (if Python)
pip-audit 2>&1

# Check for .env files in git
git ls-files | grep -i '\.env' 2>&1

# Check for hardcoded secrets patterns
grep -r "sk-\|api_key\|password\s*=\|PRIVATE_KEY\|SECRET" --include="*.ts" --include="*.tsx" --include="*.js" --include="*.py" . 2>&1 | grep -v node_modules | grep -v ".next" | grep -v __pycache__ | head -20
```

Display findings with severity levels.

---

## Mode: CI (`/ops ci [--watch]`)

### Status (`/ops ci`)

```bash
cd $WORKSPACE && gh run list --limit 5 --json status,conclusion,headBranch,name,createdAt,databaseId
```

Display:

```
GitHub Actions

  #<id>  <branch>  <workflow>  <status>  <time>
  #<id>  <branch>  <workflow>  <status>  <time>
  ...
```

### Watch (`/ops ci --watch`)

```bash
cd $WORKSPACE && gh run watch $(gh run list --limit 1 --json databaseId -q '.[0].databaseId')
```

---

## Mode: Logs (`/ops logs [target]`)

Tail production logs for the specified target. Auto-detect the log source:

- **Vercel**: `vercel logs --follow`
- **Docker**: `docker logs -f <container>`
- **Cloud Run**: `gcloud logging read ...`
- **Local**: `tail -f` log files

### `/ops logs` (no target)

Show last 10 lines from detected log sources.
