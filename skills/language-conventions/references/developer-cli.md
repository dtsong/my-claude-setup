---
type: project-convention
topic: developer CLI pattern
last_updated: 2026-02-10
token_estimate: ~1900
---

# Developer CLI Pattern

## Why a Developer CLI

- **Single entry point:** `./dev <command>` instead of remembering 20 different scripts
- **Discoverability:** `./dev --help` shows all available commands
- **Safety:** Dry-run defaults for destructive operations
- **Dependency checking:** Verify tools exist before running
- **Consistent output:** Color-coded feedback across all commands

## Structure

```bash
#!/usr/bin/env bash
set -euo pipefail

# -- Paths -------------------------------------------------
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# -- Colors ------------------------------------------------
if [ -t 1 ]; then
    BOLD='\033[1m' DIM='\033[2m'
    CYAN='\033[36m' GREEN='\033[32m'
    YELLOW='\033[33m' RED='\033[31m'
    RESET='\033[0m'
else
    BOLD='' DIM='' CYAN='' GREEN='' YELLOW='' RED='' RESET=''
fi

# -- Utilities ---------------------------------------------
info()    { printf "${CYAN}|${RESET} %s\n" "$1"; }
success() { printf "${GREEN}v${RESET} %s\n" "$1"; }
warn()    { printf "${YELLOW}!${RESET} %s\n" "$1"; }
error()   { printf "${RED}x${RESET} %s\n" "$1" >&2; }

require_deps() {
    local missing=""
    for dep in "$@"; do
        command -v "$dep" >/dev/null 2>&1 || missing="$missing $dep"
    done
    [ -n "$missing" ] && { error "Missing:${missing}"; exit 1; }
}

confirm() {
    printf "${YELLOW}?${RESET} %s [y/N] " "$1"
    read -r answer
    [[ "$answer" =~ ^[Yy]$ ]]
}

# -- Help --------------------------------------------------
show_help() {
    printf "${BOLD}<Project> Developer CLI${RESET}\n\n"
    printf "${DIM}Usage:${RESET}  ./<cli-name> <command> [args...]\n\n"

    printf "${CYAN}${BOLD}WORKFLOW${RESET}\n"
    printf "  ${CYAN}dev${RESET}           Start development servers\n"
    printf "  ${CYAN}setup${RESET}         Install dependencies and configure\n"
    printf "  ${CYAN}check${RESET}         Run all quality checks\n\n"

    printf "${GREEN}${BOLD}TEST${RESET}\n"
    printf "  ${GREEN}test${RESET}          Run test suite\n"
    printf "  ${GREEN}test-all${RESET}      Run all tests with coverage\n\n"

    printf "${YELLOW}${BOLD}VERIFY${RESET}\n"
    printf "  ${YELLOW}lint${RESET}          Run linters\n"
    printf "  ${YELLOW}typecheck${RESET}     Run type checkers\n"
    printf "  ${YELLOW}format${RESET}        Format code\n\n"

    printf "${RED}${BOLD}PROD${RESET}\n"
    printf "  ${RED}prod${RESET} <sub>     Production operations\n"
}

# -- Commands ----------------------------------------------
cmd_dev() {
    info "Starting development servers..."
    # Start backend and frontend
}

cmd_test() {
    info "Running tests..."
    # Run test suite
}

cmd_check() {
    info "Running all quality checks..."
    cmd_lint
    cmd_typecheck
    cmd_test
    success "All checks passed"
}

cmd_lint() {
    info "Running linters..."
    # Run linters
}

cmd_typecheck() {
    info "Running type checkers..."
    # Run type checkers
}

cmd_prod() {
    case "${1:-}" in
        logs)    # Fetch production logs ;;
        db)      # Connect to production database ;;
        trigger) # Trigger a pipeline (dry-run by default) ;;
        *)       error "Unknown prod command: ${1:-}"; exit 1 ;;
    esac
}

# -- Dispatch ----------------------------------------------
case "${1:-}" in
    -h|--help|"")  show_help ;;
    dev)            cmd_dev ;;
    setup)          cmd_setup ;;
    check)          cmd_check ;;
    test)           cmd_test ;;
    test-all)       cmd_test_all ;;
    lint)           cmd_lint ;;
    typecheck)      cmd_typecheck ;;
    format)         cmd_format ;;
    prod)           shift; cmd_prod "$@" ;;
    *)              error "Unknown: $1"; show_help; exit 1 ;;
esac
```

## Semantic Categories

Organize commands into categories with visual grouping in help output:

| Category | Color | Purpose | Examples |
|----------|-------|---------|----------|
| WORKFLOW | Cyan | Composite runners | `dev`, `setup`, `check` |
| TEST | Green | Testing commands | `test`, `test-all`, `coverage` |
| VERIFY | Yellow | Validation | `lint`, `typecheck`, `format-check` |
| PROD | Red | Production access | `prod db`, `prod logs`, `prod trigger` |
| DATA | Blue | Data operations | `seed`, `migrate`, `snapshot` |

## Design Principles

- **Dry-run by default:** Destructive operations require `--execute` flag
- **Dependency checking:** `require_deps docker uv pnpm` before commands that need them
- **Color-coded output:** Green for success, red for errors, cyan for info, yellow for warnings
- **TTY detection:** Disable colors when piped (`[ -t 1 ]`)
- **Help as default:** Running without args shows help, not an error
- **Subcommand dispatch:** `case` statement with help fallback for unknown commands
- **Script delegation:** Complex commands delegate to scripts in `scripts/` directory
- **Fail fast:** `set -euo pipefail` at the top of every script

## Common Patterns

### Composite Commands
Composite commands call multiple operations in sequence:
```bash
cmd_check() {
    cmd_lint
    cmd_typecheck
    cmd_test
    success "All checks passed"
}
```

### Dry-Run Safety
```bash
cmd_prod_trigger() {
    local pipeline="$1"
    local execute="${2:-}"
    if [ "$execute" = "--execute" ]; then
        info "Triggering $pipeline (LIVE)..."
        # Actually trigger
    else
        warn "DRY RUN: Would trigger $pipeline"
        info "Add --execute to run for real"
    fi
}
```

### Confirmation Prompts
```bash
cmd_reset_db() {
    confirm "This will delete all local data. Continue?" || exit 0
    info "Resetting database..."
}
```

### Progress Indicators
```bash
cmd_deploy() {
    info "Building..."    && build
    info "Pushing..."     && push
    info "Deploying..."   && deploy
    success "Deployed successfully"
}
```
