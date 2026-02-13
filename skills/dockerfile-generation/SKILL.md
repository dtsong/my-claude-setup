---
name: dockerfile-generation
description: "Create or modify Dockerfiles and multi-stage builds with verification-first approach. Triggers on: Dockerfile, docker build, container image. Not for: docker-compose or Kubernetes manifests (use helm-generation)."
---

# Dockerfile Generation Skill

Generate production-ready Dockerfiles through iterative verification.

## Core Principles

1. **Verification-first**: Examine codebase BEFORE adding ANY instruction
2. **Multi-arch**: Support amd64/arm64, no hardcoded paths
3. **No HEALTHCHECK**: Cannot verify health endpoints from code alone
4. **Multi-stage builds**: Builder stage → minimal runtime stage
5. **Security**: Non-root user (UID 10001+), pinned versions, no `:latest`
6. **Layer optimization**: Dependencies first, source second

## Process

### Step 1: Analyze Codebase

Before writing ANY Dockerfile instruction, verify:

```
[ ] Language/runtime detected (package.json, requirements.txt, go.mod, etc.)
[ ] Entry point identified (main file, start script)
[ ] Build command identified (if compilation needed)
[ ] Dependencies file location confirmed
[ ] Required environment variables documented
[ ] Exposed ports identified from code (NOT assumed)
```

### Step 2: Generate Dockerfile

**Structure:**
```dockerfile
# syntax=docker/dockerfile:1

# Build stage
FROM <base>:<pinned-version> AS builder
WORKDIR /app
# Install deps first (cache layer)
COPY <deps-file> .
RUN <install-deps>
# Copy source
COPY . .
RUN <build-command>

# Runtime stage
FROM <minimal-base>:<pinned-version>
WORKDIR /app

# Security: non-root user
RUN addgroup --gid 10001 appgroup && \
    adduser --uid 10001 --ingroup appgroup --disabled-password appuser
USER appuser

# Copy artifacts from builder
COPY --from=builder --chown=appuser:appgroup /app/<artifact> .

EXPOSE <verified-port>
CMD ["<verified-entrypoint>"]
```

**Language-specific bases:**
| Language | Builder | Runtime |
|----------|---------|---------|
| Node.js | `node:<version>-alpine` | `node:<version>-alpine` |
| Python | `python:<version>-slim` | `python:<version>-slim` |
| Go | `golang:<version>-alpine` | `gcr.io/distroless/static` |
| Java | `eclipse-temurin:<version>` | `eclipse-temurin:<version>-jre-alpine` |
| Rust | `rust:<version>-alpine` | `gcr.io/distroless/cc` |

### Step 3: Validation Loop (Max 5 iterations)

```bash
# Build
docker build -t test-image:local .

# Run and capture logs
docker run --rm test-image:local 2>&1 | head -50

# If error: analyze → fix → rebuild
# If success: verify functionality
```

**Stop conditions:**
- Container starts and responds correctly
- 5 iterations reached (escalate to user)

## Anti-patterns to Avoid

- `FROM <image>:latest` - Always pin versions
- `RUN apt-get update && apt-get install` without cleanup
- `COPY . .` before dependency installation
- Running as root
- Hardcoded secrets or credentials
- Assuming ports without code verification
- Adding HEALTHCHECK without verified endpoint

## Output Format

When generating a Dockerfile, output:

1. **Analysis summary**: What was detected in codebase
2. **Dockerfile**: The generated file
3. **Build command**: Exact command to build
4. **Run command**: Exact command to test
5. **Notes**: Any assumptions or manual verification needed
