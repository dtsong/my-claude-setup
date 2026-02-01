# Claude Code - Daniel Song

## Workflow

1. Brainstorm → plan → implement (for non-trivial features)
2. Write failing test first, then implementation
3. Verify with actual command output before marking done

## Commits

Format: `<type>: <description>`
Types: feat, fix, refactor, test, docs, chore

# Plans
- Make the plan extremely concise. Sacrifice grammar for the sake of concision.
- At the end of each plan, give me a list of unresolved questions to answer, if any.

## Node.js / NVM

When running `node`, `npm`, `npx`, or any Node.js tools, first source nvm:
```bash
source ~/.nvm/nvm.sh && nvm use default --silent && <your command>
```

Example: `source ~/.nvm/nvm.sh && nvm use default --silent && npm install`

## Don'ts

- Don't refactor unrelated code
- Don't add dependencies without asking
- Don't skip verification step

## Project Setup Commands

| Command | Use When |
|---------|----------|
| `/new-python` | Starting a Python project |
| `/new-typescript` | Starting a TypeScript project |
| `/new-mcp-server` | Starting an MCP server |
| `/new-terraform` | Starting a Terraform module |

## Skills (auto-activate by context)

| Skill | Activates When |
|-------|----------------|
| `superpowers` | Complex features, planning, TDD |
| `terraform-skill` | Working with Terraform/OpenTofu |
| `vercel-react-best-practices` | React/Next.js components |
| `web-security-hardening` | Security audits, API endpoints |
| `web-design-guidelines` | UI review, accessibility |
| `dockerfile-generation` | Creating/modifying Dockerfiles |
| `cicd-generation` | CI/CD pipeline work (GitHub Actions) |
| `helm-generation` | Helm chart/values work |

## Plugins

| Plugin | Purpose |
|--------|---------|
| `claude-hud` | Status line with session info |
| `pr-review-toolkit` | Code review before commits |
| `astral-sh/claude-code-plugins` | Python tooling (uv, ruff, ty) |
