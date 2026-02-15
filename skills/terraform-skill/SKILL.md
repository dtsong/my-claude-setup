---
name: terraform-skill
description: Use when working with Terraform or OpenTofu - creating modules, writing tests (native test framework, Terratest), setting up CI/CD pipelines, reviewing configurations, choosing between testing approaches, debugging state issues, implementing security scanning (trivy, checkov), or making infrastructure-as-code architecture decisions
license: Apache-2.0
metadata:
  author: Anton Babenko
  version: 1.5.0
---

# Terraform Skill for Claude

Terraform and OpenTofu guidance covering testing, modules, CI/CD, and production patterns. Based on terraform-best-practices.com.

## Activation

Use this skill when: creating Terraform/OpenTofu configs or modules, setting up IaC testing, deciding between testing approaches, structuring multi-environment deployments, implementing CI/CD for IaC, reviewing or refactoring projects, choosing module patterns or state management.

Do not use for: basic syntax questions, provider-specific API reference, cloud platform questions unrelated to Terraform/OpenTofu.

## Core Principles

### Module Hierarchy

| Type | When to Use | Scope |
|------|-------------|-------|
| **Resource Module** | Single logical group | VPC + subnets, SG + rules |
| **Infrastructure Module** | Collection of resource modules | Multiple modules in one region/account |
| **Composition** | Complete infrastructure | Spans regions/accounts |

Hierarchy: Resource -> Resource Module -> Infrastructure Module -> Composition

Separate environments (prod, staging) from modules (reusable components). Use `examples/` as both documentation and test fixtures. Keep modules small and focused.

For detailed module architecture, load: `references/module-patterns.md`

### Naming Conventions

**Resources:** Use descriptive names (`aws_instance "web_server"`). Use `"this"` for singleton resources only. Avoid generic names for non-singletons.

**Variables:** Prefix with context (`var.vpc_cidr_block`, not `var.cidr`).

**Files:** `main.tf` (resources), `variables.tf` (inputs), `outputs.tf` (outputs), `versions.tf` (providers), `data.tf` (data sources, optional).

### Resource Block Ordering

1. `count` or `for_each` FIRST (blank line after)
2. Other arguments
3. `tags` as last real argument
4. `depends_on` after tags (if needed)
5. `lifecycle` at the very end (if needed)

### Variable Block Ordering

1. `description` (ALWAYS required)
2. `type`
3. `default`
4. `validation`
5. `nullable` (when setting to false)

For complete structure guidelines, load: `references/code-patterns.md`

## Testing Strategy

### Decision Matrix

| Situation | Approach | Tools | Cost |
|-----------|----------|-------|------|
| Quick syntax check | Static analysis | `validate`, `fmt` | Free |
| Pre-commit validation | Static + lint | `validate`, `tflint`, `trivy`, `checkov` | Free |
| Terraform 1.6+, simple logic | Native test framework | `terraform test` | Free-Low |
| Pre-1.6, or Go expertise | Integration testing | Terratest | Low-Med |
| Security/compliance focus | Policy as code | OPA, Sentinel | Free |
| Cost-sensitive workflow | Mock providers (1.7+) | Native tests + mocking | Free |

### Native Test Key Points (1.6+)

- Validate schemas with Terraform MCP before writing tests
- `command = plan` for input validation; `command = apply` for computed values and set-type blocks
- Set-type blocks cannot be indexed with `[0]` -- use `for` expressions or `command = apply`

For detailed testing guides, load: `references/testing-frameworks.md`

## Count vs For_Each

| Scenario | Use | Why |
|----------|-----|-----|
| Boolean condition | `count = condition ? 1 : 0` | Simple on/off toggle |
| Simple numeric replication | `count = 3` | Fixed number of identical resources |
| Items may be reordered/removed | `for_each = toset(list)` | Stable resource addresses |
| Reference by key | `for_each = map` | Named access to resources |

For migration guides, load: `references/code-patterns.md`

## Module Development

Standard structure:
```
my-module/
├── README.md
├── main.tf
├── variables.tf
├── outputs.tf
├── versions.tf
├── examples/
│   ├── minimal/
│   └── complete/
└── tests/
    └── module_test.tftest.hcl
```

Variables: always include `description`, use explicit `type`, provide sensible defaults, add `validation` blocks, use `sensitive = true` for secrets.

Outputs: always include `description`, mark sensitive, consider returning objects for related values.

For detailed module patterns, load: `references/module-patterns.md`

## CI/CD Integration

Stages: Validate (format + syntax + lint) -> Test (native or Terratest) -> Plan (review execution plan) -> Apply (with approvals for prod).

Cost optimization: use mocking for PR validation (free), run integration tests only on main branch, implement auto-cleanup, tag all test resources.

For CI/CD templates, load: `references/ci-cd-workflows.md`

## Security & Compliance

```bash
trivy config .
checkov -d .
```

Avoid: secrets in variables, default VPC, skipping encryption, open security groups (0.0.0.0/0).

Do: use Secrets Manager / Parameter Store, create dedicated VPCs, enable encryption at rest, use least-privilege security groups.

For detailed security guidance, load: `references/security-compliance.md`

## Version Management

| Component | Strategy | Example |
|-----------|----------|---------|
| Terraform | Pin minor version | `required_version = "~> 1.9"` |
| Providers | Pin major version | `version = "~> 5.0"` |
| Modules (prod) | Pin exact version | `version = "5.1.2"` |
| Modules (dev) | Allow patch updates | `version = "~> 5.1"` |

### Modern Features

| Feature | Version | Use Case |
|---------|---------|----------|
| `try()` | 0.13+ | Safe fallbacks |
| `nullable = false` | 1.1+ | Prevent null values |
| `moved` blocks | 1.1+ | Refactor without destroy/recreate |
| `optional()` with defaults | 1.3+ | Optional object attributes |
| Native testing | 1.6+ | Built-in test framework |
| Mock providers | 1.7+ | Cost-free unit testing |
| Provider functions | 1.8+ | Provider-specific transforms |
| Cross-variable validation | 1.9+ | Validate variable relationships |
| Write-only arguments | 1.11+ | Secrets never stored in state |

### Terraform vs OpenTofu

Both fully supported. For licensing, governance, and feature comparison, load: `references/quick-reference.md`

## Output Format

When generating Terraform code, follow all ordering and naming conventions above. Ask user preference for Terraform vs OpenTofu before generating commands or documentation.

## Reference Files

| File | Content |
|------|---------|
| `references/testing-frameworks.md` | Static analysis, native tests, Terratest |
| `references/module-patterns.md` | Module structure, variables, outputs, anti-patterns |
| `references/ci-cd-workflows.md` | GitHub Actions, GitLab CI, cost optimization |
| `references/security-compliance.md` | Trivy/Checkov, secrets, state security, compliance |
| `references/quick-reference.md` | Command cheat sheets, decision flowcharts, troubleshooting |
| `references/code-patterns.md` | Block ordering, count vs for_each, modern features, versioning |

Load one reference at a time based on the task at hand.

## License

Apache License 2.0. See LICENSE file.

**Copyright (c) 2026 Anton Babenko**
