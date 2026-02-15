# Quick Reference

## Command Cheat Sheet

### Static Analysis

```bash
terraform fmt -recursive -check    # or: tofu fmt -recursive -check
terraform validate                 # or: tofu validate
tflint --init && tflint
checkov -d .
```

### Native Tests (1.6+)

```bash
terraform test                     # Run all tests
terraform test -test-directory=tests/unit/
terraform test -verbose
```

### Plan Validation

```bash
terraform plan -out tfplan
terraform show -json tfplan | jq -r '.' > tfplan.json
terraform show tfplan | grep "will be created"
```

## Testing Decision Flowchart

```
Need to test Terraform/OpenTofu code?
|
+- Just syntax/format? -> terraform/tofu validate + fmt
+- Static security scan? -> trivy + checkov
+- Terraform/OpenTofu 1.6+?
|  +- Simple logic? -> Native terraform/tofu test
|  +- Complex integration? -> Terratest
+- Pre-1.6?
   +- Go team? -> Terratest
   +- Neither? -> Plan to upgrade
```

## Module Development Workflow

1. **Plan:** Define inputs/outputs, document purpose
2. **Implement:** Create resources, pin versions, add examples
3. **Test:** Static analysis, unit tests, integration tests
4. **Document:** Update README, document inputs/outputs, add CHANGELOG
5. **Publish:** Tag version, push to registry

## Version-Specific Guidance

**1.0-1.5:** No native testing. Use Terratest. Focus on static analysis + plan validation.

**1.6+:** Native `terraform test` / `tofu test`. Migrate simple tests from Terratest. Keep Terratest for complex integration.

**1.7+:** Mock providers for unit testing. Reduce costs with mocking. Real integration tests for final validation.

## Terraform vs OpenTofu

| Factor | Terraform | OpenTofu |
|--------|-----------|----------|
| **License** | BSL 1.1 | MPL 2.0 |
| **Governance** | HashiCorp | Linux Foundation |
| **Native Testing** | 1.6+ | 1.6+ |
| **Mock Providers** | 1.7+ | 1.7+ |
| **Feature Parity** | Reference impl | Compatible fork |
| **Migration** | N/A | Drop-in for TF <= 1.5 |

Choose Terraform if: using HCP Terraform, enterprise support with HashiCorp, need latest features first.

Choose OpenTofu if: prefer open-source governance, avoid vendor lock-in, BSL 1.1 incompatible.

Both use identical HCL. Commands shown for both. Since OpenTofu 1.6, platforms have diverged with unique features.

## Troubleshooting

**Tests fail in CI but pass locally:** Pin versions explicitly in `versions.tf`. Check environment variables and AWS credentials/permissions.

**Parallel tests conflict:** Use unique identifiers for resource names (`random.UniqueId()`).

**High test costs:** Use mocking (1.7+), tag resources with TTL, run integration only on main branch, use smaller instances, share stable resources (VPCs, SGs).

## Migration Paths

**Manual -> Automated:** Static analysis -> plan review -> automated tests -> CI/CD integration.

**Terratest -> Native (1.6+):** Keep Terratest for complex integration. Migrate simple unit/logic tests to native. Maintain both during transition.

**Terraform -> OpenTofu:** Drop-in replacement. No code changes needed. Update CI/CD commands (`terraform` -> `tofu`). Update documentation.

## Pre-Commit Checklist

### Naming
- All identifiers use `_` not `-`
- No resource names repeating type (`aws_vpc.main_vpc`)
- Singleton resources named `this`
- Plural names for list variables (`subnet_ids`)
- All variables and outputs have descriptions

### Structure
- `count`/`for_each` at top (blank line after)
- `tags` as last real argument
- `depends_on` after tags
- `lifecycle` at end
- Variables ordered: description, type, default, sensitive, nullable, validation

### Modern Features
- Using `try()` not `element(concat())`
- `nullable = false` on non-null variables
- `optional()` in object types (1.3+)
- Write-only arguments or external secrets (not in state)

### Architecture
- `terraform.tfvars` only at composition level
- Remote state configured (never local)
- Resource modules use variables (no hardcoded values)
- Standard file structure: main.tf, variables.tf, outputs.tf, versions.tf

## Version Constraint Syntax

| Syntax | Meaning | Use Case |
|--------|---------|----------|
| `"5.0.0"` | Exact | Avoid (inflexible) |
| `"~> 5.0"` | 5.0.x only | Recommended |
| `">= 5.0, < 6.0"` | Any 5.x | Range |
| `">= 5.0"` | Minimum | Risky |

## Refactoring Decision Tree

```
What are you refactoring?
+- Resource addressing (count -> for_each) -> moved blocks
+- Secrets in state -> Secrets Manager + write-only args (1.11+)
+- Legacy syntax (0.12/0.13) -> Modern feature checklist
+- Module structure (rename/reorg) -> moved blocks
```

Before refactoring: backup state, test in dev first, review plan carefully. During: one change at a time, verify each step. After: verify idempotency, test in staging, update docs.
