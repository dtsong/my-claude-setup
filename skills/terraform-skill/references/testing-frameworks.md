# Testing Frameworks

## Static Analysis

Always do this first. Zero cost, catches 40%+ of issues.

```yaml
- repo: https://github.com/antonbabenko/pre-commit-terraform
  hooks:
    - id: terraform_fmt
    - id: terraform_validate
    - id: terraform_tflint
```

- `terraform fmt` -- code formatting consistency
- `terraform validate` -- syntax and internal consistency
- `TFLint` -- best practices, provider-specific rules
- `trivy` / `checkov` -- security vulnerabilities

## Plan Testing

```bash
terraform init
terraform plan -out=tfplan
terraform show -json tfplan | jq '.'
```

Validates expected resources, catches auth issues, validates variable combinations. Cannot catch runtime issues or resource-specific bugs.

## Native Terraform Tests (1.6+)

Use when team works in HCL, testing module logic, avoiding external dependencies.

### Basic Structure

```hcl
run "create_bucket" {
  command = apply

  assert {
    condition     = aws_s3_bucket.main.bucket != ""
    error_message = "S3 bucket name must be set"
  }
}
```

### Schema Validation

Always validate resource schemas before writing tests. Some blocks are **sets** (unordered, no `[0]` indexing), some are **lists** (ordered, indexable).

| AWS Resource Block | Type | Indexing |
|-------------------|------|----------|
| `rule` in S3 encryption config | set | Cannot use `[0]` |
| `transition` in lifecycle config | set | Cannot use `[0]` |
| `noncurrent_version_expiration` | list | Can use `[0]` |

### Set-Type Block Solutions

**Use `command = apply` to materialize:**
```hcl
run "test_encryption" {
  command = apply
  assert {
    condition = alltrue([
      for rule in aws_s3_bucket_server_side_encryption_configuration.this.rule :
      alltrue([
        for config in rule.apply_server_side_encryption_by_default :
        config.sse_algorithm == "AES256"
      ])
    ])
    error_message = "Encryption should use AES256"
  }
}
```

**Or check at resource level (plan mode):**
```hcl
run "test_encryption_exists" {
  command = plan
  assert {
    condition     = aws_s3_bucket_server_side_encryption_configuration.this != null
    error_message = "Encryption configuration should be created"
  }
}
```

### command = plan vs command = apply

```
Checking input values? -> command = plan
Checking computed values? -> command = apply
Accessing set-type blocks? -> command = apply
Need fast feedback? -> command = plan (with mocks)
Testing real behavior? -> command = apply (without mocks)
```

**Pitfall:** Computed values (IDs, ARNs, generated names) are unknown at plan time. Use `command = apply` for these.

### Mocking (1.7+)

```hcl
mock_provider "aws" {
  mock_resource "aws_instance" {
    defaults = {
      id  = "i-mock123"
      arn = "arn:aws:ec2:us-east-1:123456789:instance/i-mock123"
    }
  }
}
```

**Pros:** Native HCL syntax, no external dependencies, fast with mocks, good for unit testing.

**Cons:** Newer/less mature, limited ecosystem, mocking misses real-world behavior.

## Terratest (Go-based)

Use when team has Go experience, needs robust integration testing, testing multiple providers.

```go
func TestS3Module(t *testing.T) {
    t.Parallel()

    terraformOptions := &terraform.Options{
        TerraformDir: "../examples/complete",
        Vars: map[string]interface{}{
            "bucket_name": "test-bucket-" + uniqueId(),
        },
    }

    defer terraform.Destroy(t, terraformOptions)
    terraform.InitAndApply(t, terraformOptions)

    bucketName := terraform.Output(t, terraformOptions, "bucket_name")
    assert.NotEmpty(t, bucketName)
}
```

**Critical patterns:** Always use `t.Parallel()`, always `defer terraform.Destroy()`, use unique identifiers, tag resources, use separate test accounts.

**Costs:** Small module (S3, IAM): $0-5/run. Medium (VPC, EC2): $5-20/run. Large (RDS, ECS): $20-100/run.

**Test stages** for faster iteration -- skip setup/teardown during development with `SKIP_setup=true`.

## Framework Selection

```
Quick syntax check? -> terraform validate + fmt
Security scan? -> trivy + checkov
Terraform 1.6+, simple logic? -> Native tests
Pre-1.6, or complex integration? -> Terratest
```

## Cost Optimization

1. Use mocking for unit tests (1.7+)
2. Tag test resources with TTL for auto-cleanup
3. Run integration tests only on main branch
4. Use smaller instance types in tests
5. Share stable test resources (VPCs, security groups) when safe
