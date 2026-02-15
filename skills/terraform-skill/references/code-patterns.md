# Code Patterns & Structure

## Block Ordering & Structure

### Resource Blocks

1. `count` or `for_each` FIRST (blank line after)
2. Other arguments (alphabetical or logical grouping)
3. `tags` as last real argument
4. `depends_on` after tags (if needed)
5. `lifecycle` at the very end (if needed)

```hcl
resource "aws_nat_gateway" "this" {
  count = var.create_nat_gateway ? 1 : 0

  allocation_id = aws_eip.this[0].id
  subnet_id     = aws_subnet.public[0].id

  tags = { Name = "${var.name}-nat" }

  depends_on = [aws_internet_gateway.this]

  lifecycle { create_before_destroy = true }
}
```

### Variable Blocks

1. `description` (ALWAYS required)
2. `type`
3. `default`
4. `sensitive` (when true)
5. `nullable` (when false)
6. `validation`

Prefer simple types over `object()` unless strict validation needed. Use `optional()` for optional object attributes (1.3+). Use `any` for mixed types.

### Output Pattern

Pattern: `{name}_{type}_{attribute}`. Omit `this_` prefix. Use plural names for lists.

```hcl
output "security_group_id" {
  description = "The ID of the security group"
  value       = try(aws_security_group.this[0].id, "")
}
```

## Count vs For_Each

**Use count for:** simple numeric replication (`count = 3`), boolean conditions (`count = condition ? 1 : 0`), when order is fixed.

**Use for_each for:** keyed access (`aws_subnet.private["us-east-1a"]`), items that may be added/removed, multiple named resources.

### Migration (count -> for_each)

1. Add `for_each` to resource
2. Add `moved` blocks to preserve existing resources
3. Verify with `terraform plan` (should show "moved", not "destroy/create")

```hcl
moved {
  from = aws_subnet.private[0]
  to   = aws_subnet.private["us-east-1a"]
}
```

## Modern Terraform Features (1.0+)

**try() (0.13+)** -- safe fallbacks:
```hcl
output "sg_id" {
  value = try(aws_security_group.this[0].id, "")
}
```

**nullable = false (1.1+)** -- prevent null values in variables.

**moved blocks (1.1+)** -- rename resources/modules without destroy/recreate.

**optional() with defaults (1.3+):**
```hcl
variable "config" {
  type = object({
    name    = string
    timeout = optional(number, 300)
  })
}
```

**Cross-variable validation (1.9+):**
```hcl
variable "backup_days" {
  type = number
  validation {
    condition     = var.environment == "prod" ? var.backup_days >= 7 : true
    error_message = "Production requires backup_days >= 7"
  }
}
```

**Write-only arguments (1.11+):**
```hcl
resource "aws_db_instance" "this" {
  password_wo = data.aws_secretsmanager_secret_version.db_password.secret_string
}
```

## Version Management

```hcl
terraform {
  required_version = "~> 1.9"  # Pin minor, allow patch

  required_providers {
    aws = {
      source  = "hashicorp/aws"
      version = "~> 5.0"       # Pin major, allow minor/patch
    }
  }
}
```

| Syntax | Meaning | Use Case |
|--------|---------|----------|
| `"5.0.0"` | Exact | Avoid (inflexible) |
| `"~> 5.0"` | 5.0.x only | Recommended |
| `">= 5.0"` | Minimum | Risky (breaking changes) |

**Update workflow:** `terraform init` (lock) -> `terraform init -upgrade` (update) -> `terraform plan` (review) -> commit `.terraform.lock.hcl`.

## Refactoring Patterns

### 0.12/0.13 -> 1.x Checklist

- Replace `element(concat(...))` with `try()`
- Add `nullable = false` to non-null variables
- Use `optional()` in object types (1.3+)
- Add `validation` blocks
- Migrate secrets to write-only arguments (1.11+)
- Use `moved` blocks for resource refactoring (1.1+)
- Add cross-variable validation (1.9+)

### Secrets Remediation

Move secrets out of state. Use AWS Secrets Manager + write-only arguments (1.11+), or reference pre-existing secrets via data sources for older versions.

## Locals for Dependency Management

Use locals to enforce correct resource deletion order:

```hcl
locals {
  vpc_id = try(
    aws_vpc_ipv4_cidr_block_association.this[0].vpc_id,
    aws_vpc.this.id,
    ""
  )
}

resource "aws_subnet" "public" {
  vpc_id     = local.vpc_id  # Implicit dependency on CIDR association
  cidr_block = "10.1.0.0/24"
}
```

Prevents deletion errors by ensuring subnets are deleted before CIDR associations. Useful for complex VPC configurations with secondary CIDR blocks.
