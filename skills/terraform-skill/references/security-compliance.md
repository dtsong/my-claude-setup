# Security & Compliance

## Security Scanning Tools

```bash
trivy config .
checkov -d .
terraform-compliance -f compliance/ -p tfplan.json
```

### Trivy Integration

```bash
# macOS
brew install trivy

# Linux
curl -sfL https://raw.githubusercontent.com/aquasecurity/trivy/main/contrib/install.sh | sh -s -- -b /usr/local/bin

# In CI
- uses: aquasecurity/trivy-action@master
  with:
    scan-type: 'config'
    scan-ref: '.'
```

Trivy is the successor to tfsec, maintained by Aqua Security.

### Checkov Integration

```bash
checkov -d . --framework terraform
checkov -d . --skip-check CKV_AWS_23
checkov -d . -o json > checkov-report.json
```

## Common Security Issues

**Secrets in variables:**
```hcl
# BAD
variable "database_password" {
  default = "SuperSecret123!"
}

# GOOD: Use Secrets Manager
data "aws_secretsmanager_secret_version" "db_password" {
  secret_id = "prod/database/password"
}
resource "aws_db_instance" "this" {
  password = data.aws_secretsmanager_secret_version.db_password.secret_string
}
```

**Default VPC:** Create dedicated VPCs with private subnets instead.

**Missing encryption:**
```hcl
resource "aws_s3_bucket_server_side_encryption_configuration" "data" {
  bucket = aws_s3_bucket.data.id
  rule {
    apply_server_side_encryption_by_default {
      sse_algorithm = "AES256"
    }
  }
}
```

**Open security groups:** Restrict to specific ports and sources. Never use `0.0.0.0/0` for ingress.

## Compliance Testing

### terraform-compliance

```bash
pip install terraform-compliance
terraform plan -out=tfplan
terraform show -json tfplan > tfplan.json
terraform-compliance -f compliance/ -p tfplan.json
```

```gherkin
Feature: AWS Resources must be encrypted
  Scenario: S3 buckets must have encryption
    Given I have aws_s3_bucket defined
    When it has aws_s3_bucket_server_side_encryption_configuration
    Then it must contain rule
    And it must contain apply_server_side_encryption_by_default
```

### Open Policy Agent (OPA)

```rego
package terraform.s3
deny[msg] {
  resource := input.resource_changes[_]
  resource.type == "aws_s3_bucket"
  not resource.change.after.server_side_encryption_configuration
  msg := sprintf("S3 bucket '%s' must have encryption enabled", [resource.address])
}
```

## Secrets Management

### AWS Secrets Manager Pattern

```hcl
resource "aws_secretsmanager_secret" "db_password" {
  name                    = "prod/database/password"
  recovery_window_in_days = 30
}

resource "aws_secretsmanager_secret_version" "db_password" {
  secret_id     = aws_secretsmanager_secret.db_password.id
  secret_string = random_password.db_password.result
}

resource "random_password" "db_password" {
  length  = 32
  special = true
}
```

Never commit secrets. Add to `.gitignore`: `*.tfvars`, `.env`, `secrets/`.

## State File Security

### Encrypt State at Rest

```hcl
terraform {
  backend "s3" {
    bucket         = "my-terraform-state"
    key            = "prod/terraform.tfstate"
    region         = "us-east-1"
    dynamodb_table = "terraform-locks"
    encrypt        = true
  }
}
```

### Secure State Bucket

Enable versioning, encryption, and block all public access:

```hcl
resource "aws_s3_bucket_versioning" "terraform_state" {
  bucket = aws_s3_bucket.terraform_state.id
  versioning_configuration { status = "Enabled" }
}

resource "aws_s3_bucket_server_side_encryption_configuration" "terraform_state" {
  bucket = aws_s3_bucket.terraform_state.id
  rule {
    apply_server_side_encryption_by_default { sse_algorithm = "AES256" }
  }
}

resource "aws_s3_bucket_public_access_block" "terraform_state" {
  bucket                  = aws_s3_bucket.terraform_state.id
  block_public_acls       = true
  block_public_policy     = true
  ignore_public_acls      = true
  restrict_public_buckets = true
}
```

Restrict state access with IAM policies scoped to specific roles and bucket paths.

## IAM Best Practices

Use least-privilege policies with specific actions and resources. Never use wildcard `*` for Action or Resource.

## Compliance Checklists

**SOC 2:** Encryption at rest/transit, least-privilege IAM, logging, MFA, CI/CD scanning.

**HIPAA:** PHI encrypted, access logs, dedicated VPC, backup/retention, audit trail.

**PCI-DSS:** Network segmentation, no default passwords, strong encryption, scanning, access control.
