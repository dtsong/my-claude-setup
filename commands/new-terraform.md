# New Terraform Module Setup

Initialize a Terraform module with Daniel's preferred structure and testing.

## Stack

- **IaC**: Terraform (or OpenTofu)
- **Testing**: Terratest or terraform test
- **Linting**: tflint, tfsec
- **Docs**: terraform-docs

## Setup Steps

1. Create module structure:
```bash
mkdir <module-name> && cd <module-name>
```

2. Create standard files:
```
main.tf          # Primary resources
variables.tf     # Input variables
outputs.tf       # Output values
versions.tf      # Provider/Terraform version constraints
README.md        # Documentation
```

3. Create `versions.tf`:
```hcl
terraform {
  required_version = ">= 1.0"

  required_providers {
    aws = {
      source  = "hashicorp/aws"
      version = ">= 5.0"
    }
  }
}
```

4. Create `variables.tf` template:
```hcl
variable "name" {
  description = "Name prefix for resources"
  type        = string
}

variable "tags" {
  description = "Tags to apply to resources"
  type        = map(string)
  default     = {}
}
```

5. Create `outputs.tf` template:
```hcl
output "id" {
  description = "The ID of the created resource"
  value       = aws_xxx.this.id
}
```

6. Create examples directory:
```
examples/
  complete/
    main.tf
    outputs.tf
```

7. Create tests directory (using native terraform test):
```
tests/
  basic.tftest.hcl
```

8. Create `.pre-commit-config.yaml`:
```yaml
repos:
  - repo: https://github.com/antonbabenko/pre-commit-terraform
    rev: v1.96.0
    hooks:
      - id: terraform_fmt
      - id: terraform_validate
      - id: terraform_docs
      - id: terraform_tflint
      - id: terraform_tfsec
```

9. Create project CLAUDE.md:
```markdown
# <Module Name> Terraform Module

## Commands
terraform fmt -recursive   # format
terraform validate         # validate
terraform test             # run tests
terraform-docs .           # generate docs

## Structure
main.tf       - resources
variables.tf  - inputs
outputs.tf    - outputs
examples/     - usage examples
tests/        - terraform tests

## Best Practices
Uses terraform-skill for guidance.
```

10. Initialize git:
```bash
git init
echo ".terraform/\n*.tfstate*\n.terraform.lock.hcl" > .gitignore
git add .
git commit -m "chore: initial module setup"
```

## Verification

```bash
terraform fmt -check -recursive && terraform validate
```

## Best Practices Reference

The `terraform-skill` auto-activates when working with Terraform.
For comprehensive patterns, see: https://www.terraform-best-practices.com/
