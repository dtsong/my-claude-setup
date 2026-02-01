---
name: helm-generation
description: Generating Helm values files with minimal-diff approach
---

# Helm Values Generation Skill

Generate Helm values files that only override necessary defaults.

## Core Principles

1. **Minimal diff**: Output ONLY values that differ from chart defaults
2. **Proper types**: Booleans as booleans, not strings
3. **Constraint validation**: Verify values against chart's allowed options
4. **CLI args for metadata**: `name`/`namespace` are CLI args, not values
5. **Verification-first**: Read chart defaults before generating

## Process

### Step 1: Analyze Chart

Before generating values, understand the chart:

```bash
# Get chart info
helm show values <chart> [--version <version>]

# Or for OCI charts
helm show values oci://registry/chart

# Check chart README for constraints
helm show readme <chart>
```

**Gather:**
```
[ ] Default values identified
[ ] Required values (no defaults) identified
[ ] Value constraints documented (enums, ranges)
[ ] Chart version pinned
```

### Step 2: Generate Values

**Structure:**
```yaml
# values.yaml
# Only override what differs from defaults

# Example: Overriding replica count (default: 1)
replicaCount: 3

# Example: Overriding image (default: nginx:latest)
image:
  repository: myregistry/myapp
  tag: "1.2.3"  # Quotes for version strings

# Example: Boolean (NOT "true" string)
autoscaling:
  enabled: true
```

**What to EXCLUDE:**
- Values matching chart defaults
- `name:` or `namespace:` (use `helm install <name> -n <ns>`)
- Commented-out defaults
- Redundant nested keys

### Step 3: Type Handling

| YAML Type | Example | Common Mistake |
|-----------|---------|----------------|
| Boolean | `enabled: true` | `enabled: "true"` |
| Integer | `replicas: 3` | `replicas: "3"` |
| String version | `tag: "1.2.3"` | `tag: 1.2.3` (parsed as float) |
| Null | `value: null` | `value: ""` |
| List | `- item` | Forgetting `-` |

### Step 4: Validation

```bash
# Lint values
helm lint <chart> -f values.yaml

# Template to verify
helm template <release> <chart> -f values.yaml

# Dry-run install
helm install <release> <chart> -f values.yaml --dry-run
```

## Common Chart Patterns

**Ingress:**
```yaml
ingress:
  enabled: true
  className: nginx
  hosts:
    - host: app.example.com
      paths:
        - path: /
          pathType: Prefix
  tls:
    - secretName: app-tls
      hosts:
        - app.example.com
```

**Resources:**
```yaml
resources:
  requests:
    cpu: 100m
    memory: 128Mi
  limits:
    cpu: 500m
    memory: 512Mi
```

**Service Account (with IRSA/Workload Identity):**
```yaml
serviceAccount:
  create: true
  annotations:
    eks.amazonaws.com/role-arn: arn:aws:iam::ACCOUNT:role/ROLE
```

## Anti-patterns to Avoid

- Including `name:` or `namespace:` in values
- Copying all defaults with minor changes
- String booleans: `"true"` instead of `true`
- Unquoted version strings that look like numbers
- Hardcoded secrets (use external-secrets, sealed-secrets, etc.)
- Values that don't exist in the chart schema

## Output Format

When generating values, output:

1. **Chart analysis**: What chart, version, key constraints
2. **Values file**: Only overridden values with comments
3. **Install command**: Full helm install/upgrade command
4. **Validation command**: How to verify before applying
5. **Notes**: Any external dependencies (secrets, CRDs, etc.)

## Example Workflow

User: "Generate Helm values for nginx-ingress"

Response:
```yaml
# values.yaml for ingress-nginx
# Chart: ingress-nginx/ingress-nginx v4.10.0
# Only non-default values shown

controller:
  replicaCount: 2

  resources:
    requests:
      cpu: 100m
      memory: 90Mi
    limits:
      cpu: 500m
      memory: 256Mi

  service:
    type: LoadBalancer
```

```bash
# Install command
helm install ingress-nginx ingress-nginx/ingress-nginx \
  --namespace ingress-nginx \
  --create-namespace \
  -f values.yaml

# Verify
helm template ingress-nginx ingress-nginx/ingress-nginx -f values.yaml | kubectl apply --dry-run=client -f -
```
