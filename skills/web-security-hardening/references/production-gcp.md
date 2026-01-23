# Production Security (GCP + Python/TypeScript)

Extended checklist for production deployments on GCP with Python backends and TypeScript frontends.

## GCP Infrastructure

### IAM & Access Control
- [ ] Dedicated service accounts per service (not default compute SA)
- [ ] Workload Identity for GKE instead of JSON keys
- [ ] IAM Conditions for time-bound or context-aware access
- [ ] Regular access reviews and unused permission cleanup

```bash
# Create minimal service account
gcloud iam service-accounts create my-api-sa --display-name="My API Service Account"
gcloud projects add-iam-policy-binding $PROJECT \
  --member="serviceAccount:my-api-sa@$PROJECT.iam.gserviceaccount.com" \
  --role="roles/cloudsql.client"
```

### Network Security
- [ ] Cloud Armor enabled for WAF/DDoS at load balancer
- [ ] VPC Service Controls for sensitive projects
- [ ] Private Google Access (no public IPs on backends)
- [ ] Firewall rules: ingress only through load balancer

### Secrets Management
- [ ] All secrets in Secret Manager (not env vars or config files)
- [ ] No secrets in git (use gitleaks or trufflehog in CI)
- [ ] Secret rotation policy with versioning
- [ ] Audit logging enabled for secret access

```python
from google.cloud import secretmanager

def get_secret(secret_id: str, project_id: str) -> str:
    client = secretmanager.SecretManagerServiceClient()
    name = f"projects/{project_id}/secrets/{secret_id}/versions/latest"
    response = client.access_secret_version(name=name)
    return response.payload.data.decode("utf-8")

# Usage
db_password = get_secret("db-password", "my-project")
```

### Cloud Run / GKE Hardening
- [ ] Min instances > 0 for critical paths (avoid cold start auth bypass)
- [ ] CPU always allocated if doing background auth checks
- [ ] Ingress restricted to internal + load balancer
- [ ] Binary Authorization for container provenance (GKE)

## Python Backend

### Dependency Security
- [ ] Dependencies pinned with hashes (`poetry.lock`, `pip-compile --generate-hashes`)
- [ ] Automated vulnerability scanning (Dependabot, Snyk, `pip-audit`)
- [ ] Regular update schedule (weekly for patches, monthly for minor)

```bash
# Audit dependencies
pip-audit --require-hashes -r requirements.txt
```

### Error Handling
- [ ] No stack traces in production responses
- [ ] Structured logging without sensitive data
- [ ] PII masking in logs (emails, tokens, IPs if needed)

```python
import logging
import structlog

# Bad - leaks internals
except Exception as e:
    return {"error": str(e)}, 500

# Good - log details, return generic message
except Exception:
    structlog.get_logger().exception("payment_failed", user_id=user.id)
    return {"error": "An unexpected error occurred"}, 500
```

### Session & Authentication
- [ ] Signed, HttpOnly, Secure, SameSite=Strict cookies
- [ ] CSRF tokens on all state-changing endpoints
- [ ] Short session TTLs (15-30 min) with refresh tokens
- [ ] Token revocation list for logout/compromise

```python
# Secure cookie settings (Flask)
app.config.update(
    SESSION_COOKIE_SECURE=True,
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE='Strict',
    PERMANENT_SESSION_LIFETIME=timedelta(minutes=30),
)
```

### Request Hardening
- [ ] Timeouts on all external HTTP calls
- [ ] Database connection pool limits
- [ ] Request body size limits (beyond file uploads)
- [ ] Slowloris protection (gunicorn/uvicorn timeouts)

```python
import httpx

# Always set timeouts
async with httpx.AsyncClient(timeout=httpx.Timeout(10.0, connect=5.0)) as client:
    response = await client.get(url)

# SQLAlchemy pool limits
engine = create_engine(url, pool_size=5, max_overflow=10, pool_timeout=30)
```

### Async Security
- [ ] No blocking calls in async handlers
- [ ] Task cancellation handling for auth state
- [ ] Rate limiting aware of concurrent requests per user

## TypeScript Frontend

### Build-Time Security
- [ ] Subresource Integrity (SRI) for CDN scripts
- [ ] No secrets in client bundles (use runtime config from API)
- [ ] Source maps disabled or uploaded privately to error tracking
- [ ] Dead code elimination enabled

```html
<!-- SRI for external scripts -->
<script src="https://cdn.example.com/lib.js"
  integrity="sha384-abc123..."
  crossorigin="anonymous"></script>
```

### Runtime Security
- [ ] CSP nonces for inline scripts (if any)
- [ ] No `innerHTML` or `dangerouslySetInnerHTML` with user content
- [ ] DOMPurify for any displayed user-generated HTML
- [ ] Strict TypeScript config (`strict: true`, `noUncheckedIndexedAccess`)

```typescript
import DOMPurify from 'dompurify';

// Sanitize user content before display
const safeHtml = DOMPurify.sanitize(userGeneratedHtml, {
  ALLOWED_TAGS: ['b', 'i', 'em', 'strong', 'a', 'p'],
  ALLOWED_ATTR: ['href'],
});
```

### Storage & Auth State
- [ ] HttpOnly cookies for auth tokens (not localStorage)
- [ ] Clear all auth state on logout (cookies, memory, service workers)
- [ ] No sensitive data in sessionStorage/localStorage
- [ ] PKCE for OAuth flows

```typescript
// Clear auth state completely
function logout() {
  // Clear cookies via API call
  await fetch('/api/auth/logout', { method: 'POST', credentials: 'include' });
  // Clear any in-memory state
  authStore.reset();
  // Redirect
  window.location.href = '/login';
}
```

## CI/CD Pipeline

### Static Analysis
- [ ] SAST scanning (Semgrep, Bandit for Python, ESLint security plugins)
- [ ] Dependency vulnerability scanning in CI
- [ ] Secrets detection (gitleaks, trufflehog)
- [ ] Container image scanning via Artifact Registry

```yaml
# Example GitHub Actions step
- name: Run Bandit
  run: bandit -r src/ -ll -ii

- name: Run gitleaks
  uses: gitleaks/gitleaks-action@v2
```

### Deployment Security
- [ ] Immutable deployments (new revisions, not in-place updates)
- [ ] Rollback tested and documented
- [ ] Staging environment with production-like security
- [ ] Deploy keys/tokens scoped minimally and rotated

## Monitoring & Incident Response

### Logging & Alerting
- [ ] Cloud Logging with log-based alerts for:
  - Authentication failures (brute force detection)
  - 5xx error spikes
  - Unusual traffic patterns
- [ ] Error Reporting for unhandled exceptions
- [ ] Uptime checks with alerting

### Audit Trail
- [ ] GCP Admin Activity audit logs enabled
- [ ] Data Access logs for sensitive resources
- [ ] Application-level audit log for user actions
- [ ] Log retention policy (90+ days for security events)

### Incident Prep
- [ ] Documented runbooks for common incidents
- [ ] Contact list for security escalation
- [ ] Log access for on-call without over-privileged standing access
