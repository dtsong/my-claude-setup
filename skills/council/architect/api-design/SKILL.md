---
name: "API Design"
department: "architect"
description: "[Council] REST/RPC endpoint contracts with request/response types and error handling. Used during council/academy deliberation only."
version: 1
triggers:
  - "API"
  - "endpoint"
  - "route"
  - "REST"
  - "RPC"
  - "server action"
  - "webhook"
  - "contract"
---

# API Design

## Purpose

Design REST/RPC endpoint contracts with request/response types, error handling, and versioning strategy. Produces TypeScript type definitions and endpoint documentation that serve as the contract between frontend and backend.

## Inputs

- Feature requirements (from interview/idea phase)
- Schema design output (entities, relationships — drives endpoint shape)
- Existing endpoints (current route handlers, naming conventions)
- Authentication/authorization model (who can call what)

## Process

### Step 1: Inventory Existing Endpoints

Read current route handlers and list all existing paths, HTTP methods, request/response shapes, and auth requirements. Note naming conventions and patterns in use.

### Step 2: Identify New Endpoints Needed

From the feature requirements and schema design output, determine what operations the frontend needs. Group by resource and map to CRUD operations where applicable.

### Step 3: Define Endpoint Contracts

For each endpoint, specify:
- **Method**: GET, POST, PUT, PATCH, DELETE
- **Path**: Following existing naming conventions
- **Request**: Body schema, URL params, query params
- **Response**: Success shape (with HTTP status), error shape
- **Auth**: Required role/permission, or public

### Step 4: Design Type Definitions

Write TypeScript interfaces for:
- Request body types
- Response types (success and error)
- Shared types (enums, union types, reusable shapes)
- Zod schemas for runtime validation where applicable

### Step 5: Plan Authentication/Authorization

For each endpoint, define:
- Whether authentication is required
- What role or permission is needed
- How authorization is enforced (middleware, RLS, inline check)
- Service-to-service auth if applicable

### Step 6: Define Error Contract

Design a consistent error response shape:
- Error code enum (application-level codes, not just HTTP status)
- Error response structure (code, message, details)
- HTTP status mapping (which app errors map to which HTTP statuses)
- Validation error format (field-level errors for form submissions)

### Step 7: Consider Pagination and Filtering

For list endpoints:
- Pagination strategy (cursor-based preferred for real-time data, offset for static)
- Filter parameters (query string format, supported operators)
- Sort parameters (field + direction)
- Default and maximum page sizes

### Step 8: Document Rate Limits and Caching

If applicable:
- Rate limit tiers per endpoint or endpoint group
- Cache-Control headers for GET endpoints
- ETag/If-None-Match for conditional requests
- Stale-while-revalidate strategies

## Output Format

```markdown
# API Design: [Feature Name]

## Endpoint Overview

| Method | Path | Auth | Description |
|--------|------|------|-------------|
| GET    | /api/... | authenticated | ... |
| POST   | /api/... | authenticated | ... |

## Type Definitions

```typescript
// Shared types
interface PaginatedResponse<T> {
  data: T[];
  cursor: string | null;
  hasMore: boolean;
}

// Request types
interface CreateFooRequest {
  name: string;
  // ...
}

// Response types
interface FooResponse {
  id: string;
  name: string;
  createdAt: string;
  // ...
}
```

## Error Contract

```typescript
enum ErrorCode {
  VALIDATION_ERROR = 'VALIDATION_ERROR',
  NOT_FOUND = 'NOT_FOUND',
  UNAUTHORIZED = 'UNAUTHORIZED',
  FORBIDDEN = 'FORBIDDEN',
  // ...
}

interface ApiError {
  code: ErrorCode;
  message: string;
  details?: Record<string, string[]>; // field-level errors
}
```

| Error Code | HTTP Status | When |
|-----------|-------------|------|
| VALIDATION_ERROR | 400 | Request body fails validation |
| NOT_FOUND | 404 | Resource does not exist |
| UNAUTHORIZED | 401 | Missing or invalid auth |
| FORBIDDEN | 403 | Authenticated but lacking permission |

## Endpoint Details

### [METHOD] [path]

**Auth**: [requirement]

**Request**:
```typescript
// params / body / query
```

**Response** (200):
```typescript
// success shape
```

**Errors**:
- 400: [when]
- 404: [when]

**Example**:
```bash
curl -X POST /api/foo \
  -H "Authorization: Bearer ..." \
  -d '{"name": "bar"}'
```

## Pagination Strategy
- **Method**: [cursor-based / offset]
- **Default page size**: [N]
- **Max page size**: [N]

## Caching Strategy
| Endpoint Pattern | Cache-Control | Notes |
|-----------------|---------------|-------|
| GET /api/...    | ...           | ...   |
```

## Quality Checks

- [ ] Every endpoint has defined auth requirements
- [ ] Error cases are enumerated for each endpoint
- [ ] Request and response types are fully specified (no `any` types)
- [ ] Naming follows existing project conventions (REST or RPC, plural vs singular)
- [ ] List endpoints include pagination strategy
- [ ] Shared types are extracted (no duplication across endpoints)
- [ ] Error contract is consistent across all endpoints
- [ ] Examples include realistic request/response payloads

## Evolution Notes
<!-- Observations appended after each use -->
