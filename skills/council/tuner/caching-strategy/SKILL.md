---
name: "Caching Strategy"
department: "tuner"
description: "Cache hierarchy design with TTL policies, invalidation flows, and warming strategies"
version: 1
triggers:
  - "cache"
  - "caching"
  - "CDN"
  - "stale"
  - "invalidation"
  - "TTL"
  - "edge"
  - "stale-while-revalidate"
---

# Caching Strategy

## Purpose

Design a multi-layer caching architecture that minimizes latency and server load while maintaining data freshness. Produces a cache hierarchy diagram, key schema, TTL policy table, and invalidation flow for each cacheable resource.

## Inputs

- Application architecture (server framework, database, CDN provider)
- Resource inventory (pages, API responses, static assets, database queries)
- Access patterns (read/write ratio, update frequency, personalization requirements)
- Freshness requirements (how stale can each resource be before it hurts the user?)
- Current caching setup (if any) and known pain points

## Process

### Step 1: Identify Cacheable Resources and Access Patterns

Inventory all resources served by the application:
- Static assets (JS, CSS, images, fonts) — versioned or content-hashed?
- HTML pages — fully static, SSG, SSR, or dynamic?
- API responses — public or user-specific? How often do underlying data change?
- Database query results — read frequency vs write frequency per table/query
- Computed/aggregated data — dashboards, reports, search indexes

For each resource, document the read:write ratio and acceptable staleness window.

### Step 2: Design Cache Hierarchy

Define what is cached at each layer, from closest to the user outward:
- **Browser cache** — immutable versioned assets, prefetched resources
- **CDN / Edge cache** — public HTML, public API responses, optimized images
- **Application cache** — session data, computed results, frequently-accessed records
- **Database query cache** — prepared statement results, materialized views

Document which layer is the primary cache for each resource type.

### Step 3: Define Cache Key Schema

Design consistent, collision-free cache keys:
- Include resource type, identifier, and variant (e.g., `page:blog:slug:v2:locale:en`)
- Account for personalization dimensions (user role, locale, feature flags)
- Define key namespacing to support bulk invalidation (e.g., `page:blog:*`)
- Document key generation patterns for each resource type

### Step 4: Specify TTL Policies per Resource Type

Assign time-to-live values based on staleness tolerance:
- Immutable assets — long TTL (1 year) with content-hash cache busting
- Semi-static content (blog posts, product pages) — medium TTL (minutes to hours)
- Dynamic/personalized content — short TTL (seconds) or no-cache with revalidation
- API responses — TTL matched to underlying data change frequency

Document TTL as both `max-age` and `s-maxage` where CDN behavior differs from browser.

### Step 5: Design Invalidation Strategy

Define how stale cache entries are removed or refreshed:
- **Event-driven invalidation** — cache purge triggered by data mutations (webhook, pub/sub)
- **Time-based expiry** — TTL-only, no active invalidation
- **Versioned keys** — new key on data change, old key expires naturally
- **Tag-based invalidation** — associate cache entries with tags, purge by tag

Map each resource to its invalidation method. Document the mutation-to-purge flow.

### Step 6: Plan Stale-While-Revalidate Patterns

Design graceful degradation for cache misses:
- Which resources support `stale-while-revalidate`? Define the stale window.
- Which resources require strict freshness (financial data, auth state)?
- Define fallback behavior when the origin is unavailable (serve stale? show error?)
- Document `Cache-Control` header construction for each resource class

### Step 7: Specify Cache Warming Strategy for Cold Starts

Plan for empty caches after deployments, CDN purges, or scaling events:
- Which resources should be pre-warmed? (High-traffic pages, critical API responses)
- Warming method — build-time generation, deployment hook, background job, on-demand
- Warming priority order — warm the hottest paths first
- Cold start latency budget — acceptable response time before cache is warm

## Output Format

```markdown
# Caching Strategy: [Application Name]

## Cache Hierarchy

```
[User] → Browser Cache → CDN/Edge → App Cache → DB Query Cache → [Database]
```

| Layer | Resources Cached | TTL Range | Invalidation |
|-------|-----------------|-----------|-------------|
| Browser | ... | ... | ... |
| CDN/Edge | ... | ... | ... |
| Application | ... | ... | ... |
| DB Query | ... | ... | ... |

## Cache Key Reference

| Resource Type | Key Pattern | Variants | Example |
|--------------|-------------|----------|---------|
| ...          | ...         | ...      | ...     |

## TTL Policy Table

| Resource | Browser max-age | CDN s-maxage | stale-while-revalidate | Rationale |
|----------|----------------|-------------|----------------------|-----------|
| ...      | ...            | ...         | ...                  | ...       |

## Invalidation Flows

### [Resource Type]
1. Mutation occurs in [source]
2. [Event/webhook] triggers cache purge
3. [Layer] invalidates entries matching [pattern]
4. Next request triggers revalidation

## Cache Warming Plan

| Resource | Method | Trigger | Priority |
|----------|--------|---------|----------|
| ...      | ...    | ...     | ...      |

## Cache-Control Headers

| Route Pattern | Cache-Control Value |
|--------------|-------------------|
| ...          | ...               |
```

## Quality Checks

- [ ] Every cacheable resource has an assigned cache layer and TTL
- [ ] Cache keys include all variant dimensions (locale, role, version)
- [ ] Invalidation strategy is defined for every resource that can be mutated
- [ ] Stale-while-revalidate windows are specified where appropriate
- [ ] Personalized content is excluded from shared caches (CDN/edge)
- [ ] Cache warming covers the highest-traffic paths
- [ ] Cache-Control headers are specified for all route patterns
- [ ] Cold start scenario is addressed with acceptable latency budgets

## Evolution Notes
<!-- Observations appended after each use -->
