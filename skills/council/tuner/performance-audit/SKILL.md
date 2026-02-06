---
name: "Performance Audit"
department: "tuner"
description: "Bottleneck identification with profiling baselines and prioritized optimization roadmap"
version: 1
triggers:
  - "performance"
  - "slow"
  - "bottleneck"
  - "Core Web Vitals"
  - "lighthouse"
  - "profiling"
  - "LCP"
  - "CLS"
  - "INP"
  - "TTFB"
  - "speed"
---

# Performance Audit

## Purpose

Identify performance bottlenecks across the full stack — rendering, network, bundle, database, and infrastructure. Produces a profiled baseline, a prioritized bottleneck inventory, and an optimization roadmap with estimated impact for each recommendation.

## Inputs

- Application URL or local dev environment access
- Current performance complaints or targets (e.g., "page loads slowly", "LCP > 4s")
- Tech stack details (framework, database, hosting, CDN)
- Traffic profile (approximate users, peak times, geographic distribution)

## Process

### Step 1: Profile Current Performance Baseline

Run Lighthouse (or equivalent) on key pages. Record Core Web Vitals: LCP, CLS, INP, TTFB. Capture p50, p95, and p99 values where available. Document the baseline as the reference point for all improvements.

### Step 2: Identify Render Bottlenecks

Analyze the critical rendering path:
- Largest Contentful Paint — what element is the LCP candidate? Is it blocked by fonts, images, or JS?
- Cumulative Layout Shift — which elements shift? Are dimensions reserved?
- Interaction to Next Paint — which event handlers are slow? Is there long-task blocking?
- Time to First Byte — is the server response slow, or is it DNS/TLS overhead?

### Step 3: Analyze Bundle Size and Code Splitting

Inspect the JavaScript and CSS bundles:
- Total bundle size (compressed and uncompressed)
- Largest modules/chunks and their purpose
- Unused code ratio (tree shaking effectiveness)
- Code splitting boundaries — are routes lazy-loaded?
- Third-party script impact (analytics, chat widgets, ads)

### Step 4: Audit Database Queries

Review server-side data access patterns:
- Identify N+1 query patterns
- Check for missing indexes on filtered/sorted columns
- Review slow query logs or EXPLAIN plans for high-frequency queries
- Evaluate connection pooling configuration
- Check for unnecessary data fetching (selecting columns not used)

### Step 5: Evaluate Network Waterfall

Analyze the network request pattern:
- Total request count and payload size per page load
- Request sequencing — are there blocking chains?
- Compression (gzip/brotli) on text assets
- Image optimization (format, sizing, lazy loading)
- HTTP/2 or HTTP/3 multiplexing usage

### Step 6: Assess Core Web Vitals Scores

Compile field data (CrUX) and lab data (Lighthouse) into a scorecard:
- Green/amber/red status for each vital
- Comparison against industry benchmarks
- Mobile vs desktop performance gap
- Geographic performance variance if applicable

### Step 7: Recommend Prioritized Optimizations

Rank each finding by impact (estimated improvement) and effort (implementation cost):
- High impact / low effort — do immediately
- High impact / high effort — plan and schedule
- Low impact / low effort — batch together
- Low impact / high effort — skip or defer

## Output Format

```markdown
# Performance Audit: [Application/Page Name]

## Baseline Scorecard

| Metric | Current | Target | Status |
|--------|---------|--------|--------|
| LCP    | ...     | ...    | ...    |
| CLS    | ...     | ...    | ...    |
| INP    | ...     | ...    | ...    |
| TTFB   | ...     | ...    | ...    |
| Bundle Size (gzip) | ... | ... | ... |
| Request Count | ... | ... | ... |

## Bottleneck Inventory

### Critical (High Impact)
1. **[Bottleneck name]** — [Description, current metric, estimated improvement]

### Moderate (Medium Impact)
1. **[Bottleneck name]** — [Description, current metric, estimated improvement]

### Minor (Low Impact)
1. **[Bottleneck name]** — [Description, current metric, estimated improvement]

## Optimization Roadmap

| Priority | Optimization | Expected Impact | Effort | Metric Affected |
|----------|-------------|-----------------|--------|-----------------|
| P0       | ...         | ...             | ...    | ...             |
| P1       | ...         | ...             | ...    | ...             |
| P2       | ...         | ...             | ...    | ...             |

## Database Query Findings

| Query/Pattern | Issue | Current Cost | Recommendation |
|--------------|-------|-------------|----------------|
| ...          | ...   | ...         | ...            |

## Bundle Analysis

| Chunk | Size (gzip) | Purpose | Optimization |
|-------|-------------|---------|-------------|
| ...   | ...         | ...     | ...         |
```

## Quality Checks

- [ ] Baseline measurements are recorded with specific numbers, not vague descriptions
- [ ] Every bottleneck has a measured current value and an estimated improvement
- [ ] Optimizations are prioritized by impact-to-effort ratio
- [ ] Core Web Vitals are assessed for both mobile and desktop
- [ ] Database queries are reviewed with EXPLAIN plans or equivalent evidence
- [ ] Bundle analysis includes both first-party and third-party code
- [ ] Network waterfall identifies blocking request chains
- [ ] Recommendations include specific implementation steps, not just "optimize X"

## Evolution Notes
<!-- Observations appended after each use -->
