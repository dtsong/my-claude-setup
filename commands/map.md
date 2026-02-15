---
name: map
description: Map a route's component tree -- trace imports, detect boundaries, cache the result
---

# /map

Map a Next.js route to its component tree. Traces imports from the route entry point, detects server/client boundaries, captures props and hooks, and caches the result for downstream skills.

## Usage

```
/map /dashboard
/map /settings/billing
/map --depth 5 /dashboard
/map --fresh /dashboard
```

## Options

- `--depth N` -- Trace N levels deep (default: 3)
- `--fresh` -- Rebuild from scratch, ignoring cache

## Output

A component tree showing project components with file paths, server/client boundaries, and library component counts. Saved to `.claude/qa-cache/component-maps/`.
