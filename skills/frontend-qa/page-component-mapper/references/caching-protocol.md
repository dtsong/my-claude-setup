# Caching Protocol

## Cache Location

All cached artifacts live in `.claude/qa-cache/` at the project root:

```
.claude/qa-cache/
  project-config.json              # Stack auto-detection result
  component-maps/
    dashboard-settings.json        # One file per route (keyed by route slug)
    auth-login.json
  artifacts/                       # Diagnosis, fix, and test artifacts
```

Route slug derivation: replace `/` with `-`, strip leading `-`.
- `/dashboard/settings` -> `dashboard-settings`
- `/auth/login` -> `auth-login`
- `/` -> `root`

## Cache Validation Protocol

Execute this sequence when a cached ComponentMap exists:

```
1. Read the cached ComponentMap JSON
2. Run: git diff --name-only HEAD
3. Compare the output against the cachedFiles array in the map
4. Decision:
   - NO overlap between git diff output and cachedFiles → cache is VALID
   - ANY overlap → cache is STALE, rebuild from scratch
   - git command fails (not a repo, no commits) → SKIP cache, always rebuild
```

### Config-Busting Files

If ANY of these files appear in `git diff --name-only HEAD`, invalidate ALL cached component maps (not just the current route):

- `tsconfig.json`, `tsconfig.*.json`
- `next.config.js`, `next.config.mjs`, `next.config.ts`
- `tailwind.config.ts`, `tailwind.config.js`, `tailwind.config.mjs`
- `postcss.config.js`, `postcss.config.mjs`
- `package.json`, `package-lock.json`, `pnpm-lock.yaml`, `yarn.lock`
- `components.json` (shadcn config)

Rationale: These files affect module resolution, styling, or dependency versions across the entire project.

### Edge Cases

| Situation | Behavior |
|-----------|----------|
| Not a git repository | Skip cache entirely. Print: `"No git history — caching disabled (maps rebuilt each run)"` |
| No commits yet (`git diff` fails) | Same as above |
| Uncommitted changes to cached files | `git diff --name-only HEAD` includes uncommitted changes — cache invalidated correctly |
| File deleted since cache was built | File appears in `git diff` output — cache invalidated correctly |
| File renamed | Old path in `git diff`, new path not in cache — cache invalidated correctly |
| Branch switched | Changed files appear in `git diff` — cache invalidated correctly |
| `--fresh` flag provided | Skip validation entirely, rebuild from scratch |
| `--depth N` differs from cached depth | Rebuild from scratch (no incremental deepening) |

## First-Run Notice

The first time caching is used in a project (no `.claude/qa-cache/` directory exists), print this notice ONCE before the map output:

```
Component maps are cached in .claude/qa-cache/ to speed up repeat investigations.
Cache is validated against git changes automatically.
Use --fresh to force a full rebuild. Clear all caches: rm -rf .claude/qa-cache/
```

Do not repeat this notice on subsequent runs.

## Cache Status Display

On every invocation, show cache status inline:

| Outcome | Display |
|---------|---------|
| Cache hit (valid) | `Using cached map (2m old, 23 components, completeness: shallow) \| --fresh to rebuild` |
| Cache miss (stale) | `Rebuilt map (3 cached files changed since last map)` |
| Cache miss (no cache) | `Built new map (first run for this route)` |
| Cache disabled (no git) | `No git history — caching disabled` |
| Cache bypassed (--fresh) | `Rebuilt map (--fresh flag)` |

## Garbage Collection

On each qa-coordinator startup:
1. List all files in `.claude/qa-cache/artifacts/`
2. Delete any artifact file with `generatedAt` older than 7 days
3. Component maps are NEVER garbage-collected — they are validated by git diff on each use
4. `project-config.json` is invalidated only when `package.json` changes (detected via `git diff`)

## What NOT to Cache

- Diagnosis reports, fix results, and test results are stored in `artifacts/` but are NOT cached across sessions. They are write-once references, not reusable caches.
- The component map is the ONLY artifact with a cache-hit/miss validation flow.
- Never cache intermediate state (partial maps, in-progress traces). The map is either complete or not written.
