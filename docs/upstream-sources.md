# Upstream Sources

This repository vendors some third-party content for convenience.

Where possible, prefer contributing improvements upstream and then syncing the local snapshot.

## Vendored Directories

### skills/terraform-skill/

- Upstream: https://github.com/antonbabenko/terraform-skill
- License: Apache-2.0 (see `skills/terraform-skill/LICENSE`)

### skills/vercel-react-best-practices/

- Upstream reference: https://github.com/vercel-labs/agent-skills/tree/main/skills/react-best-practices
- Announcement: https://vercel.com/blog/introducing-react-best-practices

This repo includes a stub skill that fetches the upstream compiled rulebook (`AGENTS.md`) at runtime.

## Updating From Upstream

This repo currently maintains vendored content as a snapshot.

Recommended workflow:

1. Make changes upstream when possible.
2. Sync local vendored directories from upstream.
3. Keep `THIRD_PARTY_NOTICES.md` current.
