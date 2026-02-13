# Third-Party Notices

This repository vendors some third-party content for convenience.

Each vendored directory retains its own license and attribution requirements.

## skills/terraform-skill/

- Upstream: https://github.com/antonbabenko/terraform-skill
- License: Apache-2.0 (see `skills/terraform-skill/LICENSE`)
- Notes: This directory is maintained upstream. Prefer contributing improvements upstream.

## skills/vercel-react-best-practices/

- Upstream references:
  - https://github.com/vercel-labs/agent-skills/tree/main/skills/react-best-practices
  - https://vercel.com/blog/introducing-react-best-practices
- Attribution: Vercel Engineering
- Notes: This repo intentionally does *not* vendor the full rule set. The local skill is a stub that fetches upstream guidance at runtime.

## skills/tdd/

- Upstream sources:
  - https://github.com/mattpocock/skills/tree/main/tdd (TDD skill with reference files)
  - https://github.com/obra/superpowers (test-driven-development skill + testing-anti-patterns)
- Licenses: MIT (superpowers)
- Notes: Merged skill combining planning and interface design guidance from
  mattpocock/skills with discipline enforcement from obra/superpowers.
  Reference files adapted from both upstream sources.
