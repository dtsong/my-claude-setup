# Design Sketch: /council --page

## Overview

Add `--page [<slug>] [--pick]` as a session-management command (execute and
exit, like --list/--status): resolve a session with the exact resolver
--resume uses, rerun the scribe, open session.html, always print the path,
never spawn agents or mutate session state. Composition over construction:
zero new runtime code, the flag is engine prose plus help text.

## Key Recommendations

**Architect (9):** Slot it in the session-management parse group at position 4
(after --status), before any session mode; first-match-wins parsing means
mis-placement below the modes would let a stray token fall through and spin up
a full council. Reuse Resume Logic items 1-2 for resolution and Contract item 3
for the render+open sequence verbatim. Read-only: no index writes, no locks.

**Craftsman (7):** One slug resolver, not two: call the existing Resume Logic
so --page and --resume can never drift. The executable surface is already
covered by pipeline/tests/test_render_session.py (idempotency and the
complete-session refresh-tag tests). The real work is consistency across five
surfaces: engine priority list, engine --help block, a new ### --page
subsection, council.md argument-hint/examples, and the agentic-council port.

**Advocate (7):** --page means "show me the window", not "continue the work".
Status-agnostic (reopening a completed session's page is legitimate), silent
most-recent-active default with a one-line orientation when other sessions
exist, same picker as --resume on ambiguity, and always print the file path
(it is the deliverable for SSH users).

## Open Questions / Trade-offs

1. **Pre-F11 sessions (no session.html):** Architect and Craftsman say print a
   pointer to --resume and exit; Advocate says reconstruct best-effort from
   session.md + index. Recommended resolution: reconstruct (it is Contract
   item 3 plus a synthesized state file, cheap and read-only), degrade to the
   friendly pointer only when reconstruction fails.
2. **Default scope:** most recent active (Architect) vs any status when a slug
   is given (Advocate). Both: no-slug prefers active, slug opens anything.
3. **Cross-repo parity:** the same five-surface patch must land in
   agentic-council deliberately, not be assumed automatic.
