## Architect Position — `--page` flag for /council

**Core recommendation:** Model `--page` as a read-only, execute-and-exit **session management command** (a sibling of `--list`/`--status`), not a session mode. It resolves a target session using the exact same logic as `--resume`, then reruns the scribe and opens `session.html` per the Presentation Contract open command, then exits. Zero new data model, zero new files, zero new infrastructure.

**Key argument:**
The engine already owns every primitive this feature needs, so the correct move is composition, not construction. Three existing contracts compose cleanly:

1. **Session resolution** is already specified in [Resume Logic](#resume-logic) items 1-2: no slug ⇒ most recent `active` session by `updated` timestamp from `index.json`; `<slug>` ⇒ fuzzy prefix-match in the index, picker on ambiguity. `--page` reuses this verbatim. Do **not** re-implement resolution; call the same routine.
2. **Rendering + open** is already specified in [Touchpoint Presentation Contract](#touchpoint-presentation-contract) item 3 (the `python3 render-session.py … || true` then `open … || xdg-open … || echo path` sequence) and reused by Resume Logic item 6. `--page` reuses that same open command.
3. **Placement in the parser** is the load-bearing decision. It MUST sit in the "Session management commands (execute and exit — no session started)" group in *Argument Parsing & Mode Resolution*, matched **before** any session mode. Slot it at position 4 (right after `--status`, before `--archive`). Because parsing is first-matching-flag-wins, mis-placing it below the modes would let a stray token fall through to **standard** mode and spin up a whole council — the single worst failure here.

Contract for the command:

| Aspect | Behavior |
|--------|----------|
| Accepts | `--page` (no arg) or `--page <slug>` |
| Resolves | Resume Logic items 1-2 (most-recent-active, or fuzzy slug) |
| Side effects | Rerun scribe if `render-session.py` + `session-state.json` present (idempotent, cheap), then open `session.html`. Never mutates `session.md`, never re-spawns agents, never advances phase. |
| No session found | Print `No active session. Start one with /<command> "idea" or list with /<command> --list` and **EXIT**. Never fall through to a new session. |
| Session predates live page (`session.html` absent) | Do NOT reconstruct here. Print `This session predates the live page. Reopen it with /<command> --resume <slug>` and **EXIT** (resume item 6 already does the fresh setup). |
| Headless | Same degradation as Contract item 6: `open` fails silently, print the page path once. |

This keeps `--page` a pure projection over existing state: it reads `index.json` (to resolve) and the session dir's pinned scribe artifacts (to render/open). It introduces no state of its own, so there is nothing to migrate, invalidate, or keep consistent.

**Risks if ignored:**
- **Precedence inversion (structural):** if `--page` is not in the execute-and-exit group and matched before the modes, an unmatched-arg path starts a real session — burning tokens and creating a junk session dir. This is the non-negotiable.
- **Re-render staleness vs. cost (performance):** re-rendering is O(read a few small files); always re-render before open so a page whose artifacts changed out-of-band is fresh, rather than serving a stale cached `session.html`. Cheap enough that a single code path (render-then-open) beats a conditional.
- **Reconstruction scope creep (integration/migration):** trying to auto-heal pre-live-page sessions inside `--page` duplicates Resume Logic item 6 and blurs the read-only boundary. Delegate to `--resume`; keep `--page` incapable of writing session content.

**Dependencies on other domains:**
- **Advocate (UX):** owns the exact copy and choice for the two dead-ends (no active session; session predates live page) — specifically whether we hard-stop or offer a follow-up action. I've proposed hard-stop-with-hint; defer the final wording.
- **Skeptic:** validate the precedence-ordering risk and confirm no arg-shape (`--page --pick`, `--page` with trailing idea text) can leak into a session-start.
- **Craftsman/Operator:** the mechanical edit to the parser list, `--help` text (add a `--page [<slug>]` line under SESSION MANAGEMENT), and headless `open` handling.

**Scope check (self-audit against my blind spots):** I considered supporting `--page --pick` and a `--page --all` cross-workspace variant. Both are YAGNI for this idea — `--resume --pick` already exists for interactive selection, and page-opening is inherently single-session. Ship the two forms (`--page`, `--page <slug>`) only.
