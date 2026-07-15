## Advocate Position — `--page` flag

**Core recommendation:** Make `--page` a pure "show me the window" command: a session-management verb (execute-and-exit, never spawns agents, never mutates state) that re-renders and reopens `session.html` for a resolved session, always printing the file path as a fallback.

**Key argument:**

The user's job here is not "continue the work" (that's `--resume`) but "get my eyes back on the live view I lost." These are two different intentions and must feel different. `--resume` picks up deliberation and burns tokens; `--page` is a zero-cost, read-only reopen. Conflating them would violate Krug's Law: the user typing `--page` after closing a tab mid-session expects the tab back, not a fresh round of agent debate. So `--page` slots into the **session-management** block (alongside `--list`, `--status`, `--archive`): parse, act, exit. It reuses `--resume`'s slug resolution verbatim so there is one mental model for "which session":

- **No slug:** most recent session by `updated` timestamp, silently opened (viewing is cheap and reversible, so no forced picker). Print a one-line orientation: `Opened "voice-onboarding" (most recent of 3 active). Use --page --pick to choose another.`
- **With slug:** fuzzy prefix match on the index; on ambiguity, show the same `AskUserQuestion` picker `--resume` uses.
- **`--page --pick`:** always show the interactive picker.

**Moment-of-need walkthrough:**

1. *Closed tab mid-session, back same day* → `/council --page` re-renders from current `session-state.json` and reopens. The page fills in with whatever progress has been written. No agents wake up.
2. *Back a day later* → identical. Crucially `--page` must resolve **any** status, not just `active`: users legitimately want to reread a `completed` or `stale` session's page. `--resume` is active-biased; `--page` is status-agnostic. Default no-slug still prefers most recent active, but a slug pointing at a completed session opens it without complaint.
3. *Three active sessions* → silent open of the most recent, plus the orientation line above so the user knows there were others and how to pick. No modal wall in the common case.
4. *Session predates F11 (no `session.html`)* → **do not crash and do not show a raw error.** Reconstruct the page best-effort per Contract item 3: copy `render-session.py` + template into the session dir, synthesize a `session-state.json` from `session.md` + the index (phase, mode, profile, roster names if recorded), render, open. If reconstruction is impossible, degrade to a friendly line: `This session predates the live page; showing what we can. Full detail: session.md`. The empty/legacy state IS an onboarding moment, not a dead end.
5. *SSH / no browser* → the `open || xdg-open || echo path` chain already degrades silently (Contract item 6). `--page` must **always** print the path, not only on failure, because the file path is the actual deliverable for a headless user.

**Error / empty states (force-specified):**

- No sessions at all → `No sessions found. Start one with /council <your idea>.`
- Slug matches nothing → `No session matching "<slug>". Run /council --list to see them.`
- Slug is ambiguous → picker (same as resume).
- Session dir exists but render fails → print the path and `session.md` fallback; never a stack trace.

**Risks if ignored:**

- **Intent collision:** if `--page` re-spawns agents or advances a phase, users lose trust and money; the "just show me the window" job is silently broken and there's no other verb that does it.
- **Legacy dead-ends:** pre-F11 sessions with no `session.html` throwing an error teaches users the flag is flaky, and they stop using it. Reconstruct-or-degrade is non-negotiable.
- **Headless invisibility:** if the path isn't printed on success, SSH/CI users see nothing happen and assume a no-op.
- **Picker fatigue:** forcing a picker on every multi-session invocation punishes the common case; silent-most-recent + orientation line respects Krug's Law.

**Dependencies on other domains:**

- **Architect:** confirm `--page` belongs in the session-management parse block (execute-and-exit), and define the `session-state.json` reconstruction contract for pre-F11 sessions (which fields are recoverable from `session.md` + index).
- **Craftsman:** factor the slug-resolution logic (`--resume`'s fuzzy prefix + picker) into a shared helper so `--page` and `--resume` cannot drift; add the `--page` row to `--help` and the docs table; ensure the `open` fallback chain and always-print-path behavior are one reused snippet, not copy-paste.
