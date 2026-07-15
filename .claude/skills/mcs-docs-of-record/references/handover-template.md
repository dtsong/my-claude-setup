# Handover doc template

Canonical generator: `/handover` (defined in `commands/handover.md`). Prefer running the command over hand-writing a handover; it captures branch, recent commits, and full session context automatically. Use this reference when reviewing an existing handover for completeness, or writing one by hand when `/handover` is unavailable.

Target length: 80-120 lines. Output path: `memory/HANDOVER-<YYYY-MM-DD-HHMM>.md` (repo root `memory/`, not `.claude/`).

## Section-by-section (from `commands/handover.md` and the `2026-06-22-0036` exemplar on disk)

1. **Title + tag comment**: `# Session Handover` + date/time, followed by `<!-- Tag: <label> -->` if the session had a `--tag`. Note: both `commands/handover.md`'s own template and the on-disk exemplar use an em dash between "Handover" and the timestamp, a pre-existing house-style violation (the no-em-dash rule postdates them, commit `48af508`). Use a hyphen or colon instead when writing a new one; fixing the template itself is in scope next time this file is touched. The exemplar's tag was `openrouter-integration + acceptance-gate-fix`, a compound tag when the session covered two threads.
2. **Session Summary**: 2-3 sentences. State the starting goal, the actual arc if it diverged (the exemplar: "Started as a 'how do we use OpenRouter?' question that turned into a brainstorm... Mid-session, two screenshots of a misbehaving hook interrupted twice"), and what shipped vs what was explicitly NOT started.
3. **What Was Done**: bulleted, one item per concrete change, each tagged with its commit SHA in parens. Not a narrative, a changelog.
4. **Key Decisions Made**: the highest-value section, per the command's own instructions ("spend extra effort here"). Each entry is 3 sub-bullets: **Decision** (what), **Context** (why it came up), **Rationale** (why this option over the alternatives considered). Capture WHY, not just WHAT; a decision without a rejected alternative is not useful to the next session.
5. **Pitfalls & Gotchas**: errors actually hit, dead ends explored, workarounds applied. Concrete enough to save the next session the same debugging time. Example from the exemplar: "`git commit --only -- <paths> -m <msg>` FAILS, the `--` swallows `-m` as a pathspec. Put `-m` BEFORE `--`."
6. **Open Questions**: unresolved items needing more research or explicit owner input. Do not silently resolve these yourself when picking up a handover; they were left open on purpose.
7. **Next Steps**: ordered, numbered, priority order (do #1 before #2). Not a wishlist.
8. **Important Files**: 2-column table, File | Role. Only files a fresh session would need to orient itself, not every file touched.
9. **Session Context**: branch name, last 5 commits one-line each (`git log --oneline -5`).

## Rules that matter

- Write a REAL reflection, not a blank template. If a section genuinely has nothing, write "None", do not invent content to fill it.
- Do not ask the user what to include; the session has full context, just write it.
- `CLAUDE.md` (this machine: also `~/.claude/CLAUDE.md`, see SKILL.md gotcha) instructs every new session to check `ls -t memory/HANDOVER-*.md | head -3` and read the newest one before starting work. A handover that omits Next Steps or buries the real blocker defeats this mechanism silently, no error is raised, the next session just doesn't know.
- Only one handover exists on disk as of 2026-07-02 (`memory/HANDOVER-2026-06-22-0036.md`); the `PreCompact` auto-hook (`hooks/pre-compact-handover.sh`) also writes `memory/HANDOVER-<timestamp>-auto.md` on automatic (not manual `/compact`) context compaction, piping the last 500 transcript lines through `claude -p --model sonnet`. Verify current count: `ls memory/HANDOVER-*.md | wc -l`.
