# Council Live Session Page (F11): Design

Date: 2026-07-14
Status: Approved
Predecessor: US-008 / F10 (HTML verdict render at design approval, PR #74)

## Problem

During a live council session, decision context never reliably reaches the user in chat:

1. During the interview, the conductor wrote comparison detail (option shapes, trade-offs) to a session file via `cat >` and then asked "Given the detail above, which shape should we scaffold?" The detail existed only on disk and in the conductor's context. The user was choosing blind.
2. At Assembly, the engine spec says the `AskUserQuestion` must include the roster score table, rationale, and cost estimate, but the rendered question showed only the option list.
3. During deliberation the workflow runs in the background and the user sees nothing until synthesis returns.

PR #74 addressed presentation at exactly one touchpoint (the design-approval verdict, `design.html`). Every other touchpoint is text-only and unreliable.

## Goals

- Every decision touchpoint is self-contained in chat (compact summary) AND richly visible in a browser page.
- One live page per session that fills in as the session progresses, including position-by-position deliberation progress.
- Zero new runtime dependencies. No server. Graceful degradation identical to the F10 contract.

## Non-Goals

- Keystroke-level streaming of agent output.
- Replacing `AskUserQuestion` as the approval mechanism or markdown files as artifacts of record.
- Reworking `design.html` (F10). It stays as-is; the session page links to it.
- Interactive controls in the page (buttons, forms). It is a read-only window.

## Decisions Made (from brainstorming)

| Decision | Chosen | Rationale |
|----------|--------|-----------|
| Touchpoint coverage | All decision touchpoints plus live deliberation progress | User selected all options |
| Page model | One live `session.html` per session, opened once | No tab spam, full session history in one place |
| Chat role | Compact chat summaries mandatory, HTML carries full detail | Fixes root bug even when render or browser fails |
| Update transport | Static regeneration + `<meta http-equiv="refresh" content="10">` | Works on `file://`, no server, no ports |
| Regenerator | Deterministic scribe script invoked by agents/conductor after writes | Zero LLM cost, race-safe via idempotent full regeneration |

## Architecture

### New reference assets (`skills/council/references/`)

**`session-page.template.html`**
Self-contained, theme-aware (light and dark) page. Structure:

- Masthead: idea, session ID, mode, profile, backend, phase tracker (Interview, Assembly, Deliberation, Verdict, Planning, Verification).
- Interview section: Q&A transcript, detail asides rendered in full.
- Assembly section: roster table with scores, rationale, lens-color dots, cost estimate, loaded skills per agent.
- Deliberation section: one position card per agent (Round 1), tension-pair list, challenge exchange cards (Round 2), convergence cards (Round 3). Cards render in pending / in-progress / complete states.
- Verdict section: overview summary plus a link to `design.html` when present.
- Planning section: PRD goals, non-goals, user story list, acceptance contract summary.
- Verification section: contract status table (mirrors the verification sweep output).

Sections for phases a mode skips are hidden, driven by `session-state.json`.

**`render-session.py`** (the scribe)
python3, stdlib only. Reads whatever exists under the session dir:

- `session.md`, `session-state.json`
- `interview-transcript.md`, `interview-summary.md`, `detail-*.md`
- `deliberation/round1/*.md`, `round2/*.md`, `round3/*.md`
- `design.md`, `design.html` (presence check only), `prd.md`, `acceptance-contract.md`, `plan.md`

Regenerates `session.html` in one pass from the template copy sitting next to it in the session dir. Includes a minimal markdown-to-HTML converter (headings, paragraphs, bold, lists, tables, fenced code). Idempotent full regeneration: concurrent invocations are race-safe, last writer includes everything on disk at that moment. When `session-state.json` marks the session complete, the scribe omits the meta-refresh tag.

Invocation: `python3 render-session.py <session-dir>` (the script is copied into the session dir at setup, so agents run it with a fixed relative path).

**`session-state.json`** (written per session; the engine doc carries this example as the schema of record)

```json
{
  "phase": "deliberation",
  "complete": false,
  "idea": "...",
  "mode": "standard",
  "profile": "balanced",
  "backend": "workflow",
  "roster": [
    {"name": "Architect", "color": "#4A90D9", "score": 9, "rationale": "...", "skills": ["codebase-context"], "status": "position-written"}
  ],
  "tensionPairs": [["Architect", "Skeptic"]],
  "costEstimate": "~120-180K tokens",
  "phases": ["interview", "assembly", "deliberation", "verdict", "planning", "verification"]
}
```

Only holds what file presence cannot infer. The scribe derives card states primarily from files on disk and uses `session-state.json` for roster metadata and phase labels.

### Engine changes (`commands/_council-engine.md`)

1. **Phase 1.1 setup**: copy `render-session.py` AND `session-page.template.html` into `$SESSION_DIR` (pins both for the session, keeps `--resume` stable across upgrades), write initial `session-state.json`, run the scribe, open `session.html` once (`open` on macOS, `xdg-open` on Linux). Applies to quick, standard, deep, auto, guided, meeting, and audit modes. Brainstorm creates no files and is excluded.
2. **Touchpoint Presentation Contract** (new engine-wide rule section): every `AskUserQuestion` must be self-contained. Referencing "the detail above", a prior turn, or a file path as the sole context source is prohibited. When the conductor produces comparison detail mid-interview, it must (a) print a compact rendering in chat, (b) write the full version to `$SESSION_DIR/detail-<n>.md`, (c) rerun the scribe.
3. **Per-phase scribe hooks**: after each interview round, after assembly selection, at synthesis, after PRD scope generation, and after the verification sweep, the conductor updates `session-state.json` and reruns the scribe. Cleanup performs a final run with `complete: true`.
4. **Deliberation, workflow backend**: workflow `args` gain `scribePath`. Round prompts in `skills/council/references/workflows/council-deliberation.template.js` add one instruction: after saving your round file, run `python3 <scribePath> <sessionDir>`. Teams and sequential backends: the conductor runs the scribe between rounds.
5. **Mode table**: Output column entries note `session.html` where applicable.

### Update loop behavior

- Browser re-reads `session.html` from disk every 10 seconds via meta refresh.
- Worst-case latency from artifact-written to visible: scribe runtime plus one refresh tick, roughly 10 to 15 seconds.
- Positions appear card by card as agents finish. Agents still deliberating show pending states.

## Error Handling

Identical degradation contract to F10, extended:

- Scribe failure, missing python3, missing template, or write failure: skip silently, text flow continues.
- No GUI browser (SSH, headless): page is still written; print its path once so the user can open it elsewhere. Chat compact summaries guarantee the session is fully usable without it.
- A failed scribe run inside a deliberation agent must not fail the agent's round: the instruction wraps the call with `|| true` semantics.
- `--resume` reopens the existing `session.html` and continues updating it.

## Testing

- Fixture-based tests for the scribe under `pipeline/tests/` (following existing hook test conventions): empty session dir, mid-round-1 dir (2 of 5 positions present), complete session dir. Assert section states and that regeneration is idempotent (two runs produce identical output).
- Pre-commit governance hooks stay green. Verify how the token-budget validator treats `references/` assets; `design-verdict.template.html` (178 lines) is the precedent. If scripts/templates need an explicit exemption, add it to the validator config rather than splitting files artificially.
- Manual smoke: run `/council --quick` end to end and confirm the page opens, fills, and finalizes.

## Documentation and Distribution

- `skills/council/README.md`: document the live session page and the Touchpoint Presentation Contract.
- Engine mode table and help text updated.
- Port to the public plugin repo at `~/Development/agentic-council`: engine, reference assets, workflow template, README ("Every decision is tracked" section gains the live page), CHANGELOG entry, MkDocs pages, version bump to v1.4.0.

## Implementation Order

1. Scribe script + page template + fixtures/tests (standalone, no engine coupling).
2. Engine edits: setup, Touchpoint Presentation Contract, per-phase hooks, mode table.
3. Workflow template edit (`scribePath` arg + round-prompt instruction).
4. README + docs in this repo.
5. Port to agentic-council + v1.4.0 release notes.
