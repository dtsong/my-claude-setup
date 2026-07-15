# registry.json broken-instrument era, and settings.json's model flip-flops

## Part A: registry.json, 0/67 committed uses until 2026-07-02

`skills/council/registry.json` tracks per-skill usage counters. It has a write path (something updates it as skills are used) but for over 2 months **nothing committed those writes**.

- `git log -- skills/council/registry.json` shows the last commit touching it before today was `729adcd` (2026-04-24, "docs(council): align documentation with current 22-agent state"), before that `9e1111b` (PR #48, 2026-03-26).
- `git show 729adcd:skills/council/registry.json | ... last_updated` = `2026-04-24`. Every counter was 0.
- The file *did* get modified in working trees during live sessions (e.g. a session in this repo, and a cross-workspace session `klearpath-gtm-acceleration`: see the ghost-session note below): those writes just never got `git add`ed/committed by anything.
- Fixed 2026-07-02: `dc44611` ("chore(council): ship-state queue and skill-usage bookkeeping for config-optimization session") is the commit that finally lands non-zero counts. `git show HEAD:skills/council/registry.json` now shows `last_updated: 2026-07-02` with 18 committed uses (verified 2026-07-02, will grow from here).

**Consequence for anyone reading this file historically**: any claim about "which skills get used" sourced from `registry.json` for any date before 2026-07-02 is not evidence: it reflects only whichever session happened to be open and committed at that exact moment, not real usage. Treat pre-2026-07-02 registry snapshots as noise, full stop.

### The "ghost session" cross-workspace write

`~/.claude/skills` is a symlink into this repo (this-machine-only fact, not load-bearing for anyone without the same symlink setup). Consequence: **every Claude Code workspace on this machine that uses skills shares one `registry.json`**: including workspaces completely unrelated to `my-claude-setup`, like a `klearpath-gtm-acceleration` council session running against a different project directory. Its skill-usage counters land in *this* repo's `registry.json` even though the session itself has nothing to do with this repo. If you see a registry entry for a skill this repo doesn't obviously use, that's why: check `~/.claude/council/global-registry.json`'s session list for the workspace path, not this repo's own session history.

## Part B: settings.json tracking flip-flop

| Commit | Date | Change |
|---|---|---|
| `b9e2ca6` | earlier | Gitignored settings.json ("machine-specific"). |
| `abf3489` | later | Re-tracked it ("no secrets, portable config"). |
| `452acc5` | later | Added deny-reads of sensitive values. |
| `009dbc9`, `7cc6383` | later | Further tweaks. |

Net effect: settings.json is tracked in git today, and `~/.claude/settings.json` is a **symlink into this repo** on this machine (this-machine-only fact). Every commit to settings.json on `main` is a live production config deploy the moment the Claude Code app next reads it. Rollback is `git checkout settings.json` (or `git revert` the offending commit): there is no separate deploy step.

## Part C: model flip-flops, and how they got settled

| Commit | Date | `model` value | Rationale in commit body |
|---|---|---|---|
| `8c0cf14` | 2026-06-10 | → `"fable"` (bare alias, part of the wider sweep, see `02-fable5-sweep-and-academy-removal.md`) | "switch default model to Fable 5" |
| `78fbf46` | 2026-06-22 | → `"opus"` | "default model opus; silence workflow usage warning": **no rationale given for the model change itself**, only the workflow-warning half is explained. |
| `0954f52` | 2026-07-02 | → `"claude-fable-5[1m]"` (pinned ID, not an alias) + `"tui": "fullscreen"` + reordered `mcpServers` block | Commit message: "pre-session state (fable pin, fullscreen tui, mcpServers relocation) ... User's pre-existing uncommitted change, committed as-is for branch hygiene. Issue #60 reconciles the model pin to a tier alias per the council design." This commit **knowingly commits a wrong value** to unblock other work, with an explicit forward pointer to the fix. |
| `a1a8a72` (PR #68) | 2026-07-02 | → `"opus"` (tier alias, `[1m]` suffix removed) | "session default model to tier alias, 1M stance made deliberate. settings.json model reverts from the pinned claude-fable-5[1m] to the opus tier alias per the repo's alias-only governance. The [1m] suffix conflicted with CLAUDE_CODE_DISABLE_1M_CONTEXT=1; the env flag is now the single stance." Implements/closes #60. |

**Status: settled as of PR #68 (2026-07-02).** The `[1m]`-suffix-vs-`CLAUDE_CODE_DISABLE_1M_CONTEXT=1` self-contradiction is resolved: the env flag is the one standing stance (1M disabled), and `settings.json.model` holds a tier alias only. This is now documented at `docs/model-routing.md` (new file, created as part of #60/PR #68), which states the rule explicitly: "Pinned `claude-*` IDs are forbidden: they go stale and bypass profile routing" and gives the profile table (max-plan → `opus` default with `fable` escalation; api-billed → `sonnet` default). **Do not re-pin a versioned model ID or re-add a `[1m]` suffix to `settings.json.model` without updating `docs/model-routing.md` in the same change**: that file is now the intended single source of truth, per the repo's own design doc for this session.

## Evidence commands

```bash
git log --oneline -- skills/council/registry.json
git show HEAD:skills/council/registry.json | python3 -c "import json,sys; print(json.load(sys.stdin)['last_updated'])"
git log --oneline -- settings.json | grep -E "b9e2ca6|abf3489|8c0cf14|78fbf46|0954f52"
git show origin/main:settings.json | grep -n '"model"'
git show origin/main:docs/model-routing.md
gh issue view 60
```
