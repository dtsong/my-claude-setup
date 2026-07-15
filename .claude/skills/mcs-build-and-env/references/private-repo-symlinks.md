# Optional private sibling repo: what breaks without it

"This machine only" throughout: paths under `/Users/danielsong/...` describe
this deployment, not a portable contract. A clone on another machine has none
of these symlinks unless it recreates the same sibling checkouts at the same
paths.

## The 8 content symlinks (verified live 2026-07-02)

All resolve on this machine today. Each degrades independently: if the
sibling repo is absent, the symlink is simply a dangling/missing path and the
corresponding skill or command does not exist. Nothing else in the harness
fails because of it (confirmed: none of these are referenced from
`commands/_council-engine.md`'s core phases).

| Path in this repo | Target | Sibling repo |
|---|---|---|
| `skills/ece` | `~/Development/my-claude-setup-private/skills/ece` | my-claude-setup-private |
| `skills/research-consulting-skills` | `~/Development/my-claude-setup-private/skills/research-consulting-skills` | my-claude-setup-private |
| `skills/resume-tailor` | `~/Development/my-claude-setup-private/skills/resume-tailor` | my-claude-setup-private |
| `skills/soc-security` | `~/Development/my-claude-setup-private/skills/soc-security` | my-claude-setup-private |
| `commands/analyze-workflow.md` | `~/Development/my-claude-setup-private/commands/analyze-workflow.md` | my-claude-setup-private |
| `commands/ece.md` | `~/Development/my-claude-setup-private/commands/ece.md` | my-claude-setup-private |
| `commands/tailor.md` | `~/Development/my-claude-setup-private/commands/tailor.md` | my-claude-setup-private |
| `skills/heavy-file-ingestion` | `~/Development/llm/skills/skill-governance/skills/heavy-file-ingestion` | a second, separate sibling repo (`llm/skills/skill-governance`), not `my-claude-setup-private` |

Note: `commands/heavy-file-ingestion.md` is a real tracked file (not a
symlink), a 7-line stub that invokes the `heavy-file-ingestion` skill by
name. It is unaffected by the sibling repo's presence; only
`skills/heavy-file-ingestion` itself depends on `llm/skills/skill-governance`.

`.gitignore` also lists 4 more private-repo symlink paths under
`skills/council/{chronicler,operator,oracle}/...` as expected artifacts.
**None of the four exist on this machine as of 2026-07-02**: they are either
not-yet-materialized or stale entries. Don't treat the `.gitignore` list as
proof a symlink is currently live; check with `[ -L <path> ]`.

## The 5 telemetry hook events (before/after issue #59)

`settings.json` wires the same command to five hook events:
`SessionStart`, `PostToolUse`, `PostToolUseFailure`, `Stop`, `SessionEnd`
(all matcher `""`, i.e. every tool).

**Before issue #59 (older commits, e.g. as described in pre-2026-07-02
snapshots):** each event invoked
`python3 $HOME/Development/my-claude-setup-private/hooks/session_telemetry.py`
directly. On a machine without that private repo, every one of those 5 events
spawned a `python3` process that immediately failed with
`FileNotFoundError`, silently, since Claude Code hook failures don't
normally surface to the transcript unless something inspects stderr.

**Current state (issue #59 / US-001, landed, verified live in `settings.json`
as of 2026-07-02):** all 5 events instead run a one-line inline wrapper that
gates on file existence before invoking `hooks/telemetry-dispatch.sh`:
```bash
bash -c 'f="$HOME/Development/my-claude-setup/hooks/telemetry-dispatch.sh"; [ -f "$f" ] || exit 0; exec bash "$f"'
```
`telemetry-dispatch.sh` (`hooks/telemetry-dispatch.sh`, tracked, 33 lines)
is a **fail-soft dispatcher**, contract documented in its own header comment:
- Never exits 2 (a blocking code in the hooks protocol; on `Stop` it would
  prevent Claude from stopping).
- Missing private repo (default case on a fresh clone) → fully silent exit 0.
- `CLAUDE_TELEMETRY_HOOK` env var can override the target path (for testing
  or for a differently-located private repo); if set but unreadable, warns on
  stderr and still exits 0.
- python3 missing, or the dispatched script exits non-zero → warns on stderr,
  exits 1 (non-blocking, but visible), never propagates the child's raw
  status silently.

Net effect: on a fresh machine with no `my-claude-setup-private`, telemetry is
now a no-op with zero spawned failing processes (vs. 5 silently-failing
`python3` invocations per tool call before #59). Re-verify:
`grep -n "telemetry-dispatch" settings.json` and
`cat hooks/telemetry-dispatch.sh`.

## Sanity check for a new machine

```bash
for p in skills/ece skills/heavy-file-ingestion skills/research-consulting-skills \
         skills/resume-tailor skills/soc-security commands/analyze-workflow.md \
         commands/ece.md commands/tailor.md; do
  if [ -L "$p" ]; then echo "SYMLINK $p -> $(readlink "$p")"; else echo "ABSENT $p (expected on a fresh clone)"; fi
done
```
`ABSENT` for all 8 is the correct, healthy state for anyone who is not this
machine's owner and has not cloned the private sibling repos.
