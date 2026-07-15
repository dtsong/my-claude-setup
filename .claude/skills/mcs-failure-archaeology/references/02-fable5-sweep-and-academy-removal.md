# The June 10, 2026 Fable-5 modernization sweep, and the earlier academy removal

## Trigger

`8c0cf14` (2026-06-10, 02:19 local) switched the session default model to Fable 5 ("feat(settings): switch default model to Fable 5"). Over the next 66 minutes, 5 more commits removed things that existed to compensate for weaker/older model behavior, on the theory that Fable 5 (and modern Claude Code's own context handling) no longer needed them. A 6th and 7th commit followed same night for governance and council-engine upgrades. Status: **settled, do not re-add any of the removed items without a new, current reason**: the fact that Fable 5 shipped is not itself a reason to revert this sweep.

## The 9-commit chain

| Commit | Time | What it removed/changed | Why (from commit message) |
|---|---|---|---|
| `8c0cf14` | 02:19 | Default model → Fable 5 | Trigger for the rest of the sweep. |
| `9cba263` | 02:20 | CLAUDE.md: -36/+4 lines. Removed step-0 dead-code rule, 5-file phase cap, mandatory sub-agent swarming, context-decay re-reads, file-read budget, tool-result truncation warnings, per-edit verification re-reads. | These were written to babysit pre-Fable models that lost track of state; current Claude Code tracks file state itself. **Kept**: senior-dev override, forced type-check/lint, slimmed rename rule: these are still live in `~/.claude/CLAUDE.md` today. |
| `5ef9f2c` | 02:22 | settings.json: -14 lines. Removed `context_decay_alert.py` and `cost_sink_alert.py` hooks, and a no-op `ENABLE_TOOL_SEARCH` env var. | Both hooks compensated for context-decay behavior current Claude Code doesn't have; auto-compaction now summarizes and continues across context resets. **Explicitly kept**: `CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS` ("still required as of June 2026" per commit body). |
| `f50caa2` | 02:25 | Removed `model: claude-opus-4-6` frontmatter pins from all 20 council agents, and `roadmap-executor`'s `model: claude-sonnet-4-20250514` pin. Agents now inherit the session model. Bumped `pipeline/config/model-routing.yaml` opus tier to `claude-opus-4-8`. Documented the no-pin convention in ARCHITECTURE.md. Also removed an accidental self-referencing `agents/agents` symlink. | Versioned model-ID pins go stale; tier aliases inherited from the session are the intended pattern (this is the same principle later codified in `docs/model-routing.md`, see `05-registry-and-settings-churn.md`). |
| `16833bd` | 02:26 | Deleted 5 whole skills (-312 lines): `code-search`, `git-status`, `evaluate-diagram`, `generate-diagram`, `generate-plot`. | `code-search`/`git-status` only documented what native Grep/Glob/git tooling already does, and their descriptions cost context every session just by existing. The 3 diagram/plot skills were exact duplicates of the `research-toolkit` plugin's skills, so they double-loaded the same capability every session. |
| `415dec6` | 02:27 | Deprecated `/brainstorm` → `/council --brainstorm`, `/tdd` → `superpowers:test-driven-development`, `/review-fix` → built-in `/code-review --fix`. Left thin redirect stubs (net -275 lines). | Each was a duplicate or thin wrapper superseded by a better home. |
| `69cdb56` | 02:29 | Diff-verified (`git show --stat 69cdb56`): adds governance "Scope Constraints" sections to `dbt-skill` and `web-security-hardening` only. The commit *message* additionally claims it moved `resume-tailor` skill and `/tailor` command to `my-claude-setup-private`, symlinked back (same pattern as pre-existing `soc-security`/`ece` symlinks), but that move is not present in this commit's diff, it is a message-only assertion about prior state. | Governance spec 3.3 requires explicit scope constraints. Commit body states resume-tailor "contain[s] a real person's resume data and do not belong in a public repo" and notes: "the moved files remain in git history; scrubbing history is a separate decision." Corrected 2026-07-05: that content was never on `main` in the first place (see `06-privacy-and-issues.md`), so "scrubbing" applies only to the one now-deleted branch/fork object, not to `main`'s history. |
| `3c698c5` | 02:50 | Added `.pre-commit-config.yaml` wiring gitleaks + 7 `pipeline/hooks/` validators (frontmatter, references, isolation, token-budget as warn-only, etc.). | Commit message: this config was something "CLAUDE.md and the governance spec promised but never existed: every prior commit silently skipped enforcement." |
| `9cee199` | 03:25 | Adopted upstream `agentic-council` v1.2.0 into the vendored engine: cost profiles (`lean`/`balanced`/`max`), backend fallback chain `workflow -> teams -> sequential`, agent-teams flag now optional. Retired the local Phase 3 workflow pilot `.claude/workflows/council-deliberate.js`, superseded by upstream templates under `skills/council/references/workflows/`. Local divergences kept: 22-agent roster, nested DEPARTMENT.md layout, tracked registry.json. | Upstream engine caught up to and passed the local fork's capability; keep local customizations, adopt upstream mechanics. |

## Earlier, unrelated removal: the academy theme

`12c34df` (2026-03-01) deleted the entire "academy" theme: 17 agents, a command, and several skills, **-2,779 lines** net. Verified via `git show --stat 12c34df`: the diff includes deletions of `skills/academy/house-tensions.md` (94 lines), `skills/academy/promotion-system.md` (123 lines), `skills/academy/support-system.md` (108 lines), among 27 changed files totaling 38 insertions / 2,779 deletions. Status: **settled, do not resurrect**: no open issue or design doc references reviving it.

## What this means for you

If you're about to propose any of the following, first read the specific commit message above; the removal reason is very likely still valid:
- Adding a `model:` frontmatter pin to a council agent or command.
- Adding a step-0/file-budget/mandatory-swarm-style babysitting directive to CLAUDE.md.
- Re-adding `code-search`, `git-status`, or a diagram/plot skill outside the `research-toolkit` plugin.
- Reviving anything under an `academy/` path.

## Evidence commands

```bash
git show --stat 8c0cf14 9cba263 5ef9f2c f50caa2 16833bd 415dec6 69cdb56 3c698c5 9cee199
git show --stat 12c34df
```
