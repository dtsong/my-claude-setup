---
name: mcs-docs-of-record
description: Use when editing or auditing README.md, ARCHITECTURE.md, CONTRIBUTING.md, CHANGELOG.md, SECURITY.md, THIRD_PARTY_NOTICES.md, docs/, pipeline/specs/, or memory/HANDOVER-*.md in my-claude-setup, when two docs disagree on a number (agent/skill/command counts, token budgets, spec versions), when writing a handover or design doc, or when asked "which doc is right" or "is this stale". Not for skill-authoring mechanics (use mcs-claude-code-platform or the governance spec directly), release/novelty claims (use mcs-external-positioning), or live incident triage (use mcs-debugging-playbook).
---

# mcs-docs-of-record

## Overview

This repo has two documentation layers that drift independently: narrative docs (README, ARCHITECTURE, CONTRIBUTING) written by hand, and governance docs (`pipeline/specs/`, `pipeline/config/budgets.json`) enforced by code. Narrative docs go stale silently because nothing checks them; governance docs are truth because pre-commit hooks and CI read them at runtime. When they disagree, the enforcement code wins, never the prose.

## When to use and when NOT to

Use this skill to: locate the doc that owns a fact, resolve a conflict between two docs, fix a stale count, write a handover or design doc in house style, or run the drift audit before a docs PR.

Do NOT use this skill for:
- Skill frontmatter/budget/structure rules themselves. Those live in `pipeline/specs/SKILL-GOVERNANCE-SPEC.md`; read the spec directly or route to `mcs-claude-code-platform` for skill-loading mechanics.
- OSS release readiness, novelty claims, licensing posture. Route to `mcs-external-positioning`.
- Live symptom triage (a hook failing right now). Route to `mcs-debugging-playbook`.
- Commit/PR gate rules themselves (this skill uses them, does not define them). Route to `mcs-change-control`.

## The doc map

| File | Audience | Owns | Freshness |
|---|---|---|---|
| `README.md` | External/user-facing | Install quick-start, feature pitch, counts | Stale (counts last touched 2026-02-16) |
| `ARCHITECTURE.md` | Contributors | Engine design, phase flow, agent/skill schema, hooks, scripts | Stale in places, see drift queue |
| `CONTRIBUTING.md` | New contributors | PR workflow, local validation commands, branch protection | Current |
| `CHANGELOG.md` | Release consumers | Keep-a-Changelog `[Unreleased]` since `[0.1.0] - 2026-02-12` | Stale, no entries added despite months of shipped work |
| `SECURITY.md` | Security reporters | Report process | Current but no maintainer email/handle listed |
| `THIRD_PARTY_NOTICES.md` | Legal/compliance | Vendored-directory attribution | Stale, references 2 deleted directories |
| `docs/adoption.md`, `release-checklist.md`, `upstream-sources.md`, `onboarding-feedback.md`, `open-source-launch.md`, `model-routing.md` | Contributors/operators | Operational checklists | `model-routing.md` is new (2026-07-02, issue #60/#63) |
| `docs/superpowers/{specs,plans}/*` | Contributors | Dated design docs, e.g. `2026-06-22-openrouter-integration-design.md` | Source of truth for that feature's design intent, frozen at date |
| `pipeline/specs/*.md` (4 files) | Pipeline tooling + contributors | Enforcement rules | Self-declares "single source of truth" (`SKILL-GOVERNANCE-SPEC.md:9`) |
| `memory/HANDOVER-*.md` | Next session | Session continuity, one file per session | Current, sparse (1 file on disk) |
| Repo `CLAUDE.md` | Claude sessions | Communication style, engineering directives, governance summary | See gotcha below: on this machine it IS `~/.claude/CLAUDE.md` |

## Authority ranking when docs conflict

Highest to lowest. Assert one, do not average:

1. **Enforcement code** (`pipeline/hooks/*.py`, `.pre-commit-config.yaml`, `settings.json` hook wiring, `hooks.json`), what actually runs.
2. **`pipeline/specs/*.md`**, the versioned, self-declared source of truth for governance numbers.
3. **`ARCHITECTURE.md`**, hand-maintained contributor reference, drifts but is second-line for design intent.
4. **`README.md`**, user-facing pitch, drifts fastest, lowest authority for factual counts.
5. **`CLAUDE.md` numbers**, lowest priority when a number also lives in a spec; treat as summary, not source.

Worked example (verified 2026-07-02): repo `CLAUDE.md:57` says "Maximum simultaneous context load: ≤5,000 tokens" under a heading titled "Hard Limits". `pipeline/config/budgets.json:11` and `pipeline/specs/SKILL-GOVERNANCE-SPEC.md:110,126` both say **5,500**, and the spec's own changelog (lines 14-16) demoted per-file budgets from hard to warn-tier, leaving the suite ceiling as the only hard limit. `pipeline/hooks/check_token_budget.py` calls `sys.exit(0)` unconditionally: it never blocks a commit. Conclusion: 5,500 is enforced; CLAUDE.md's "5,000" and "Hard Limits" label are both wrong. Only the owner's intent (was 5,000 ever meant to be real) is open, not the fact. Second worked example (README vs department README on agent count) and the reasoning template to reuse for a new conflict: `references/authority-worked-examples.md`.

## Current drift list (as of 2026-07-02)

Top 3 by user-facing impact; full 12-row table with a verification command per row is `references/drift-fix-queue.md`:

| # | Claim | Reality |
|---|---|---|
| 1 | README "21 agents, 57 skills" | 38 agent files (23 council + 15 ece), 22 skill packs, 68 council SKILL.md |
| 2 | README "16 slash commands", engine "~1200 lines" | 29 files in `commands/`, engine is 1753 lines |
| 3 | ARCHITECTURE "Active Hooks" table lists only PreCompact | `hooks/` has 6 scripts; 2 wired via `settings.json`, 2 (`careful-mode.sh`, `freeze-mode.sh`) invoked by `/careful` `/freeze` but never wired to a lifecycle event so they protect nothing, 1 (`skill-telemetry.sh`) documented in spec but registered nowhere |

Also queued: THIRD_PARTY_NOTICES referencing deleted `skills/terraform-skill/` and `skills/tdd/`; ARCHITECTURE self-contradiction on agent `model` frontmatter; commands/council.md skill tree stale `.claude/skills/council/` path header plus 2 missing entries; spec Appendix A "v1.4" banner inside the v1.5 doc; `budgets.json` `spec_version: "1.3"` against v1.5; accountant DEPARTMENT.md's 6 dead skill links (survive the HARD `check_references` hook because that hook only validates `references/`, `shared-references/`, `templates/`, `scripts/`, `assets/`, `examples/` paths, `pipeline/hooks/check_references.py:21`, by design not evasion). Full detail and commands: `references/drift-fix-queue.md`.

## House style

- No em dashes, anywhere, ever (owner's absolute rule, codified in repo CLAUDE.md and commit `48af508`). README/ARCHITECTURE predate the rule and still contain them; fixing them is in scope for any docs touch you make nearby.
- Answer-first structure: lead with the fact or decision, push reasoning to an appendix.
- Tables for enumerable facts (counts, file lists, comparisons); prose for narrative only.
- Skill descriptions are third person; procedures inside skill bodies are imperative.
- Date-stamp every volatile fact ("as of 2026-07-02"), especially counts, versions, session-derived claims.
- Commit convention (enforced HARD at `commit-msg` stage by `check_commit_msg.py`): `docs(scope): summary` for narrative docs, `skill-docs(name): summary` for a skill's own files. Valid types: `skill, skill-fix, skill-ref, skill-eval, skill-docs, chore, feat, fix, docs, style, refactor, test, ci, perf, build, revert`.

## Templates and deeper references

| Reference | Load when |
|---|---|
| `references/drift-fix-queue.md` | Fixing or re-auditing any doc-drift item; full table plus verification command per row |
| `references/authority-worked-examples.md` | Adjudicating a conflict not already covered above |
| `references/handover-template.md` | Writing or reviewing a handover doc |
| `references/design-doc-template.md` | Writing or reviewing a council synthesis design doc |
| `references/drift-audit-procedure.md` | Running a full drift sweep before a docs PR; points to `mcs-diagnostics-and-tooling`'s `scripts/doc-drift-check.sh` as the scripted instrument |

## Gotchas

- **Two "CLAUDE.md" files are one file, on this machine.** `~/.claude/CLAUDE.md` symlinks to this repo's root `CLAUDE.md` (`readlink ~/.claude/CLAUDE.md`). Editing one edits both instantly. This is machine-specific (depends on `install.sh --with-claude-md`); do not assume it holds on a fresh clone.
- **Root README and `skills/council/README.md` disagree on the agent roster** (21 vs 22) and neither is automatically synced to the other. Verify counts directly rather than trusting either by default.
- **A commit titled "align documentation" may not have touched root README.** `729adcd`'s message says "documentation" but `git show --stat` shows it only edited `skills/council/README.md`, `commands/council.md`, `registry.json`. Check `--stat` before citing a sync commit as evidence.
- **`check_references.py`'s HARD gate does not cover every markdown link**, only `references/`, `shared-references/`, `templates/`, `scripts/`, `assets/`, `examples/` paths. A DEPARTMENT.md can link to nonexistent files indefinitely without failing CI.
- **`check_token_budget.py` always exits 0.** A clean pre-commit run is not proof a skill is under budget; it is warn-only by design since spec v1.1.
- **`.pre-commit-config.yaml` only matches `files: ^skills/.*\.md$`.** Files under `.claude/skills/` (this skill included) get none of the repo's automated frontmatter/reference/isolation checks; review by hand against the spec.
- **CHANGELOG staleness is not yours to silently fix.** Backfilling `[Unreleased]` entries asserts release claims that belong to `mcs-external-positioning`; flag it, don't unilaterally write it.

## Provenance and maintenance

Last verified 2026-07-02, against a repo with 5 unpushed local commits ahead of the last known remote sync (`105427a` newest at verification time). Counts drift fast; re-run before citing a number.

| Fact | Re-verification command |
|---|---|
| Agent file count / breakdown | `find agents -maxdepth 1 -name '*.md' \| wc -l` (split `council-*.md` vs `ece-*.md`) |
| Top-level skill packs / council SKILL.md count | `ls -d skills/*/ \| wc -l`; `git ls-files 'skills/council/**/SKILL.md' \| wc -l` |
| Command count / engine line count | `find commands -maxdepth 1 -name '*.md' \| wc -l`; `wc -l commands/_council-engine.md` |
| Hooks table gap | `ls hooks/`; `grep -n '"command"' settings.json`; `cat hooks.json` |
| terraform-skill / tdd vendoring | `ls skills/terraform-skill skills/tdd` (both should fail) |
| CLAUDE.md vs spec budget ceiling | `grep -n '5,000\|5000' CLAUDE.md`; `grep max_simultaneous_tokens pipeline/config/budgets.json` |
| Spec version banner / budgets.json spec_version | `sed -n '1p;1193p' pipeline/specs/SKILL-GOVERNANCE-SPEC.md`; `head -3 pipeline/config/budgets.json` |
| CHANGELOG staleness | `cat CHANGELOG.md`; `git log -1 --format=%ai` |
| CLAUDE.md symlink (this machine only) | `readlink ~/.claude/CLAUDE.md` |
