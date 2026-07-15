---
name: mcs-external-positioning
description: Use when deciding what this project (my-claude-setup) may claim publicly (README pitch, launch post, "why is this different" answers, OSS release announcements), when someone asks for a v1.0/launch readiness verdict against GitHub issue 3 (the v1.0 tracking issue), when evaluating third-party attribution or license compliance before a release, or when history/privacy exposure (real personal data reachable in pushed git refs) needs a decision framed for the owner. Not for fixing drifted docs (mcs-docs-of-record) or for open-research novelty claims (mcs-research-frontier).
---

# mcs-external-positioning

## Overview

This repo is pre-1.0 (issue #3, open, 0 of 22 boxes checked as of 2026-07-05, re-verify with `gh issue view 3 --json body -q .body | grep -c '\- \[ \]'`) and is actively mutating under a live ship run. Public claims must be evidence-backed today, not aspirational, and must not overstate what a fresh clone (no owner-only private repo, no owner's machine) actually gets. Core principle: rank claims by demonstrated evidence, not by design intent; anything without committed proof is "candidate," not "shipped."

## When to use, and when NOT to

Use for: drafting/reviewing public-facing claims (README pitch, launch checklist sign-off, "what makes this different"), v1.0 readiness verdicts, license/attribution audits before release, and structuring (never resolving) the privacy/history-exposure decision.

Do NOT use for:
- Fixing README/ARCHITECTURE drift itself (the numbers, the file paths): that's `mcs-docs-of-record`.
- Judging whether a technique is a genuine research contribution: that's `mcs-research-frontier`.
- Executing the actual git-history scrub, force-push, or BFG pass: no skill does this; it is an owner-only action, never automated.

## Positioning inventory (ranked by evidence strength, verified 2026-07-02)

1. **Acceptance-contract-gated autonomous execution.** `hooks/acceptance-gate.sh`, wired `PreToolUse` on `TaskUpdate` (lines 69/75 as of 2026-07-05 via `grep -n '"PreToolUse"\|acceptance-gate' settings.json`; approximate only, re-grep before citing, since settings.json is under active rewrite), denies (exit 2) completion while unverified criteria remain; selects the contract by mtime, skips stale ones. Took 3 fail-open bugs to reach this state (299a264 → 6bc7c1a → 4bb8bf2 → 605112d). Live proof: today's session verified AC-001..AC-006 with real pytest runs before merging PR #67/#68. Gap: no observed case of it *catching* a real regression, only "fail-open bug" or "criteria passed". Claim "gates completion," not "catches bugs."
2. **Shared-engine multi-theme council on native Workflow substrate.** `commands/_council-engine.md` (1,753 lines) is parameterized by 14 `$THEME_ID`-style variables; two themes instantiate it: `commands/council.md` (public) and `commands/ece.md` (private-repo symlink, undocumented in README/ARCHITECTURE). Backend fallback `workflow → teams → sequential` is real and recorded per session. Gap: the substrate is Anthropic's, not this repo's differentiator (claim the degradation design, not the tools); say "proven by two themes, one public," not "multiple public themes."
3. **Enforced skill-governance pipeline with 3-tier evals.** Pre-commit Tier 1 (static) is real and hard-blocking (`skill-frontmatter`, `skill-references`, `skill-isolation`, `skill-context-load`, `skill-commit-msg`; `skill-token-budget`/`skill-prose-check` warn-only, per `.pre-commit-config.yaml`). Spec defines Tier 2 (E2E via `claude -p`) and Tier 3 (LLM-as-judge) at `pipeline/specs/SKILL-GOVERNANCE-SPEC.md` §7.6, with working scripts (`run-evals.sh`, `judge-skill-quality.sh`). Gap: Tiers 2-3 are **not wired into CI or pre-commit**, zero committed run output. Claim "Tier 1 static enforcement is continuous; Tiers 2-3 are unexercised tooling," not "3-tier enforcement."

**Commodity, don't lead with these:** the skills/commands/agents collection itself (many public repos do this); the symlink-based installer; project scaffolding commands (`/new-python`, `/new-terraform`). Competent execution, not novelty.

**Cross-cutting gap for all three ranked claims:** zero committed cost or quality telemetry for council sessions. `skills/council/registry.json` (v2.1) tracks per-skill **usage counts** only (`uses`, `last_used`, `sessions`), no token cost, latency, or quality score. (`grep -n cost skills/council/registry.json` matches only a skill named `cost-analysis`, not a telemetry field.) Any "council sessions are cheap/fast/high-quality" claim is unmeasured: label it "candidate, no telemetry."

## v1.0 readiness ledger

Full issue-#3 checklist with live per-item verification: `references/v1-readiness-ledger.md`. Headline blockers as of 2026-07-02:

- **Docs accuracy**: README's agent/skill/command counts are drifted from reality. Fix routes to `mcs-docs-of-record`; this skill only flags it as a v1.0 gate.
- **Third-party notices**: `THIRD_PARTY_NOTICES.md` lists 2 dead directories (`skills/terraform-skill/`, `skills/tdd/`) and misses 2 real adaptations (`agentic-council v1.2.0`, steipete-derived skill-audit tooling). See Licensing below.
- **CI/security gates**: `validate.yml` (ubuntu+macos) + `secret-scan` (gitleaks) are required status checks, but `enforce_admins: false` and `required_approving_review_count: 0`; CODEOWNERS exists but isn't enforced. Vulnerability alerts and Dependabot security updates are enabled; Dependabot version updates cover only GitHub Actions, not `mcp/openrouter`'s Python deps.
- **Onboarding validation**: issue #3 requires 3+ onboarding feedback reports via the issue template; zero exist.
- **Private-repo coupling (unstated blocker)**: 7 symlinks point into `$HOME/Development/my-claude-setup-private`. `install.sh`'s existence guards silently skip broken symlinks, so a fresh clone's install is functionally fine; gap is cosmetic. Tracked by open issue #65 (US-007, queued).
- **Machine-local paths in settings.json (unstated blocker)**: 2 hardcoded `/Users/danielsong/...` paths remain (OpenRouter MCP command, `research-toolkit-local` marketplace), opt-in only but non-functional for anyone else. No issue owns this gap yet.
- **README prerequisites incomplete**: `python3` is a hard `install.sh` dependency, absent from README's Prerequisites list.
- **Newly resolved, don't carry forward**: prior "fresh clone gets broken telemetry hooks" is fixed as of PR #67 (2026-07-02): `hooks/telemetry-dispatch.sh` is fail-soft, wired to all 5 events, zero private-repo strings remain in `settings.json`.

## Privacy and history exposure: decision framing only, no action

Real personal content is exposed on two different surfaces (corrected 2026-07-06): SOC/security and ECE content IS reachable from pushed remote refs (6 branches); the named individual's resume was never on `main` and survives only as one orphaned commit object on a fork, a much smaller exposure. Full options ledger, exact refs, and consequences: `references/privacy-history-exposure.md`. This skill states options; it never recommends or executes one. Deleting remote refs or rewriting pushed history (BFG/force-push) is irreversible-in-practice and owner-only. Do not perform it, do not suggest a default, and do not treat commit 69cdb56's "scrubbing history is a separate decision" note as consent.

## Licensing and attribution

- Root license: MIT, copyright 2025 Daniel Song (`LICENSE:1-3`).
- `THIRD_PARTY_NOTICES.md` has 3 entries: `skills/terraform-skill/` (stale, directory deleted), `skills/vercel-react-best-practices/` (accurate stub), `skills/tdd/` (stale, directory deleted; only `commands/tdd.md` redirect stub remains).
- Missing attribution: the `agentic-council v1.2.0` orchestration adoption (commit `9cee199`) and the steipete/agent-scripts `skill-cleaner`-derived audit tooling. Both real, neither in `THIRD_PARTY_NOTICES.md` or `docs/upstream-sources.md` (the latter is documented only in prose inside `pipeline/scripts/README.md`'s "Origin" section, uncross-referenced).
- A maintenance procedure exists (`docs/upstream-sources.md`) but nothing enforces it: no hook checks notice entries against actual directory existence, which is why it drifted silently twice.

## Reproducibility standard for any public claim

A public claim needs a fresh-clone quickstart that actually works, or it doesn't ship.

- `./install.sh --dry-run --preset skills` runs clean; private-repo symlinks are silently skipped by design (`[[ -d ]]` on a broken symlink is false), verified by reading `install.sh:83-149`, not by an executed absent-private-repo CI run. Label this "verified by code inspection," not "verified by CI."
- No CI job actually simulates the absent-private-repo state; the ubuntu/macos matrix runs inside this same checkout.
- Benchmark/token numbers: never present an estimate as a measurement. The only committed telemetry today is `skills/council/registry.json` usage counts (18 total uses as of 2026-07-02). No cost, latency, or token data is committed anywhere. Any number not traceable to a `git show`-able file is an estimate and must be labeled one.

## Gotchas

- WRONG: "First system with acceptance-contract-gated autonomous execution." RIGHT: state what's verified and stop; novelty claims belong to `mcs-research-frontier`.
- WRONG: assuming `THIRD_PARTY_NOTICES.md` is complete because it's well-formatted. Check both directions: every listed path exists, every real adaptation has an entry.
- WRONG: treating `registry.json`'s usage counts as quality or cost evidence: no cost/quality/outcome field exists.
- WRONG: assuming PR review is required for main. `enforce_admins: false` means the owner can and does push directly.
- WRONG: reading "install.sh is stable" from CI alone: CI smoke-tests `skills`/`core` only, never `full`.
- WRONG: quoting README's agent/skill counts in a launch post: pull live counts at write time (`mcs-docs-of-record` owns the fix).
- SILENT FAILURE: `settings.json`'s 2 hardcoded personal paths only surface as a broken MCP entry for a `--with-settings` opt-in, no install-time error.
- Everything here drifts fast under the live ship run. Re-run Provenance commands before repeating any number publicly.

## Provenance and maintenance

Last verified: 2026-07-05, against a live, actively-mutating repo (PRs #67-#70 merged since original authoring, US-002 model tier alias / US-003 permissions rewrite / US-004 OpenRouter model ID refresh / settings schema guard work). Re-verify every fact below before reusing it.

| Fact | Re-verification command |
|---|---|
| Issue #3 checkbox count | `gh issue view 3 --json body -q .body \| grep -c '\- \[ \]'` |
| PreToolUse/acceptance-gate.sh line position in settings.json (approximate, expect drift) | `grep -n '"PreToolUse"' settings.json; grep -n acceptance-gate settings.json` |
| THIRD_PARTY_NOTICES stale entries | `ls skills/terraform-skill skills/tdd 2>&1` (expect "No such file") |
| Missing agentic-council/steipete attribution | `grep -in "agentic-council\|steipete" THIRD_PARTY_NOTICES.md docs/upstream-sources.md` (expect no match) |
| Branch protection review/admin settings | `gh api repos/dtsong/my-claude-setup/branches/main/protection -q '{reviews:.required_pull_request_reviews.required_approving_review_count, admins:.enforce_admins.enabled}'` |
| Vulnerability alerts / Dependabot security updates | `gh api repos/dtsong/my-claude-setup -q .security_and_analysis` |
| Onboarding feedback report count | `gh issue list --search "onboarding" --state all --json number,title` |
| Private-repo symlink list | `find skills commands -maxdepth 1 -type l -exec sh -c 'readlink "$1" \| grep -q private && echo "$1"' _ {} \;` |
| Machine-local hardcoded paths in settings.json | `grep -n '/Users/danielsong' settings.json` |
| registry.json has no cost/quality field | `python3 -c "import json;print(list(json.load(open('skills/council/registry.json')).keys()))"` |
| Pushed refs holding personal content | `git branch -r \| grep -E "worktree-agent\|renovate"` |
| Governance pre-commit hard vs warn tiers | `grep -B1 "(hard)\|(warn)" .pre-commit-config.yaml` |
| Eval Tier 2/3 wiring into CI | `grep -rn "run-evals\|judge-skill-quality" .github/workflows/ .pre-commit-config.yaml` (expect no match) |
