# v1.0 readiness ledger

Source of truth: GitHub issue #3, "v1.0.0 release criteria," state OPEN, 0 of 22 checkboxes checked as of 2026-07-05 (re-verify: `gh issue view 3 --json body -q .body | grep -c '\- \[ \]'`). Re-fetch: `gh issue view 3`. Every row below was independently verified against the live repo/GitHub state on 2026-07-02 and the count re-confirmed 2026-07-05; re-run the command in the last column before citing any row publicly.

## Installer + Adoption

| Criterion | Status 2026-07-02 | Verify |
|---|---|---|
| install.sh behavior stable and documented | Partial. Flags in README/`docs/adoption.md` match the parser (`--preset`, `--conflict-policy`, `--dry-run`, `--skills`, `--list-skills`, `--with-settings`, `--with-hooks-json`, `--with-hooks-scripts`, `--with-claude-md`, `--uninstall`). `--uninstall` only works as the first argument; `./install.sh --preset full --uninstall` fails. | `./install.sh --help` |
| Default remains skills-only; config opt-in explicit | True. `WITH_SETTINGS`/`WITH_HOOKS_JSON`/`WITH_CLAUDE_MD` all default 0. | `grep -n "WITH_SETTINGS=0" install.sh` |
| `--uninstall` removes only managed symlinks | True by design (manifest-based, `~/.claude/.managed/my-claude-setup.json`), but the ordering trap above means misuse can look like failure. | Read `install.sh` uninstall function |
| `--dry-run` output matches real actions | Not independently verified this cycle (no dry-run-vs-real diff test exists in CI or locally). | Manual: run `--dry-run`, then real install, diff link set |
| Onboarding validated via >=3 feedback reports | False. Zero reports found. | `gh issue list --search "onboarding" --state all --json number,title` |
| Selective skill installs reliable | True, code-verified (`--list-skills`, `--skills <csv>` both parse and gate correctly), no dedicated CI test. | `./install.sh --list-skills` |

## Documentation

| Criterion | Status | Verify |
|---|---|---|
| README.md accurate | False, materially drifted (agent/skill/command counts, engine line count). Route the fix to `mcs-docs-of-record`; this skill only flags it as a v1.0 blocker. | `wc -l commands/_council-engine.md`; `find skills -name SKILL.md \| wc -l` |
| docs/adoption.md covers common paths | Believed accurate (installer walkthrough mirrors flags), not line-by-line re-diffed this cycle. | Read `docs/adoption.md` against `install.sh --help` |
| docs/upstream-sources.md documents vendored content | Incomplete: covers only `terraform-skill` (stale) and `vercel-react-best-practices`; omits `agentic-council` adoption and the steipete-derived skill-audit tooling. | `cat docs/upstream-sources.md` |
| THIRD_PARTY_NOTICES.md complete and current | False: 2 stale entries (dirs deleted), 2 missing entries (real adaptations undocumented). See main SKILL.md Licensing section. | `cat THIRD_PARTY_NOTICES.md`; `ls skills/terraform-skill skills/tdd` |

## CI / Quality Gates

| Criterion | Status | Verify |
|---|---|---|
| CI required on PRs and for merge to main | True. `validation (ubuntu-latest)`, `validation (macos-latest)`, `secret-scan` are all required status-check contexts. | `gh api repos/dtsong/my-claude-setup/branches/main/protection -q .required_status_checks.contexts` |
| Secret scanning enabled + gitleaks passes in CI | True. GitHub secret scanning + push protection both enabled; `secret-scan` job runs `gitleaks/gitleaks-action@v2` with `fetch-depth: 0`. | `gh api repos/dtsong/my-claude-setup -q .security_and_analysis.secret_scanning` |
| Branch protections enforced including admins | Partial/False on the "including admins" clause: `enforce_admins.enabled` is `false`. Required PR review count is `0`; CODEOWNERS exists but `require_code_owner_reviews` is `false`, so it is advisory, not enforced. | `gh api repos/dtsong/my-claude-setup/branches/main/protection` |

## Security / Maintenance

| Criterion | Status | Verify |
|---|---|---|
| Vulnerability alerts + Dependabot security updates enabled | True (GitHub API confirms both `enabled`/`status: enabled`). | `gh api repos/dtsong/my-claude-setup -q .security_and_analysis`; `gh api repos/dtsong/my-claude-setup/vulnerability-alerts -i` (expect HTTP 204) |
| Dependabot version updates configured for GitHub Actions | True for GitHub Actions only (`.github/dependabot.yml`, `package-ecosystem: github-actions`, weekly). No ecosystem entry for `mcp/openrouter`'s Python dependencies. | `cat .github/dependabot.yml` |
| SECURITY.md reporting path accurate | Partial: process (GitHub Security Advisories or "contact the maintainer directly") is documented, but no email/handle is given for the "contact the maintainer directly" fallback. | `cat SECURITY.md` |

## Community + Governance

| Criterion | Status | Verify |
|---|---|---|
| Issue templates and PR template reflect desired workflow | `.github/ISSUE_TEMPLATE/onboarding_feedback.md` exists and is used as designed (template exists, zero submissions yet: that's the onboarding-validation gap above, not a template gap). | `ls .github/ISSUE_TEMPLATE/` |
| CODEOWNERS requires maintainer review | File exists (`.github/CODEOWNERS`, single wildcard rule `* @dtsong`) but branch protection does not enforce it (`require_code_owner_reviews: false`). Existence != enforcement. | `cat .github/CODEOWNERS`; branch-protection command above |
| Labels exist for triage | Not re-audited this cycle against the full recommended set (bug, enhancement, docs, good first issue, question). | `gh label list` |

## Release Process

| Criterion | Status | Verify |
|---|---|---|
| CHANGELOG.md documents changes user-facing | False. `[Unreleased]` says only "OSS hardening in progress" despite ~5 months of substantive commits since the last entry (`[0.1.0] - 2026-02-12`). | `cat CHANGELOG.md` |
| Releases tagged with curated notes | Only one tag/release exists: `v0.1.0` (2026-02-12). No v0.1.x or later. | `git tag -l`; `gh release list` |
| v1.0.0 notes include 0.x migration note | N/A, not yet written (no v1.0.0 release exists). | n/a |

## Unstated blockers (not in issue #3's checklist, found by direct repo inspection)

1. **Private-repo coupling.** 7 symlinks point into `$HOME/Development/my-claude-setup-private`. Fresh-clone impact is cosmetic, not functional (`install.sh`'s existence guards skip broken symlinks silently); see main SKILL.md. Tracked partially by open issue #65 (US-007, queued).
2. **Machine-local paths in settings.json.** Two absolute `/Users/danielsong/...` paths remain in the OpenRouter MCP server entry and the `research-toolkit-local` marketplace entry, both opt-in via `--with-settings` but non-functional for anyone else. No issue currently owns this specific gap.
3. **README prerequisites incomplete.** `python3` is a hard install.sh dependency, absent from README's Prerequisites list.
