# Drift fix queue (verified 2026-07-02)

All 12 rows independently re-verified against the repo at commit `105427a`. Re-run the command in the last column before fixing or re-citing a row; counts move fast in this repo.

## 1. README agent/skill counts

- Claim: `README.md:3` "21 agents, 57 skills", plus the directory-tree comments "21 council agent personas" and "57 structured skill templates" (locate via `grep -n 'council agent personas\|structured skill templates' README.md`; exact line numbers drift as the README grows).
- Reality: 38 files in `agents/` (23 `council-*.md`, including the conductor `council-steward.md`, plus 15 `ece-*.md`). 22 top-level packs in `skills/`. 68 `SKILL.md` under `skills/council/` alone.
- Verify: `find agents -maxdepth 1 -name 'council-*.md' | wc -l`; `find agents -maxdepth 1 -name 'ece-*.md' | wc -l`; `ls -d skills/*/ | wc -l`; `git ls-files 'skills/council/**/SKILL.md' | wc -l`

## 2. README roster table is 20 rows, missing 2 agents

- Claim: `README.md:90` "roster of 20"; `README.md:180-207` "The 20 Agents" table.
- Reality: `commands/council.md:79-101` roster table has 22 rows, adding Foundry (#21, Copper) and Accountant (#22, Emerald). The entire ECE theme (15 agents, `commands/ece.md`) is also absent from README.
- Verify: `grep -c '^| [A-Z]' README.md` in the agent table section vs `sed -n '79,101p' commands/council.md`

## 3. README command count is stale

- Claim: `README.md:214` "16 slash commands + shared engine".
- Reality: 29 `.md` files directly under `commands/` (including the engine). README's command reference table omits `/analyze-workflow`, `/careful`, `/deepen`, `/diagnose`, `/ece`, `/fix`, `/freeze`, `/heavy-file-ingestion`, `/map`, `/qa`, `/review-fix`, `/ship`, `/tailor`, `/tdd`.
- Verify: `find commands -maxdepth 1 -name '*.md' | wc -l`

## 4. Engine line count is stale

- Claim: `README.md:216`, `ARCHITECTURE.md:9` "~1200 lines".
- Reality: 1753 lines.
- Verify: `wc -l commands/_council-engine.md`

## 5. ARCHITECTURE department count is stale

- Claim: `ARCHITECTURE.md:110` "(20 departments total)"; `README.md:220` "20 departments x 2-3 skills each".
- Reality: 22 department directories under `skills/council/` (excludes `references/`, `registry.json`, `model-routing.json`, `README.md`).
- Verify: `ls -d skills/council/*/ | grep -v references`

## 6. ARCHITECTURE skill-location claim is stale

- Claim: `ARCHITECTURE.md:133` "Skills are not duplicated, all 57 SKILL.md files live in `skills/council/`."
- Reality: 68 SKILL.md files under `skills/council/`; 22 additional top-level skill packs live outside it entirely (cicd-generation, dbt-skill, ece, frontend-qa, etc.).
- Verify: `git ls-files 'skills/council/**/SKILL.md' | wc -l`

## 7. ARCHITECTURE self-contradicts on agent frontmatter

- Claim A: `ARCHITECTURE.md:73-75` "Agents omit the `model` field so they inherit the session model. To pin one, use a tier alias ... never a versioned model ID."
- Claim B: `ARCHITECTURE.md:226` "Create `agents/council-<name>.md` with YAML frontmatter (`name`, `description`, `model`) ..."
- These directly contradict each other in the same file. Follow Claim A; it matches actual agent files (verify: `grep -L 'model:' agents/council-*.md | wc -l` should equal the total council agent count, confirming none pin `model` in frontmatter).
- Verify: `grep -n 'model' ARCHITECTURE.md`

## 8. ARCHITECTURE hooks table is incomplete

- Claim: `ARCHITECTURE.md:164-170` "Active Hooks" table lists exactly one row, `PreCompact` -> `pre-compact-handover.sh`.
- Reality: `hooks/` has 6 scripts. `hooks.json` wires only `PreCompact`. `settings.json`'s own `hooks` block separately wires `PreToolUse` (matcher `TaskUpdate`) -> `acceptance-gate.sh`, and `SessionStart`/`PostToolUse`/`PostToolUseFailure`/`Stop`/`SessionEnd` -> `telemetry-dispatch.sh` (fail-soft: exits 0 if the file is missing). `careful-mode.sh` and `freeze-mode.sh` are invoked directly by `/careful` and `/freeze` (they write a state file and have a `check` subcommand meant for a PreToolUse hook) but no PreToolUse hook in `settings.json` or `hooks.json` calls that `check` subcommand, so enabling careful/freeze mode currently blocks nothing. `skill-telemetry.sh` is described in `pipeline/specs/SKILL-GOVERNANCE-SPEC.md:1148` ("Register `hooks/skill-telemetry.sh` as a PreToolUse hook in `settings.json`") but appears zero times in `settings.json` as of this verification; this was independently confirmed by 3 council agents (Craftsman, Scout, Operator) during the `claude-config-model-optimization-20260702-0003` session's Round 1-3 deliberation, cited there as "the odometer was unplugged."
- Verify: `ls hooks/`; `cat hooks.json`; `python3 -c "import json;d=json.load(open('settings.json'));print(list(d['hooks'].keys()))"`; `grep -c skill-telemetry settings.json` (expect 0)

## 9. THIRD_PARTY_NOTICES references a deleted vendored directory (terraform-skill)

- Claim: `THIRD_PARTY_NOTICES.md:7-13` and `docs/upstream-sources.md:9-12` both describe `skills/terraform-skill/` as a vendored, upstream-maintained directory.
- Reality: the directory does not exist. Terraform skill content is now consumed as a plugin, `"terraform-skill@antonbabenko": true` in `settings.json`'s `enabledPlugins`.
- Verify: `ls skills/terraform-skill` (fails); `grep terraform-skill settings.json`

## 10. THIRD_PARTY_NOTICES references a deleted vendored directory (tdd)

- Claim: `THIRD_PARTY_NOTICES.md:21-27` describes `skills/tdd/` as a merged skill vendoring mattpocock/skills and obra/superpowers content, MIT-licensed.
- Reality: the directory does not exist. Only `commands/tdd.md` remains, a deprecated stub that redirects to `superpowers:test-driven-development` (part of the `superpowers@claude-plugins-official` plugin, not a vendored local copy). The MIT attribution obligation for the `superpowers` portion is arguably now satisfied by the plugin's own license, not this repo; the mattpocock/skills portion's disposition is open (owner-unconfirmed).
- Verify: `ls skills/tdd` (fails); `cat commands/tdd.md`

## 11. commands/council.md skill tree has a stale path header

- Claim: `commands/council.md`'s "Department Skills Tree" code block opens with `.claude/skills/council/`.
- Reality: no such path exists under `.claude/`. The real, current location is `skills/council/` at the repo root (verify by checking `.claude/skills/` is empty on this machine and `skills/council/registry.json` exists at the root path).
- Verify: `sed -n '110,113p' commands/council.md`; `ls .claude/skills/`; `ls skills/council/registry.json`

## 12. commands/council.md skill tree is missing 2 skill entries

- Claim: the tree lists 3 skills each for `scout/` and `foundry/`.
- Reality: `scout/` has 4 skills on disk (adds `enterprise-search-strategy`, committed 2026-06-22 per handover); `foundry/` has 4 skills on disk (adds `verilator-simulation`).
- Verify: `find skills/council/scout -name SKILL.md`; `find skills/council/foundry -name SKILL.md`; compare against the listing in `commands/council.md`'s tree block.

## Lower-severity, still queued

| Item | Verify |
|---|---|
| Spec Appendix A banner says "v1.4 QUICK REFERENCE" (line 1193) inside a doc whose header says v1.5 (line 1) | `sed -n '1p;1193p' pipeline/specs/SKILL-GOVERNANCE-SPEC.md` |
| `pipeline/config/budgets.json` `"spec_version": "1.3"` against the v1.5 spec it configures | `head -3 pipeline/config/budgets.json` |
| `skills/council/accountant/DEPARTMENT.md` lists 6 skill links (`core/reconciliation`, `core/journal-engine`, `tax/tax-research`, `audit/risk-assessment`, `reporting/financial-statements`, `advisory/variance-analysis`) that all 404, department is index-only, zero skills implemented | `find skills/council/accountant -name SKILL.md` (empty) |
| CHANGELOG `[Unreleased]` unchanged since `[0.1.0] - 2026-02-12` despite OpenRouter MCP server, new agents (Foundry, Accountant, 15-agent ECE theme), and the governance pipeline all shipping since | `cat CHANGELOG.md`; `git log --oneline --since=2026-02-13 -- mcp/ pipeline/ agents/ | wc -l` |
