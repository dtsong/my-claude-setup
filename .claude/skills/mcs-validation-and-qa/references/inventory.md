# Golden and certified inventory (2026-07-02)

What is actually tested vs merely present. "Tested" means a command exists
that exits 0/1 or produces a checkable number; "present" means the file
exists but nothing currently runs it as a gate.

| Component | Evidence type | Status | Re-run command |
|---|---|---|---|
| `mcp/openrouter/tests/` (test_smoke, test_routing, test_openrouter_client, test_check_models) | pytest, 32 tests | Tested. 31 pass, 1 skipped (live call, needs `OPENROUTER_SMOKE=1` + key) | `pytest mcp/openrouter/tests/ -q` |
| Active council session `test-stubs/test_acceptance.py` | pytest, 10 tests | Tested. 6 passed (US-001/002 shipped), 4 `NotImplementedError` for pending AC-013/014/017/018 (correctly RED) | `pytest .claude/council/sessions/*/test-stubs/test_acceptance.py -q` |
| Active session `acceptance-contract.md` | AC table, 26 criteria | Tested per-row. 9/26 verified as of 2026-07-02 (not the earlier "0/26" snapshot; US-001 and US-002 executed) | `grep -n "^Progress:" .claude/council/sessions/*/acceptance-contract.md` |
| `check_frontmatter.py`, `check_references.py`, `check_isolation.py`, `check_context_load.py` | pre-commit hard hooks | Tested, currently passing on all git-tracked `skills/*.md` | `pre-commit run --all-files` |
| `check_token_budget.py`, `check_prose.py` | pre-commit warn hooks | Tested but non-blocking; several live WARNING/INFO findings exist today (e.g. `skills/data-engineering-skills/ai-data-integration/SKILL.md` over target by 10 words) | `pre-commit run skill-token-budget --all-files -v` |
| `check_commit_msg.py` | pre-commit hard, commit-msg stage | Tested at every commit | `python3 pipeline/hooks/check_commit_msg.py <msgfile>` |
| `.github/workflows/validate.yml` | CI: shell syntax, JSON validity, installer smoke, gitleaks | Tested on every PR/push to main | `bash -n install.sh hooks/*.sh scripts/*.sh` (local approximation) |
| Branch protection (main) | required status checks | Enforced: 3 checks, 0 required reviews | `gh api repos/dtsong/my-claude-setup/branches/main/protection` |
| `skill-audit.py` | read-only report (inventory, dupes, description cost) | Present, not a gate. 123 skills, ~5,966 description tokens, 0 name dupes, 0 identical bodies | `python3 pipeline/scripts/skill-audit.py --json` |
| `eval-cases/trigger-evals.json` (9 council departments) | trigger-eval fixtures | Present, not run automatically by anything; only executes when a human runs `run-evals.sh` | `find skills/council -name trigger-evals.json` |
| `run-evals.sh` tier 2/3 results | `eval-results/tier2-*` / `eval-results/judge-*` | No committed run artifacts found in the repo as of 2026-07-02: treat "we ran evals" claims without a results.jsonl path as unverified | `ls eval-results/ 2>&1` (expect: directory absent or empty until someone runs it) |
| `skills/council/registry.json` usage counters | telemetry, not a test | Present but historically untrustworthy: committed HEAD once showed 0/67 uses while working-tree counts were session noise. As of commit `dc44611` HEAD shows 18 committed uses, but this was a manual bookkeeping commit, not a durable increment mechanism; do not treat it as self-verifying evidence | `git show HEAD:skills/council/registry.json \| grep -o '"uses": [0-9]*' \| awk -F': ' '{s+=$2} END{print s}'` |
| `pipeline/config/budgets.json` overrides for `threat-model-skill` / `verification-scaffold-skill` | per-file budget override | Present but non-functional: override keys are `skills/threat-model-skill/...`, actual path (via the machine-only symlink) is `skills/soc-security/skills/threat-model-skill/...`, so the override never matches | `python3 pipeline/hooks/check_context_load.py skills/soc-security/SKILL.md` (fails today; not gated by pre-commit since the path is gitignored) |
| `skills/council/model-routing.json` | routing config | Present, still no live traffic: as of 2026-07-05 `tasks` carries current OpenRouter IDs (`openai/gpt-5.4-nano`, `google/gemini-3.5-flash`, `openai/gpt-5.4-mini`, refreshed by US-004/#70), file is `spec_version: "2.0"` and gated by a hard `check_model_routing.py` pre-commit hook (US-005, commit `82292e1`); zero callers of `routed_consult` anywhere in the repo outside its own tests | `cat skills/council/model-routing.json` (model IDs and spec_version) + `grep -rn "routed_consult(" --include=*.py .` (caller count) |
| `mcp/openrouter/` MCP server | registered in `settings.json.mcpServers.openrouter` | Present, requires one-time venv bootstrap or it FileNotFoundErrors; `OPENROUTER_API_KEY` unset by default in this environment | `mcp/openrouter/.venv/bin/python3 -c "from mcp.server.fastmcp import FastMCP"` (confirms bootstrap; unset key still blocks live calls) |

## Reading this table

- "Tested" rows are the only ones you may cite as evidence in a PR
  description, commit message, or AC `Evidence:` field.
- "Present" rows are candidates for the recipes in `adding-evidence.md`, not
  proof of anything by themselves.
- If a claim in a PRD/design doc cites a number from this table, re-run the
  command before repeating it; several of these numbers (registry uses,
  contract progress) are known to drift within the same day.
