# Deep-dive repros

Full transcripts for the two densest triage-table rows in `../SKILL.md`: OpenRouter's `error_kind` taxonomy, and the two soc-security pre-commit bugs. Read this only after the one-line table entry wasn't enough.

## OpenRouter `consult()` error kinds

`mcp/openrouter/openrouter_client.py` never raises. Every failure path returns `{"error": <message>, "error_kind": <kind>, "fallback": "claude"}`. A caller that only checks `if "error" in response` cannot distinguish these; branch on `error_kind`:

| `error_kind` | Cause | Check |
|---|---|---|
| `missing_key` | `OPENROUTER_API_KEY` unset in the launching shell | `[ -n "${OPENROUTER_API_KEY:-}" ] && echo set \|\| echo unset` |
| `transport` | Network/DNS failure before a response arrived | Reproduce with `transport` raising (unit tests inject this) |
| `http` | OpenRouter returned 4xx/5xx | Caught explicitly since `898174d` (PR #55 review fix): previously misclassified as `transport` |
| `parse` | Response JSON didn't have the expected shape (e.g. `message.content` not a string) | Same PR fixed a crash-on-null-content bug here |

Reproduce `missing_key` directly (no network call, safe to run anywhere):
```bash
cd mcp/openrouter && .venv/bin/python -c "
from openrouter_client import consult
print(consult(model='openai/gpt-4o-mini', system='s', prompt='p', api_key=None))
"
# -> {'error': 'OPENROUTER_API_KEY not set', 'error_kind': 'missing_key', 'fallback': 'claude'}
```

Separately, the server itself (not the client) needs its interpreter to exist:
```bash
test -x mcp/openrouter/.venv/bin/python && echo venv-ok || echo venv-missing
```
`mcp/openrouter/.venv/` is gitignored (`.gitignore:59`). On this machine (2026-07-02) it is bootstrapped and works. On a fresh clone it will not exist, and `settings.json`'s `mcpServers.openrouter.command` (hardcoded to that `.venv/bin/python` path) fails with `FileNotFoundError` at MCP-server-launch time: a symptom that looks nothing like "missing Python package," so don't chase dependency errors first. Bootstrap with `pip install -r mcp/openrouter/requirements.txt` into a venv at that exact path (see `mcp/openrouter/README.md`).

## The soc-security pre-commit pair

Both bugs share one cause: `pipeline/config/budgets.json` and `pipeline/hooks/check_isolation.py` were written assuming a skill suite sits directly under `skills/<suite>/skills/<specialist>/`. `soc-security` is a symlink to a private sibling repo (`skills/soc-security -> /Users/danielsong/Development/my-claude-setup-private/skills/soc-security`) and is itself a suite-of-suites: `skills/soc-security/skills/threat-model-skill/` etc. The extra `soc-security/` path segment breaks both checks.

### Bug 1: context-load budget override never matches

`pipeline/config/budgets.json`'s overrides are keyed `"skills/threat-model-skill"` and `"skills/verification-scaffold-skill"` (correct only if soc-security were the repo root: which it is, in its own private repo, where it carries an identical `pipeline/config/budgets.json` with the same keys). Under `my-claude-setup`, `check_context_load.py` computes the real relative path as `skills/soc-security/skills/threat-model-skill`, which never matches the override key, so it silently falls back to the global default ceiling (5,500 tokens) instead of the intended 6,100.

Reproduce (fails standalone, no other file staged):
```bash
python3 pipeline/hooks/check_context_load.py skills/soc-security/SKILL.md
# FAIL: skills/soc-security/skills/threat-model-skill: context load 6081 tokens
#   exceeds ceiling of 5500 (coordinator=623 + specialist(threat-model-skill)=3762
#   + reference(...output-templates-examples.md)=1696)
# FAIL: skills/soc-security/skills/verification-scaffold-skill: context load 6026
#   tokens exceeds ceiling of 5500 (...)
```
This fires whenever `skills/soc-security/SKILL.md` (the coordinator) is staged, even if the actual oversized specialist files were untouched: the failure message blames files you didn't edit.

Fix: re-key the two overrides in `pipeline/config/budgets.json` to the full repo-relative path (`skills/soc-security/skills/threat-model-skill`, `skills/soc-security/skills/verification-scaffold-skill`). Do not raise the global `max_simultaneous_tokens` default: that weakens the ceiling for every other suite in the repo to fix one symlinked suite. This may resolve itself if/when `soc-security` is extracted out of this repo (tracked as an open "F7" workstream, not yet done as of 2026-07-02): verify the extraction actually removes the symlink before assuming the bug is gone.

### Bug 2: isolation check computes the wrong sibling set

`check_isolation.py`'s `find_sibling_specialists()` finds the specialist name by taking the path segment immediately after the FIRST occurrence of `skills/` in the file path. For `skills/soc-security/skills/threat-model-skill/SKILL.md`, the first `skills/` is the repo-root one, so it picks `soc-security` as the "specialist" and treats every other top-level skill pack (`council`, `dbt-skill`, `docx-to-pdf`, `git-workflows`, ~21 total) as its siblings: instead of soc-security's real siblings (`compliance-pipeline-skill`, `verification-scaffold-skill`, `executive-brief-skill`, etc., which live one `skills/` segment deeper).

Reproduce:
```bash
python3 -c "
import sys; sys.path.insert(0, 'pipeline/hooks')
from check_isolation import find_sibling_specialists
siblings, name = find_sibling_specialists(
    'skills/soc-security/skills/threat-model-skill/SKILL.md', '.')
print('specialist_name:', name)
print('num siblings:', len(siblings))
print(sorted(siblings)[:10])
"
# specialist_name: soc-security
# num siblings: 21
# ['cicd-generation', 'council', 'data-engineering-skills', 'dbt-skill', ...]
```
Consequences, both directions:
- **False positive**: a threat-model-skill SKILL.md that happens to mention `skills/dbt-skill` or `council/SKILL.md` in prose (plausible in a security skill discussing example attack surfaces) trips a "cross-reference to sibling specialist" error against a completely unrelated pack.
- **False negative**: a real cross-reference between true siblings (e.g. `threat-model-skill` linking to `verification-scaffold-skill`) is never checked, because `verification-scaffold-skill` isn't in the computed sibling set at all.

There is no safe automated workaround short of a code fix (advance past the second `skills/` segment when the first-level directory itself contains a nested `skills/` subdirectory). Until fixed, verify isolation on nested suites (soc-security is the only one as of 2026-07-02) by manual read, and don't treat a clean run as proof of isolation.
