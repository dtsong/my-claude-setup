# Worked examples for mcs-analysis-toolkit

Full narratives for the six recipes in `SKILL.md`. Each was reproduced against this repo on 2026-07-02; commands are copy-pasteable.

## Table of contents

1. Token/context-load key-path mismatch
2. Trigger-reliability: git-workflows vs. prompt-wizard
3. Hook-blocking live-fire: acceptance-gate.sh
4. Cost estimation for today's council session
5. Instrument-trust audit: registry.json
6. Refute-first review: commit 898174d

## 1. Token/context-load key-path mismatch

Suite: `skills/soc-security/skills/threat-model-skill`. Word counts (`wc -w`):

| File | Words | Tokens (`ceil(words*1.33)`) |
|---|---|---|
| `skills/soc-security/SKILL.md` (coordinator) | 468 | 623 |
| `skills/soc-security/skills/threat-model-skill/SKILL.md` (specialist) | 2828 | 3762 |
| `.../threat-model-skill/references/output-templates-examples.md` (largest reference) | 1275 | 1696 |
| **Total simultaneous load** | | **6081** |

Ceiling: 5,500 tokens (`pipeline/config/budgets.json:11`). 6081 - 5500 = 581 over. Reproduce: `python3 pipeline/hooks/check_context_load.py skills/soc-security/SKILL.md`.

`budgets.json` carries a `max_simultaneous_tokens: 6100` override that would cover 6081 (lines 77-79), keyed `"skills/threat-model-skill"`. But `check_suite()` computes the lookup key as `os.path.relpath(spec_dir, repo_root)`, which for this nested suite is `skills/soc-security/skills/threat-model-skill`, not `skills/threat-model-skill`. `get_context_ceiling()` (`_utils.py:186-221`) does an exact-match lookup on that key, stripping only a trailing slash, never checking the tail segment alone. The override silently never applies and the hook hard-fails. A second override at the same file, keyed `"skills/threat-model-skill/SKILL.md"` (lines 13-16), is a `max_words` budget, a different mechanism, also non-matching.

Lesson: an override for a specialist nested inside a coordinator's own `skills/` subdirectory must be keyed with the full nested relpath the hook computes, not the specialist's own directory name. Verify a candidate key by re-deriving `os.path.relpath(spec_dir, repo_root)` yourself before trusting an override exists.

## 2. Trigger-reliability: git-workflows vs. prompt-wizard

`python3 pipeline/scripts/skill-audit.py --json` over `skills/` (2026-07-02): `skill_count=123`, `total_description_tokens=5966`, `description_threshold_tokens=120`, `over_threshold=[]`, `duplicate_names=[]`, `identical_bodies=[]`. No description is oversized; the audit does not flag undersized ones that under-trigger.

`skills/git-workflows/SKILL.md`: `description: "Local git operations for syncing, branching, merging, and conflict resolution"`, exactly 10 words. Nested `skills/` subdirectory with 13 specialists (abort, branch, branches, conflicts, delete-branch, merge-main, pull, push, rebase, squash, stash, switch, sync) makes it a coordinator under `classify_file()`, held to a stricter bar under spec §1.6 ("cast a wide net," ANY/ALL, "this is the entry point"). No quoted phrases, no negative boundary, no breadth signal. Body 524 words / 697 tokens, well under the 800-token coordinator ceiling, so the gap is entirely the description.

`skills/prompt-wizard/SKILL.md`: `description: "Interactive wizard to craft effective prompts using Claude Code best practices"`, 11 words, no nested `skills/` dir so classifies as specialist. Body 1335 words / 1776 tokens, under the 2000-token ceiling. Same gap: no quoted phrases, no negative boundary, about a quarter of the §1.5 40-80 word target.

Both pass `check_frontmatter.py` (`MIN_DESCRIPTION_WORDS = 10`), proving only the word-count floor, nothing about trigger reliability.

Eval-case shape: `skills/council/skeptic/eval-cases/trigger-evals.json`, 15 cases (10 positive, 5 negative), each `{id, input, expected_skill, type, description}`. This as-built shape is the one to copy; the spec's fuller markdown template (Classification/Grading fields) is not implemented anywhere in the repo.

## 3. Hook-blocking live-fire: `acceptance-gate.sh`

Current registration: `settings.json`, `PreToolUse` matcher `TaskUpdate`, command `bash hooks/acceptance-gate.sh` (this machine only path). Script reads stdin JSON via `jq -r '.tool_name'` and `.tool_input.status`, gates only when `tool_name == "TaskUpdate"` and `status == "completed"`.

Live-fire test run 2026-07-02:

```
echo '{"tool_name":"TaskUpdate","tool_input":{"status":"completed"}}' | bash hooks/acceptance-gate.sh; echo "exit=$?"
echo '{"tool_name":"TaskUpdate","tool_input":{"status":"in_progress"}}' | bash hooks/acceptance-gate.sh; echo "exit=$?"
```

Blocking payload: exit 2, denial message on stderr. Control payload: exit 0, no output. Confirms the current script both fires and blocks as documented.

History (`git log --oneline -- hooks/acceptance-gate.sh`): `299a264` (2026-02-16) introduced the script wired as `PostToolUse`, message to stdout, exit 1 on violation. Any non-zero `PostToolUse` exit is logged but non-blocking, so through two more revisions (`6bc7c1a`, `4bb8bf2`) the gate never once denied a completion, decorative for roughly four months. `605112d` (2026-06-22) fixed it: `PreToolUse` plus `exit 2`. The same live-fire experiment against `git show 299a264:hooks/acceptance-gate.sh`, plus the event type in `settings.json` history, would have surfaced the non-blocking behavior on day one.

## 4. Cost estimation for today's council session

`.claude/council/sessions/claude-config-model-optimization-20260702-0003/session.md`: `Profile: max`, `Backend: workflow`, 7 selected agents. No explicit `Mode:` field; "standard" mode is inferred, owner-unconfirmed, from the artifact set (multi-round design doc plus per-agent scoring), not read off a labeled field.

`commands/_council-engine.md` §Cost Profiles & Model Routing, "Estimated session cost" table, standard mode, max profile, 5-agent baseline: 180,000-270,000 tokens. Scale factor `agents_selected / 5 = 7/5 = 1.4`. Scaled range: 180K*1.4 = 252K to 270K*1.4 = 378K tokens.

This is a hand-derived estimate from the engine's documented table, not a telemetry-backed actual. No file in this repo records real per-session token totals as of 2026-07-02; the engine text (`commands/_council-engine.md:116`, `:598`) points readers to a README "Cost guide" for $/MTok, but `grep -i cost README.md` returns zero hits, so that pointer is stale and should not be followed as if it resolves.

## 5. Instrument-trust audit: `skills/council/registry.json`

Write instruction: `commands/_council-engine.md:650-680`, Phase 2.5 "Skill Loading" step 7: "Update registry.json... Increment `uses` for each loaded skill... Set `last_used`... Append session slug." This is prose in a markdown command file, not code; nothing enforces the write, or that it gets committed.

`git log --oneline -- skills/council/registry.json`: last commit before 2026-07-02 was `729adcd` (2026-04-24), every entry at `uses: 0`. Next commit `dc44611` (2026-07-02, `+375/-69` lines, `git show --numstat dc44611 -- skills/council/registry.json`) brings the file to 18 total committed `uses` across 15 nonzero entries: a 69-day gap in which the documented write step either never ran, or ran repeatedly but was never committed. Commit history alone cannot distinguish those two.

Cross-workspace contamination: one session slug in the registry has no matching directory in `.claude/council/sessions/`. `~/.claude/skills` symlinks into this repo (this machine only), so every workspace on this machine writes the same physical `registry.json`, with no workspace tag per entry. A `uses` count answers "how many invocations across every project on this machine," not "how many sessions in this repo." Cite as a lower bound on activity, never a complete or repo-scoped history.

## 6. Refute-first review: commit `898174d`

Claim under review: fixing OpenRouter's `urllib_transport()` to catch `urllib.error.HTTPError` prevents 4xx/5xx responses from being misclassified as transport failures.

Pre-fix (`git show 898174d^:mcp/openrouter/openrouter_client.py`): `urllib_transport()` calls `urlopen(...)` with no `try/except`. `urlopen` raises `HTTPError` on any non-2xx status, so the exception propagates to `consult()`'s outer `try/except Exception`, classified `kind="transport"`.

Post-fix (current file): `urllib_transport()` catches `HTTPError` internally, returns `(exc.code, body)` as a normal response tuple, so `consult()`'s `if status >= 400` branch classifies it `kind="http"` instead.

Discriminating experiment: monkeypatch `urlopen` to raise `HTTPError(url, 429, "rate limited", {}, None)`, call `consult(...)`, read `result["error_kind"]`, against both versions (loaded as standalone modules via `importlib` from a temp copy of each git blob). Post-fix: `"http"`. Pre-fix (`898174d^`): `"transport"`. The two disagree on a caller-visible field, so the fix is load-bearing, not a cosmetic refactor.

`898174d` also added `test_urllib_transport_maps_http_error_to_status` and `test_consult_null_content_fails_soft` (a second, unrelated null-content guard). Caveat: `gh pr view 55 --json reviews,comments` shows PR #55 merged with zero GitHub-recorded human reviews and zero comments. The self-run experiment above is the only verification this fix has actually received.
