# Adding evidence: worked recipes

Table of contents: 1. pytest to mcp/openrouter, 2. eval case + trigger evals
to a council department, 3. AC to a live contract, 4. new pre-commit
validator.

## 1. Add a pytest to `mcp/openrouter/tests/`

Conventions, read from the three existing test files (`test_smoke.py`,
`test_routing.py`, `test_openrouter_client.py`, 253 lines total) and
`mcp/openrouter/conftest.py`:

- `conftest.py` inserts `mcp/openrouter/` onto `sys.path`, so tests
  `import openrouter_client as oc` or `import routing` directly (no package
  install, no `src/` layer).
- Pure unit tests dominate: `test_build_payload_minimal`,
  `test_parse_success`, `test_resolve_task_model_known` construct inputs and
  assert on return values, no mocking framework.
- Network/live calls are dependency-injected, not monkeypatched: functions
  like `routed_consult(..., transport=lambda *a, **k: (500, {}))` accept a
  `transport` callable so tests substitute a fake without hitting the
  network.
- The one genuinely live test (`test_live_cheap_call` in `test_smoke.py`) is
  gated:
  ```python
  @pytest.mark.skipif(
      os.environ.get("OPENROUTER_SMOKE") != "1",
      reason="set OPENROUTER_SMOKE=1 (and OPENROUTER_API_KEY) to run the live call",
  )
  def test_live_cheap_call():
      ...
  ```
  Follow this pattern for any new test that would otherwise need a real
  API key or network access. `OPENROUTER_API_KEY` is unset in this
  environment by default, so an ungated live test will fail CI-style runs
  for everyone, not just you.

Steps:
1. Add `test_<behavior>.py` under `mcp/openrouter/tests/`, or a new
   `test_*` function in an existing file if it is the same module under
   test.
2. Import the target module directly (relies on `conftest.py`'s sys.path
   insert; do not add your own path hacks).
3. If the behavior needs a fake transport/response, add a parameter to the
   function under test rather than reaching for `unittest.mock.patch` (matches
   the existing dependency-injection style).
4. Run from the package root, not the repo root:
   ```bash
   cd mcp/openrouter && python3 -m pytest . -q
   ```
   (`mcp/openrouter/CLAUDE.md` documents this exact command as the canonical
   "unit tests, no network" invocation.) Or from repo root:
   ```bash
   pytest mcp/openrouter/tests/ -q
   ```
5. This test is not wired into CI (`.github/workflows/validate.yml` runs no
   pytest at all). If you need it enforced on every PR, that CI wiring does
   not exist yet and is a separate, unshipped change: do not claim "CI
   covers this" without adding the workflow step yourself and confirming it
   runs on a real PR.

## 2. Add an eval case + trigger evals to a council department

Location: `skills/council/<department>/eval-cases/`. Nine departments have
`trigger-evals.json` today: `alchemist, architect, cipher, forge, guardian,
oracle, prover, skeptic, warden`. The other 13+ departments (including
`accountant`, which has no skills implemented at all) do not.

Eval case structure (`SKILL-GOVERNANCE-SPEC.md` section 7.1), one markdown
file per case:

```markdown
# Eval Case: [Name]

## Metadata
- Case ID, Tier (1-3), Route/Input, Estimated components

## Input
[JSON block with the skill's input parameters]

## Expected Output
[Concrete, checkable expectations, tables or specific values]

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] [Specific, verifiable assertion]

### Should Pass (partial credit)
- [ ] [Secondary assertion]

### Bonus
- [ ] [Nice-to-have assertion]
```

Case selection (7.3): 5-7 cases per skill, tiered 1-2 simple / 2-3 medium /
1-2 complex, covering all key scenarios for the skill's domain, with a Raw
Trace Log section for traceability.

Trigger evals (7.2), `eval-cases/trigger-evals.json`: minimum 5 positive
cases (natural-language inputs that should activate the skill) and minimum 3
negative cases (inputs that should NOT activate it, each with
`expected_skill: null` and a note on the correct routing target). Look at
one of the 9 existing files, e.g.
`skills/council/architect/eval-cases/trigger-evals.json`, for the exact JSON
shape before writing a new one from scratch; do not invent a new schema.

Run it:
```bash
pipeline/scripts/run-evals.sh --tier 2 --targets council/<department> --model sonnet
```

## 3. Add an AC to a live contract

Only do this if the contract's header does not say `Status: locked`, or you
have owner sign-off to amend a locked one (inferred convention; no script
enforces it, but a locked contract represents a PRD-level agreement, and
scope changes to it should not be silent). Format for a new AC block
(`commands/_council-engine.md:1038`):

```markdown
#### AC-NNN: <Criterion text>
- **Method:** unit-test | integration-test | e2e-test | build-output | manual-check | metric
- **Test:** `path/to/test` > "test description"
- **Status:** pending
- **Evidence:** (empty until run)
- **Verified-by:** (empty until run)
```

Then add the matching row to the `## Verification Summary` table (this is
the table `hooks/acceptance-gate.sh` actually parses via
`grep -c '| pending |'` etc., so a detail block with no summary row is
invisible to the gate) and bump the `Progress: N/M verified` denominator.

If a BDD stub does not already exist for the new AC, add one to
`test-stubs/test_acceptance.py` (or the session's equivalent) that raises
`NotImplementedError("Not implemented - AC-NNN pending")`, matching the
existing stubs, so the criterion starts RED like every other AC in the
contract.

## 4. Add a new pre-commit validator

1. Write `pipeline/hooks/check_<name>.py`. Reuse `pipeline/hooks/_utils.py`
   for `classify_file()`, `is_excluded()`, budget/override resolution
   (`find_repo_root`, `load_budgets`, `estimate_tokens`,
   `get_context_ceiling`) rather than reimplementing them; every existing
   hook does this.
2. Decide the tier. Hard: `sys.exit(1)` on failure, blocks the commit. Warn:
   always `sys.exit(0)`, print `WARNING:`/`INFO:` lines only.
3. Wire it into `.pre-commit-config.yaml` as a `repo: local` hook with
   `entry: python3 pipeline/hooks/check_<name>.py`, `language: system`, and
   the correct `files:` glob. Every existing hook is scoped
   `files: ^skills/.*\.md$`; matching that pattern is what makes it apply to
   the same surface as the other 6. A narrower or wider glob is a deliberate
   choice, document why.
4. Add `verbose: true` if it is warn-tier (matches `check_token_budget`,
   `check_prose`), so advisories print even without `-v`.
5. Test it directly before relying on pre-commit's cache:
   ```bash
   python3 pipeline/hooks/check_<name>.py <some/matching/file.md>
   pre-commit run check-<name> --all-files
   ```
6. Critical, currently-skipped step: add the same check as a step in
   `.github/workflows/validate.yml`. Without that, the hook only runs on
   machines that have `pre-commit install`'d locally, and is fully bypassed
   by `git commit --no-verify` plus the repo's 0-required-reviews branch
   protection. As of 2026-07-02 none of the 6 existing skill-governance
   hooks are CI-enforced this way; whether that is an accepted gap or an
   oversight is owner-unconfirmed. Do not describe a new hard hook as
   "enforced" in commit messages or PRD text unless you have actually added
   the CI step and watched it run on a PR.
