# Acceptance Contract: Claude Code Configuration + Model Optimization
Session: claude-config-model-optimization-20260702-0003 | PRD: prd.md | Status: locked

## Quality Gates
| Gate | Command | Required |
|------|---------|----------|
| pre-commit | `pre-commit run --all-files` | yes |
| openrouter tests | `python3 -m pytest mcp/openrouter/tests/ -q` | when OpenRouter files touched |
| type-check | none: no tsc/eslint surface in this bash/python/markdown repo (stated per CLAUDE.md directive 2) | n/a |

## Acceptance Criteria

### US-001: Fail-soft telemetry dispatcher (F3a)

#### AC-001: Dispatcher script exists with env-var path resolution and fail-soft exit
- **Method:** unit-test
- **Test:** `.claude/council/sessions/claude-config-model-optimization-20260702-0003/test-stubs/test_acceptance.py` > `test_ac_001_*` (env-var forwarding incl. spaces; default-path resolution)
- **Status:** verified
- **Evidence:** test_ac_001_dispatcher_env_var_forwarding + test_ac_001_default_path_resolution passed (pytest, 2026-07-02, review cycle 1)
- **Verified-by:** looper #59 (feat/59-fail-soft-telemetry-dispatcher)

#### AC-002: All five hook events use the dispatcher; no private-repo path in settings.json
- **Method:** build-output
- **Test:** `test-stubs/test_acceptance.py` > `test_ac_002_settings_wiring`
- **Status:** verified
- **Evidence:** test_ac_002_settings_wiring (automated pytest: 5 events on dispatcher, 0 private-path occurrences)
- **Verified-by:** looper #59 (feat/59-fail-soft-telemetry-dispatcher)

#### AC-003: Missing DEFAULT path yields exit 0 and silence; explicit env misconfig warns (exit 0); child failures never exit 2
- **Method:** unit-test
- **Test:** `test-stubs/test_acceptance.py` > `test_ac_003_missing_default_noop` (+ explicit-env warn, exit-2 normalization)
- **Status:** verified
- **Evidence:** test_ac_003_missing_default_noop (default path absent: exit 0, silent) + test_ac_003_explicit_env_var_missing_warns (explicit misconfig warns on stderr, still exit 0) + test_hook_failure_never_exits_2 (child exit 2 normalized to 1)
- **Verified-by:** looper #59 (feat/59-fail-soft-telemetry-dispatcher)

### US-002: Session default model to tier alias (F1)

#### AC-004: model is a tier alias, no [1m], no pinned claude-* ID
- **Method:** build-output
- **Test:** `jq -r .model settings.json` = `opus`
- **Status:** verified
- **Evidence:** jq -r .model settings.json = opus (tier alias, no pin, no [1m])
- **Verified-by:** looper #60 (feat/60-model-tier-alias)

#### AC-005: 1M stance is one deliberate state (env flag retained, no [1m] anywhere)
- **Method:** build-output
- **Test:** `grep -c '\[1m\]' settings.json` returns 0; env flag present
- **Status:** verified
- **Evidence:** grep -c '[1m]' settings.json = 0; CLAUDE_CODE_DISABLE_1M_CONTEXT=1 retained as the deliberate stance
- **Verified-by:** looper #60 (feat/60-model-tier-alias)

#### AC-006: Escalation rule documented in routing doc
- **Method:** manual-check
- **Status:** verified
- **Evidence:** docs/model-routing.md section 'Session Default and Escalation' records opus daily / fable ceiling on Max; sonnet default on API
- **Verified-by:** looper #60 (feat/60-model-tier-alias)

### US-003: Permissions rewrite (F2)

#### AC-007: Allowlist matches real workload; imagined-TS entries removed
- **Method:** build-output
- **Test:** `jq` assertions on permissions.allow
- **Status:** verified
- **Evidence:** allow list = 27 entries: pre-commit/pytest/python3/jq + gh scoped to pr/issue/label/repo-view/auth-status (blanket gh * rejected in review: unprompted repo delete/secret set/gist exfil on live global config) + Write scopes for agents,commands,skills,hooks,pipeline,docs,mcp; npm/tsc/src/tests removed
- **Verified-by:** looper #61 (feat/61-permissions-rewrite)

#### AC-008: Deny list preserved intact
- **Method:** build-output
- **Test:** `jq` diff of permissions.deny vs baseline
- **Status:** verified
- **Evidence:** deny strengthened, nothing weakened: original 22 entries intact + 4 gh guards (repo delete, secret set, gist create, repo create)
- **Verified-by:** looper #61 (feat/61-permissions-rewrite)

#### AC-009: settings.local.json gitignored and documented
- **Method:** build-output
- **Test:** `git check-ignore settings.local.json` succeeds; doc grep
- **Status:** verified
- **Evidence:** git check-ignore settings.local.json passes; convention documented in docs/model-routing.md 'Experiment Lane'
- **Verified-by:** looper #61 (feat/61-permissions-rewrite)

### US-004: OpenRouter ID refresh (F4)

#### AC-010: No 2024-era IDs; replacements validated via list_models()
- **Method:** build-output
- **Test:** `grep -cE 'gpt-4o-mini|gemini-flash-1.5' skills/council/model-routing.json` returns 0
- **Status:** verified
- **Evidence:** routing table now openai/gpt-5.4-nano (classification), google/gemini-3.5-flash (scout-research), openai/gpt-5.4-mini (scoring); all 3 verified live against the public catalog 2026-07-02 (338 models; gemini-flash-1.5 confirmed GONE, would have 404ed)
- **Verified-by:** looper #62 (feat/62-openrouter-id-refresh)

#### AC-011: Refresh mechanism exists (script or documented procedure, wired or scheduled)
- **Method:** manual-check
- **Status:** verified
- **Evidence:** mcp/openrouter/check_models.py exits 1 on stale IDs; cadence (monthly + before enabling callers) documented in mcp/openrouter/README.md and _id_refresh key in the routing table
- **Verified-by:** looper #62 (feat/62-openrouter-id-refresh)

#### AC-012: OpenRouter pytest suite passes with new IDs
- **Method:** unit-test
- **Test:** `python3 -m pytest mcp/openrouter/tests/ -q`
- **Status:** verified
- **Evidence:** python3 -m pytest mcp/openrouter/tests/ -q: 31 passed, 1 skipped (incl. 6 check_models tests covering missing-table, empty-set, network-failure, stale-ID, all-live paths)
- **Verified-by:** looper #62 (feat/62-openrouter-id-refresh)

### US-005: Unified routing table (F5)

#### AC-013: model-routing.json extended with tiers/profiles/spawn_sites/egress_policy
- **Method:** unit-test
- **Test:** `test-stubs/test_acceptance.py` > `test_ac_013_routing_schema_shape`
- **Status:** pending
- **Evidence:** —
- **Verified-by:** —

#### AC-014: Validation test rejects pinned IDs, missing profiles, missing egress_policy
- **Method:** unit-test
- **Test:** `test-stubs/test_acceptance.py` > `test_ac_014_routing_validator`
- **Status:** pending
- **Evidence:** —
- **Verified-by:** —

#### AC-015: Routing design doc renders full spawn-site x profile table with Max/API rules
- **Method:** manual-check
- **Status:** pending
- **Evidence:** —
- **Verified-by:** —

#### AC-016: Engine cost-profile section references model-routing.json as source of truth
- **Method:** build-output
- **Test:** `grep -c model-routing.json commands/_council-engine.md` >= 1 in the cost-profile section
- **Status:** pending
- **Evidence:** —
- **Verified-by:** —

### US-006: settings.json schema guard

#### AC-017: JSON-schema + pre-commit hook validate settings.json
- **Method:** unit-test
- **Test:** `test-stubs/test_acceptance.py` > `test_ac_017_settings_schema_hook`
- **Status:** pending
- **Evidence:** —
- **Verified-by:** —

#### AC-018: Hook fails on pinned IDs, [1m] suffixes, private-repo paths
- **Method:** unit-test
- **Test:** `test-stubs/test_acceptance.py` > `test_ac_018_schema_negative_cases`
- **Status:** pending
- **Evidence:** —
- **Verified-by:** —

#### AC-019: pre-commit run --all-files passes on final tree
- **Method:** build-output
- **Status:** pending
- **Evidence:** —
- **Verified-by:** —

### US-007: Dormant suite extraction (F7)

#### AC-020: Pre-flight reference enumeration + /ece coupling documented
- **Method:** manual-check
- **Status:** pending
- **Evidence:** —
- **Verified-by:** —

#### AC-021: Atomic extraction commit + README manifest/pointer
- **Method:** manual-check
- **Status:** pending
- **Evidence:** —
- **Verified-by:** —

#### AC-022: Reference-integrity hook passes; no dangling refs
- **Method:** build-output
- **Test:** `pre-commit run --all-files`; `grep -rE 'ece-|resume-tailor|soc-security|docx-to-pdf'` audit
- **Status:** pending
- **Evidence:** —
- **Verified-by:** —

#### AC-023: No secrets travel with the suites
- **Method:** build-output
- **Test:** secrets scan on the private-repo commit
- **Status:** pending
- **Evidence:** —
- **Verified-by:** —

### US-008: HTML presentation layer (F10)

#### AC-024: Engine synthesis touchpoint generates design.html and opens it before approval
- **Method:** build-output
- **Test:** grep engine synthesis section for design.html generation directive
- **Status:** pending
- **Evidence:** —
- **Verified-by:** —

#### AC-025: Reference HTML template exists under skills/council/references/
- **Method:** build-output
- **Status:** pending
- **Evidence:** —
- **Verified-by:** —

#### AC-026: Graceful degradation to text-only flow on HTML failure
- **Method:** manual-check
- **Status:** pending
- **Evidence:** —
- **Verified-by:** —

## Verification Summary
| ID | Criterion | Method | Status | Evidence |
|----|-----------|--------|--------|----------|
| AC-001 | Dispatcher fail-soft | unit-test | verified | see detail |
| AC-002 | Five events via dispatcher, no private path | build-output | verified | see detail |
| AC-003 | Missing path no-op | unit-test | verified | see detail |
| AC-004 | Tier alias model | build-output | verified | see detail |
| AC-005 | 1M single state | build-output | verified | see detail |
| AC-006 | Escalation rule doc | manual-check | verified | see detail |
| AC-007 | Workload allowlist | build-output | verified | see detail |
| AC-008 | Deny list intact | build-output | verified | see detail |
| AC-009 | Local experiment lane | build-output | verified | see detail |
| AC-010 | No stale IDs | build-output | verified | see detail |
| AC-011 | Refresh mechanism | manual-check | verified | see detail |
| AC-012 | OpenRouter tests pass | unit-test | verified | see detail |
| AC-013 | Routing schema shape | unit-test | pending | — |
| AC-014 | Routing validator | unit-test | pending | — |
| AC-015 | Routing doc table | manual-check | pending | — |
| AC-016 | Engine references table | build-output | pending | — |
| AC-017 | Settings schema hook | unit-test | pending | — |
| AC-018 | Schema negative cases | unit-test | pending | — |
| AC-019 | pre-commit all green | build-output | pending | — |
| AC-020 | Extraction pre-flight | manual-check | pending | — |
| AC-021 | Atomic move + manifest | manual-check | pending | — |
| AC-022 | No dangling refs | build-output | pending | — |
| AC-023 | No secrets travel | build-output | pending | — |
| AC-024 | Engine HTML directive | build-output | pending | — |
| AC-025 | Reference template | build-output | pending | — |
| AC-026 | Graceful degradation | manual-check | pending | — |

Progress: 12/26 verified
