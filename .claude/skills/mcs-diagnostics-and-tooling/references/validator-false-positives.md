# Known validator false-positive / silent-skip families

Every finding here is verified directly against source and/or a live run on 2026-07-02 (HEAD `936322e`). These are documented so you recognize them and can decide whether to route a real fix (mcs-debugging-playbook), not so you patch the validator on the spot.

## 1. `context-load-analysis.py` / `check-regressions.py` report zero on this repo

Both scripts define `find_skill_dirs()` to scan repo-root entries matching `entry.endswith("-skill")`. This repo has zero such directories (`ls -d *-skill` at repo root: no matches); all real skills live under `skills/`. Result: `python3 pipeline/scripts/context-load-analysis.py` prints an empty table, `check-regressions.py` prints "Skills checked: 0. No regressions detected." Neither is a bug in the sense of crashing or misreporting; each is scanning the wrong directory shape for this repo's layout. See `pipeline-shell-helpers.md` for the origin of the `*-skill/`-at-root convention.

## 2. `pre-commit run --all-files` looks clean despite real hook failures

`resume-tailor`, `soc-security`, `ece`, and other symlinked skill directories point into the private sibling repo `my-claude-setup-private` and are gitignored. `pre-commit run --all-files` iterates `git ls-files`, which never lists gitignored paths (symlink or not), so these files are silently excluded from every `--all-files` run and every CI `validation` job.

Evidence: `python3 pipeline/hooks/check_isolation.py skills/resume-tailor/SKILL.md` run directly → `FAIL: skills/resume-tailor/SKILL.md:79: cross-reference to sibling specialist 'docx-to-pdf' violates isolation rule`, exit 1. The same file passes silently (by omission) under `pre-commit run --all-files`.

Fix for verification purposes: never trust `--all-files` for symlinked skills; invoke the hook directly on the explicit path, or `pre-commit run --files <path>`.

## 3. Hooks silently no-op on anything not literally named `SKILL.md`

`check_frontmatter.py` and `check_references.py` both check `basename(file) == "SKILL.md"` early and return/skip otherwise (`check_references.py` returns at its `check_file()` entry). A `DEPARTMENT.md` file with broken links, e.g. `skills/council/accountant/DEPARTMENT.md` (6 listed sub-skill links, all currently broken), always exits 0 when run through these hooks, by construction, not by evasion. `check_isolation.py` and `check_context_load.py` use `classify_file()` from `_utils.py` instead, which has its own (different) skip logic; don't assume all four hard hooks share one skip rule.

## 4. `budgets.json` per-file overrides never match `soc-security`'s real path

`pipeline/config/budgets.json` overrides are keyed like `skills/threat-model-skill/SKILL.md` (25 entries total). The actual on-disk path is `skills/soc-security/skills/threat-model-skill/SKILL.md` (one extra path segment). Because the override lookup is an exact-path match, it never fires for `soc-security`'s nested specialists, and `check_context_load.py` hard-fails them against the unmodified 5,500-token ceiling every time it's run directly:

`python3 pipeline/hooks/check_context_load.py skills/soc-security/SKILL.md` → two FAIL lines (`threat-model-skill`: 6,081 tokens; `verification-scaffold-skill`: 6,026 tokens), exit 1.

## 5. Unknown frontmatter fields are WARN-only, not a hard failure

Contrary to an earlier (incorrect) investigation note, `check_frontmatter.py`'s handling of unknown top-level frontmatter keys (e.g. `git-workflows`, `prompt-wizard`'s `triggers:` / `user_invocable:`) only appends to a `warnings` list and still exits 0. Verified: `python3 pipeline/hooks/check_frontmatter.py skills/git-workflows/SKILL.md` → `WARNING: ... unknown frontmatter field 'user_invocable'`, exit 0. Hard failures are reserved for missing `name`/`description`, non-kebab `name`, description under 10 words, and an invalid `model` enum value.

## 6. `templates/` is excluded from validation entirely

`_utils.py`'s `is_excluded()` treats any path containing the segment `templates` (along with `pipeline`, `eval-cases`, `node_modules`, `.github`) as skipped. A skill's own `templates/*.md` bundle files are never checked by any of the six governance hooks, regardless of content.

## 7. `.claude/skills/**` (this skill included) is outside pre-commit's scope entirely

All six local governance hooks in `.pre-commit-config.yaml` are scoped `files: ^skills/.*\.md$`. That regex does not match `.claude/skills/mcs-diagnostics-and-tooling/SKILL.md` or any sibling `.claude/skills/*` skill. Nothing here gets automated frontmatter, reference, isolation, context-load, budget, or prose validation from pre-commit. Manual invocation (`python3 pipeline/hooks/check_*.py <path>`) still works and is the only way to check these files today.

## 8. `check_references.py` treats any backtick span that "looks like a path" as a reference to verify

`BACKTICK_PATH_RE` matches any backtick-wrapped text ending in `.md` or `/` that contains a `/` and no space, then `_looks_like_file_path()` accepts it. This fires on prose that merely resembles a path: documenting the hook's own bundle-dir alternation pattern in backticks (e.g. a regex like `references/\|scripts/\|...`) gets treated as a literal broken reference to a directory named that whole string. It also resolves any `~/.claude/`-prefixed backtick path against repo root (because `~/.claude/{skills,commands,...}` are symlinks into this repo), which produces a real FAIL for genuine runtime-state paths that live only under the user's home directory and were never symlinked in, such as `~/.claude/agent-context/shared/task-board.md`. Verified: running `check_references.py` against an early draft of this very skill's SKILL.md, before the two offending lines were rewritten as plain prose without backticks, produced exactly these two FAIL lines. Workaround: don't wrap a non-bundle path or a regex-alternation string in backticks ending in `/` or `.md`; describe it in prose instead.
