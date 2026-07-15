# Pre-merge checklist

Run the items matching your change class from `../SKILL.md`'s classification table. Skip items for classes you did not touch.

## Always (every commit)

1. `git pull --rebase` (or `git log origin/main..HEAD` to confirm you're not behind): another session may have committed to `main` in the last few minutes on an active day.
2. Commit message matches `type(scope): description`, type from the valid set (`skill`, `skill-fix`, `skill-ref`, `skill-eval`, `skill-docs`, or a standard conventional-commit type), description ≥10 characters, no trailing period, subject ≤100 characters. `check_commit_msg.py` will reject anything else at the `commit-msg` stage.
3. `pre-commit run --all-files` (or at minimum `git commit` without `--no-verify`, letting the hooks run on the staged diff). Never bypass with `--no-verify`; CI never re-checks what pre-commit would have caught.
4. If you touched `.claude/` session-state files (`ship-state.md`, `looper-state.md`, `council/sessions/**`), confirm via `git log --oneline -10` and `gh pr list` that no other session's in-flight work is being clobbered by your edit.

## `skills/*.md` changes

5. `python3 pipeline/hooks/check_frontmatter.py <file>`: name/description present, kebab-case name, description ≥10 words.
6. `python3 pipeline/hooks/check_references.py <file>`: every path referenced in backticks/tables/bare text under `references/`, `shared-references/`, `templates/`, `scripts/`, `assets/`, `examples/` exists on disk.
7. `python3 pipeline/hooks/check_isolation.py <file>`: specialist SKILL.md does not reference sibling specialist directories.
8. `python3 pipeline/hooks/check_context_load.py <file>`: coordinator plus specialist plus largest reference stays under the 5,500-token suite ceiling (the only hard budget; per-file word targets are warn-only).

## `.claude/skills/*.md` changes (this skill's own class)

9. No pre-commit hook covers this path (every glob in `.pre-commit-config.yaml` is anchored `^skills/`). Manually run the four hooks above against your file(s) before committing: nothing else will catch a broken reference or malformed frontmatter here.
10. Optionally run `python3 pipeline/scripts/skill-audit.py --root .claude/skills --json` for an inventory/duplicate-name/token-cost check; it is read-only and reports, does not enforce.

## `settings.json` / `hooks.json` changes

11. `python3 -m json.tool settings.json` and `python3 -m json.tool hooks.json` both parse cleanly (this is literally the only CI check on these files today).
12. `grep '"model"' settings.json` returns a bare tier alias (`opus`, `sonnet`, `haiku`, `fable`), no `claude-*` prefix, no `[1m]` suffix.
13. No stray uncommitted edit is being left behind: `git status --short settings.json hooks.json` is clean after you commit (or you've deliberately reverted with `git checkout -- <file>`), because the symlink makes any leftover edit live regardless of commit state.
14. If you changed hook wiring (`PreToolUse`/`PostToolUse`/`Stop` blocks), re-read the matcher and confirm blocking intent: `PreToolUse` + exit 2 + stderr denies the tool; `PostToolUse` + any non-zero exit is a **non-blocking** warning only (see incident #2 in `incident-history.md` for what happens when this distinction is missed).

## `hooks/*.sh` changes

15. `bash -n <script>` (CI's only check on these files).
16. Manually pipe a representative JSON payload through the hook and check both stdout/stderr routing and the exit code match your intended blocking semantics, e.g.: `echo '{"tool_name":"TaskUpdate","tool_input":{"status":"completed"}}' | bash hooks/<script>.sh; echo $?`.
17. `set -euo pipefail` present, and any `grep -c` usage guards the zero-match case with a separate `|| VAR=0` assignment, not `$(grep -c ... || echo 0)` (see incident #2).

## Anything touching `commands/**` (engine docs)

18. Confirm the change is additive/clarifying, not a silent behavior change to a shared conductor path used by every `/council`, `/ship`, `/looper` session on this machine. If it changes model-selection language, confirm it still says "tier alias, never a pinned ID."
