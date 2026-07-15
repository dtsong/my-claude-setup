# Research frontier candidates, full detail (ranks 4-5)

Ranked order and one-line rationale live in `SKILL.md`. Ranks 1-3 are in `references/candidates-top3.md`. Every "why SOTA falls short" claim is training-knowledge, early-2026, author's characterization, unverified against a live literature search: treat as `open, owner-unconfirmed`.

## 4. Config-as-production discipline for agent harnesses (candidate, weakest novelty)

**Why current SOTA falls short:** dotfile managers (chezmoi, GNU stow) and GitOps patterns already solve "config lives in git, deploys on merge" in general; the gap here is narrower and more specific: almost none of them apply schema validation *and* a governance-lint layer to a config file that is simultaneously (a) symlinked into a running, stateful agent harness and (b) capable of silently breaking every tool call on malformed JSON. That combination (live-production + agent-harness-specific lint rules) is under-documented, but the underlying pattern is not new: this is the weakest novelty claim of the five.

**This repo's asset:** the symlink-deploy architecture itself (`~/.claude/settings.json` → repo, "this machine only" fact); `pipeline/config/settings.schema.json` + `pipeline/hooks/check_settings.py` (merged 2026-07-05, issue #64/PR #71, hard pre-commit hook `settings-schema`) encoding 3 harness-specific lint rules beyond structural shape (tier-alias-only model, no `[1m]` suffix conflict, no private-repo paths in hook commands); CI's installer smoke test (`install.sh --dry-run/--preset/--uninstall` on 2 OSes); the fail-soft telemetry dispatcher (US-001, merged) that makes a fresh clone degrade silently instead of hard-failing.

**First three steps, in this repo:**
1. `git log --oneline -3 -- pipeline/config/settings.schema.json pipeline/hooks/check_settings.py` and `git branch --show-current` to confirm #64's merge status before building on it.
2. Time a real fresh-clone run in a scratch dir: `git clone`, `./install.sh --dry-run`, `./install.sh --preset core`, `pre-commit run --all-files`, `python3 -m pytest mcp/openrouter/tests/ -q`, wall-clocking each step.
3. Wire the timing into a new `pipeline/scripts/fresh-clone-verify.sh` (does not exist yet) that clones to a temp dir, runs the sequence above, and fails loudly on timeout or any manual edit.

**You have a result when:** a fresh clone (no `my-claude-setup-private` present) reaches fully green (install core preset + `pre-commit run --all-files` + the openrouter pytest suite) in <=5 minutes wall-clock with zero manual file edits, reproduced on 2 separate runs.

## 5. Cross-session organizational memory vs auto-memory (open, weakest asset)

**Why current SOTA falls short:** most harnesses in early 2026 pick one extreme: full auto-memory (raw transcript summarization re-injected every session) or nothing. This repo deliberately chose neither, but almost nobody instruments whether a structured handover artifact measurably reduces rework versus either extreme, because that requires a rework metric most setups never build.

**This repo's asset:** the deliberate `CLAUDE_CODE_DISABLE_AUTO_MEMORY=1` decision (`settings.json:5`) plus `/handover`'s fixed-schema output (Session Summary/Decisions/Pitfalls/Open Questions/Next Steps/Important Files). Weak point: exactly 1 file exists in `memory/` (`HANDOVER-2026-06-22-0036.md`); there is no baseline dataset, so this is not yet a testable hypothesis, only a chosen policy.

**First three steps, in this repo:**
1. `ls -t memory/HANDOVER-*.md | wc -l`: confirm the count is still 1; this is the blocking gap, not a research step.
2. Build a rework proxy from git history: find repeated flip-flops on a decision recorded in a handover's "Key Decisions" (e.g. the `settings.json` model flip-flop 8c0cf14→78fbf46→uncommitted→`a1a8a72`) and note there is currently no marker distinguishing sessions that read the handover from ones that didn't.
3. Add a cheap `SessionStart` hook (pattern: `hooks/skill-telemetry.sh`) that logs "handover read: yes/no/stale(>7d)" to a local file, so future sessions produce comparable data.

**You have a result when:** across >=10 sessions with the read-marker in place, sessions that read a <7-day-old handover before starting show a measured rework rate (reverted/contradicted decisions per session, via the git-log proxy in step 2) at least 30% lower than sessions that didn't.
