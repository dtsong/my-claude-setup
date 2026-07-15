# Privacy and history exposure: options ledger

This is a decision framework only. No option here is a recommendation. Executing any option requires the repo owner's explicit, separate instruction; this file (and the skill that points to it) never performs the action.

## What is exposed

- A named individual's resume content (`skills/resume-tailor/`). Corrected 2026-07-06: this content was NEVER on `main` (`git rev-list main -- skills/resume-tailor/SKILL.md` is empty). Commit `69cdb56`'s message claims a move to the private repo, but its diff touches only dbt-skill and web-security-hardening; treat that message as an assertion, not diff-verified fact. The only ref that carried the content (a dependabot branch, PR #51, closed unmerged) is deleted; residual risk is one orphaned, fetchable-by-SHA commit object (`8073361`) on the `dtsong-harness` fork, purgeable only via GitHub Support. Full derivation: mcs-failure-archaeology, `references/06-privacy-and-issues.md`.
- SOC/security and ECE (personal/career-coaching) content, moved out in an earlier commit (`bacac76`, 2026-04-04). That commit's diff is only 7 `.gitignore` lines; the actual content commits (`59d911d`, `f08b295`) predate it and remain reachable from pushed refs.
- Reachable *pushed* refs carrying this content, verified 2026-07-02: `origin/renovate/configure`, and 5 `origin/worktree-agent-*` branches (`a4e4a708`, `a4e9c020`, `a52e7b9f`, `a750c352`, `abe26a26`). Re-verify: `git branch -r | grep -E "worktree-agent|renovate"`.
- Deleting *local* branches does not remove this exposure: the content is reachable because these are **remote** refs on `origin`, independent of local branch state.

## Why this matters for public positioning

Any public launch/OSS-readiness claim ("safe to clone," "no personal data") is false while these refs exist on a public remote, regardless of what the default branch (`main`) currently contains. `docs/open-source-launch.md`'s checklist does not currently include a history-exposure check. This is a gap in the launch checklist itself, separate from the exposure.

## Options (present all three, recommend none)

| Option | Mechanism | Consequences |
|---|---|---|
| **A. Accept and document** | Leave refs as-is; add a documented, dated decision record (e.g., a note in `docs/open-source-launch.md` or a tracking issue) stating the exposure is known and accepted. | Content stays publicly reachable indefinitely (git history + GitHub caches/forks may have already copied it). Lowest effort, zero risk of breaking clones/CI/other branches. Does not remove the underlying exposure. |
| **B. Delete remote refs** | `git push origin --delete <branch>` for each of the 6 refs above. | Removes the refs from `origin`'s branch list, but does **not** guarantee removal from GitHub's object storage (orphaned commits can persist and remain fetchable by SHA for a retention window, and any existing fork/clone already has the objects). Cheaper and less destructive than a full history rewrite; does not fix `origin/main`'s own history (69cdb56's issue is separate from these branches). |
| **C. History rewrite (BFG or `git filter-repo`) + force-push** | Strip the offending blobs/commits from every affected ref including `main`, then force-push all rewritten refs. | Only option that actually removes the content from the *served* history. Highly disruptive: rewrites commit SHAs on `main` (breaks every existing clone, fork, open PR, and any external reference to old SHAs), requires all collaborators/forks to re-clone, and is irreversible once old refs are garbage-collected. Must coordinate with GitHub Support to purge cached views/PR diffs referencing old SHAs. This is the only option that satisfies a strict "no personal data ever reachable" bar. |

## Decision inputs the owner needs (do not answer these; surface them)

1. Has this repository ever been public with these refs pushed (i.e., is the exposure already irreversible via forks/mirrors/search-engine caches), or is it still effectively private-audience? This changes whether B/C meaningfully reduce risk or only manage it going forward.
2. Are any of the 5 `worktree-agent-*` branches or `renovate/configure` still needed for anything (git-archaeology notes: all are superseded, content re-landed via PR #42/#43/#48/#49)? If truly dead, Option B has near-zero cost beyond the rewrite question above.
3. Is the orphaned resume-tailor commit object on the fork (`8073361`, no live ref points to it) worth a GitHub Support purge request? This is a materially smaller remediation than any history rewrite: `main` itself needs no rewrite for resume-tailor (corrected 2026-07-06; the soc-security/ece branch refs are the surface that rewrite decisions apply to).
4. Does the real individual whose resume/personal content is exposed need to be notified or consent to any remediation timeline? This skill cannot determine that; it is explicitly out of scope for an engineering skill to advise on.

## What this skill will never do

- Never suggest a default ("just delete the branches" / "just rewrite history") without the owner initiating that specific instruction.
- Never treat commit `69cdb56`'s "scrubbing history is a separate decision" note as standing consent to act later.
- Never execute `git push --force`, `git filter-repo`, `BFG`, or `git push origin --delete` as part of routine repo work. These are the repo's own git-safety-protocol destructive operations and require explicit, current, user-issued instruction.
