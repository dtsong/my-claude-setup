# Authority worked examples

Reasoning template: identify which tier (see SKILL.md's 5-level ranking) each conflicting claim sits at, prefer the higher tier, verify the higher-tier claim directly rather than trusting it by inheritance, then state the conclusion as an assertion with a re-verification command. Do not average or hedge between two docs.

## Example 1: token budget ceiling, 5,000 vs 5,500

- Tier 5 claim: repo `CLAUDE.md:57`, "Maximum simultaneous context load: ≤5,000 tokens", under a heading titled "Token Budgets (Hard Limits)".
- Tier 2 claim: `pipeline/specs/SKILL-GOVERNANCE-SPEC.md:110` ("Hard ceiling on simultaneous load: ≤5,500 tokens") and `:126` (table row "Suite ceiling ... ≤5,500 tokens").
- Tier 1 claim: `pipeline/config/budgets.json:11`, `"max_simultaneous_tokens": 5500`, is the literal value `pipeline/hooks/check_context_load.py` reads at commit time.
- Resolution: 5,500 wins on two independent grounds, it is both the higher-authority tier (spec + enforcement code vs CLAUDE.md) and the spec explicitly narrates the change ("Per-file token budgets reclassified from hard limits to guideline targets... Suite context load ceiling remains the only hard budget limit", spec changelog lines 14-16). CLAUDE.md also mislabels per-file targets as "Hard Limits" when the spec's own table (line 120) marks them "Warn At" with "Hard Limit: None (ceiling applies)". Two errors in one heading, both resolved the same direction.
- What is NOT resolved: whether the owner ever intended 5,000, or always meant 5,500 and CLAUDE.md has a typo. That is a 1-line fix once the owner confirms intent; do not silently change it without asking, since it also changes the labeled semantics ("Hard" to "target/warn").

## Example 2: agent roster count, root README vs department README

- Tier 4 claim: `README.md:3`, "21 agents"; `README.md:90`, "roster of 20"; `README.md:180`, "The 20 Agents" (table has 20 rows).
- Also-tier-4 claim, different file: `skills/council/README.md:3`, "a roster of 22".
- Neither file is a spec or enforcement code; both are narrative docs at the same authority tier. Do not default to "root wins because it's the top-level README."
- Resolution method when two same-tier docs disagree: verify against the artifact both claim to describe, not against each other. `commands/council.md`'s roster table (the input the conductor actually scores against at runtime) has 22 rows, adding Foundry and Accountant. `skills/council/README.md` matches this; root `README.md` does not. Verify: `grep -c '^| [0-9]' commands/council.md` in the roster section, count should be 22.
- Provenance detail that explains the gap: commit `729adcd` ("docs(council): align documentation with current 22-agent state") touched `skills/council/README.md`, `commands/council.md`, and `skills/council/registry.json`, three files, zero of which is root `README.md` (`git show --stat 729adcd`). The sync pass that would have fixed root README simply never reached it. This is common in this repo: a commit message saying "documentation" without a path is not evidence any specific doc was touched. Always check `--stat`.

## Example 3: when the higher tier itself has an internal contradiction

`ARCHITECTURE.md` (tier 3) contradicts itself: line ~74 says agents omit the `model` frontmatter field, line 226 lists `model` as required frontmatter for a new agent. Same tier, same file, opposite claims. Resolution: fall through to tier 1, the artifacts on disk. `grep -L 'model:' agents/council-*.md | wc -l` shows every council agent file omits `model` in frontmatter. The on-disk convention matches the earlier claim (line ~74); line 226 is the error. When a tier-3+ doc contradicts itself, verify against tier-1 evidence (the files it is describing) rather than picking a side by document position or recency.
