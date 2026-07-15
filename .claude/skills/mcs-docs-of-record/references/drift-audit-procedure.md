# Drift audit procedure

Primary instrument: `.claude/skills/mcs-diagnostics-and-tooling/scripts/doc-drift-check.sh`. Run it first; it is scripted, deterministic, and already exists in this repo (verified 2026-07-02, run below). It checks README/ARCHITECTURE's numeric claims (agents, commands, skills, departments) against live counts and always exits 0 (informational, not a gate). It does not cover every item in `references/drift-fix-queue.md`, hooks-table gaps, THIRD_PARTY_NOTICES, spec version banners, and dead links need the manual steps below.

## Step 1: run the scripted check

```bash
bash .claude/skills/mcs-diagnostics-and-tooling/scripts/doc-drift-check.sh
```

Output as of 2026-07-02:

```
DRIFT agents       claimed=21 actual=38 delta=17
DRIFT commands     claimed=16 actual=28 delta=12
DRIFT skills       claimed=57 actual=123 delta=66
DRIFT departments  claimed=20 actual=22 delta=2
council SKILL.md files: 68
  DRIFT: 68 council SKILL.md files falls outside that range
```

Note the metric mismatch trap: the script's `skills` count (123) is every `SKILL.md` anywhere under `skills/`, including symlinked private-repo suites (ece, soc-security, resume-tailor, research-consulting-skills, heavy-file-ingestion) and nested council skills. This SKILL.md's doc map uses "22 top-level skill packs" (`ls -d skills/*/`) as a separate, narrower metric for the doc-map table. Both are correct, for different questions; state which one you mean when reporting a number.

## Step 2: manual checks the script does not cover

Run each of these; every one is also listed with its command in `references/drift-fix-queue.md`:

1. Engine line count: `wc -l commands/_council-engine.md`
2. ARCHITECTURE hooks table vs actual: `ls hooks/`, `cat hooks.json`, `grep -n '"command"' settings.json`
3. THIRD_PARTY_NOTICES vendored dirs still exist: `ls skills/terraform-skill skills/tdd` (expect both to fail)
4. ARCHITECTURE internal contradictions: `grep -n 'model' ARCHITECTURE.md`, read lines around every hit
5. Spec version banner vs header: `sed -n '1p;1193p' pipeline/specs/SKILL-GOVERNANCE-SPEC.md`
6. budgets.json spec_version vs spec header: `head -3 pipeline/config/budgets.json`
7. Dead links in any DEPARTMENT.md: for each linked path, `test -f <path> || echo MISSING <path>` (the HARD `check_references` pre-commit hook does not catch these outside `references/`, `shared-references/`, `templates/`, `scripts/`, `assets/`, `examples/`)
8. commands/council.md skill tree vs disk, per department: compare `find skills/council/<dept> -name SKILL.md` output against the tree block's listed entries for that department
9. CHANGELOG staleness: `cat CHANGELOG.md`; compare `[Unreleased]` content against `git log --oneline --since=<last-changelog-date>` for anything release-worthy

## Step 3: report format

For each finding, state: file:line of the claim, the verification command run, the actual value observed, and the authority tier of the doc making the claim (see SKILL.md's ranking). Do not silently fix a finding that touches release claims (CHANGELOG additions, version bumps); route those to `mcs-external-positioning` or ask the owner. Do fix stale counts, dead links, and path typos directly, they carry no release-claim risk.

## When this procedure and the script disagree

Trust a fresh manual `find`/`wc`/`grep` over either this doc or the script's cached expectations; both are point-in-time snapshots that can themselves go stale. If `doc-drift-check.sh` itself starts reporting `SKIP` for a claim it used to catch, the README's wording changed, update the script's `extract_claim` pattern (owned by `mcs-diagnostics-and-tooling`) rather than assuming the drift is resolved.
