# Craftsman Response to Scout

**Their position:** Registry telemetry works (10/67 council skills show uses>0), so skip the rebuild, generate a usage-decay report, instrument for 2-4 weeks, and prune on that evidence.

**My response:** Modify

**Reasoning:** I re-verified the instrument and both of us were partially wrong, but Scout's "tracking works" fails the durability test. The facts: (1) `git show HEAD:skills/council/registry.json` contains **zero** nonzero `uses`; all 10 `uses: 1` values Scout cites are **uncommitted working-tree writes made by this very session** hours ago. (2) The global registry (`~/.claude/council/global-registry.json`) records at least 4 council sessions before today (roster-gap-analysis 2026-03-25, mediatek 2026-04-06, alan-yu 2026-05-31, klearpath 2026-07-02), and none of them persisted a single increment. So the mechanism I said was "not wired" does exist, at `_council-engine.md:672-673` as a conductor prose step, and it demonstrably fired once, which is a concession from my Round 1 framing. But an instrument that recorded 0 events across 4 sessions and whose only data point is volatile uncommitted state (one `git checkout .` erases it; cross-workspace sessions write through the `~/.claude/skills` symlink into this repo's dirty tree) is not "working", it is untrustworthy by construction. I therefore accept the Operator's 2-4 week instrumentation window, conditional on hardening first: (a) make increments durable, either move usage data to an untracked sidecar (e.g. `~/.claude/council/usage.json`) or auto-commit it, so data survives git operations; (b) close the coverage gap, since the engine step only sees council sessions while standalone suites (resume-tailor, docx-to-pdf, soc-security) load via the Skill tool, which requires actually registering `hooks/skill-telemetry.sh` in settings.json (still absent, verified today); (c) scope the window correctly: it can adjudicate the council long tail (which of 67 skills earn their slot), but it should not gate the dormant-suite extraction, because workload fit already decides that (user confirmed no ECE/hardware work; waiting 4 weeks to confirm a zero we can predict is delay without information). Prune ECE and friends now on labeled workload judgment; prune council skills later on hardened data.

## Verified evidence (2026-07-02)

| Claim | Verdict | Evidence |
|-------|---------|----------|
| Craftsman R1: "skill-telemetry.sh appears zero times in settings.json" | Correct | grep of settings.json hooks block: only acceptance-gate.sh and session_telemetry.py |
| Craftsman R1: "uses are hand-incremented" | Partially correct | Engine-prose mechanism at `_council-engine.md:672-673`; conductor-executed, not hook-executed |
| Scout R1: "10/67 skills show uses>0" | Literally true, misleading | All 10 are uncommitted; `git show HEAD:...registry.json` has 0 nonzero uses |
| Scout R1: "tracking works" | Overreach | 0 increments persisted across >=4 sessions (2026-03 through 2026-07); only this session wrote any |
| Operator: "instrument 2-4 weeks then prune" | Sound with preconditions | Requires durability fix + Skill-tool hook registration, and only for the council long tail |
