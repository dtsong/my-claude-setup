# Cross-Framework Synthesis Checklist

Mandatory checklist for Phase 3 cross-framework synthesis step. Compensates for
Sonnet-tier execution by providing explicit structure for multi-framework
threat correlation.

## Pre-Synthesis Validation

- [ ] All selected frameworks (STRIDE, Attack Trees, Standards) have completed
- [ ] Each framework's findings are tagged with framework source
- [ ] Finding IDs are assigned before synthesis begins

## De-Duplication Pass

For each pair of findings across frameworks:

- [ ] Compare attack vector + target component + impact
- [ ] If overlap >80%: merge into single finding, list all framework sources
- [ ] If partial overlap: keep separate, add `relatedFindings` cross-reference
- [ ] If no overlap: no action

## Priority Correlation Check

For each finding that appears in 2+ frameworks:

- [ ] Compare severity assignments across frameworks
- [ ] If severity differs: use the higher severity, document the divergence in `assessmentNotes`
- [ ] If confidence differs: apply the framework quality hierarchy — standards-derived (GROUNDED) > STRIDE (may be INFERRED) > attack tree leaves (may be SPECULATIVE); use the confidence that corresponds to the highest-quality grounding source. If all contributing frameworks are at the same tier and still disagree, use the lower confidence (conservative).
- [ ] Flag findings where cross-framework correlation changes the priority
  (e.g., MEDIUM in STRIDE but HIGH when attack tree shows feasible chain)

**When priority changes across frameworks** — this is the trigger for Opus
escalation per the `hold_at: opus` condition. If running at Sonnet tier:
document the correlation explicitly, do not attempt novel synthesis of
conflicting framework outputs.

## Coverage Gap Analysis

- [ ] Build a matrix: attack surfaces (rows) x frameworks (columns)
- [ ] Mark each cell: COVERED / NOT COVERED / PARTIAL
- [ ] For each surface covered by only one framework: verify the finding is
  not framework-specific (e.g., attack trees may find chains that STRIDE misses)
- [ ] For each surface NOT COVERED by any framework: add ABSENT finding

## Synthesis Quality Gates

Before proceeding to Phase 4:

- [ ] Every finding has exactly one framework source (or merged source list)
- [ ] No duplicate findings remain (same vector + target + impact)
- [ ] Coverage matrix has no unmarked cells
- [ ] All priority changes from cross-framework correlation are documented
- [ ] ABSENT findings exist for all uncovered attack surfaces
