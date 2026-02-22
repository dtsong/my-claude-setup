# Verification Methodology — Confidence Propagation Rules

## Purpose

Rules for propagating confidence tiers from upstream threat findings through verification items.

**Primary consumer:** verification-scaffold-skill (Phase 5 output assembly, confidence reporting)

---

## The Confidence Chain

```
ThreatFinding.confidenceTier     -> upstream confidence
VerificationItem.tierConfidence  -> tier-inherent confidence
VerificationItem.overallConfidence = min(upstream, tier)
```

## Tier Confidence Assignments

| Tier | Tier Confidence | Rationale |
|------|----------------|-----------|
| Tier 1 | HIGH | SVA assertions are mechanically checkable — if signals exist, property can be verified |
| Tier 2 | MEDIUM | NL properties require human formalization — scaffold is a starting point |
| Tier 3 | REFERENCE | Specification references provide direction but no verification artifact |

## Propagation Examples

| Upstream Confidence | Tier | Tier Confidence | Overall | Interpretation |
|--------------------|------|----------------|---------|----------------|
| GROUNDED | 1 | HIGH | GROUNDED | Strongest: well-grounded threat, mechanically verifiable |
| GROUNDED | 2 | MEDIUM | MEDIUM | Strong threat, but verification requires formalization |
| GROUNDED | 3 | REFERENCE | REFERENCE | Strong threat, but no automated verification possible |
| INFERRED | 1 | HIGH | INFERRED | Inference-based threat, but assertion pattern is solid |
| INFERRED | 2 | MEDIUM | INFERRED | Both threat and verification have uncertainty |
| SPECULATIVE | 1 | HIGH | SPECULATIVE | Even a perfect assertion cannot fix a speculative threat |
| SPECULATIVE | 3 | REFERENCE | SPECULATIVE | Lowest useful combination — speculative and unverifiable |
| ABSENT | any | any | ABSENT | No analysis performed — no verification item generated |

## Confidence Reporting

In the coverage mapping, always show both upstream and overall confidence so the engineer can distinguish between "low confidence because the threat is speculative" and "low confidence because the verification method is weak."
