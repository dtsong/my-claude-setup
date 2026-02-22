# JIL Attack Potential Scoring — Countermeasure Effectiveness & Residual Risk

---

## 6. Scoring Adjustments for Countermeasures

When countermeasures are present, adjust the base scores:

| Countermeasure | Affected Categories | Typical Score Increase |
|---------------|--------------------|-----------------------|
| 1st-order masking | Elapsed Time (+3-7), Expertise (+3), Equipment (+2) | +8-12 total |
| 2nd-order masking | Elapsed Time (+7-13), Expertise (+3-5), Equipment (+2-4) | +12-22 total |
| Random delays / shuffling | Elapsed Time (+2-4), Expertise (+3) | +5-7 total |
| Dual-rail logic (WDDL) | Elapsed Time (+4-7), Expertise (+3), Knowledge (+4) | +11-14 total |
| Voltage glitch sensor | Elapsed Time (+4-7), Expertise (+3), Knowledge (+4) | +11-14 total |
| Active shield / mesh | Access (+3-7), Equipment (+2-4), Knowledge (+4) | +9-15 total |
| Retry limiting (< 100 attempts) | Elapsed Time (+4-7), Access (+3-7) | +7-14 total |

**Important:** Countermeasure adjustments are not additive — overlapping countermeasures may have diminishing returns. Assess the combined effect realistically.

---

## 7. Application to Combined Attacks

For combined attacks (e.g., fault + SCA), score the most difficult component but account for the combined complexity:

**Scoring principle:** Take the maximum score per category across the individual attack components, then add 1-3 points to Elapsed Time and Expertise to account for integration complexity.

**Example: Glitch to disable masking, then CPA:**

| Category | FI Component | SCA Component | Combined |
|----------|-------------|---------------|----------|
| Elapsed Time | 4 | 4 | max(4,4) + 2 = 6 |
| Expertise | 3 | 6 | max(3,6) + 2 = 8 |
| Knowledge | 3 | 3 | max(3,3) = 3 |
| Access | 1 | 0 | max(1,0) = 1 |
| Equipment | 2 | 4 | max(2,4) = 4 |
| **TOTAL** | | | **22 (High)** |

---

## 8. Scoring Checklist

Use this checklist when scoring each attack vector:

```
JIL Scoring Checklist
=====================
[ ] Elapsed Time: Have I accounted for development, characterization, AND execution time?
[ ] Expertise: Does the attack require novel technique development, or can standard tools/methods be used?
[ ] Knowledge: What implementation details must the attacker know? Are they public, restricted, or sensitive?
[ ] Access: Can the attacker take the device to their lab? Is decapping required? Are there access restrictions?
[ ] Equipment: What is the most specialized piece of equipment required? Is it commercially available?
[ ] Countermeasures: Have I adjusted scores for deployed countermeasures?
[ ] Combined attacks: If combining techniques, have I scored the combined complexity?
[ ] Consistency: Are scores consistent across findings? (Same attack class on similar targets should have similar scores)
```
