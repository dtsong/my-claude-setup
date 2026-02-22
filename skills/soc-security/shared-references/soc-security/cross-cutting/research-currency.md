# Research Currency — Quarterly Update Methodology

## Purpose

Defines the methodology for maintaining research currency in skills that reference academic papers, CVEs, and evolving attack techniques. Ensures that citations are traceable, freshness is visible, and the boundary between established knowledge and recent findings is clear.

**Primary consumers:** microarch-attack-skill, emerging-hw-security-skill, physical-sca-skill
**Secondary consumers:** All skills referencing external research

---

## Research Reference Format

Every research citation in skill outputs must follow this format:

```
{Authors}, "{Title}", {Venue} {Year}; {CVE-ID if applicable}
```

**Examples:**
- `Kocher et al., "Spectre Attacks: Exploiting Speculative Execution", IEEE S&P 2019; CVE-2017-5715`
- `Primas et al., "Single-Trace Attacks on Keccak", CHES 2023`
- `NIST, "FIPS 203: Module-Lattice-Based Key-Encapsulation Mechanism Standard", 2024`

### Reference Fields in Entity Schema

The `researchReference` field in `MicroarchAttackFinding` and `EmergingHWFinding` entities uses this format. When a finding is grounded in a specific paper, the reference provides traceability.

---

## Currency Tiers

Research references are categorized by age and verification status:

| Tier | Age | Verification | Marker |
|------|-----|-------------|--------|
| **Current** | < 6 months from last verified date | Paper published, CVE assigned, or standard ratified | No marker needed |
| **Recent** | 6-18 months | Peer-reviewed or widely reproduced | `[RECENT]` |
| **Established** | > 18 months | Part of accepted body of knowledge | `[ESTABLISHED]` |
| **From Training** | Unknown recency | From LLM training data, not verified against current literature | `[FROM TRAINING]` |

### Assignment Rules

1. References with specific venue and year that fall within the current tier are **Current**
2. References with specific venue and year older than 6 months are **Recent** or **Established**
3. References from LLM training knowledge without specific publication verification are always `[FROM TRAINING]`
4. When a finding combines a `[FROM TRAINING]` reference with a verified reference, the combined confidence follows the lower tier

---

## Quarterly Update Process

Skills that reference research should be reviewed quarterly to maintain currency. The process:

### 1. Attack Catalog Review (Quarterly)

**Scope:** `threat-catalog/microarchitectural-attacks.md`, `threat-catalog/kernel-attacks.md`

- Scan for new CVEs in the relevant attack classes
- Check for new academic publications at top security venues (IEEE S&P, USENIX Security, CCS, NDSS, CHES, TCHES)
- Update attack entries with new variants, mitigations, or affected hardware
- Add new entries for novel attack classes
- Mark superseded entries (e.g., when a mitigation renders an attack class impractical)

### 2. Standards Tracking (Quarterly)

**Scope:** `standards-registry/` (all entries)

- Check for new standard versions or errata
- Update version numbers and requirement extracts
- Add new standards as they reach ratification
- Note deprecations or supersessions

### 3. Mitigation Currency (Quarterly)

**Scope:** Skill reference files (`speculation-barrier-patterns.md`, `jil-scoring-guide.md`, etc.)

- Update hardware mitigation recommendations based on new CPU microcode, firmware patches, or hardware revisions
- Update software mitigation recommendations based on kernel patches, compiler updates, or tool releases
- Flag mitigations that have been shown ineffective by new research

### 4. Freshness Metadata

Each reference file should include a `Last verified` date at the bottom:

```markdown
*[FROM TRAINING] All content in this file is derived from publicly available research
and general domain knowledge. Specific details should be verified against original
publications. Last verified: YYYY-MM-DD.*
```

Update this date when the quarterly review is performed.

---

## Citation Integrity Rules

1. **Never fabricate citations.** If a finding is based on general knowledge without a specific paper, use `[FROM TRAINING]` — do not invent a plausible-sounding reference.
2. **CVEs must be real.** CVE IDs are verifiable. If you are not certain of a CVE ID, omit it and note `[CVE-ID unverified]`.
3. **Venue abbreviations are standard.** Use: IEEE S&P, USENIX Security, CCS, NDSS, CHES, TCHES, CRYPTO, EUROCRYPT, ASIACRYPT, IEEE HOST, DAC, DATE.
4. **Year is publication year, not discovery year.** Spectre was discovered in 2017 but published at IEEE S&P 2019.
5. **When citing standards, include version.** "FIPS 203" is insufficient; use "FIPS 203 (2024)" or "NIST FIPS 203, August 2024."

---

## Guidance for Skill Consumers

### microarch-attack-skill
The attack catalog (`microarchitectural-attacks.md`) is the primary reference. Each attack entry includes research references. When generating findings, propagate references from the catalog to the `researchReference` field.

### physical-sca-skill
References to ISO 17825, JIL methodology, and published DPA/CPA research follow the standard format. Lab measurement results are `user-provided` grounding and do not require research references.

### emerging-hw-security-skill
PQC and chiplet security references evolve rapidly. Always check the `Last verified` date on reference files. FIPS 203/204/205 ratification dates anchor the PQC timeline.

### tlaplus-security-skill
Formal method references are generally `[ESTABLISHED]` (Lamport's TLA+, model checking theory). New references apply when modeling novel attack patterns that appear in recent research.

---

*[FROM TRAINING] This methodology is based on general best practices for research currency management. Verify venue names and standard versions against authoritative sources. Last verified: 2026-02-13.*
