# Eval Case: PQC Algorithm Selection Review for SoC

## Metadata
- **Case ID:** EH-001
- **Tier:** 1 (simple)
- **Skill Route:** emerging-hw-security-skill
- **Estimated Complexity:** low

## Input
```json
{
  "user_prompt": "Review our PQC algorithm selection for a next-generation automotive SoC. We plan to implement:\n- ML-KEM-768 (FIPS 203) for key encapsulation — hardware accelerator with dedicated NTT unit\n- ML-DSA-65 (FIPS 204) for digital signatures — hardware accelerator sharing the NTT unit with ML-KEM\n- Replacing ECDH P-256 and ECDSA P-256 currently used for V2X communication\n\nImplementation plan:\n- Dedicated polynomial arithmetic unit (NTT butterfly, modular reduction)\n- SHAKE-256 hash core (shared with ML-KEM and ML-DSA)\n- TRNG for polynomial sampling\n- No hybrid mode planned — direct replacement (big-bang migration)\n- Target deployment: 2027 vehicle model year\n- Standards: FIPS 203, FIPS 204 (both final as of August 2024)\n\nMaturity: early-adoption. No prior PQC assessment.\nSoC family: Automotive. Technology domain: Post-Quantum Cryptography.",
  "context": "PQC algorithm selection review for automotive V2X. ML-KEM-768 and ML-DSA-65 replacing ECDH/ECDSA. Big-bang migration (no hybrid period). Hardware accelerator with shared NTT. Simple review — algorithm choice and migration strategy."
}
```

## Expected Output
EmergingHWFindings covering:
- Algorithm selection assessment (ML-KEM-768 and ML-DSA-65 suitability for automotive)
- Migration risk from big-bang replacement (no hybrid fallback)
- NTT unit as a shared resource — SCA implications
- Key size and bandwidth impact for V2X communication
- Standards maturity assessment (FIPS 203/204 final status)

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output contains at least one EmergingHWFinding related to PQC algorithm selection or migration
- [ ] Finding specifies paradigm as post-quantum
- [ ] Finding includes maturityLevel assessment (early-adoption)
- [ ] Finding includes standardsTrack reference (FIPS 203 and/or FIPS 204)
- [ ] Finding has a confidence tier and severity rating
- [ ] Finding has a research reference or `[FROM TRAINING]` marker

### Should Pass (partial credit)
- [ ] Big-bang migration risk assessed — no hybrid fallback means algorithm weakness requires full re-deployment
- [ ] ML-KEM-768 key size impact noted: public key 1184 bytes vs ECDH P-256 32 bytes — V2X bandwidth implications
- [ ] ML-DSA-65 signature size noted: ~3293 bytes vs ECDSA P-256 64 bytes — V2X message overhead
- [ ] NTT unit sharing between ML-KEM and ML-DSA identified as a resource contention and SCA cross-leakage point
- [ ] Migration readiness assessed as conditionally ready with blocking issues identified

### Bonus
- [ ] Notes that automotive lifecycle (15+ years) means algorithm must remain secure through ~2042 — NIST security category assessment
- [ ] Recommends hybrid mode for the transition period despite added complexity, citing algorithm agility
- [ ] Identifies SHAKE-256 as a potential bottleneck if shared between KEM decapsulation and DSA verification

## Raw Trace Log
