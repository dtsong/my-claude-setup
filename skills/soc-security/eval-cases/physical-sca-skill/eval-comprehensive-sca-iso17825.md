# Eval Case: Comprehensive SCA Assessment per ISO 17825

## Metadata
- **Case ID:** PS-005
- **Tier:** 3 (complex)
- **Skill Route:** physical-sca-skill
- **Estimated Complexity:** high

## Input
```json
{
  "user_prompt": "Conduct a comprehensive physical SCA assessment per ISO 17825 for our multi-algorithm crypto subsystem in a government-grade secure element SoC. Full details:\n\nCryptographic assets:\n1. AES-256-GCM — hardware accelerator, 2nd-order threshold implementation (TI) masking, shuffled S-box computation order\n2. RSA-4096 — hardware accelerator, constant-time Montgomery multiplication, message blinding enabled, exponent blinding enabled\n3. ECDSA P-384 — hardware accelerator, scalar randomization (random projective coordinates), no masking on field arithmetic\n4. SHA-384 — hardware, used for HMAC key derivation — no SCA countermeasures (considered non-secret-dependent)\n5. TRNG — ring-oscillator based, continuous health tests (repetition count + adaptive proportion per SP 800-90B)\n\nKey management:\n- Root key: 256-bit, hardware-bound (PUF-derived), never leaves the crypto boundary\n- Session keys: derived via HKDF-SHA-384 from root key + nonce\n- Key lifetime: session keys rotate every 10,000 operations\n- Key zeroization: active zeroization on tamper detect\n\nPhysical protections:\n- Active shield mesh (all 6 metal layers)\n- Voltage glitch sensor (dual-threshold, 50ns detection window)\n- Clock glitch sensor (frequency monitor, 5% deviation threshold)\n- Temperature sensor (operating range: -25C to 85C, lockout outside range)\n- Light sensor under shield mesh (laser FI detection)\n- Environmental tamper response: zeroize all keys, enter lockdown\n\nAttacker model:\n- Funded attacker with dedicated lab: FIB (Focused Ion Beam), high-end oscilloscope (6GHz, 20GS/s), tunable laser for fault injection, full EM probe station\n- Can attempt decapping (shield mesh is the barrier)\n- Can trigger operations with chosen inputs (API access)\n- Has datasheet and hardware user manual (no RTL)\n- Unlimited time (government threat model)\n\nTarget certification: FIPS 140-3 Level 4, CC EAL6+. ISO 17825 TVLA compliance required.\n\nPrior lab data (partial):\n- AES-256-GCM: TVLA non-specific first-order t-test, 100K traces, max |t| = 3.2 (pass, threshold 4.5)\n- AES-256-GCM: TVLA non-specific second-order t-test, 100K traces, max |t| = 6.8 (FAIL, threshold 4.5)\n- RSA-4096: no TVLA data\n- ECDSA P-384: no TVLA data\n\nSoC family: Government Secure Element. Technology domain: Cryptographic Operations, Key Management.",
  "context": "Multi-algorithm crypto subsystem with layered countermeasures targeting FIPS 140-3 Level 4 and CC EAL6+. Partial TVLA data shows AES second-order leakage detected. Funded attacker with FIB capability. 5 crypto operations to assess across power, EM, timing, and fault injection channels. ISO 17825 compliance deliverable required."
}
```

## Expected Output
A comprehensive physical SCA assessment covering:
- PhysicalSCAFindings for each crypto algorithm across all applicable channels (power, EM, timing, FI)
- Full JIL scoring for every attack vector with 5-factor breakdown
- ISO 17825 TVLA status table with provided lab data integrated (AES first-order pass, second-order fail)
- Leakage surface coverage matrix: all 5 crypto ops x all channels
- Countermeasure effectiveness table with residual risk per countermeasure
- TRNG health assessment (SPA on ring oscillator, FI on health tests)
- Key management attack surface (HKDF derivation, key zeroization bypass)
- DocumentEnvelope with confidence summary and FIPS 140-3 Level 4 / CC EAL6+ implications

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output contains PhysicalSCAFindings for at least AES-256, RSA-4096, and ECDSA P-384
- [ ] Every finding has a complete JIL score with all 5 subtotals, total, and rating
- [ ] ISO 17825 TVLA table present with AES first-order marked pass (|t|=3.2 < 4.5) and second-order marked fail (|t|=6.8 > 4.5)
- [ ] RSA and ECDSA TVLA status marked as not-assessed
- [ ] Leakage surface coverage matrix present covering all 5 crypto operations across power/EM/timing/FI channels
- [ ] Every finding has confidence tier, severity, and research reference or `[FROM TRAINING]`
- [ ] Countermeasure summary table present with effectiveness per countermeasure
- [ ] Caveat block present noting this requires lab validation for non-assessed operations

### Should Pass (partial credit)
- [ ] AES-256 second-order leakage finding references the TVLA failure data (|t|=6.8) as GROUNDED evidence
- [ ] 2nd-order TI masking assessed for 3rd-order attack feasibility — trace count scaling documented
- [ ] ECDSA P-384 finding identifies lack of masking on field arithmetic as a leakage gap despite scalar randomization
- [ ] RSA-4096 assessed with blinding — notes blinding raises trace count but does not eliminate leakage theoretically
- [ ] Active shield mesh assessed for FIB bypass feasibility — impacts JIL access and equipment scores
- [ ] Key management assessed: HKDF derivation as potential SPA target, key zeroization bypass via controlled power-down
- [ ] At least one finding rated GROUNDED (using the provided TVLA lab data)
- [ ] FIPS 140-3 Level 4 implications noted — requires mitigation of the AES second-order TVLA failure

### Bonus
- [ ] TRNG ring oscillator assessed for SPA (locking/bias detection) and EM injection (frequency manipulation)
- [ ] SHA-384/HMAC assessed for timing leakage in HKDF — even if data-independent, implementation may have variable timing
- [ ] Notes that key rotation (10K ops) bounds the attacker's trace collection window per key, providing a protocol-level mitigation factor
- [ ] Dual-threshold voltage glitch sensor assessed against slow-ramp attacks that stay within each threshold individually
- [ ] Provides explicit FIPS 140-3 Section 7.8 mapping for each finding

## Raw Trace Log
