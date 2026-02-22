# PQC Hardware Implementation — Algorithm Overview and ML-KEM/ML-DSA Requirements

## FIPS 203 — ML-KEM (Module-Lattice-Based Key Encapsulation Mechanism)

Formerly CRYSTALS-Kyber. Standardized August 2024.

### NTT Implementation Security

The Number Theoretic Transform (NTT) is the core computational kernel for ML-KEM. Hardware implementations of NTT present specific side-channel attack surfaces.

**NTT Butterfly Operations:**
- Each butterfly performs a multiply-accumulate on polynomial coefficients
- Secret coefficients are operands to the butterfly — their values influence power consumption and EM emissions
- Single-trace attacks may recover coefficients if the butterfly lacks countermeasures
- Multi-trace DPA on butterfly operations targets intermediate values in the modular reduction step

**NTT Security Requirements:**
- Constant-time execution: butterfly operation must complete in the same number of cycles regardless of operand values
- Constant-power: power consumption must not correlate with coefficient values (requires masking or hiding)
- No early termination: modular reduction must not short-circuit on zero or small values
- Shuffled execution order: randomize the order of butterfly operations within each NTT stage

**Hardware NTT Unit Threat Model:**

| Threat | Attack Type | Target | Countermeasure |
|--------|-----------|--------|---------------|
| DPA on butterfly multiply | Power SCA | Secret coefficients in multiply step | First-order Boolean masking on NTT inputs |
| SPA on NTT stage pattern | Power SCA | NTT stage structure reveals polynomial degree | Constant execution pattern regardless of input |
| EM analysis on modular reduction | EM SCA | Intermediate reduction values | Randomized reduction algorithm |
| Fault injection on NTT output | FI | Skip NTT to output identity transform | Redundant NTT computation with comparison |
| Cache-timing on coefficient access | Microarch SCA | Memory access pattern reveals coefficient values | Linear (non-table-based) NTT implementation |

### Decapsulation Failure Oracle

ML-KEM uses a Fujisaki-Okamoto (FO) transform for CCA security. The decapsulation includes a re-encryption check that must not leak whether decapsulation succeeded or failed.

**Failure Oracle Threats:**
- Timing difference between successful and failed decapsulation reveals validity of ciphertexts
- Power profile difference in the re-encryption comparison step
- Fault injection to skip the FO validity check, converting CCA-secure scheme to CPA-only

**Countermeasures:**
- Constant-time comparison in the FO transform — both paths (valid/invalid) must execute identical operations
- Implicit rejection: on failure, derive shared secret from secret key and ciphertext (not from decryption result) — this is mandatory per FIPS 203
- Hardware implementation must ensure the branch (valid vs. implicit reject) does not affect observable behavior

### Side-Channel on Polynomial Operations

**Polynomial multiplication (NTT-based):**
- Secret polynomial `s` is transformed via NTT before pointwise multiplication
- Each NTT coefficient of `s` is a target for power/EM SCA
- Pointwise multiplication `a * s` in NTT domain leaks `s` if `a` is known

**Polynomial compression/decompression:**
- Compression rounds coefficients — rounding operation may leak coefficient magnitude
- Decompression is not security-sensitive (operates on public data)

**Sampling (CBD — Centered Binomial Distribution):**
- CBD sampling from seed must use constant-time operations
- Random byte consumption rate must not vary with output distribution

---

## FIPS 204 — ML-DSA (Module-Lattice-Based Digital Signature Algorithm)

Formerly CRYSTALS-Dilithium. Standardized August 2024.

### Signing Side-Channels

ML-DSA signing involves multiple rejection sampling loops and operations on secret key components.

**Key Operations in Signing:**
1. Expand mask vector `y` from nonce `rho'` and counter `kappa`
2. Compute `w = A * y` (NTT-based polynomial multiplication)
3. HighBits extraction and hashing
4. Compute `z = y + c * s1` (response vector)
5. Rejection check: if `z` or hint exceeds bounds, restart from step 1

**Signing SCA Threats:**

| Operation | Threat | Impact |
|-----------|--------|--------|
| `c * s1` multiplication | DPA on the product of challenge and secret key | Secret key `s1` recovery |
| `c * s2` multiplication | DPA on challenge times second secret component | Secret key `s2` recovery |
| NTT of secret vectors | Same NTT threats as ML-KEM | Secret vector recovery |
| Rejection loop count | Timing side-channel reveals information about intermediate values | Partial secret recovery over many signatures |

### Nonce Generation Security

**Critical requirement:** The signing nonce `rho'` must be generated with fresh entropy or deterministically from the secret key and message. Nonce reuse or predictability completely breaks ML-DSA security.

**Hardware Requirements:**
- Dedicated entropy source (TRNG) meeting NIST SP 800-90B requirements
- If deterministic nonce: SHAKE-256 computation must be side-channel protected (secret key is input)
- Nonce must not be stored in accessible memory after use
- Nonce generation must be atomic — no partial nonce exposure on fault/interrupt

### Rejection Sampling Leakage

ML-DSA signing uses rejection sampling: if the response vector exceeds bounds, the entire signing attempt is discarded and restarted with a new nonce.

**Leakage Vectors:**
- **Timing:** Number of rejection iterations leaks information about the secret key. Average ~4-7 attempts per signature, but the distribution depends on `s1`, `s2`.
- **Power profile:** Each rejection loop iteration has a distinguishable power profile. The number of iterations is observable.
- **Cache state:** If NTT tables are evicted between attempts, cache reload pattern reveals iteration count.

**Countermeasures:**
- Constant-time rejection: always execute a fixed maximum number of iterations, selecting the first valid result
- Alternatively: mask the timing by adding random delays (less effective than constant iteration count)
- Do not short-circuit: even after finding a valid signature, continue processing remaining iterations (discarding results)

---

## Hardware Acceleration Considerations

### Dedicated NTT Unit Security

**Architecture Options:**

| Architecture | Performance | SCA Resistance | Area |
|-------------|-------------|----------------|------|
| Iterative butterfly (1 butterfly unit) | Low | Easier to mask (one unit) | Small |
| Parallel butterfly (N butterfly units) | High | Must mask all N units; leakage from any one compromises security | Large |
| Pipelined NTT (staged butterflies) | Medium-High | Pipeline registers hold intermediate secret values; more leakage points | Medium |

**Security Requirements for NTT Unit:**
- All butterfly multipliers must implement identical masking
- Pipeline flush on context switch (prevent secret coefficient leakage to next operation)
- Dedicated NTT memory (coefficient storage) must be zeroized between operations
- NTT twiddle factors (roots of unity) are public — no masking needed for these
- Intermediate NTT results are secret — must not be exposed via debug or DMA

### Entropy Source Requirements

**For ML-KEM Key Generation:**
- TRNG must provide at least 256 bits of entropy for seed `d` and randomness `z`
- Entropy source must meet NIST SP 800-90B requirements
- Health tests must run continuously during key generation
- Seed expansion (SHAKE-based) from TRNG output to full polynomial must be constant-time

**For ML-DSA Nonce Generation:**
- In randomized mode: 256 bits fresh entropy per signature
- In deterministic mode: SHAKE computation over secret key and message must be SCA-protected
- TRNG failure during signing must abort — not fall back to deterministic mode without explicit policy

### Constant-Time Implementation Requirements

**Operations That Must Be Constant-Time:**

| Operation | Why | Common Pitfall |
|-----------|-----|---------------|
| NTT butterfly | Processes secret coefficients | Variable-time modular reduction |
| Polynomial comparison (FO transform) | Compares secret decryption result | Early-exit on first mismatch |
| Rejection sampling loop | Iteration count leaks secret info | Loop termination on first valid result |
| Barrett/Montgomery reduction | Intermediate values correlate with input | Conditional subtraction at end |
| Coefficient encoding/compression | Rounding depends on coefficient value | Lookup tables with variable access time |
