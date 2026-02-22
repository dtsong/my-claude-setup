# SCA Assessment Methodology — Combined Attacks, Leakage Detection & Trace Requirements

## Contents

- [4. Combined Attack Methodology](#4-combined-attack-methodology)
  - [4.1 Combined SCA + Fault Injection](#41-combined-sca--fault-injection)
  - [4.2 Template Attacks](#42-template-attacks)
- [5. Leakage Detection Methodology](#5-leakage-detection-methodology)
  - [5.1 Test Vector Leakage Assessment (TVLA)](#51-test-vector-leakage-assessment-tvla)
  - [5.2 Non-Specific TVLA (Fixed vs. Random)](#52-non-specific-tvla-fixed-vs-random)
  - [5.3 Specific TVLA](#53-specific-tvla)
  - [5.4 Statistical Significance](#54-statistical-significance)
- [6. Trace Collection Requirements](#6-trace-collection-requirements)
  - [6.1 Sampling Rate](#61-sampling-rate)
  - [6.2 Trace Alignment](#62-trace-alignment)
  - [6.3 Number of Traces](#63-number-of-traces)
  - [6.4 Measurement Setup Quality](#64-measurement-setup-quality)

Covers combined attack methodology, TVLA leakage detection, template attacks, and trace collection requirements.

---

## 4. Combined Attack Methodology

### 4.1 Combined SCA + Fault Injection

**Objective:** Use fault injection to disable or weaken countermeasures, then apply SCA.

**Examples:** Glitch RNG to fix mask value then apply first-order DPA; fault masking logic to reduce order; disable sensor by faulting its config register then perform SCA.

**Procedure:** (1) Identify countermeasure components (RNG, sensor, redundancy). (2) Apply fault injection to disable/weaken. (3) Verify countermeasure is disabled. (4) Apply standard SCA on weakened implementation.

**JIL scoring:** Combined attacks inherit higher equipment/expertise scores from both components.

### 4.2 Template Attacks

**Objective:** Build statistical templates from profiling device, classify target device traces.

**Profiling phase (clone device with known key):** Collect traces for all key byte values, compute mean and covariance at POIs.

**Attack phase (target device):** Collect small number of traces (potentially 1), evaluate likelihood per key hypothesis via multivariate Gaussian, select maximum likelihood key.

**Statistical framework:** P(trace | key=k) = N(mean_k, Cov_k); key* = argmax_k P(trace|key=k). POI selection via SOSD or PCA.

**Trace requirements:** Profiling: 1,000-10,000 per key value. Attack: 1-10 traces (ideal conditions).

**Limitations:** Requires clone device; sensitive to device-to-device variation; POI selection critical.

---

## 5. Leakage Detection Methodology

### 5.1 Test Vector Leakage Assessment (TVLA)

**Purpose:** Determine whether an implementation exhibits statistically detectable leakage without full key recovery. Primary metric for ISO 17825 compliance.

### 5.2 Non-Specific TVLA (Fixed vs. Random)

**Procedure:** (1) Collect two sets: fixed set (same plaintext repeatedly), random set (different random plaintexts). (2) Compute Welch's t-test at each time sample: t = (mean_fixed - mean_random) / sqrt(var_fixed/N_fixed + var_random/N_random). (3) Compare |t| against threshold.

**Threshold:** |t| > 4.5 = statistically significant leakage (ISO 17825).

**Interpretation:** |t| < 4.5 at all points: PASS (no detectable first-order leakage). |t| > 4.5 at any point: FAIL. PASS does not guarantee security — higher-order leakage may exist.

**Trace requirements:** Minimum 10,000 per set (20,000 total). Recommended 100,000-1,000,000 for high confidence.

### 5.3 Specific TVLA

Partition traces based on a specific bit of a chosen intermediate value. Detects leakage at specific key-dependent computation points. Requires implementation knowledge.

### 5.4 Statistical Significance

**Multiple testing:** TVLA tests thousands of time points simultaneously. Expected false positives at |t| > 4.5 with 10,000 tests: ~0.07. Threshold of 4.5 accounts for multiple testing.

**Confidence levels:**

| Scenario | Interpretation |
|----------|---------------|
| |t| < 4.5, N > 100,000 | High confidence: no detectable first-order leakage |
| |t| < 4.5, N < 10,000 | Low confidence: insufficient traces |
| |t| > 4.5, localized | Leakage present at specific operations |
| |t| > 4.5, widespread | Significant leakage throughout — no effective countermeasure |
| |t| > 4.5, N < 1,000 | Verify with more traces — may be noise |

---

## 6. Trace Collection Requirements

### 6.1 Sampling Rate

| Target Clock | Minimum | Recommended |
|-------------|---------|-------------|
| 10 MHz | 20 MS/s | 100 MS/s |
| 50 MHz | 100 MS/s | 500 MS/s |
| 100 MHz | 200 MS/s | 1 GS/s |
| 200 MHz | 400 MS/s | 2 GS/s |
| 1 GHz | 2 GS/s | 5-10 GS/s |

Nyquist minimum is 2x; 5-10x provides better intra-cycle resolution.

### 6.2 Trace Alignment

**Why it matters:** Misalignment reduces correlation peaks and can mask leakage. Hiding countermeasures deliberately introduce misalignment.

**Techniques:** Static trigger (GPIO sync), pattern-based (correlate reference pattern), elastic alignment (DTW), resynchronization (detect and excise random delays).

### 6.3 Number of Traces

| Attack Type | Unprotected | 1st-Order Masking | 2nd-Order Masking |
|-------------|-------------|--------------------|--------------------|
| SPA | 1-20 | 1-20 (if control-flow) | 1-20 (if control-flow) |
| DPA (1st-order) | 200-1,000 | Not effective | Not effective |
| CPA (1st-order) | 50-500 | Not effective | Not effective |
| 2nd-order CPA | N/A | 50,000-500,000 | Not effective |
| 3rd-order CPA | N/A | N/A | 1,000,000-10,000,000 |
| Template (profiling) | 1,000-10,000/key | Same | Same |
| Template (attack) | 1-10 | 10-100 | 100-1,000 |
| TVLA (non-specific) | 10,000-1,000,000 | Same | Same |

Order-of-magnitude estimates. Actual counts depend on SNR, alignment, and implementation.

### 6.4 Measurement Setup Quality

| Indicator | Good | Acceptable | Poor |
|-----------|------|------------|------|
| SNR | > 10 dB | 3-10 dB | < 3 dB |
| Trigger jitter | < 1 ns | 1-10 ns | > 10 ns |
| Alignment | < 0.1 clock cycles | 0.1-1 cycles | > 1 cycle |
| Vertical resolution | 12+ bits | 8-12 bits | < 8 bits |
| Bandwidth vs. clock | > 5x | 2-5x | < 2x |
