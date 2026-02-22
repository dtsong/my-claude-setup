# SCA Assessment Methodology — Power, EM & Fault Analysis

## Contents

- [1. Power Analysis Methodology](#1-power-analysis-methodology)
  - [1.1 Simple Power Analysis (SPA)](#11-simple-power-analysis-spa)
  - [1.2 Differential Power Analysis (DPA)](#12-differential-power-analysis-dpa)
  - [1.3 Correlation Power Analysis (CPA)](#13-correlation-power-analysis-cpa)
  - [1.4 Higher-Order Power Analysis](#14-higher-order-power-analysis)
- [2. Electromagnetic Analysis Methodology](#2-electromagnetic-analysis-methodology)
  - [2.1 Near-Field EM Probing](#21-near-field-em-probing)
  - [2.2 Differential EMA (DEMA)](#22-differential-ema-dema)
- [3. Fault Injection Methodology](#3-fault-injection-methodology)
  - [3.1 Voltage Glitch](#31-voltage-glitch)
  - [3.2 Clock Glitch](#32-clock-glitch)
  - [3.3 Laser Fault Injection](#33-laser-fault-injection)
  - [3.4 Electromagnetic Fault Injection (EMFI)](#34-electromagnetic-fault-injection-emfi)

Detailed methodology for power analysis (SPA/DPA/CPA/higher-order), electromagnetic analysis, and fault injection techniques.

---

## 1. Power Analysis Methodology

### 1.1 Simple Power Analysis (SPA)

**Objective:** Extract secret information from a single (or very few) power traces by identifying key-dependent operations.

**Applicable when:** Cryptographic implementation has key-dependent control flow (conditional branches, variable-time operations like square-and-multiply for RSA, conditional point doubling for ECC).

**Procedure:** (1) Acquire high-resolution power trace during crypto execution. (2) Identify operation boundaries (clock alignment, trigger sync). (3) Correlate visible patterns with key-dependent branches. (4) Extract key bits from observable pattern differences.

**Trace requirements:** Minimum 1 trace, typical 5-20 for averaging. Sampling >= 5x clock frequency, bandwidth >= 2x clock.

**Limitations:** Defeated by constant-time implementations, hiding countermeasures increase difficulty.

### 1.2 Differential Power Analysis (DPA)

**Objective:** Extract secret key bytes by statistically correlating power consumption with hypothetical intermediate values.

**Procedure:** (1) Collect N traces with known inputs. (2) For each key hypothesis k: compute predicted intermediate, partition traces by selection function bit, compute difference of means. (3) Correct key produces highest differential peak.

**Trace requirements:** Unprotected AES: 200-1,000. 1st-order masked: not applicable (use 2nd-order). Alignment critical.

**Limitations:** Defeated by first-order masking; misaligned traces reduce peaks; ghost peaks need validation.

### 1.3 Correlation Power Analysis (CPA)

**Objective:** Refine DPA using power model (Hamming weight/distance) to correlate predicted consumption with measured traces.

**Power models:**

| Model | Formula | Best for |
|-------|---------|----------|
| Hamming Weight | HW(v) = popcount(v) | CMOS devices |
| Hamming Distance | HD(v_prev, v_new) = HW(v_prev XOR v_new) | Register transitions |
| Identity | v itself | 8-bit MCUs with strong linear leakage |
| Bit Model | Single bit of v | When only one bit leaks |
| Stochastic | Linear combination with learned coefficients | Device-specific leakage |

**Procedure:** (1) Collect N traces. (2) Per key hypothesis: compute predicted intermediate, apply power model, compute Pearson correlation at each time sample. (3) Highest |r| = correct key.

**Trace requirements:** CPA with HW: 50-500. CPA with HD: 30-300 (often better). Alignment critical.

### 1.4 Higher-Order Power Analysis

**Objective:** Defeat d-th order masking using (d+1)-th order statistical analysis.

**Combination functions:** Centered product, absolute difference, normalized product.

**Procedure:** (1) Identify time points t1 (mask processing) and t2 (masked value). (2) Pre-process with combination function. (3) Apply standard CPA on combined trace.

**Trace requirements:** 2nd-order on 1st-order masking: ~50K-500K. 3rd-order: millions. Exponential scaling.

**Limitations:** Beyond 3rd order often impractical; time point identification is hard; shuffling further increases search space.

---

## 2. Electromagnetic Analysis Methodology

### 2.1 Near-Field EM Probing

**Advantages over power analysis:** Spatial selectivity isolates functional units; bypasses power filtering; multiple probe positions reveal different leakage.

**Equipment:** Near-field EM probe (H-field/E-field), LNA (30+ dB), oscilloscope, XYZ positioning stage.

**Spatial resolution:** H-field loops: ~loop diameter (50-500 um). Decapping improves resolution but increases JIL access score.

**Procedure:** (1) Position probe over crypto engine. (2) Acquire EM traces. (3) Apply CPA/DPA on EM traces. (4) Optional: XY grid scan for spatial leakage map.

### 2.2 Differential EMA (DEMA)

Same as DPA/CPA but using EM traces. Trace requirements comparable to power analysis, may need more (lower SNR) or fewer (spatial selectivity) traces. Probe positioning is critical and not always reproducible.

---

## 3. Fault Injection Methodology

### 3.1 Voltage Glitch

**Parameters:** Glitch amplitude (30-70% VDD), width (1-100 ns), offset (clock-cycle precision).

**DFA on AES (Piret-Quisquater):** Inject fault in round 8/9, collect 2 faulty ciphertexts, algebraic analysis recovers round 10 key, key schedule inversion yields master key.

**Equipment:** Voltage glitch generator (ChipWhisperer, Riscure Inspector). Countermeasure bypass via slow ramp or multi-glitch.

### 3.2 Clock Glitch

**Parameters:** Shortened clock cycle (50-90% normal), insertion point, burst count.

**Limitations:** Internal PLLs filter external glitches; requires clock distribution knowledge; less precise than voltage glitching.

### 3.3 Laser Fault Injection

**Parameters:** Wavelength (1064 nm for backside), spot size (1-5 um), ns-range pulse duration.

**Advantages:** Highest spatial precision, can target individual registers, repeatable. Requires IC decapping. JIL: high equipment/access scores.

### 3.4 Electromagnetic Fault Injection (EMFI)

**Parameters:** Pulse voltage (100-500 V), probe tip (500 um-2 mm), synchronized timing.

**Advantages:** Non-invasive (no decapping), affects larger areas, lower cost than laser. **Limitations:** Lower spatial precision (mm-range), may cause multi-bit faults, less predictable fault model.
