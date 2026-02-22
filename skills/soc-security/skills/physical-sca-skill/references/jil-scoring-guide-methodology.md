# JIL Attack Potential Scoring — Methodology & Factor Definitions

---

## 1. Overview

The JIL attack potential framework quantifies the practical difficulty of mounting an attack by scoring five independent factors. The sum of these scores determines the attack's rating, which maps to a Common Criteria resistance level. Higher total scores indicate more difficult attacks that require greater resources.

**Five scoring categories:**
1. Elapsed Time (0-19)
2. Expertise (0-8)
3. Knowledge of TOE (0-11)
4. Window of Opportunity / Access (0-10)
5. Equipment (0-9)

**Total score** = sum of all five categories.

---

## 2. Scoring Categories

### 2.1 Elapsed Time

The total time taken by the attacker to identify the vulnerability, develop the attack, and execute it successfully.

| Score | Elapsed Time | Description |
|-------|-------------|-------------|
| 0 | < 1 day | Attack can be identified and executed within hours |
| 1 | < 1 week | Attack requires a few days of effort |
| 2 | < 2 weeks | Attack requires roughly one to two weeks |
| 4 | < 1 month | Attack requires several weeks of development and execution |
| 7 | < 2 months | Attack requires one to two months |
| 10 | < 3 months | Attack requires up to a quarter |
| 13 | < 4 months | Attack requires several months |
| 15 | < 5 months | Attack requires close to half a year |
| 17 | < 6 months | Attack approaches half a year of effort |
| 19 | >= 6 months | Attack requires six months or more |

**SCA-specific guidance:**
- SPA on unprotected RSA: typically 0-1 (hours to identify pattern)
- First-order CPA on unprotected AES: typically 1-4 (days to set up and execute)
- Second-order CPA on masked AES: typically 7-13 (weeks to months for trace collection and analysis)
- Template attack development (profiling + attack): typically 4-10 (weeks to months)
- DFA via voltage glitch: typically 2-7 (days to weeks for glitch parameter characterization)
- Laser FI with reverse engineering: typically 13-19 (months for decapping, RE, and targeting)

---

### 2.2 Expertise

The level of technical skill required by the attacker.

| Score | Expertise Level | Description |
|-------|----------------|-------------|
| 0 | Layperson | No specialized knowledge; follows published tutorial |
| 3 | Proficient | Familiar with the target type; undergraduate-level technical skills |
| 6 | Expert | Deep knowledge of SCA techniques, signal processing, and cryptographic algorithms; can develop novel attack variations |
| 8 | Multiple experts | Attack requires collaboration of experts from different domains (e.g., SCA + IC reverse engineering + cryptanalysis) |

**SCA-specific guidance:**
- Running an off-the-shelf CPA attack with commercial tools: 3 (Proficient)
- Developing custom higher-order analysis with novel leakage models: 6 (Expert)
- Combined laser FI + EM analysis requiring RE and custom tooling: 8 (Multiple experts)
- SPA on obvious key-dependent branches: 3 (Proficient)
- Template attack with custom POI selection and portability analysis: 6 (Expert)

---

### 2.3 Knowledge of TOE (Target of Evaluation)

The level of knowledge about the target implementation required to mount the attack.

| Score | Knowledge Level | Description |
|-------|----------------|-------------|
| 0 | Public | Only public information needed (datasheets, published specs) |
| 3 | Restricted | Non-public information that can be obtained through authorized channels (e.g., NDA documentation, reference designs) |
| 7 | Sensitive | Internal design details (RTL, layout, proprietary countermeasure details) |
| 11 | Critical | Full implementation details including secret design elements, proprietary algorithms, or unpublished countermeasure parameters |

**SCA-specific guidance:**
- CPA on standard AES implementation (publicly known algorithm): 0-3
- Attack requiring knowledge of specific masking scheme and share representation: 7
- Attack requiring knowledge of proprietary countermeasure timing and threshold parameters: 7-11
- DFA requiring knowledge of internal pipeline stages: 3-7
- Laser FI requiring detailed IC layout knowledge: 7-11

---

### 2.4 Window of Opportunity / Access

The level of physical or logical access to the target device required, and any time constraints on that access.

| Score | Access Level | Description |
|-------|-------------|-------------|
| 0 | Unlimited | Unrestricted access; no time limit; attacker owns the device |
| 1 | Large | Extended access possible (days/weeks); device can be taken to lab |
| 4 | Moderate | Limited access sessions; device must be returned; moderate time window |
| 7 | Small | Brief physical access; constrained environment; limited trace collection |
| 10 | None | No direct physical access possible; attack must be remote or via a proxy |

**SCA-specific guidance:**
- Lab evaluation (attacker has purchased evaluation board): 0 (Unlimited)
- Attacker has temporary physical access to deployed device: 4-7
- Secure facility with limited physical access windows: 7
- Remote timing attack (no physical access): may not apply to physical SCA
- Key stored in HSM with anti-tamper: access score depends on tamper resistance

**Note:** For physical SCA, the access score also accounts for whether the device can be decapped (increases access difficulty if tamper-resistant packaging is present).

---

### 2.5 Equipment

The type and cost of equipment required to mount the attack.

| Score | Equipment Level | Description |
|-------|----------------|-------------|
| 0 | Standard | Commonly available equipment (multimeter, basic oscilloscope, logic analyzer) |
| 2 | Specialized | Specialized SCA equipment readily available for purchase (ChipWhisperer, mid-range oscilloscope with 1+ GS/s) |
| 4 | Bespoke | Custom-built or highly specialized equipment (high-end oscilloscope > 5 GS/s, custom EM probes, commercial SCA platforms like Riscure Inspector) |
| 6 | Advanced bespoke | Expensive, purpose-built equipment (laser fault injection station, FIB, high-resolution EM scanning) |
| 9 | Multiple advanced bespoke | Multiple pieces of advanced equipment used in combination (laser FI station + EM scanning + custom FPGA-based data acquisition) |

**SCA-specific guidance:**
- Basic timing attack with standard equipment: 0
- First-order CPA with ChipWhisperer: 2
- CPA with commercial SCA platform (Inspector, Langer): 4
- EMFI with commercial injector: 4
- Laser fault injection station: 6
- Full SCA lab (laser FI + EM scanning + oscilloscope + positioning stage): 9
