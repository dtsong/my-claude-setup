## Board-Level Audience

**Profile:** Non-technical directors and C-suite. Evaluate risk in terms of shareholder impact, regulatory liability, competitive position.

### Vocabulary Guide

| Technical Term | Board Translation |
|---|---|
| Threat model | Security risk assessment |
| Vulnerability | Security weakness |
| CVE / exploit | Known security issue |
| Silicon respin | Chip redesign (significant cost and schedule impact) |
| SVA assertion | Hardware verification check |
| TDISP / CXL / DICE / SPDM | [Full expansion on first use, then avoid] |
| Compliance gap | Regulatory requirement not yet met |
| RTL | Chip design |
| Side-channel attack | Data leak through physical measurement |
| Trust domain | Isolated security boundary |

### Depth Calibration

- BLUF: 3-5 sentences maximum
- Risk table: High/Medium/Low with trend arrows. No more than 10 rows.
- Body: 1-2 paragraphs per critical finding. Focus on business risk and action.
- Technical detail: Appendix only
- Verification status: "Assessment confidence: X% verified, Y% under review"

### Action Framing

- "Approve budget for..." / "Accept risk of deferring..."
- Investment-style language: cost, return, risk-adjusted timeline
- Comparative framing only if factual

## CISO-Level Audience

**Profile:** Security executives. Comfortable with threat models, risk frameworks, compliance. Need context to defend positions to board and prioritize across portfolio.

### Vocabulary Guide

| Technical Term | CISO Translation |
|---|---|
| TDISP handshake bypass | Device authentication bypass in PCIe security protocol |
| CDI derivation error | Platform identity chain broken at boot |
| CXL TSP partition | Hardware memory isolation for multi-tenant |
| CHERI capability | Hardware-enforced memory access control |
| SVA assertion | Formal hardware verification property |
| FSM state machine | Protocol state management |
| RTL module | Hardware design component |

### Depth Calibration

- BLUF: 5-8 sentences. Include highest-severity items and overall posture.
- Risk table: Full table with trend arrows and verification status.
- Body: 2-4 paragraphs per finding. Include security context and compliance implications.
- Technical detail: Summarized in body; full detail in appendix
- Verification status: Per-finding with [HV]/[TV]/[LA] badges

### Action Framing

- "Remediate before [milestone]..." / "Track as accepted risk with compensating control..."
- Security program language: risk register, compensating controls, residual risk
- Compliance language: "Required for [FIPS/ISO/SOC2] certification"

## Program-Level Audience

**Profile:** Engineering managers, security architects, technical program managers. Understand both security and hardware concepts. Need prioritization and resource allocation guidance.

### Vocabulary Guide

- Use technical terms directly. No translation needed.
- Include entity IDs for traceability (TF-2026-001, SR-2026-005, etc.)
- Reference specific RTL modules, verification approaches, and engineering tasks

### Depth Calibration

- BLUF: Full technical summary with prioritized action list
- Risk table: Full table with verification tier and effort estimates
- Body: Full detail per finding, Layer 0 and Layer 2 together
- Technical detail: In body, not just appendix
- Verification status: Per-finding with specific method and coverage

### Action Framing

- "Assign [N] engineer-weeks to [module] for [specific fix]..."
- Sprint/milestone language: "Target Q2 respin for critical items"
- Resource allocation: specific team, module, verification approach
