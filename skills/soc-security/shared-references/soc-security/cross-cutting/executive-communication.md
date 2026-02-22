# Executive Communication — Cross-Cutting Reference

## Purpose

This reference provides the audience calibration framework and communication patterns for translating hardware security findings into executive-level briefs. It defines the 4-layer abstraction model, audience profiles, vocabulary calibration, and structural templates used by the executive-brief-skill.

**Primary consumer:** executive-brief-skill
**Secondary consumers:** All skills (when generating user-facing summaries)

---

## 4-Layer Abstraction Model

Every security finding exists at four levels of abstraction. The executive-brief-skill must translate findings upward through these layers, maintaining accuracy at each step.

```
Layer 1: Raw Technical         "TDISP state machine allows CONFIG→RUN transition
                                without IDE stream active (REQ-TDISP-007 violation)"

Layer 2: Security Impact       "A device can be assigned to a confidential VM without
                                link encryption, exposing data in transit to physical
                                interposer attacks"

Layer 3: Business Risk         "Confidential customer data processed on shared GPU
                                accelerators could be intercepted by a physical attacker
                                with data center access, potentially causing regulatory
                                violation and customer trust breach"

Layer 4: Executive Action      "Recommend: Block GPU passthrough to confidential VMs
                                until IDE enforcement is verified (2-week fix).
                                Risk: High — affects data center tenant isolation guarantee"
```

### Translation Rules

| Transition | Rule | Common Error |
|---|---|---|
| Layer 1 → Layer 2 | Name the security property violated and the attack enabled | Stopping at the technical description without naming the consequence |
| Layer 2 → Layer 3 | Quantify business impact: revenue, reputation, compliance, safety | Using security jargon instead of business language |
| Layer 3 → Layer 4 | Provide specific action, owner, timeline, and risk rating | Vague recommendations ("improve security") without specifics |

### Accuracy Preservation

Each upward translation must be traceable to the layer below. If Layer 4 says "High risk," there must be a Layer 3 business impact justification. If Layer 3 says "regulatory violation," there must be a Layer 2 security impact that maps to a specific regulation. No layer may introduce claims not supported by the layer below.

---

## Audience Profiles

### Board-Level (Directors, Non-Technical Executives)

| Aspect | Guidance |
|---|---|
| **Abstraction** | Layer 4 only. Layer 3 in appendix if requested. |
| **Vocabulary** | Zero technical terms. No acronyms without business context. |
| **Length** | 1 page maximum. 3-5 bullet points. |
| **Focus** | Strategic risk posture, competitive impact, regulatory exposure, investment needed |
| **Avoid** | Any technical detail. Standard names. Architecture descriptions. |
| **Example phrasing** | "Our chip's tenant isolation guarantee has a gap that could expose customer AI data. A targeted fix is in progress with a 2-week timeline. Until resolved, we recommend limiting multi-tenant deployments." |

### CISO-Level (Chief Information Security Officer, VP Security)

| Aspect | Guidance |
|---|---|
| **Abstraction** | Layer 4 primary. Layer 3 supporting. Layer 2 in appendix. |
| **Vocabulary** | Security concepts without hardware implementation details. Standard names acceptable with brief context. |
| **Length** | 2-3 pages. Findings table with severity/status/owner. |
| **Focus** | Risk ratings, compliance gaps, mitigation status, resource allocation, timeline |
| **Avoid** | RTL signal names. SVA assertion details. Register addresses. |
| **Example phrasing** | "Finding: TDISP device assignment does not enforce link encryption prerequisite. Impact: Device passthrough to confidential VMs lacks data-in-transit protection, creating a FIPS 140-3 gap for encrypted link requirement. Severity: High. Mitigation: Enforce IDE stream check in TDISP state machine (verification-scaffold has SVA template). ETA: 2 weeks. Owner: RTL team." |

### Program-Level (Security Architects, Engineering Managers)

| Aspect | Guidance |
|---|---|
| **Abstraction** | Layer 4 + Layer 3 + Layer 2. Layer 1 in appendix. |
| **Vocabulary** | Full technical vocabulary. Standard names and requirement IDs. |
| **Length** | 5-10 pages. Detailed findings with traceability. |
| **Focus** | Technical findings, root cause, specific remediation steps, verification evidence needed, standards requirements |
| **Acceptable** | Requirement IDs (REQ-TDISP-007), SVA template references, RTL module names |
| **Example phrasing** | "REQ-TDISP-007 violation: TDI state machine transitions LOCK→RUN without checking ide_stream_active signal. Root cause: Missing guard condition in tdisp_fsm.sv:L234. Fix: Add ide_active to LOCK→RUN transition guard. Verification: sva_tdisp_state_machine template assertion assert_ide_before_run will catch regression. Compliance: Resolves FIPS 140-3 gap for encrypted channel requirement." |

---

## Vocabulary Calibration

### Terms to Always Translate for Non-Technical Audiences

| Technical Term | Board Translation | CISO Translation |
|---|---|---|
| TDISP state machine | Device assignment security check | Device security protocol |
| IDE stream | Link encryption | Encrypted connection between chip and device |
| DICE CDI derivation | Chip identity verification at startup | Boot-time identity chain |
| SPDM measurement | Firmware health check | Device firmware attestation |
| SVA assertion | Automated security check | Hardware verification test |
| CXL TSP partition | Memory isolation between customers | Multi-tenant memory protection |
| CHERI capability | Hardware-enforced access boundary | Memory safety enforcement |
| OTP fuse | Permanent hardware configuration | One-time security setting |
| Bus firewall | Internal data access barrier | On-chip access control |
| Side-channel | Physical information leakage | Data leakage through hardware behavior |

### Severity Taxonomy

| Severity | Technical Criteria | Business Language |
|---|---|---|
| **Critical** | Exploitable by remote attacker; no mitigation available; affects trust root | "Immediate action required — fundamental security guarantee broken" |
| **High** | Exploitable with physical access or elevated privilege; mitigation available but not yet deployed | "Near-term action required — significant security gap with known fix" |
| **Medium** | Exploitable under constrained conditions; partial mitigation in place | "Planned remediation — security improvement opportunity with moderate risk" |
| **Low** | Theoretical risk; no known exploit; defense-in-depth covers the gap | "Tracked for future improvement — low residual risk with current mitigations" |

### Trend Indicators

| Indicator | Meaning | When to Use |
|---|---|---|
| **Improving** (↑) | Gap count decreasing, mitigations being deployed, verification coverage increasing | Positive progress since last review |
| **Stable** (→) | No significant change in risk posture | Steady state between reviews |
| **Degrading** (↓) | New gaps discovered, mitigations delayed, coverage decreasing | Negative trend requiring attention |

---

## BLUF-First Template Structure

All executive briefs must follow BLUF (Bottom Line Up Front) structure:

### Template

```
# [Title — descriptive, not alarming]

## Bottom Line
[1-3 sentences: What is the situation? What action is recommended? What is the risk?]

## Risk Summary
| Finding | Severity | Status | Owner | ETA |
|---------|----------|--------|-------|-----|
| ...     | ...      | ...    | ...   | ... |

## Key Findings
[Numbered findings at appropriate abstraction layer for audience]

## Recommendations
[Specific, actionable recommendations with owners and timelines]

## Appendix (optional)
[Supporting detail at one layer more technical than the main body]
```

---

## What to Include vs. Exclude Per Audience Level

| Content | Board | CISO | Program |
|---|---|---|---|
| Risk ratings | Yes | Yes | Yes |
| Business impact | Yes | Yes | Yes |
| Standard names | No | Brief context | Full reference |
| Requirement IDs | No | No | Yes |
| SVA assertion names | No | No | Appendix |
| RTL module names | No | No | Appendix |
| Mitigation technical details | No | Summary | Full detail |
| Compliance gap specifics | Revenue/reputation impact | Standard + clause | Full traceability |
| Verification evidence | No | Summary status | Full coverage report |
| Trend arrows | Yes | Yes | Yes |
| Threat catalog IDs | No | No | Yes |

---

## Traceability Requirements

Every finding in an executive brief must trace back to a source:

```
Finding → Threat Model Finding ID (or Compliance Gap ID)
       → Threat Catalog Entry (PHYS-xxx, FW-xxx, etc.)
       → Standards Requirement (REQ-xxx)
       → Verification Status (Tier 1/2/3, Verified/Gap)
```

This trace is maintained in the brief's metadata (not necessarily visible in the document body for Board audiences, but available for audit).

### Example Traceability Chain

```
Executive Finding: "GPU device assignment lacks encryption enforcement"
  ← Threat Model: TM-COMPUTE-007 (TDISP IDE bypass)
  ← Threat Catalog: INTF-003 (TDISP handshake bypass)
  ← Standard: REQ-TDISP-007 (IDE stream before RUN)
  ← Verification: sva_tdisp_state_machine.assert_ide_before_run — FAIL (not yet bound)
```

---

*[FROM TRAINING] Communication patterns are based on general security consulting best practices. Adjust for organizational culture and communication norms. Last verified: 2026-02-13.*
