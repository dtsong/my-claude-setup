# Abstraction Methodology — 4-Layer Translation Rules

## Contents

- [Purpose](#purpose)
- [4-Layer Process Overview](#4-layer-process-overview)
- [Layer 0 -> Layer 1: Technical to Security Impact](#layer-0---layer-1-technical-to-security-impact)
  - [Translation Operations](#translation-operations)
- [Layer 1 -> Layer 2: Security Impact to Business Risk](#layer-1---layer-2-security-impact-to-business-risk)
- [Layer 2 -> Layer 3: Business Risk to Executive Action](#layer-2---layer-3-business-risk-to-executive-action)
- [Vocabulary Calibration](#vocabulary-calibration)
  - [Technology Domain to Business Language](#technology-domain-to-business-language)
  - [Severity Terms by Audience](#severity-terms-by-audience)

## Purpose

Detailed translation rules for the 4-layer abstraction process that transforms technical security findings into executive communication. Includes per-layer operations and vocabulary calibration.

**Primary consumer:** executive-brief-skill (SKILL.md Layer 0-3 translation)

---

## 4-Layer Process Overview

```
Layer 0 -> Layer 1 -> Layer 2 -> Layer 3
(What)    (So what)  (So what   (What to
           for       for the    do about
           security) business)  it)
```

---

## Layer 0 -> Layer 1: Technical to Security Impact

**Input:** Raw technical finding from upstream entity.
**Output:** Security impact statement comprehensible to someone who understands security concepts but not hardware implementation.

### Translation Operations

**1. Replace hardware-specific nouns with security-domain nouns:**

| Hardware Term | Security Domain Term |
|---|---|
| TLP (Transaction Layer Packet) | Bus transaction / protocol message |
| FSM (Finite State Machine) | Protocol state management |
| CDI (Compound Device Identifier) | Platform identity token |
| UDS (Unique Device Secret) | Hardware root key |
| TDI (TEE Device Interface) | Secure device connection |
| SVA assertion | Hardware verification check |
| RTL module | Hardware design component |
| PCIe link | Device interconnect |
| CXL fabric | Memory interconnect fabric |
| Capability (CHERI) | Hardware access permission |
| OTP fuse | Permanent hardware configuration |

**2. Specify the attacker profile:**

| Technical Prerequisite | Security Language |
|---|---|
| Physical access to PCIe bus | Attacker with physical access to hardware |
| Compromised firmware | Attacker who has compromised device firmware |
| Adjacent VM/tenant | Co-located attacker on shared infrastructure |
| Debug port access | Attacker with debug interface access |

**3. State the security property violated:** Isolation, Authenticity, Confidentiality, Integrity, Freshness, Access Control.

**4. State the scope of impact:** What is and is NOT affected.

---

## Layer 1 -> Layer 2: Security Impact to Business Risk

**1. Map security impact to business assets:**

| Security Impact | Business Asset at Risk |
|---|---|
| Data disclosure | Customer data, IP, trade secrets |
| Identity forgery / auth bypass | Platform trust, supply chain integrity |
| Integrity violation | Product reliability, safety-critical functions |
| Isolation failure | Multi-tenant SLA, service guarantees |
| Availability disruption | Service uptime, revenue |
| Compliance gap | Regulatory standing, certifications |

**2. Quantify exposure scope:** Product families, customers, market segments, revenue exposure.

**3. Reference applicable regulations:**

| SoC Family | Likely Frameworks |
|---|---|
| Compute (Server) | FIPS 140-3, FedRAMP, SOC 2, PCI DSS |
| Automotive | ISO 21434, ISO 26262, UNECE R155/R156 |
| Client | TCG TPM 2.0, FIPS 140-3 |
| Data Center | FIPS 140-3, PCI DSS, CSA STAR, SOC 2 |

**4. Avoid catastrophizing:** Factual consequences only.

---

## Layer 2 -> Layer 3: Business Risk to Executive Action

**1. Frame action in imperative form:** "Prioritize [fix] in [milestone]", "Implement [control] before [event]", "Accept risk with compensating control [description]"

**2. Attach timeline to milestones:** Silicon respin dates, FW releases, product launches, certification deadlines.

**3. Estimate cost:**

| Complexity | Typical Estimate | Example |
|---|---|---|
| Minor RTL fix | 1-2 engineer-weeks | Register lock fix, FSM guard |
| Protocol fix | 2-4 engineer-weeks | State machine redesign |
| Architecture change | 4-8 engineer-weeks | New security IP block |
| Full subsystem redesign | 8-16+ engineer-weeks | Security subsystem overhaul |
| Firmware update | 1-2 engineer-weeks | Configuration change |

Always mark estimates `[ESTIMATED]` unless engineer provides actual data.

**4. State deferral consequence** in business terms, specific: "Cannot launch CXL pooling feature securely" not "Bad things may happen."

---

## Vocabulary Calibration

### Technology Domain to Business Language

| Domain | Board-Level | CISO-Level | Program-Level |
|---|---|---|---|
| Confidential AI / TEE | Data protection for AI on shared infra | VM isolation and memory encryption | TEE attestation, memory encryption engine |
| TDISP / CXL | Secure device connectivity | PCIe device authentication | TDISP state machine, IDE stream setup |
| Supply Chain | Hardware authenticity verification | Firmware attestation | SPDM measurement, DICE identity chain |
| Secure Boot / DICE | Trusted startup and identity | Boot chain measurement | CDI derivation, alias certificates |
| CHERI | Hardware memory safety | Capability-based access control | Capability encoding, tag bits |

### Severity Terms by Audience

| Severity | Board | CISO | Program |
|---|---|---|---|
| Critical | Requires immediate executive attention | Active exploitation path — remediate now | P0 — block release |
| High | Significant risk requiring near-term action | Feasible attack — remediate this quarter | P1 — target next milestone |
| Medium | Manageable risk requiring planned attention | Limited exposure — schedule remediation | P2 — next available window |
| Low | Tracked risk, no immediate action | Theoretical — monitor and track | P3 — fix opportunistically |
