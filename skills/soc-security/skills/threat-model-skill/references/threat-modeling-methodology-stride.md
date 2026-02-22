# Threat Modeling Methodology — STRIDE for Hardware

## Contents

- [Purpose](#purpose)
- [Quick Reference](#quick-reference)
- [Background](#background)
- [STRIDE Category Adaptations](#stride-category-adaptations)
  - [Spoofing in Hardware Context](#spoofing-in-hardware-context)
  - [Tampering in Hardware Context](#tampering-in-hardware-context)
  - [Repudiation in Hardware Context](#repudiation-in-hardware-context)
  - [Information Disclosure in Hardware Context](#information-disclosure-in-hardware-context)
  - [Denial of Service in Hardware Context](#denial-of-service-in-hardware-context)
  - [Elevation of Privilege in Hardware Context](#elevation-of-privilege-in-hardware-context)
- [STRIDE Application Sequence](#stride-application-sequence)
- [Worked Example: STRIDE on TDISP Device Assignment Interface](#worked-example-stride-on-tdisp-device-assignment-interface)

## Purpose

STRIDE adaptation for hardware systems. Covers per-category analysis patterns and application sequence for systematic per-interface threat identification.

**Primary consumer:** threat-model-skill (Phase 3 threat identification, Framework 1)

---

## Quick Reference

| Methodology | Use When | Output | Typical Scope |
|---|---|---|---|
| STRIDE for Hardware | Systematic per-interface threat identification for any HW component | Categorized threat list with per-interface coverage | All components |

---

## Background

STRIDE (Spoofing, Tampering, Repudiation, Information Disclosure, Denial of Service, Elevation of Privilege) was developed by Microsoft for software threat modeling. Its application to hardware systems requires systematic adaptation because hardware attack vectors differ fundamentally:

- **Physical access** creates attack paths that do not exist in pure software systems
- **Side channels** (timing, power, electromagnetic) are hardware-specific information disclosure vectors
- **Fault injection** (voltage glitching, clock manipulation, laser) enables tampering with no software analog
- **Manufacturing supply chain** introduces threats before deployment
- **Immutability** of hardware means some vulnerabilities cannot be patched post-silicon

---

## STRIDE Category Adaptations

### Spoofing in Hardware Context

Software spoofing typically involves network identity or credential theft. Hardware spoofing encompasses:

**Device Identity Spoofing:** Malicious device on a shared bus presenting a legitimate device's identity; counterfeit component with cloned identification fuses or certificates; rogue endpoint responding to SPDM authentication with stolen or forged certificates.

**Authentication Bypass:** Debug authentication bypassed via known default keys or implementation flaw; SPDM mutual authentication skipped due to configuration or timing attack; boot authentication bypassed via fuse manipulation or glitch during verification.

**Attestation Forgery:** DICE attestation certificate forged by compromising an intermediate layer's signing key; PCR values manipulated before attestation report is signed; remote attestation replayed from a previously-valid state.

**Analysis Pattern:** For each external interface: (1) Identify what identity is presented. (2) Identify the authentication mechanism. (3) Can the identity be cloned or forged? (4) Can the authentication mechanism be bypassed? (5) Can a valid identity be replayed from a different context?

### Tampering in Hardware Context

**Physical Tampering:** Fault injection (voltage glitching, clock manipulation, laser), probe attacks on internal signals.

**Firmware/Configuration Tampering:** Boot image modification before authentication (TOCTOU), security configuration register modification, fuse value manipulation, anti-rollback counter manipulation.

**Protocol Tampering:** TLP modification on PCIe/CXL fabric, IDE stream key injection, SPDM message modification.

**Analysis Pattern:** For each data flow and stored asset: (1) Identify the integrity protection mechanism. (2) Can data be modified before the integrity check? (TOCTOU) (3) Can the integrity check be bypassed? (fault injection on comparator) (4) Can protection be disabled? (config register access) (5) Can protection be circumvented via alternate path? (DMA, debug port)

### Repudiation in Hardware Context

**Analysis Pattern:** For each security-relevant operation: (1) Is the operation logged? Where? Can the log be tampered with? (2) Is it timestamped with a trustworthy source? (3) Can it be performed without leaving evidence? (4) Can an authorized party deny performing it?

**Common gaps:** Debug sessions without authentication logging, fuse programming without timestamp, security configuration changes without audit trail, key provisioning without chain-of-custody record.

### Information Disclosure in Hardware Context

**Direct Access:** Cross-trust-boundary memory reads, key material readable in debug mode, firmware accessible in plaintext via SPI flash.

**Side-Channel:** Timing, power (DPA/SPA), electromagnetic, cache, thermal.

**Microarchitectural:** Speculative execution, shared resource contention, branch predictor state leaking.

**Analysis Pattern:** For each sensitive asset: (1) List all access paths (intended and unintended). (2) Assess feasibility of unintended paths. (3) For side-channel paths: physical access, equipment, skill level required. (4) For microarchitectural paths: shared resources that could leak.

### Denial of Service in Hardware Context

**Analysis Pattern:** For each interface and shared resource: (1) Can it be flooded? (2) Can the component be forced into a locked/non-functional state? (3) Can shared resources be exhausted? (4) Can the component be reset maliciously? (5) Can it be kept in a boot loop?

**HW-specific considerations:** Watchdog timer manipulation, power management attacks, clock domain crossing exploitation, thermal throttling via induced workload.

### Elevation of Privilege in Hardware Context

**Analysis Pattern:** For each privilege boundary: (1) What defines the privilege level? (2) Can it be modified directly? (3) Can a privilege transition be exploited? (4) Can debug/test modes bypass the privilege model? (5) Can a lower-privilege agent influence higher-privilege behavior? (confused deputy)

**HW-specific considerations:** JTAG/DFT mode bypassing production security, interrupt handler executing at elevated privilege with attacker-controlled context, bus master bit granting DMA beyond intended range, CHERI capability amplification.

---

## STRIDE Application Sequence

1. **Per-interface analysis:** For each external interface, evaluate all 6 STRIDE categories
2. **Per-asset analysis:** For each sensitive asset, evaluate T, I, and E
3. **Per-operation analysis:** For each security-relevant operation, evaluate S, R, and E
4. **Cross-boundary analysis:** For each trust boundary, evaluate S, T, I, and E
5. **System-level analysis:** Consider compound threats spanning multiple interfaces

---

## Worked Example: STRIDE on TDISP Device Assignment Interface

**Component:** TDISP Device Assignment Module
**Interface:** PCIe TLP interface (external, cross trust boundary)

| Category | Threat | Severity | Confidence |
|----------|--------|----------|------------|
| **S** | Rogue device responds to assignment with forged device certificate | HIGH | GROUNDED (SPDM 1.4 Section 10) |
| **T** | TLP modification during handshake changes assigned memory range | CRITICAL | GROUNDED (TDISP 1.0 Section 4.3) |
| **R** | Device assignment without logging, preventing audit | MEDIUM | INFERRED |
| **I** | IDE key material observable on fabric during key exchange | HIGH | GROUNDED (TDISP 1.0 Section 5.1) |
| **D** | Repeated invalid requests exhausting TDISP state machine | MEDIUM | INFERRED |
| **E** | Malicious device manipulates BAR to access memory outside range | CRITICAL | GROUNDED (TDISP 1.0 Section 4.4) |
