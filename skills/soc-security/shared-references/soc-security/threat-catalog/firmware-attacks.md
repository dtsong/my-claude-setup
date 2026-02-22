# Firmware Attacks — Threat Catalog

## Overview

Firmware attacks target the software executing on the SoC — boot loaders, security firmware, device firmware, and update mechanisms. These attacks can be executed remotely (via OTA update mechanisms) or locally (via debug interfaces or physical flash access).

---

## FW-001: Boot Chain Subversion

| Field | Value |
|---|---|
| **STRIDE** | Tampering (T), Elevation of Privilege (E) |
| **Description** | Attacker modifies a firmware image in the boot chain (stored in SPI flash, eMMC, or other non-volatile storage) to execute unauthorized code. If the modification targets a stage before measurement/verification, the entire DICE identity chain is compromised. |
| **Target Assets** | Boot ROM image (if mutable — should not be), bootloader images, security firmware, SPI flash contents |
| **Affected Domains** | Secure Boot / DICE, Supply Chain Security, Confidential AI / TEE |
| **Affected SoC Families** | All |
| **Preconditions** | Write access to firmware storage (physical or via exploited firmware vulnerability); bypass of signature verification (if present) |
| **Key Mitigations** | Immutable first-stage ROM (REQ-DICE-002), cryptographic signature verification at each boot stage, hardware root of trust, write-protection for flash (WP# pin, hardware write-protect) |
| **Verification Approach** | Tier 1 — SVA for signature-check-before-execute gating; Tier 2 — protocol check for complete measurement chain |
| **Related Requirements** | REQ-DICE-002, REQ-DICE-003, REQ-DICE-005 |

---

## FW-002: Firmware Rollback Attack

| Field | Value |
|---|---|
| **STRIDE** | Tampering (T), Elevation of Privilege (E) |
| **Description** | Attacker replaces current firmware with an older version that contains known vulnerabilities. The older firmware's signature may still be valid (signed by the same key), so signature verification alone does not prevent rollback. |
| **Target Assets** | Anti-rollback counters, firmware version metadata, security patch state |
| **Affected Domains** | Secure Boot / DICE, Supply Chain Security |
| **Affected SoC Families** | All — Automotive critical due to long field lifetime and OTA updates |
| **Preconditions** | Access to older signed firmware image; ability to write firmware storage; anti-rollback mechanism absent or bypassable |
| **Key Mitigations** | Monotonic anti-rollback counters in OTP fuses, Security Version Number (SVN) in DICE measurement, firmware version minimum enforcement in boot ROM |
| **Verification Approach** | Tier 1 — SVA for monotonic counter enforcement (increment-only, never decrement) |
| **Related Requirements** | REQ-DICE-011 (firmware version binding) |

---

## FW-003: Supply Chain Firmware Implant

| Field | Value |
|---|---|
| **STRIDE** | Tampering (T), Spoofing (S) |
| **Description** | Malicious firmware is inserted during manufacturing, distribution, or refurbishment. The implant may be a modified version of legitimate firmware or additional code injected into unused flash regions. The implant activates on specific triggers or provides persistent backdoor access. |
| **Target Assets** | Firmware images (bootloader, security firmware, device firmware), manufacturing provisioning flow |
| **Affected Domains** | Supply Chain Security, Secure Boot / DICE |
| **Affected SoC Families** | All — Data Center at highest risk due to complex multi-vendor supply chains |
| **Preconditions** | Access to firmware during manufacturing or distribution; ability to modify firmware without detection |
| **Key Mitigations** | SPDM measurement attestation (detect unexpected firmware), DICE identity binding (implant changes identity), firmware signing with manufacturer key, supply chain auditing, SBOM/FBOM tracking |
| **Verification Approach** | Tier 2 — protocol check for SPDM measurement mismatch detection; Tier 1 — SVA for boot-time measurement computation |
| **Related Requirements** | REQ-SPDM-004, REQ-SPDM-005, REQ-DICE-005 |

---

## FW-004: Debug-Based Code Injection

| Field | Value |
|---|---|
| **STRIDE** | Tampering (T), Elevation of Privilege (E) |
| **Description** | Attacker exploits debug interfaces (JTAG, SWD, DCI) to inject code into running firmware, modify register values, or extract secrets from memory. Debug interfaces often operate at the highest privilege level and can bypass all software security controls. |
| **Target Assets** | CPU registers, SRAM contents, security configuration registers, key material, firmware execution flow |
| **Affected Domains** | All — debug is a cross-cutting interface |
| **Affected SoC Families** | All — Automotive (OBD-II connected), Client (physical access), Compute (RMA scenarios) |
| **Preconditions** | Debug interface accessible (not permanently disabled); debug authentication bypassable or credentials known |
| **Key Mitigations** | Debug authentication FSM (challenge-response before debug enable), permanent debug disable fuse, debug access hierarchy (manufacturing/production/field), secret zeroization on debug unlock, DAP (Debug Access Port) filtering |
| **Verification Approach** | Tier 1 — SVA for debug auth FSM transitions (auth required before debug enable); SVA for secret zeroization on debug access |
| **Related Requirements** | Verification patterns `sva-templates/fsm-transitions.sv` |

---

## FW-005: OTA Update Hijacking

| Field | Value |
|---|---|
| **STRIDE** | Tampering (T), Spoofing (S) |
| **Description** | Attacker intercepts or manipulates the Over-The-Air firmware update process to deliver malicious firmware. Attack vectors include MITM on the update channel, compromised update server, or DNS hijacking to redirect update requests. |
| **Target Assets** | Update server authentication, firmware transport channel, firmware image integrity, update metadata (version, target device) |
| **Affected Domains** | Supply Chain Security, Secure Boot / DICE |
| **Affected SoC Families** | Automotive (primary — vehicle OTA), Client (OS-managed updates), Data Center (fleet updates) |
| **Preconditions** | Network position for MITM or compromised update infrastructure; target device accepts remote firmware updates |
| **Key Mitigations** | TLS for update transport, firmware image signature verification (independent of transport), anti-rollback enforcement, update metadata verification (target device, version range), dual-bank (A/B) update with verified-before-activate |
| **Verification Approach** | Tier 2 — protocol check for signature verification before firmware activation; Tier 1 — SVA for anti-rollback counter enforcement |
| **Related Requirements** | REQ-DICE-011, REQ-SPDM-004 (post-update measurement) |

---

## FW-006: Key Extraction from Firmware Images

| Field | Value |
|---|---|
| **STRIDE** | Information Disclosure (I) |
| **Description** | Attacker extracts cryptographic keys, credentials, or secrets embedded in firmware images. Keys may be hardcoded (a vulnerability), stored in cleartext in non-volatile storage, or recoverable from firmware binary analysis. Extracted keys enable impersonation, decryption, or authentication bypass. |
| **Target Assets** | Hardcoded keys, provisioning secrets, debug credentials, private keys stored in firmware sections |
| **Affected Domains** | Supply Chain Security, Secure Boot / DICE |
| **Affected SoC Families** | All — particularly devices with firmware images accessible via SPI flash dump |
| **Preconditions** | Access to firmware image (physical dump from flash, downloaded from update server, extracted from update package) |
| **Key Mitigations** | Never embed keys in firmware images; use hardware key storage (OTP fuses, PUF); derive keys at runtime from hardware roots; encrypt firmware images; code review for hardcoded secrets |
| **Verification Approach** | Tier 2 — code/binary review for embedded secrets; Tier 1 — SVA that key registers sourced from hardware roots, not firmware-writable |
| **Related Requirements** | REQ-DICE-001 (UDS protection), REQ-DICE-004 (CDI secrecy), FIPS 140-3 (key management) |

---

*[FROM TRAINING] Threat descriptions are based on publicly known attack classes from academic literature and industry reports. Verify against current threat landscape assessments. Last verified: 2026-02-13.*
