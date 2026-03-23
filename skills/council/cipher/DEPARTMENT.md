---
name: "Cipher Department"
executive: "Cipher"
color: "Obsidian"
description: "Cryptographic engineering, protocol security, key management, post-quantum readiness"
---

# Cipher Department — Obsidian Lens

The Cipher's department of focused skills for reviewing cryptographic implementations, analyzing protocol security, and assessing post-quantum readiness.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [crypto-review](crypto-review/SKILL.md) | Cryptographic implementation review | default | `crypto`, `encryption`, `AES`, `RSA`, `key management`, `AEAD`, `hash` |
| [protocol-analysis](protocol-analysis/SKILL.md) | Protocol state machine security analysis | default | `protocol`, `TLS`, `SPDM`, `handshake`, `session`, `replay`, `downgrade` |
| [pqc-readiness](pqc-readiness/SKILL.md) | Post-quantum cryptography readiness assessment | default | `post-quantum`, `PQC`, `Kyber`, `Dilithium`, `ML-KEM`, `ML-DSA`, `quantum` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Encryption, decryption, algorithm choice, key management, AEAD, hash, HMAC, nonce, IV | crypto-review | High |
| Protocol, TLS, SPDM, handshake, session, replay, downgrade, state machine | protocol-analysis | High |
| Post-quantum, PQC, Kyber, Dilithium, ML-KEM, ML-DSA, quantum-safe, crypto agility | pqc-readiness | High |
| Certificate management, HSM integration, attestation protocols | crypto-review | Medium |
| Crypto agility with migration scope | crypto-review then pqc-readiness | Medium |

## Shared Directives

Load Directive, Handoff Protocol, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
