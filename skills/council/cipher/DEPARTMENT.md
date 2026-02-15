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

## Load Directive

Load one specialist skill at a time using the Skill tool. Read the classification logic table to select the appropriate specialist, then invoke the skill. Do not pre-load multiple specialists simultaneously.

## Handoff Protocol

When the specialist skill output reveals issues in another department's domain:
1. Complete the current skill's output format.
2. Note the cross-domain findings in the output.
3. Recommend loading the appropriate department and skill (e.g., "Hand off protocol state machine findings to prover/formal-spec for formal verification").
