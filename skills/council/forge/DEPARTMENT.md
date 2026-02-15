---
name: "Forge Department"
executive: "Forge"
color: "Graphite"
description: "Microarchitecture security, RTL review, physical implementation analysis"
---

# Forge Department — Graphite Lens

The Forge's department of focused skills for analyzing microarchitectural attack surfaces, reviewing RTL security, and assessing physical implementation risks.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [microarch-analysis](microarch-analysis/SKILL.md) | Microarchitectural attack surface analysis | default | `microarchitecture`, `pipeline`, `cache`, `speculation`, `side-channel`, `Spectre` |
| [rtl-security-review](rtl-security-review/SKILL.md) | RTL-level security review | default | `RTL`, `FSM`, `access control`, `gate-level`, `hardware verification` |
| [physical-design-security](physical-design-security/SKILL.md) | Physical implementation security assessment | default | `physical design`, `power domain`, `clock domain`, `timing closure`, `layout` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Microarchitecture, pipeline, cache, speculation, speculative execution, Spectre, Meltdown, branch predictor, transient execution | microarch-analysis | High |
| RTL, Verilog, SystemVerilog, FSM, access control, gate-level, hardware verification, register access | rtl-security-review | High |
| Physical design, power domain, clock domain, timing closure, layout, tape-out, DPA, fault injection | physical-design-security | High |
| Side-channel with microarchitectural scope | microarch-analysis | Medium |
| Side-channel with physical implementation scope | physical-design-security | Medium |

## Load Directive

Load one specialist skill at a time using the Skill tool. Read the classification logic table to select the appropriate specialist, then invoke the skill. Do not pre-load multiple specialists simultaneously.

## Handoff Protocol

When the specialist skill output reveals issues in another department's domain:
1. Complete the current skill's output format.
2. Note the cross-domain findings in the output.
3. Recommend loading the appropriate department and skill (e.g., "Hand off microarchitectural side-channel findings to cipher/crypto-review for constant-time implementation review").
