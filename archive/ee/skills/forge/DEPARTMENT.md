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
| [hw-security-signoff](hw-security-signoff/SKILL.md) | Builder-to-auditor handoff contract for tape-out security | default | `security signoff`, `tape-out security`, `hw security review`, `pre-tapeout` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Microarchitecture, pipeline, cache, speculation, speculative execution, Spectre, Meltdown, branch predictor, transient execution | microarch-analysis | High |
| RTL, Verilog, SystemVerilog, FSM, access control, gate-level, hardware verification, register access | rtl-security-review | High |
| Physical design, power domain, clock domain, timing closure, layout, tape-out, DPA, fault injection | physical-design-security | High |
| Side-channel with microarchitectural scope | microarch-analysis | Medium |
| Side-channel with physical implementation scope | physical-design-security | Medium |
| Security signoff, tape-out security gate, pre-tapeout security review, builder-auditor handoff | hw-security-signoff | High |

## Shared Directives

Load Directive, Handoff Protocol, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
