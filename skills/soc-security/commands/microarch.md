---
name: microarch
description: Run microarchitectural attack analysis on a SoC hardware component
---

# /soc-security:microarch

Analyze microarchitectural attack surfaces. This command activates the microarch-attack-skill to systematically identify transient execution attacks (Spectre/Meltdown/MDS), cache side-channels, branch predictor attacks, and shared-resource contention vulnerabilities.

## Usage

```
/soc-security:microarch
/soc-security:microarch "Analyze the ARM Cortex-A78 cluster for speculative execution attacks"
/soc-security:microarch --domain microarch-security --family data-center
```

## What Happens

1. **Microarchitectural context gathering:** Claude asks for the processor/accelerator microarchitectural description — pipeline depth, cache hierarchy, branch predictor type, shared resources, security domain definitions.
2. **Context mapping:** Maps all microarchitectural structures that could serve as information channels across security domain boundaries.
3. **Attack catalog check:** Systematically checks each entry in the microarchitectural attack catalog (UARCH-001 through UARCH-020) for applicability.
4. **Mitigation assessment:** For each applicable attack, evaluates hardware and software mitigations with residual risk analysis.
5. **Output generation:** Produces a microarchitectural attack assessment with MicroarchAttackFinding entities in DocumentEnvelope format.

## Attack Classes Covered

| Class | Examples |
|-------|---------|
| Transient execution — Spectre | Spectre-v1 (PHT), Spectre-v2 (BTB), Spectre-RSB, Inception, Training Solo |
| Transient execution — Meltdown | Meltdown, L1TF/Foreshadow |
| Microarchitectural data sampling | RIDL, Fallout, ZombieLoad, Downfall, Zenbleed |
| Cache side-channels | Prime+Probe, Flush+Reload, Evict+Time, Cache Occupancy |
| Other | TLBleed, PortSmash, prefetch side-channels |

## Output

The assessment is saved as a `microarch-attack-model` DocumentEnvelope with MicroarchAttackFinding entities, attack catalog coverage table, mitigation summary, and confidence breakdown.

## Next Step

After microarchitectural analysis, findings can feed into:
- `/soc-security:verify` — generate verification properties for identified attack vectors
- `/soc-security:formalize` — formalize security properties in TLA+
- `/soc-security:comply` — map findings to FIPS 140-3 timing side-channel requirements

## Skill Reference

This command invokes the [microarch-attack-skill](../microarch-attack-skill/SKILL.md). See also:
- [microarch-attack-methodology.md](../microarch-attack-skill/references/microarch-attack-methodology.md) — attack classification and analysis methodology
- [speculation-barrier-patterns.md](../microarch-attack-skill/references/speculation-barrier-patterns.md) — hardware/software mitigation catalog
- [microarchitectural-attacks.md](../shared-references/soc-security/threat-catalog/microarchitectural-attacks.md) — attack catalog (UARCH-001 to UARCH-020)
