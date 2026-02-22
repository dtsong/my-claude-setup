# Eval Case: KASLR Effectiveness Assessment for ARM SoC

## Metadata
- **Case ID:** KS-001
- **Tier:** 1 (simple)
- **Skill Route:** kernel-security-skill
- **Estimated Complexity:** low

## Input
```json
{
  "user_prompt": "Assess the effectiveness of KASLR on our ARM Cortex-A78AE compute SoC running Linux 6.6 LTS. Here is the relevant kernel configuration:\n\nCONFIG_RANDOMIZE_BASE=y\nCONFIG_RANDOMIZE_MODULE_REGION_FULL=y\nCONFIG_STACKPROTECTOR_STRONG=y\nCONFIG_ARM64_PTR_AUTH=y (but HW not present on this silicon revision)\nCONFIG_ARM64_BTI=y\nCONFIG_ARM64_MTE=n (not supported)\nCONFIG_KPTI=y (Kernel Page Table Isolation)\nCONFIG_UNMAP_KERNEL_AT_EL0=y\n\nHardware features:\n- ARM Cortex-A78AE (ARMv8.2-A)\n- No Pointer Authentication (PAC) hardware — silicon rev A0 lacks it\n- No Memory Tagging Extension (MTE)\n- SMAP equivalent: PAN (Privileged Access Never) enabled\n- SMEP equivalent: PXN (Privileged Execute Never) enabled\n- TrustZone EL3 secure monitor present\n\nDeployment: Bare metal automotive gateway, single-tenant, no containers.\nCompliance target: CIS Benchmark Level 2.\nSoC family: automotive\nTechnology domain: secure-boot-dice",
  "context": "Focused assessment on KASLR effectiveness. Kernel config provided as primary evidence. Key issue: PAC configured in kernel but hardware not present — degraded state. No LSM info provided. Single-phase analysis (Phase 1 kernel config) with brief Phase 4 (escalation paths related to KASLR bypass)."
}
```

## Expected Output
A kernel security analysis focused on KASLR effectiveness producing:
- Assessment of KASLR entropy and bypass resistance on ARMv8.2-A
- Critical finding that CONFIG_ARM64_PTR_AUTH=y has no effect without hardware PAC support
- KPTI/PAN/PXN assessed as complementary mitigations
- Known KASLR bypass techniques assessed for this configuration
- CIS Level 2 compliance check for relevant options

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output identifies that ARM64_PTR_AUTH is enabled but hardware PAC is absent — degraded security state
- [ ] KASLR entropy assessment present — notes ARM64 KASLR provides limited entropy compared to x86_64
- [ ] KPTI (UNMAP_KERNEL_AT_EL0) assessed as complementary to KASLR for kernel address leak prevention
- [ ] PAN and PXN assessed as hardware-enforced access/execute restrictions
- [ ] KernelSecFinding entities produced with correct schema fields
- [ ] Every finding has HW/SW interface context — hardware dependency documented

### Should Pass (partial credit)
- [ ] Known KASLR bypass techniques assessed: kernel address leaks via /proc, timing side-channels, exception-based probing
- [ ] CIS Level 2 compliance checked for RANDOMIZE_BASE, STACKPROTECTOR_STRONG, and KPTI
- [ ] Missing MTE noted as absent defense-in-depth for heap memory safety
- [ ] Bare metal single-tenant deployment context factored into risk assessment (reduced attack surface vs. multi-tenant)
- [ ] Confidence tiers assigned — kernel config findings GROUNDED, bypass technique assessment INFERRED or `[FROM TRAINING]`

### Bonus
- [ ] Recommendation to upgrade silicon revision to support PAC for meaningful pointer authentication
- [ ] TrustZone EL3 noted as additional privilege boundary relevant to KASLR (EL3 is not subject to KASLR)
- [ ] Module region randomization (RANDOMIZE_MODULE_REGION_FULL) assessed for separate entropy from kernel base

## Raw Trace Log
