# Navigation Eval Case: Kernel Security vs Threat Model — TEE Privilege Escalation

## Metadata
- **Case ID:** NAV-004
- **Tier:** 2 (medium)
- **Expected Route:** kernel-security-skill
- **Navigation Challenge:** "assess risks" sounds like threat modeling, but "privilege escalation" and "TEE boundary" are kernel-security keywords; the request is about analyzing existing isolation mechanisms rather than identifying new threats

## Input
```json
{
  "user_prompt": "Assess privilege escalation risks in our SoC's TEE boundary",
  "context": "The SoC runs a Linux kernel in the normal world with a TEE (TrustZone-based) in the secure world. The concern is about whether privilege escalation from EL0/EL1 in the normal world can breach the TEE boundary. IOMMU and TZASC are configured but not formally reviewed."
}
```

## Expected Routing Behavior
The coordinator should route to kernel-security-skill. Although "assess risks" has threat-modeling connotations, the core concern is privilege escalation across trust boundaries, which is a kernel-security domain concept. The kernel-security-skill handles KASLR, IOMMU configuration, seccomp policies, and privilege escalation analysis. The mention of TEE boundary, EL0/EL1 transitions, and TZASC configuration are all kernel-security indicators. Threat-model-skill would produce a broader STRIDE analysis, but the user is asking for a focused privilege escalation assessment.

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Routes to kernel-security-skill as the primary skill
- [ ] Recognizes "privilege escalation" as a kernel-security keyword
- [ ] Does NOT route to threat-model-skill as the primary skill

### Should Pass (partial credit)
- [ ] Identifies TEE/TrustZone boundary analysis as kernel-security scope
- [ ] Mentions IOMMU and TZASC review as part of the kernel-security assessment
- [ ] Notes that threat-model-skill could provide a broader analysis if needed

### Bonus
- [ ] Identifies that this could feed into a threat model as a downstream enrichment
- [ ] Notes the EL0/EL1/EL2/EL3 privilege levels as relevant kernel-security context

## Raw Trace Log
