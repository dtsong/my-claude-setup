# Eval Case: IOMMU Configuration Review for DMA Protection

## Metadata
- **Case ID:** KS-002
- **Tier:** 1 (simple)
- **Skill Route:** kernel-security-skill
- **Estimated Complexity:** low

## Input
```json
{
  "user_prompt": "Review the IOMMU/SMMU configuration on our data center DPU running Linux 6.8. The DPU hosts SR-IOV network adapters assigned to tenant VMs via VFIO.\n\nKernel configuration:\nCONFIG_IOMMU_SUPPORT=y\nCONFIG_IOMMU_DEFAULT_DMA_STRICT=n\nCONFIG_IOMMU_DEFAULT_DMA_LAZY=y\nCONFIG_IOMMU_DEFAULT_PASSTHROUGH=n\nCONFIG_ARM_SMMU_V3=y\nCONFIG_VFIO=y\nCONFIG_VFIO_PCI=y\nCONFIG_VFIO_IOMMU_TYPE1=y\n\nBoot parameters: iommu.strict=0 arm-smmu-v3.disable_bypass=1\n\nHardware:\n- ARM SMMUv3 with 2-stage translation (S1 + S2)\n- PCIe Gen5 with ACS capability at root port (ACS not enabled at switch level)\n- 4x SR-IOV NICs, 64 VFs total, assigned to tenant VMs\n- No ATS (Address Translation Service) enabled on endpoints\n\nDeployment: Multi-tenant cloud DPU, KVM hypervisor, containers inside VMs.\nSoC family: data-center\nTechnology domain: tdisp-cxl",
  "context": "Focused IOMMU/SMMU review. Kernel config and boot params provided. Key concerns: lazy DMA mode in multi-tenant environment, ACS not enabled at switch level with SR-IOV, VFIO pass-through to tenant VMs. Phase 2 (isolation) and Phase 4 (IOMMU bypass paths) are primary."
}
```

## Expected Output
A kernel security analysis focused on IOMMU/SMMU configuration producing:
- Assessment of SMMUv3 2-stage translation for VM isolation
- Critical finding: ACS not enabled at PCIe switch level allows cross-VF DMA in shared IOMMU groups
- Finding: lazy DMA mode (strict=0) creates TOCTOU window for DMA attacks
- VFIO assignment security assessment
- SR-IOV isolation analysis with IOMMU group implications

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output identifies ACS not enabled at switch level as a critical isolation gap for SR-IOV
- [ ] Lazy DMA mode (iommu.strict=0) flagged as a security concern in multi-tenant context — TOCTOU window
- [ ] SMMUv3 2-stage translation assessed for VM isolation (S1 for guest, S2 for host)
- [ ] VFIO pass-through security implications analyzed
- [ ] KernelSecFinding entities produced with `kernelSubsystem: iommu-smmu`
- [ ] Findings specify privilege levels and HW dependencies

### Should Pass (partial credit)
- [ ] IOMMU group sharing risk explained: VFs in same IOMMU group without ACS can DMA to each other's memory
- [ ] disable_bypass=1 assessed positively — prevents IOMMU bypass as default domain
- [ ] Recommendation to enable ACS at PCIe switch level or ensure per-VF IOMMU group isolation
- [ ] Recommendation to switch to strict DMA mode (iommu.strict=1) for multi-tenant deployment
- [ ] ATS disabled assessed as positive — prevents endpoint-initiated translation that could bypass SMMU

### Bonus
- [ ] Specific SMMUv3 features assessed: HTTU (Hardware Translation Table Update), PRI (Page Request Interface)
- [ ] Container-inside-VM nesting assessed — IOMMU protects VM boundary but container isolation within VM depends on separate mechanisms
- [ ] PCIe Gen5 specific considerations noted (increased bandwidth amplifies DMA attack impact)

## Raw Trace Log
