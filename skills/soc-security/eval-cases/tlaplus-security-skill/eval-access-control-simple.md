# Eval Case: Simple TLA+ Spec for Access Control Policy

## Metadata
- **Case ID:** TS-001
- **Tier:** 1 (simple)
- **Skill Route:** tlaplus-security-skill
- **Estimated Complexity:** low

## Input
```json
{
  "user_prompt": "Write a TLA+ specification for the access control policy of our SoC bus firewall. The firewall controls access from 3 bus masters to 4 memory regions.\n\nSystem description:\n- Bus masters: {CPU_SECURE, CPU_NONSECURE, DMA_ENGINE}\n- Memory regions: {SECURE_ROM, SECURE_SRAM, NORMAL_SRAM, PERIPHERAL_IO}\n- Access types: {READ, WRITE}\n\nAccess control matrix (static, configured at boot):\n- CPU_SECURE: READ+WRITE to all 4 regions\n- CPU_NONSECURE: READ+WRITE to NORMAL_SRAM and PERIPHERAL_IO only; no access to SECURE_ROM or SECURE_SRAM\n- DMA_ENGINE: READ+WRITE to NORMAL_SRAM only; no access to any other region\n\nSecurity property to verify:\n1. (Safety invariant) CPU_NONSECURE can never access SECURE_ROM or SECURE_SRAM\n2. (Safety invariant) DMA_ENGINE can never access SECURE_ROM, SECURE_SRAM, or PERIPHERAL_IO\n\nUpstream finding: TF-2025-042 — 'Bus firewall misconfiguration allows DMA access to secure SRAM'\n\nWe want a TLA+ spec that models the access control matrix and proves the two invariants hold for all reachable states.",
  "context": "Simple access control model. Static policy (no dynamic reconfiguration). 3 masters, 4 regions, 2 access types. Two safety invariants to verify. Small state space — fully checkable by TLC."
}
```

## Expected Output
A FormalSecSpec with:
- TLA+ module modeling bus masters, memory regions, access types, and the access control matrix
- AccessRequest action modeling an access attempt
- Two safety invariants as TLA+ formulas
- Type invariant
- TLC configuration with small constants (fully enumerable state space)
- Assumptions and limitations documented

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] Output contains a syntactically valid TLA+ module (EXTENDS, VARIABLES, Init, Next, Spec)
- [ ] Module models the 3 bus masters, 4 memory regions, and access control matrix
- [ ] Two safety invariants expressed as TLA+ formulas that can be checked by TLC as INVARIANT directives
- [ ] Type invariant present
- [ ] TLC configuration provided with constants and property declarations
- [ ] Upstream finding ID (TF-2025-042) referenced as the source finding

### Should Pass (partial credit)
- [ ] Access control matrix modeled as a function or set of allowed (master, region, access) tuples
- [ ] State space is small enough for exhaustive TLC checking (estimate provided)
- [ ] Assumptions list present (e.g., policy is static, no dynamic reconfiguration, atomic access checks)
- [ ] Limitations list present (e.g., does not model concurrent access, does not model bus arbitration timing)
- [ ] Confidence tier assigned (likely GROUNDED or INFERRED given explicit access control matrix)

### Bonus
- [ ] Models an attacker action that attempts to bypass the firewall (e.g., spoofed master ID) and shows the invariant still holds
- [ ] Notes that a real bus firewall implementation may have race conditions during configuration that this model abstracts away
- [ ] Includes a deadlock check rationale (ALLOWED or NOT checked, with justification)

## Raw Trace Log
