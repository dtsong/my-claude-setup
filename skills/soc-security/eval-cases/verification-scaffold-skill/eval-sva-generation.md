# Eval Case: SVA Generation — TDISP FSM Assertions

## Metadata
- **Case ID:** VS-002
- **Tier:** 2 (medium)
- **Skill Route:** verification-scaffold-skill
- **Estimated Complexity:** medium

## Input
```json
{
  "user_prompt": "Generate SVA assertion templates for the TDISP device assignment FSM threats. I have RTL signal names available:\n- clk_200mhz, rst_n\n- tdisp_fsm_state[3:0] (IDLE=0, DISCOVER=1, LOCK=2, RUN=3, STOP=4, ERROR=5)\n- spdm_auth_complete\n- device_cert_valid\n- dma_access_enable\n- host_lock_request\n- assignment_timeout_counter[15:0]\n- MAX_ASSIGNMENT_TIMEOUT = 16'd50000",
  "context": "Upstream ThreatFindings from TM-2026-001 (TDISP Device Assignment, Data Center SoC):",
  "threat_findings": [
    {
      "id": "TF-TM-2026-001-003",
      "title": "TDISP State Machine Desynchronization",
      "strideCategory": "Tampering",
      "severity": "CRITICAL",
      "confidenceTier": "GROUNDED",
      "attackSurface": "bus-access-control",
      "verificationMethod": "SVA",
      "description": "An attacker with PCIe fabric access can inject out-of-order TDISP messages to desynchronize the assignment state machine, potentially leaving a device in an inconsistent security state.",
      "standardsReferences": ["TDISP 1.0 Section 4.2.1"]
    },
    {
      "id": "TF-TM-2026-001-006",
      "title": "DMA access enabled before TDISP RUN state",
      "strideCategory": "Elevation of Privilege",
      "severity": "CRITICAL",
      "confidenceTier": "GROUNDED",
      "attackSurface": "bus-access-control",
      "verificationMethod": "SVA",
      "description": "An attacker can trigger DMA transactions before the TDISP handshake reaches the RUN state, bypassing device isolation.",
      "standardsReferences": ["TDISP 1.0 Section 4.3.1"]
    },
    {
      "id": "TF-TM-2026-001-009",
      "title": "Assignment timeout handling allows stale state",
      "strideCategory": "Denial of Service",
      "severity": "HIGH",
      "confidenceTier": "INFERRED",
      "attackSurface": "bus-access-control",
      "verificationMethod": "SVA",
      "description": "If the TDISP assignment sequence stalls, the FSM may remain in LOCK state indefinitely without timing out to ERROR, leaving the device in a partially assigned state."
    }
  ]
}
```

## Expected Output
Three Tier 1 SVA assertion templates with:
- [READY] status (RTL signal names provided)
- INTENT and DOES NOT CHECK annotations per assertion
- Correct SVA syntax using the provided signal names
- Proper confidence propagation from upstream

## Grading Rubric

### Must Pass (eval fails if wrong)
- [ ] All three assertions marked [READY] (signal names were provided)
- [ ] Every assertion has `// INTENT:` annotation describing what it checks
- [ ] Every assertion has `// DOES NOT CHECK:` annotation with specific omissions
- [ ] TF-003 assertion: FSM transition guard preventing invalid state transitions (e.g., no IDLE->RUN skip)
- [ ] TF-006 assertion: dma_access_enable only asserted when tdisp_fsm_state == RUN
- [ ] TF-009 assertion: bounded liveness using assignment_timeout_counter and MAX_ASSIGNMENT_TIMEOUT

### Should Pass (partial credit)
- [ ] SVA uses correct SystemVerilog syntax (property/assert/cover constructs)
- [ ] Assertions use `disable iff (!rst_n)` for reset handling
- [ ] TF-003 assertion checks that SPDM authentication completes before LOCK->RUN transition
- [ ] Each assertion includes a cover property to verify the antecedent fires
- [ ] Confidence propagation: TF-003 and TF-006 get GROUNDED->HIGH; TF-009 gets INFERRED->HIGH (capped at INFERRED)

### Bonus
- [ ] Assertions include error messages with VI-ID for trace-back to threat findings
- [ ] TF-009 cover property specifically targets the timeout boundary condition (counter == MAX - 1)
- [ ] Skill notes that the 6-state FSM (values 0-5 in 4-bit register) leaves 10 unused states that should have a one-hot or valid-state invariant

## Raw Trace Log
