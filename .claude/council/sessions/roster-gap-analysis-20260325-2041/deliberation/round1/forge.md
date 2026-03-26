# Forge Position -- Council Roster Gap Analysis

## Core Recommendation

Expand Forge's department with 2-3 new skills covering EE fundamentals and chip-level flows rather than creating a new agent. The missing coverage is large but contiguous with Forge's existing domain -- it is the same silicon, just different stages of the design flow and different abstraction layers. A new agent would create a jurisdictional seam exactly where the user needs seamless guidance.

## Deep Analysis of Gap #7: EE Fundamentals + Chip-Level Flows

### What Forge Handles Well Today

Forge is tightly scoped to **security-oriented digital design at the microarchitectural level**:

- RTL security review (access control, FSM correctness, information leakage)
- Microarchitectural attack analysis (Spectre-class, cache timing, branch predictor)
- Physical design security (power domain isolation, clock domain crossing)
- Timing analysis for security (constant-time enforcement, critical path identification)
- Side-channel resistance (power analysis, EM, timing channels)

All three department skills -- `microarch-analysis`, `rtl-security-review`, `physical-design-security` -- are security-first. This is the right lens for a council agent, but it means Forge currently has no skills for the **functional design flow** that dominates day-to-day semiconductor work.

### What Falls Between Forge, Sentinel, and Cipher With No Owner

Here is the gap map. I am being precise about what is missing:

| Domain | Current Owner | Gap Severity |
|--------|--------------|--------------|
| **Verification methodology** (UVM, formal, coverage-driven) | Nobody | CRITICAL -- this is 60-70% of chip engineering effort |
| **DFT / scan chain / BIST / ATPG** | Forge mentions DFT in triggers but has no skill | HIGH |
| **Analog/mixed-signal design** (PLL, ADC, DAC, SerDes, PHY) | Nobody | HIGH -- essential for SoC work |
| **PCB design / board-level integration** | Sentinel mentions PCB in triggers but has no skill | MEDIUM |
| **RF / antenna design** | Nobody | MEDIUM -- relevant for modem/wireless SoC |
| **Power management IC design** (PMIC, LDO, DCDC) | Nobody | MEDIUM |
| **Semiconductor manufacturing flow** (process nodes, PDK, foundry interaction) | Nobody | MEDIUM |
| **EDA tool flows** (Synopsys/Cadence/Siemens toolchains) | Nobody | HIGH -- the user needs practical tool guidance |
| **IP integration** (AMBA/AXI bus, IP qualification, SoC assembly) | Nobody | HIGH |
| **Firmware-hardware co-design** | Split between Forge and Sentinel, no clear protocol | MEDIUM |

Cipher covers cryptographic implementations at the algorithm level but has no awareness of hardware crypto accelerator design -- how to implement AES/SHA engines in RTL, how to design a TRNG, how to build a hardware root of trust. This is a seam between Cipher and Forge that a skill could bridge.

Sentinel covers embedded firmware and IoT protocols but has no understanding of the silicon underneath -- what the MCU's bus architecture looks like, how peripherals are memory-mapped, how interrupt controllers work at the hardware level. The firmware-hardware co-design boundary is unowned.

### Recommendation: Expand Forge, Do Not Create a New Agent

**Why not a new agent ("Electrician" or "Foundry")?**

1. **Jurisdictional seams are expensive.** The user works in semiconductor. Almost every question will touch both "security-oriented silicon" (Forge) and "functional silicon" (new agent). Two agents in every deliberation, constantly negotiating handoffs for what is fundamentally the same chip, creates friction without value.

2. **Forge's mental models are correct for the expanded scope.** Pipeline-stage thinking, timing path analysis, and gate-level reasoning apply equally to verification methodology, DFT, and IP integration. The cognitive framework does not need to change -- the skill set does.

3. **The user is unfamiliar with hardware.** A single authoritative voice on all things silicon is more useful to a newcomer than two agents who might give contradictory guidance about where one domain ends and another begins.

**Proposed new skills for Forge's department:**

1. **`chip-design-flow`** -- Covers the full ASIC/SoC design flow from spec to tape-out: RTL coding (not just review), synthesis, place-and-route, timing closure, DRC/LVS signoff, foundry handoff. Includes EDA tool selection guidance.

2. **`verification-methodology`** -- UVM testbench architecture, coverage-driven verification, formal verification (not just for security), assertion-based verification, emulation/prototyping. This is the single biggest gap because verification dominates headcount and schedule in any chip project.

3. **`soc-integration`** -- IP qualification, AMBA/AXI interconnect design, memory subsystem architecture, interrupt controller configuration, DFT insertion, and firmware-hardware interface definition (register maps, MMIO, interrupt contracts).

**What should stay out of Forge:**

- **Analog/mixed-signal and RF** -- These are fundamentally different disciplines (continuous-time vs. discrete-time, electromagnetic theory vs. digital logic). If the user needs deep analog coverage, that warrants a future agent. For now, Forge can provide surface-level awareness but should not claim expertise.
- **PCB design** -- This is closer to Sentinel's physical-digital boundary. Add a PCB skill to Sentinel's department if needed.

### Forge Persona Adjustments

If the department expands, Forge's description should broaden from "silicon design, RTL security, timing closure, physical implementation" to include "chip design flow, verification methodology, SoC integration." The security-first framing in the cognitive framework should be preserved but supplemented with functional design heuristics. The trigger keywords should add: `UVM`, `coverage`, `synthesis`, `place and route`, `P&R`, `SoC`, `AMBA`, `AXI`, `IP integration`, `register map`, `MMIO`, `PDK`, `foundry`, `tapeout flow`, `signoff`.

## Brief Takes on Gaps #1-6 and Consolidations

### Gap #1: i18n/Localization
**Skill, not agent.** Add to Artisan or Craftsman. i18n is a cross-cutting implementation concern, not a domain that needs its own reasoning framework. A checklist-style skill covering Unicode handling, locale-aware formatting, RTL layout, and string externalization covers 90% of the need.

### Gap #2: Distributed Systems
**New agent warranted.** Distributed consensus, partition tolerance, eventual consistency, and distributed transaction design are a distinct reasoning discipline. None of the current agents have the mental models for CAP theorem trade-offs, vector clocks, or Raft/Paxos analysis. Architect thinks in component boundaries but not in network partition scenarios. Operator thinks in deployment but not in distributed state machines.

### Gap #3: FinOps
**Skill on Operator or Strategist.** Cloud cost optimization is operational concern with business context. A skill covering cost modeling, right-sizing, reserved instance strategy, and cost anomaly detection fits naturally on Operator (infrastructure) or Strategist (business ROI).

### Gap #4: Accessibility
**Skill on Advocate.** Advocate already represents users. Accessibility is a specialized form of user advocacy. A skill covering WCAG compliance, screen reader compatibility, keyboard navigation, and color contrast requirements extends Advocate's existing cognitive framework without requiring a new reasoning discipline.

### Gap #5: API Consumer/DevRel
**Skill on Herald or Chronicler.** API documentation, SDK design, developer experience, and integration guides are communication/documentation tasks. Herald (stakeholder communication) or Chronicler (documentation) can absorb this with a dedicated skill.

### Gap #6: QA/E2E Testing
**Skill on Prover.** Prover already handles correctness and verification. E2E testing strategy, test pyramid design, flaky test diagnosis, and test data management extend Prover's existing verification mindset. If Prover is too formal/mathematical, Craftsman (implementation quality) is the alternative host.

### Consolidation: Skeptic + Guardian
**Support with conditions.** Both are risk/security lenses, but they approach from different angles -- Skeptic challenges assumptions and plays devil's advocate, Guardian protects against threats. If consolidated, the merged agent must preserve both the "challenge the design" and "defend against attack" modes. I would keep the Skeptic framing (challenge-first) and fold Guardian's threat-modeling skills into the department. One risk lens is sufficient if it has both offensive and defensive skills.

### Consolidation: Herald + Strategist
**Cautious support.** Herald handles stakeholder communication and Strategist handles business strategy. These are adjacent but not identical -- one is about how to communicate, the other about what to prioritize. If the user rarely needs pure communication strategy (messaging, positioning) separate from business strategy (ROI, market timing), merge them. If the user does product work where messaging and strategy diverge, keep them separate. Given 20 agents is already a large roster, I lean toward merging.

## Risks If Ignored

- **User hits a verification or DFT question, gets no useful council input.** Forge talks about security side-channels while the user needs UVM testbench architecture guidance. Sentinel talks about firmware while the user needs scan chain insertion advice. The user learns the council cannot help with their primary domain. Severity: HIGH.

- **Forge gives narrow security-only answers to broad silicon questions.** When asked about timing closure, Forge focuses on constant-time security properties instead of setup/hold violations and clock tree synthesis. The security lens distorts general chip design guidance. Severity: MEDIUM.

- **Jurisdictional confusion between Forge, Sentinel, and Cipher on hardware crypto.** User asks about implementing an AES accelerator. Cipher knows the algorithm, Forge knows the pipeline, Sentinel knows the firmware driver. Nobody owns the end-to-end hardware crypto accelerator design. Three partial answers, no complete one. Severity: MEDIUM.

## Dependencies on Other Domains

- **Sentinel** -- Need clear boundary agreement on firmware-hardware co-design. Forge owns the hardware interface definition (register maps, MMIO layout, interrupt contracts). Sentinel owns the firmware that consumes those interfaces. The boundary is the hardware abstraction layer.

- **Cipher** -- Need handoff protocol for hardware crypto. Cipher owns algorithm selection and protocol design. Forge owns the RTL implementation of crypto accelerators, TRNG design, and hardware root of trust. Cipher specifies the security requirements; Forge implements them in silicon.

- **Architect** -- If Forge expands to cover SoC integration, Architect's system decomposition skills overlap with SoC architecture decisions (bus topology, memory hierarchy, IP block partitioning). Need agreement that Forge owns silicon-level architecture and Architect owns software-level architecture.

- **Prover** -- If verification methodology becomes a Forge skill, there is overlap with Prover's formal verification domain. Forge should own hardware verification (UVM, RTL formal, gate-level simulation). Prover should own software verification (property-based testing, theorem proving, model checking at the software level).
