# Forge Final Position -- Council Roster Gap Analysis

## Revised Recommendation

One new agent -- "Foundry" -- covering both digital design flows and EE fundamentals as a single broad hardware agent. Do not split into two agents. The boundary between Foundry and Forge is constructive design vs. security audit, mirroring the real industry separation between design engineering and security review. Foundry builds; Forge challenges.

## The Scope Question: One Agent or Two?

Strategist wants analog/RF/PCB/power as a separate EE agent. I want digital design flows (verification, synthesis, SoC integration) as a separate design agent. The question is whether these should be one agent or two.

**They should be one agent. Here is my reasoning at the gate level:**

In real semiconductor companies -- Qualcomm, Samsung, MediaTek, the exact companies in the user's domain -- there is no wall between digital and analog. An SoC contains both. The SerDes PHY is analog. The PLL that generates the clock tree is analog. The ADC that interfaces with sensors is mixed-signal. The digital designer who ignores analog constraints ships a chip that fails at the board level. The analog designer who ignores digital integration ships an IP block that nobody can instantiate.

A single "Foundry" agent with a broad chip-engineering cognitive framework can hold the mental model that matters most for a newcomer: **the chip is one system, from transistor to package to PCB, and every decision at one level constrains every other level.** Splitting digital and analog into two agents would teach the user to think of them as separate disciplines, which is exactly the misconception that causes integration failures in real silicon.

The practical argument is equally strong. The user is unfamiliar with hardware. They will not know whether their question is "digital" or "analog." When they ask about clock distribution, that starts as digital (clock tree synthesis) and ends as analog (jitter, PLL loop bandwidth). When they ask about a high-speed interface, that is digital protocol (PCIe, USB) on top of analog PHY (SerDes, equalization). One agent can navigate that continuum. Two agents would force the user to classify questions they do not yet understand.

**What Foundry's cognitive framework should look like:**

- **Design-flow thinking** -- Every chip moves through spec, architecture, RTL, verification, synthesis, physical design, signoff, tape-out, bring-up. Decisions at each stage constrain downstream stages.
- **Abstraction-layer awareness** -- System level, RTL level, gate level, transistor level, layout level. Know which abstraction is appropriate for the question.
- **Constructive mindset** -- "How do we build this correctly?" not "How could this be attacked?" Design for manufacturability, testability, and integration first. Security is Forge's concern.
- **Tool-chain fluency** -- EDA tools are how chip design happens. Synopsys, Cadence, Siemens toolchains, open-source alternatives (Yosys, OpenROAD, Verilator). Practical guidance, not abstract theory.

**Foundry's founding department (5 skills):**

1. `chip-design-flow` -- ASIC/SoC flow from spec to tape-out, EDA tool selection, synthesis, P&R, signoff
2. `verification-methodology` -- UVM, formal verification, coverage-driven verification, emulation, FPGA prototyping
3. `soc-integration` -- IP qualification, AMBA/AXI interconnect, memory subsystem, DFT insertion, register maps
4. `analog-mixed-signal` -- PLL, ADC/DAC, SerDes PHY, power management circuits, SPICE simulation, PDK interaction
5. `board-integration` -- PCB design fundamentals, power delivery network, signal integrity, thermal management, package selection

Skills 1-3 are the digital flow skills from my Round 1 gap map. Skills 4-5 address Strategist's analog/EE concerns. All five live under one agent because they describe one design flow for one chip.

## Concessions Made

**I conceded that Forge should not expand to absorb chip design flows.** Strategist was right: Forge's adversarial cognitive posture -- every heuristic framed around what can go wrong, what leaks, what can be attacked -- would distort constructive design guidance. A user learning chip design needs to hear "here is how to build a correct UVM environment" before they hear "here is how your cache hierarchy leaks secrets." The security audit lens is valuable but it is not the entry point for a newcomer.

**I conceded that analog/RF/PCB coverage belongs in the hardware gap, not deferred to "future need."** The user works in the semiconductor space where SoCs contain analog IP blocks, RF front-ends, and must be integrated onto PCBs. Telling them "analog is out of scope" while they are staring at a PLL spec would be a failure of council coverage.

**I accept the risk of a jurisdictional seam between Forge and Foundry.** My Round 1 concern was real -- two silicon agents will sometimes be summoned together. But the builder/auditor boundary is well-understood in industry and can be defined cleanly through a handoff protocol.

## Non-Negotiables

**1. Forge retains exclusive ownership of hardware security analysis.** Microarchitectural attack surfaces, side-channel resistance, speculative execution windows, constant-time enforcement, hardware root of trust security review -- these stay with Forge. Foundry must not attempt security analysis because a constructive mindset will systematically underestimate adversarial threats. This is not a turf claim; it is a safety argument. The same reason you do not let the design team sign off on their own security review.

**2. The Forge-Foundry handoff protocol must be explicit.** Define it as a bridging skill (`hw-security-signoff` on Forge's side) with a clear interface contract:
- Foundry produces: block diagrams, access control intent, shared resource maps, speculation-capable pipeline descriptions, DFT scan chain topology
- Forge consumes those artifacts and produces: security findings, side-channel risk assessments, microarchitectural attack surface reports
- Neither agent operates on the other's artifacts without the handoff

**3. Foundry must not be split into two agents.** Twenty-one agents is already a large roster. Adding two (digital + analog) brings it to twenty-three and creates an artificial seam inside what is physically one chip. If analog coverage proves insufficient as a skill under Foundry, the correct response is to deepen the skill, not to spawn another agent.

## Implementation Notes

**New agent creation:**
- Agent file: `agents/council-foundry.md`
- Color: suggest **copper** (the metal that connects everything on a chip -- vias, interconnect, bond wires, PCB traces)
- Model: `claude-opus-4-6` (same as Forge -- hardware reasoning benefits from the strongest model)
- Department directory: `.claude/skills/council/foundry/`
- Trigger keywords: `chip design`, `ASIC`, `FPGA`, `SoC`, `verification`, `UVM`, `synthesis`, `place and route`, `P&R`, `timing closure`, `setup time`, `hold time`, `clock tree`, `PLL`, `SerDes`, `ADC`, `DAC`, `analog`, `mixed-signal`, `PCB`, `PDK`, `foundry`, `tape-out`, `tapeout`, `EDA`, `Synopsys`, `Cadence`, `Yosys`, `Verilator`, `AMBA`, `AXI`, `APB`, `register map`, `MMIO`, `IP integration`, `DFT`, `scan chain`, `BIST`, `ATPG`, `SPICE`, `signal integrity`, `power integrity`

**Forge modifications:**
- Add bridging skill: `hw-security-signoff` to Forge's department
- Remove constructive design triggers from Forge that now belong to Foundry (keep security-specific triggers)
- Add Foundry to Forge's "Dependencies on other domains" section
- Update Forge's description to clarify: "security analysis and audit of silicon designs" rather than implying general chip design ownership

**Trigger deconfliction:**
- Shared triggers (`ASIC`, `FPGA`, `tape-out`, `DFT`, `scan chain`) should summon both agents when they appear in a security context, but default to Foundry alone for general design questions
- The conductor should use context to disambiguate: "review this RTL for side channels" routes to Forge; "help me write RTL for this block" routes to Foundry; "design and secure this block" routes to both

**Estimated effort:** ~3 days for the agent file and founding department (5 skill stubs + DEPARTMENT.md). Another 1-2 days for Forge's `hw-security-signoff` bridging skill and trigger deconfliction updates.
