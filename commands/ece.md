---
description: "EE Design Council — multi-agent deliberation for Principal-level Electrical Engineering"
argument-hint: "[--help|--brainstorm|--quick|--deep|--auto|--guided|--meet|--audit|--resume|--list|--status|--archive|--cleanup] [IDEA...]"
---

# /ece — EE Design Council

An interview-first, dynamically-assembled council of EE perspective agents that collaborate on hardware design decisions and produce actionable engineering plans for medical devices, embedded systems, mixed-signal electronics, and related domains.

## Usage

```
/ece                                  # New session — full workflow (default)
/ece "Design ECG front-end"           # New session with idea
/ece --brainstorm "Quick idea"        # 30-second gut check from 3 agents
/ece --quick "Add defib protection"   # Fast sketch — skip interview, 1 round
/ece --deep "Redesign power system"   # Full council + mandatory deep audit
/ece --auto "Add BLE connectivity"    # Hands-off — no touchpoints
/ece --guided "New sensor board"      # Tight control — approval at every phase
/ece --meet "ASIC vs FPGA?"           # Discussion only — no action plan
/ece --audit "EMC compliance review"  # Direct design audit
/ece --resume                         # Resume most recent active session
/ece --resume <slug>                  # Resume specific session
/ece --resume --pick                  # Pick from active sessions
/ece --list                           # List sessions in workspace
/ece --list --all                     # List sessions across all workspaces
/ece --archive <slug>                 # Export session to GitHub issue
/ece --cleanup                        # Review and clean stale sessions
/ece --status                         # Quick workspace session summary
/ece --help                           # Show help with all modes
```

## Theme Configuration

This command is a **themed layer** on the shared deliberation engine at `commands/_council-engine.md`. All workflow logic, session management, and phase orchestration are defined in the engine. This file supplies the EE Design Council-specific configuration.

```
THEME_ID:               ece
THEME_NAME:             EE Design Council
INTAKE_PROMPT:          "What engineering challenge are we solving?"
AGENT_FILE_PREFIX:      ece-
CONDUCTOR_PERSONA:      ece-conductor
SESSION_DIR_ROOT:       .claude/ece/sessions/
TEAM_PREFIX:            ece-
GLOBAL_REGISTRY_PATH:   ~/.claude/ece/global-registry.json
INDEX_PATH:             .claude/ece/index.json
CHALLENGE_RULES:        organic
EXTRA_MECHANICS:        (none)
```

### Phase Labels

```
PHASE_LABELS:
  phase_0: "What engineering challenge are we solving?"
  phase_1: "EE Council Interview"
  phase_2: "EE Council Assembly — Discipline Selection"
  phase_3_round1: "Round 1: Position — Engineering Analysis"
  phase_3_round2: "Round 2: Challenge — Trade-off Debate"
  phase_3_round3: "Round 3: Converge — Design Consensus"
  phase_4: "EE Council Plan Ready"
  phase_5: "EE Council Execution"
```

### Assembly Label

```
ASSEMBLY_LABEL: "EE Council Assembly — Discipline Selection"
```

---

## Agent Roster (14 Perspectives + Conductor)

| # | Agent | Color | Lens | File | Subagent Type |
|---|-------|-------|------|------|---------------|
| 1 | **Integrator** | Cobalt | Systems engineering, requirements, V-model, cross-functional integration | `ece-integrator` | `Architect` |
| 2 | **Shield** | Slate | Patient safety, leakage current, creepage/clearance, FMEA, single-fault | `ece-shield` | `Skeptic` |
| 3 | **Regulator** | Silver | IEC-60601, FDA 510(k)/PMA, ISO 13485, ISO 14971 | `ece-regulator` | `Guardian` |
| 4 | **Analog** | Amber | Low-noise precision analog, biopotential front-ends, signal conditioning | `ece-analog` | `Forge` |
| 5 | **Tracer** | Teal | Mixed-signal PCB, stackup, signal integrity, EMC/EMI | `ece-tracer` | `Foundry` |
| 6 | **Firmware** | Olive | ARM Cortex-M, PIC, RTOS, IEC 62304, bootloaders | `ece-firmware` | `Sentinel` |
| 7 | **Silicon** | Graphite | ASIC/FPGA, RTL, synthesis, HW/SW partitioning | `ece-silicon` | `Forge` |
| 8 | **Pulse** | Crimson | IVUS phased-array, acoustic matching, beamforming, pulsers | `ece-pulse` | `Forge` |
| 9 | **Sensor** | Jade | Biosensors, electrochemistry, micro-needle arrays, wearables | `ece-sensor` | `Sentinel` |
| 10 | **Power** | Copper | BMS, SMPS, LDO, high-voltage isolation, motor control | `ece-power` | `Forge` |
| 11 | **Fabricator** | Bronze | DFM, DFT, BOM, supply chain, production ramp | `ece-fabricator` | `Operator` |
| 12 | **Verifier** | Pearl | DVT, PV, IQ/OQ/PQ, test protocols, measurement uncertainty | `ece-verifier` | `Craftsman` |
| 13 | **Link** | Indigo | USB, SPI, BLE, CAN, antenna design, cybersecurity | `ece-link` | `Sentinel` |
| 14 | **Thermal** | Rust | Thermal simulation, derating, HALT/HASS, MTBF, environmental | `ece-thermal` | `Tuner` |
| -- | **Conductor** | Platinum | Orchestration, synthesis, facilitation (Maestro) | `ece-conductor` | *(not spawned)* |

The **Conductor** (Maestro) is not a spawned agent — it is the facilitator persona the conductor adopts during sessions. See `agents/ece-conductor.md` for the full persona.

Selection cap remains at **7 agents max** per session. The larger roster (14) gives more to choose from, not more in every session.

---

## Department Skills Tree

```
.claude/skills/ece/
  registry.json                              # Usage tracking across all departments
  references/
    department-preamble.md                   # Shared directives for all ECE departments
  integrator/
    DEPARTMENT.md
    requirements-decomposition/SKILL.md      # System requirements to subsystem specs
    interface-control/SKILL.md               # ICD development and management
    v-model-planning/SKILL.md                # V&V planning aligned to V-model
  shield/
    DEPARTMENT.md
    safety-analysis/SKILL.md                 # IEC 60601-1 safety analysis
    leakage-current/SKILL.md                 # Patient leakage current analysis
    single-fault-analysis/SKILL.md           # Single-fault condition evaluation
  regulator/
    DEPARTMENT.md
    regulatory-strategy/SKILL.md             # 510(k)/PMA pathway analysis
    risk-management/SKILL.md                 # ISO 14971 risk file development
    iec60601-review/SKILL.md                 # IEC 60601-1 compliance gap analysis
  analog/
    DEPARTMENT.md
    noise-analysis/SKILL.md                  # Signal chain noise budget analysis
    front-end-design/SKILL.md                # Biopotential/sensor front-end topology
    defibrillation-protection/SKILL.md       # Defib withstand circuit design
  tracer/
    DEPARTMENT.md
    stackup-design/SKILL.md                  # PCB stackup and impedance planning
    emc-strategy/SKILL.md                    # EMC/EMI compliance strategy
    power-integrity/SKILL.md                 # PDN impedance and decoupling
  firmware/
    DEPARTMENT.md
    rtos-architecture/SKILL.md               # RTOS task design and priority analysis
    bootloader-design/SKILL.md               # Secure bootloader architecture
    iec62304-compliance/SKILL.md             # Software lifecycle compliance
  silicon/
    DEPARTMENT.md
    hw-sw-partitioning/SKILL.md              # ASIC/FPGA/software boundary analysis
    fpga-architecture/SKILL.md               # FPGA resource planning and constraints
    verification-strategy/SKILL.md           # Simulation, formal, and emulation strategy
  pulse/
    DEPARTMENT.md
    transducer-design/SKILL.md               # Piezoelectric transducer modeling
    beamformer-architecture/SKILL.md         # Phased-array beamforming design
    pulser-design/SKILL.md                   # High-voltage transmit pulser design
  sensor/
    DEPARTMENT.md
    potentiostat-design/SKILL.md             # Electrochemical measurement circuits
    electrode-interface/SKILL.md             # Skin-electrode and micro-needle design
    wearable-form-factor/SKILL.md            # Wearable mechanical/electrical integration
  power/
    DEPARTMENT.md
    power-tree-design/SKILL.md               # System power architecture
    bms-design/SKILL.md                      # Battery management system design
    isolation-design/SKILL.md                # High-voltage isolation topology
  fabricator/
    DEPARTMENT.md
    dfm-review/SKILL.md                      # Design-for-manufacturing audit
    bom-optimization/SKILL.md                # BOM cost and sourcing analysis
    test-fixture-design/SKILL.md             # Production test strategy
  verifier/
    DEPARTMENT.md
    dvt-protocol/SKILL.md                    # Design verification test protocol
    measurement-uncertainty/SKILL.md         # GR&R and measurement system analysis
    statistical-methods/SKILL.md             # Sample size, confidence intervals, DOE
  link/
    DEPARTMENT.md
    wireless-design/SKILL.md                 # BLE/Wi-Fi radio and antenna design
    protocol-selection/SKILL.md              # Communication protocol trade-off analysis
    cybersecurity-review/SKILL.md            # Connected device cybersecurity assessment
  thermal/
    DEPARTMENT.md
    thermal-simulation/SKILL.md              # Thermal modeling and heatsink design
    derating-analysis/SKILL.md               # Component derating and reliability
    environmental-qualification/SKILL.md     # HALT/HASS/environmental test planning
```

---

## Modifier Rules

### Mandatory Bonuses (+2)

- **Integrator** gets +2 for any multi-subsystem or cross-functional integration challenge
- **Shield** gets +2 for any patient-contact design, safety-critical circuit, or applied parts classification
- **Regulator** gets +2 for any design targeting FDA submission or IEC-60601 compliance
- **Analog** gets +2 for any biopotential acquisition, precision measurement, or low-noise design
- **Tracer** gets +2 for any new PCB design, board revision, or EMC compliance effort
- **Firmware** gets +2 for any embedded software architecture, RTOS selection, or IEC 62304 concern
- **Silicon** gets +2 for any ASIC design, FPGA implementation, or HW/SW partitioning decision
- **Pulse** gets +2 for any ultrasound, acoustic, or transducer-related design
- **Sensor** gets +2 for any biosensor, electrochemistry, or wearable sensing design
- **Power** gets +2 for any battery management, power conversion, or high-voltage isolation design
- **Fabricator** gets +2 for any design-for-manufacturing, BOM optimization, or production transfer concern
- **Verifier** gets +2 for any DVT/PV protocol design, test method development, or measurement uncertainty analysis
- **Link** gets +2 for any wireless connectivity, communication protocol, or cybersecurity concern
- **Thermal** gets +2 for any thermal management, environmental qualification, or reliability prediction

### Anti-Redundancy Penalties (-2)

If two agents overlap heavily for this idea, penalize the less relevant one by -2. Specific overlap rules:
- **Regulator vs Shield** (safety/compliance overlap): Regulatory submission strategy question -> penalize Shield -2. Circuit-level safety engineering -> penalize Regulator -2. Both valid for risk management (ISO 14971).
- **Analog vs Tracer** (signal integrity overlap): Board-level SI/PI question -> penalize Analog -2. Front-end circuit topology question -> penalize Tracer -2. Both valid for mixed-signal layout.
- **Firmware vs Silicon** (HW/SW boundary overlap): Pure software architecture -> penalize Silicon -2. Pure RTL/FPGA design -> penalize Firmware -2. HW/SW partitioning -> both valid.
- **Integrator vs Verifier** (requirements/V&V overlap): Requirements decomposition -> penalize Verifier -2. Test protocol design -> penalize Integrator -2. Traceability -> both valid.
- **Fabricator vs Thermal** (reliability overlap): Pure manufacturing/yield question -> penalize Thermal -2. Pure environmental/reliability question -> penalize Fabricator -2. HALT/HASS -> both valid.
- **Pulse vs Analog** (front-end overlap): General precision analog -> penalize Pulse -2. Acoustic/ultrasound-specific -> penalize Analog -2. Transducer front-end -> both valid.
- **Sensor vs Analog** (measurement overlap): General analog signal chain -> penalize Sensor -2. Electrochemistry or biosensor-specific -> penalize Analog -2. Potentiostat design -> both valid.
- **Link vs Firmware** (protocol overlap): Pure wireless RF/antenna -> penalize Firmware -2. Pure firmware protocol stack -> penalize Link -2. BLE stack integration -> both valid.
- **Power vs Thermal** (dissipation overlap): Power topology selection -> penalize Thermal -2. Thermal derating analysis -> penalize Power -2. Power dissipation budget -> both valid.
- **Shield vs Analog** (patient safety overlap): Isolation barrier topology -> penalize Analog -2. Front-end circuit with defibrillation protection -> penalize Shield -2. Patient-connected analog front-end -> both valid.

---

## Challenge Rules (Organic)

In EE Design Council mode, tension pairs for Round 2 are identified **organically** from the content of Round 1 positions. The conductor reads all positions looking for:

- **Direct contradictions** — Agent A says X, Agent B says not-X
- **Resource conflicts** — Both agents want to use the same board area, power budget, or pin differently
- **Priority clashes** — Agent A wants to invest in area Y, Agent B says defer it
- **Trade-off surfaces** — Where optimizing for one agent's concern degrades another's

Examples of common EE tension pairs:
- Analog wants a linear regulator for clean power, Power says switching regulator is mandatory for battery life
- Shield demands 2 MOPP isolation, Analog says it degrades signal fidelity
- Fabricator wants standard 4-layer stackup, Tracer needs 8-layer for impedance control
- Silicon wants custom ASIC, Fabricator says COTS FPGA reduces NRE risk
- Firmware wants over-the-air updates, Regulator flags re-validation requirements
- Pulse wants maximum pulser voltage for penetration depth, Shield flags patient exposure limits
- Sensor wants novel micro-needle array, Regulator says no predicate device exists
- Integrator wants modular architecture, Fabricator says it increases interconnect cost
- Verifier wants 95% test coverage, Fabricator says test time exceeds production takt
- Link wants BLE 5.3 for throughput, Power says the radio power budget is exceeded
- Thermal flags junction temperature concern, Tracer says rerouting violates SI constraints
- Regulator wants design freeze for submission, Firmware needs a critical bug fix

Select 2-4 tension pairs per session.

---

## Phase 5: Agent Task Mapping

When executing via team (Path A), assign tasks based on agent strengths:

- **Integrator** — Requirements decomposition, interface specification, system block diagrams, traceability matrix tasks
- **Shield** — Safety analysis, leakage current calculation, creepage/clearance verification, FMEA tasks
- **Regulator** — Regulatory strategy, predicate device analysis, risk management file, submission document tasks
- **Analog** — Schematic design, component selection, SPICE simulation, noise analysis tasks
- **Tracer** — PCB layout, stackup design, impedance simulation, EMC pre-compliance tasks
- **Firmware** — Firmware architecture, HAL design, RTOS configuration, MISRA-C compliance tasks
- **Silicon** — RTL design, FPGA constraint files, synthesis scripts, timing closure tasks
- **Pulse** — Transducer modeling, beamformer design, pulser circuit design, acoustic simulation tasks
- **Sensor** — Potentiostat design, electrode characterization, impedance spectroscopy setup tasks
- **Power** — Power tree design, BMS configuration, SMPS component selection, efficiency measurement tasks
- **Fabricator** — BOM review, DFM check, test fixture specification, vendor qualification tasks
- **Verifier** — DVT protocol writing, test method development, statistical analysis, IQ/OQ/PQ tasks
- **Link** — Protocol specification, antenna matching, wireless coexistence testing, cybersecurity review tasks
- **Thermal** — Thermal simulation, derating analysis, HALT/HASS planning, MTBF prediction tasks

---

## Workflow Execution

**Follow all instructions in `commands/_council-engine.md`**, substituting the theme variables defined above. The engine defines the complete Phase 0-5 workflow, session management commands, resume logic, and cleanup procedures.
