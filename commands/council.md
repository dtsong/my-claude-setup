---
description: "Big Ideas Multi-Agent Workflow — interview, design, plan, build"
argument-hint: "[--help|--brainstorm|--quick|--deep|--auto|--guided|--meet|--audit|--resume|--list|--status|--archive|--cleanup] [IDEA...]"
---

# /council — Big Ideas Multi-Agent Workflow

An interview-first, dynamically-assembled council of perspective agents that collaborate on design and produce an actionable development plan for ambitious features.

## Usage

```
/council                              # New session — full workflow (default)
/council "Build a tournament coach"   # New session with idea
/council --brainstorm "Quick idea"    # 30-second gut check from 3 agents
/council --quick "Add a sidebar"      # Fast sketch — skip interview, 1 round
/council --deep "Redesign auth"       # Full council + mandatory deep audit
/council --auto "Add dark mode"       # Hands-off — no touchpoints
/council --guided "New feature"       # Tight control — approval at every phase
/council --meet "Should we migrate?"  # Discussion only — no action plan
/council --audit "API security"       # Direct codebase audit
/council --resume                     # Resume most recent active session
/council --resume <slug>              # Resume specific session
/council --resume --pick              # Pick from active sessions
/council --list                       # List sessions in workspace
/council --list --all                 # List sessions across all workspaces
/council --archive <slug>             # Export session to GitHub issue
/council --cleanup                    # Review and clean stale sessions
/council --status                     # Quick workspace session summary
/council --help                       # Show help with all modes
```

> **Tip:** `/brainstorm "idea"` is a shortcut for `/council --brainstorm "idea"`.

## Theme Configuration

This command is a **themed layer** on the shared deliberation engine at `commands/_council-engine.md`. All workflow logic, session management, and phase orchestration are defined in the engine. This file supplies the Council-specific configuration.

```
THEME_ID:               council
THEME_NAME:             Council
INTAKE_PROMPT:          "What's the big idea?"
AGENT_FILE_PREFIX:      council-
CONDUCTOR_PERSONA:      council-steward
SESSION_DIR_ROOT:       .claude/council/sessions/
TEAM_PREFIX:            council-
GLOBAL_REGISTRY_PATH:   ~/.claude/council/global-registry.json
INDEX_PATH:             .claude/council/index.json
CHALLENGE_RULES:        organic
EXTRA_MECHANICS:        (none)
```

### Phase Labels

```
PHASE_LABELS:
  phase_0: "What's the big idea?"
  phase_1: "Council Interview"
  phase_2: "Council Assembly — Agent Selection"
  phase_3_round1: "Round 1: Position"
  phase_3_round2: "Round 2: Challenge"
  phase_3_round3: "Round 3: Converge"
  phase_4: "Council Plan Ready"
  phase_5: "Council Execution"
```

### Assembly Label

```
ASSEMBLY_LABEL: "Council Assembly — Agent Selection"
```

---

## Agent Roster (20 Perspectives + Maestro)

| # | Agent | Color | Lens | File | Subagent Type |
|---|-------|-------|------|------|---------------|
| 1 | **Architect** | Blue | Systems, APIs, data models, integration | `council-architect` | `Architect` |
| 2 | **Advocate** | Green | UX, product thinking, accessibility | `council-advocate` | `Advocate` |
| 3 | **Skeptic** | Red | Risk, security, devil's advocate | `council-skeptic` | `Skeptic` |
| 4 | **Craftsman** | Purple | Testing, DX, code quality, patterns | `council-craftsman` | `Craftsman` |
| 5 | **Scout** | Cyan | Research, precedent, external knowledge | `council-scout` | `Scout` |
| 6 | **Strategist** | Gold | Business value, scope, MVP, prioritization | `council-strategist` | `Strategist` |
| 7 | **Operator** | Orange | DevOps, deployment, infra, monitoring | `council-operator` | `Operator` |
| 8 | **Chronicler** | Ivory | Documentation, knowledge architecture | `council-chronicler` | `Chronicler` |
| 9 | **Guardian** | Silver | Compliance, governance, privacy | `council-guardian` | `Guardian` |
| 10 | **Tuner** | Amber | Performance, scalability, optimization | `council-tuner` | `Tuner` |
| 11 | **Alchemist** | Indigo | Data engineering, data science, ML, analytics | `council-alchemist` | `Alchemist` |
| 12 | **Pathfinder** | Coral | Mobile, cross-platform, native apps | `council-pathfinder` | `Pathfinder` |
| 13 | **Artisan** | Rose | Visual design, design systems, motion | `council-artisan` | `Artisan` |
| 14 | **Herald** | Bronze | Growth, monetization, onboarding, retention | `council-herald` | `Herald` |
| 15 | **Sentinel** | Titanium | IoT, embedded, edge, device protocols | `council-sentinel` | `Sentinel` |
| 16 | **Oracle** | Violet | AI/LLM integration, RAG, prompt engineering | `council-oracle` | `Oracle` |
| 17 | **Forge** | Graphite | Microarchitecture, silicon design, RTL security | `council-forge` | `Forge` |
| 18 | **Cipher** | Obsidian | Cryptographic engineering, protocol security, PQC | `council-cipher` | `Cipher` |
| 19 | **Warden** | Slate | OS kernel security, isolation, privilege boundaries | `council-warden` | `Warden` |
| 20 | **Prover** | Pearl | Formal methods, verification, security invariants | `council-prover` | `Prover` |
| — | **Steward** | Platinum | Orchestration, synthesis, facilitation (Maestro) | `council-steward` | *(not spawned)* |

The **Steward** (Maestro) is not a spawned agent — it is the facilitator persona the conductor adopts during sessions. See `agents/council-steward.md` for the full persona.

Selection cap remains at **7 agents max** per session. The larger roster (20) gives more to choose from, not more in every session.

---

## Department Skills Tree

```
.claude/skills/council/
  registry.json                          # Usage tracking across all departments
  architect/
    DEPARTMENT.md                        # Department index
    codebase-context/SKILL.md            # "Tech chief" — infra analysis + context briefing
    schema-design/SKILL.md               # Database schema design
    api-design/SKILL.md                  # REST/RPC endpoint contracts
  skeptic/
    DEPARTMENT.md
    threat-model/SKILL.md                # STRIDE-based threat analysis
    failure-mode-analysis/SKILL.md       # Failure scenarios + mitigations
    edge-case-enumeration/SKILL.md       # Systematic edge case discovery
  advocate/
    DEPARTMENT.md
    journey-mapping/SKILL.md             # User journey with states + emotions
    interaction-design/SKILL.md          # Component specs with all states
  craftsman/
    DEPARTMENT.md
    testing-strategy/SKILL.md            # Test plan with coverage targets
    pattern-analysis/SKILL.md            # Codebase pattern audit + conventions
  scout/
    DEPARTMENT.md
    library-evaluation/SKILL.md          # Structured library scoring + comparison
    competitive-analysis/SKILL.md        # Feature comparison matrix
    technology-radar/SKILL.md            # Technology maturity assessment
  strategist/
    DEPARTMENT.md
    mvp-scoping/SKILL.md                 # MoSCoW prioritization + value-effort matrix
    impact-estimation/SKILL.md           # RICE scoring for feature prioritization
    analytics-design/SKILL.md            # Telemetry events + A/B test instrumentation
  operator/
    DEPARTMENT.md
    deployment-plan/SKILL.md             # Deployment strategy + rollback procedures
    observability-design/SKILL.md        # Monitoring, alerting, logging strategy
    cost-analysis/SKILL.md               # Infrastructure cost modeling
  chronicler/
    DEPARTMENT.md
    documentation-plan/SKILL.md          # Documentation architecture + audiences
    adr-template/SKILL.md               # Architecture Decision Record creation
    changelog-design/SKILL.md            # Changelog + migration guide design
  guardian/
    DEPARTMENT.md
    compliance-review/SKILL.md           # GDPR/privacy compliance review
    data-classification/SKILL.md         # Data sensitivity classification
    audit-trail-design/SKILL.md          # Audit logging design
  tuner/
    DEPARTMENT.md
    performance-audit/SKILL.md           # Bottleneck identification + profiling
    caching-strategy/SKILL.md            # Cache hierarchy design
    load-modeling/SKILL.md               # Capacity planning + benchmarks
  alchemist/
    DEPARTMENT.md
    schema-evaluation/SKILL.md           # Data warehouse schema design
    pipeline-design/SKILL.md             # ETL/ELT pipeline architecture
    ml-workflow/SKILL.md                 # ML workflow + experiment tracking
  pathfinder/
    DEPARTMENT.md
    platform-audit/SKILL.md              # Platform guideline compliance
    navigation-design/SKILL.md           # Mobile navigation + deep linking
    device-integration/SKILL.md          # Hardware APIs, sensors, biometrics
  artisan/
    DEPARTMENT.md
    visual-audit/SKILL.md                # Structured visual design critique
    design-system-architecture/SKILL.md  # Token hierarchy + theming
    motion-design/SKILL.md               # Animation principles + reduced-motion
  herald/
    DEPARTMENT.md
    growth-engineering/SKILL.md          # Onboarding funnels + referral systems
    monetization-design/SKILL.md         # Pricing tiers + paywall architecture
    messaging-strategy/SKILL.md          # Product copy + value propositions
  sentinel/
    DEPARTMENT.md
    embedded-architecture/SKILL.md       # Firmware design + RTOS patterns
    protocol-design/SKILL.md             # BLE/MQTT/Matter protocol selection
    fleet-management/SKILL.md            # Device provisioning + OTA updates
  oracle/
    DEPARTMENT.md
    prompt-engineering/SKILL.md          # System prompts + structured output
    rag-architecture/SKILL.md            # Chunking + embeddings + vector DB
    ai-evaluation/SKILL.md              # Golden datasets + hallucination detection
  forge/
    DEPARTMENT.md
    microarch-analysis/SKILL.md          # Microarchitectural attack surface analysis
    rtl-security-review/SKILL.md         # RTL-level security review
    physical-design-security/SKILL.md    # Physical implementation security
  cipher/
    DEPARTMENT.md
    crypto-review/SKILL.md               # Cryptographic implementation review
    protocol-analysis/SKILL.md           # Protocol state machine security analysis
    pqc-readiness/SKILL.md              # Post-quantum cryptography readiness
  warden/
    DEPARTMENT.md
    isolation-review/SKILL.md            # Isolation boundary analysis + bypass testing
    kernel-hardening/SKILL.md            # Kernel security configuration audit
    hw-sw-boundary/SKILL.md             # HW/SW security interface review
  prover/
    DEPARTMENT.md
    formal-spec/SKILL.md                 # TLA+ specification + model checking
    invariant-analysis/SKILL.md          # Security invariant identification
```

---

## Modifier Rules

### Mandatory Bonuses (+2)

- **Architect** gets +2 for any new functionality
- **Advocate** gets +2 for any user-facing feature
- **Skeptic** gets +2 for any auth/security-related work
- **Guardian** gets +2 for any feature handling user data or PII
- **Tuner** gets +2 for any feature with significant data volume or user-facing performance concerns
- **Alchemist** gets +2 for any feature involving data pipelines, warehousing, ML workflows, or analytics
- **Pathfinder** gets +2 for any mobile or cross-platform feature
- **Artisan** gets +2 for any UI-heavy feature or design system work
- **Herald** gets +2 for any user-facing feature with growth or monetization implications
- **Sentinel** gets +2 for any IoT, embedded, or hardware feature
- **Oracle** gets +2 for any AI/LLM integration feature
- **Forge** gets +2 for any RTL design, hardware verification, or silicon implementation; +2 for any microarchitectural security analysis
- **Cipher** gets +2 for any feature involving cryptographic operations, protocol security, or key management
- **Warden** gets +2 for any feature involving kernel security, process isolation, or privilege boundaries
- **Prover** gets +2 for any feature requiring formal verification, security invariants, or protocol correctness proofs

### Anti-Redundancy Penalties (-2)

If two agents overlap heavily for this idea, penalize the less relevant one by -2. Specific overlap rules:
- **Craftsman vs Operator** (CI/CD overlap): penalize the less relevant one
- **Skeptic vs Guardian** (data handling overlap): penalize the less relevant one
- **Pathfinder vs Advocate** (mobile UX overlap): Web-only feature → penalize Pathfinder -2. Native app component → both valid.
- **Artisan vs Advocate** (UI overlap): Pure interaction design (flows, forms) → penalize Artisan -2. Visual overhaul or design system work → both valid.
- **Herald vs Strategist** (business overlap): MVP scoping question → penalize Herald -2. Growth/monetization question → penalize Strategist -2.
- **Oracle vs Alchemist** (AI/ML overlap): Training custom models → penalize Oracle -2. Integrating pre-trained LLMs → penalize Alchemist -2.
- **Sentinel vs Operator** (infrastructure overlap): Cloud-only feature → penalize Sentinel -2. Physical device component → both valid.
- **Forge vs Sentinel** (hardware overlap): Pure firmware/IoT → penalize Forge -2. Silicon/RTL design → penalize Sentinel -2. Both valid for hardware security.
- **Cipher vs Skeptic** (security overlap): General security review → penalize Cipher -2. Cryptographic protocol or key management → penalize Skeptic -2.
- **Warden vs Skeptic** (security overlap): Application-level security → penalize Warden -2. Kernel/isolation/privilege boundary → penalize Skeptic -2.
- **Prover vs Craftsman** (quality overlap): Unit/integration testing → penalize Prover -2. Formal verification or protocol correctness → penalize Craftsman -2.
- **Forge vs Warden** (HW/SW overlap): Pure software isolation → penalize Forge -2. Pure silicon design → penalize Warden -2. HW/SW boundary → both valid.
- **Cipher vs Forge** (side-channel overlap): Software crypto implementation → penalize Forge -2. Hardware crypto / physical side-channel → penalize Cipher -2.

---

## Challenge Rules (Organic)

In Council mode, tension pairs for Round 2 are identified **organically** from the content of Round 1 positions. The conductor reads all positions looking for:

- **Direct contradictions** — Agent A says X, Agent B says not-X
- **Resource conflicts** — Both agents want to use the same surface differently
- **Priority clashes** — Agent A wants to invest in area Y, Agent B says defer it
- **Trade-off surfaces** — Where optimizing for one agent's concern degrades another's

Examples of common tension pairs:
- Architect wants a new table, Strategist says defer it
- Advocate wants rich interactions, Skeptic flags complexity risks
- Craftsman wants full test coverage, Strategist wants to ship faster
- Guardian wants full consent flow, Advocate wants frictionless UX
- Tuner wants caching layer, Architect says premature optimization
- Pathfinder wants native implementation, Architect prefers web-first approach
- Artisan wants design system overhaul, Strategist says defer visual polish
- Herald wants monetization hooks, Advocate wants frictionless free experience
- Sentinel wants custom protocol, Operator prefers standard cloud infrastructure
- Oracle wants frontier model, Tuner flags latency and cost concerns
- Forge wants hardware-enforced isolation, Warden says kernel enforcement is sufficient
- Cipher wants post-quantum migration now, Strategist says defer until compliance requires it
- Prover wants formal specification before implementation, Craftsman says tests are sufficient
- Forge flags speculative execution risk, Architect says software mitigation is acceptable
- Cipher wants separate HSM for key management, Operator flags infrastructure complexity
- Warden wants minimal kernel surface, Sentinel needs kernel modules for device drivers

Select 2-4 tension pairs. Not every disagreement is worth a full challenge round — focus on tensions where the resolution would meaningfully change the design.

---

## Phase 5: Agent Task Mapping

When executing via team (Path A), assign tasks based on agent strengths:

- **Architect** — Backend, APIs, database, schema tasks
- **Advocate** — Frontend, components, UX flow tasks
- **Craftsman** — Tests, quality gates, infra tasks
- **Skeptic** — Reviews all changes (read-only, sends feedback)
- **Scout** — Research tasks, library evaluation, competitive analysis
- **Strategist** — Scope decisions, prioritization during execution
- **Operator** — Deployment, monitoring, infrastructure tasks
- **Chronicler** — Documentation tasks
- **Guardian** — Compliance review, data classification, audit trail tasks
- **Tuner** — Performance optimization, caching, load testing tasks
- **Alchemist** — Data pipeline, warehouse schema, ML workflow, analytics tasks
- **Pathfinder** — Mobile navigation, platform compliance, device API integration tasks
- **Artisan** — Visual design, design system architecture, motion design tasks
- **Herald** — Onboarding optimization, monetization architecture, product messaging tasks
- **Sentinel** — Firmware design, protocol selection, fleet management, OTA update tasks
- **Oracle** — Prompt engineering, RAG pipeline, AI evaluation, LLM integration tasks
- **Forge** — RTL security review, microarchitectural analysis, physical design security, timing analysis tasks
- **Cipher** — Cryptographic implementation review, protocol analysis, key management design, PQC migration tasks
- **Warden** — Kernel hardening, isolation boundary review, HW/SW interface security, privilege boundary tasks
- **Prover** — Formal specification writing, invariant analysis, model checking configuration, verification tasks

---

## Workflow Execution

**Follow all instructions in `commands/_council-engine.md`**, substituting the theme variables defined above. The engine defines the complete Phase 0-5 workflow, session management commands, resume logic, and cleanup procedures.
