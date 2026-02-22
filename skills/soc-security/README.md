# SoC Security Skills for Claude Code

> Structured security analysis for hardware engineers. Threat model a TDISP device assignment flow, analyze Spectre-class attacks on your CPU cluster, assess DPA resistance of your crypto engine, formalize safety properties in TLA+, map compliance gaps, and brief your CISO -- all from your terminal.

---

## What Are Claude Code Skills?

[Claude Code](https://docs.anthropic.com/en/docs/claude-code) is Anthropic's CLI tool for working with Claude in your terminal. **Skills** are reusable prompt packages that teach Claude structured methodologies for specific domains. When you install skills, Claude gains deep expertise it can apply automatically during your conversations.

This repository is a **skills package** — a collection of 9 security analysis skills, 11 slash commands, and 35+ reference files that give Claude structured knowledge about SoC hardware security engineering.

### How Skills Work

Skills activate in two ways:

1. **Auto-activation.** Claude reads the SKILL.md files in your skills directory and applies them when it detects relevant context. Mention "threat model" or "STRIDE analysis" in conversation and the threat-model-skill's methodology kicks in automatically.

2. **Slash commands.** Type `/soc-security:threat-model` in Claude Code to explicitly invoke a skill. Slash commands are defined in the `commands/` directory and namespaced by the package directory name (`soc-security`).

Skills also ship with **shared references** — curated knowledge files (threat catalogs, standards requirements, glossaries) that Claude reads on demand to ground its analysis in real specifications rather than training data alone.

---

## Prerequisites

- **Claude Code** installed and working ([installation guide](https://docs.anthropic.com/en/docs/claude-code/getting-started))
- **git** (for cloning the repo)
- **bash** (macOS/Linux — the install script is a bash script)

---

## Getting Started

### 1. Clone and Install

```bash
git clone https://github.com/dtsong/soc-security-skills.git
cd soc-security-skills
./install.sh
```

This copies the skills to `~/.claude/skills/soc-security/`, where Claude Code discovers them automatically.

### 2. Verify Installation

```bash
# Check the install directory exists and has skills
ls ~/.claude/skills/soc-security/threat-model-skill/SKILL.md

# List all installed skills
ls -d ~/.claude/skills/soc-security/*-skill/
```

You should see 9 skill directories (threat-model, verification-scaffold, compliance-pipeline, executive-brief, microarch-attack, physical-sca, kernel-security, emerging-hw-security, tlaplus-security).

### 3. Test It

Open Claude Code in any directory and try a slash command:

```
> /soc-security:threat-model "DICE attestation engine for automotive SoC"
```

Claude will ask for your component description, relevant spec sections, and security boundary, then walk through STRIDE categories systematically.

Or just describe what you need in natural language:

```
> I need to analyze the microarchitectural attack surface of our ARM Cortex-A78
  cluster. It has shared L3 cache and speculative execution enabled.
```

Claude auto-detects the relevant skill and applies the microarch-attack-skill methodology.

### Install Only What You Need

```bash
./install.sh --role soc-pipeline         # Original 4-stage pipeline only
./install.sh --role advanced-analyst     # Microarch + SCA + kernel + emerging HW
./install.sh --role formal-methods       # TLA+ formal specification only
./install.sh --role threat-analyst       # Threat model + verification scaffold
./install.sh --list                      # See all roles and skills
```

Shared references are always installed regardless of which skills you select.

### Updating

```bash
cd soc-security-skills
git pull
./install.sh    # Re-run to update installed skills
```

---

## Who Is This For

**SoC security engineers** who work across hardware security domains:
- Virtualization Access Control and Confidential AI (TEE, TDX, SEV-SNP)
- TDISP for Device Assignment with C2C CHI and CXL
- Supply Chain Security (SPDM, DICE attestation, firmware provenance)
- Secure Boot and Debug, DICE layered identity
- RISC-V CHERI capability-based memory safety

**Across SoC families:** Compute, Automotive, Client, and Data Center.

If you take a System Engineering approach to building HW security IPs tailored to SW stacks across merchant or application-specific SoCs, this is built for your workflow.

---

## What You Get

### 9 Skills, 3 Pipeline Tracks

Each skill produces concrete, structured artifacts. Use them individually or run full pipelines for end-to-end analysis.

```
ORIGINAL PIPELINE (P0 -> P1 -> P2 -> P3):
  IDENTIFY              VERIFY               COMPLY               COMMUNICATE
     |                    |                    |                       |
threat-model-skill  verification-scaffold  compliance-pipeline  executive-brief-skill
     |                    |                    |                       |
     v                    v                    v                       v
  Threat Model        Verification         Compliance              Executive Brief
  + Requirements      Checklist            Matrix + Gaps           (Board / CISO / Program)
  + STRIDE Analysis   + SVA Templates      + Evidence Map          + Risk Summary
  + Attack Surface    + Review Items       + Cross-Family          + Action Items
    Checklist           (Tier 1/2/3)         Traceability           + Trend Arrows

ADVANCED PIPELINE (A0-A3, parallel):
  MICROARCH (A0)      PHYSICAL SCA (A1)    KERNEL (A2)           EMERGING HW (A3)
       |                    |                    |                       |
  microarch-attack    physical-sca-skill   kernel-security       emerging-hw-security
       |                    |                    |                       |
       v                    v                    v                       v
  Spectre/Meltdown    DPA/SPA/FI           Hardening              PQC Readiness
  + Cache Attacks     + JIL Scores         + Isolation Map         + Chiplet Security
  + Mitigations       + ISO 17825          + Escalation Paths     + AI Accelerator
  + Paper Citations   + Countermeasures    + Attack Surface        + Migration Risk

FORMAL METHODS (F0, hub):
  Any findings --> tlaplus-security-skill --> TLA+ Specification
                                               + Safety/Liveness Properties
                                               + Model Checking Config
                                               + Assumptions & Limitations
```

### Slash Commands

| Command | What It Does |
|---------|--------------|
| `/soc-security:threat-model` | Structured threat modeling with STRIDE and attack trees |
| `/soc-security:verify` | Generate verification checklists and SVA assertion templates |
| `/soc-security:comply` | Run compliance mapping and gap analysis against standards |
| `/soc-security:brief` | Translate findings into audience-adapted executive briefs |
| `/soc-security:pipeline` | Run all 4 original stages with review checkpoints |
| `/soc-security:microarch` | Microarchitectural attack analysis (Spectre, cache, branch) |
| `/soc-security:physical-sca` | Physical SCA assessment with JIL scoring |
| `/soc-security:kernel-sec` | Kernel security analysis and privilege escalation |
| `/soc-security:emerging-hw` | Emerging HW assessment (PQC, chiplet, AI accelerator) |
| `/soc-security:formalize` | Formalize security properties in TLA+ |
| `/soc-security:advanced-pipeline` | Run advanced pipeline (A0-A3 + F0) with checkpoints |

### Every Output Tells You What It Doesn't Know

All findings carry a confidence tier:

| Tier | What It Means | What You Do |
|------|---------------|-------------|
| **GROUNDED** | Directly supported by a cited spec section or your evidence | Use it |
| **INFERRED** | Logically derived but not explicitly stated in specs | Spot-check it |
| **SPECULATIVE** | Plausible but not grounded in provided context | Verify before acting |
| **ABSENT** | A known attack category that was not analyzed | Decide if it matters |

Every output also includes a mandatory attack surface checklist showing what **was** and **was not** analyzed. No silent gaps.

---

## Example Workflows

### "I need to threat model a new security IP"

```
> /soc-security:threat-model "DICE attestation engine for automotive SoC"
```

You provide: component description, relevant TCG DICE spec sections, trust boundary definition.

You get: SecurityRequirement entities extracted from the spec, ThreatFinding entities categorized by STRIDE, attack surface checklist (ANALYZED/NOT ANALYZED), confidence-tagged findings, coverage boundary declaration.

### "I have threats -- now I need verification items"

```
> /soc-security:verify
```

Consumes your threat model output. Produces tiered verification items:
- **Tier 1** (mechanical): SVA assertion templates for register locks, FSM transitions, access control. Every assertion has `// INTENT:` and `// DOES NOT CHECK:` annotations. Marked `[TEMPLATE]` or `[READY]`.
- **Tier 2** (protocol): Natural-language property descriptions for DICE handshakes, CXL coherence, SPDM sessions. Needs engineer review.
- **Tier 3** (information flow): Specification-only descriptions. No SVA generated -- side-channel and information flow properties require human analysis.

### "Map this to FIPS 140-3 and find the gaps"

```
> /soc-security:comply --standard fips-140-3
```

Three-stage pipeline: extract requirements from the standard, map them to your implementation evidence, identify gaps. Distinguishes "no evidence found" from "requirement not met." Supports cross-family analysis when the same IP targets multiple SoC families.

### "I need to brief the CISO on this"

```
> /soc-security:brief --audience ciso
```

Translates your technical findings through 4 layers of abstraction:

```
Technical:  "DMA bypass via malformed TLP in TDISP handshake"
    -> Impact:   "Attacker with physical access can bypass memory isolation"
    -> Risk:     "Customer data in confidential AI pipelines may be exposed"
    -> Action:   "Prioritize fix in Q2 silicon respin. Cost: ~2-3 weeks eng."
```

### "Analyze microarchitectural attack surfaces"

```
> /soc-security:microarch "ARM Cortex-A78 cluster with shared L3 in data-center SoC"
```

You provide: microarchitectural details (pipeline, caches, branch predictor), shared resource configuration, deployed mitigations.

You get: MicroarchAttackFinding entities mapped to UARCH-001 through UARCH-020 catalog entries, speculative execution window analysis, mitigation assessment with residual risk, paper citations for each attack class.

### "Assess DPA resistance of a crypto engine"

```
> /soc-security:physical-sca "AES-256 crypto engine targeting FIPS 140-3 Level 3"
```

You provide: cryptographic operations, key material handling, existing countermeasures (masking order, hiding techniques).

You get: Leakage surface analysis per cryptographic operation, JIL attack potential scores, ISO 17825 TVLA status, countermeasure effectiveness assessment.

### "Check kernel hardening and escalation paths"

```
> /soc-security:kernel-sec "Data-center Linux with SR-IOV and container workloads"
```

You provide: kernel config, deployed security mechanisms, hardware platform details.

You get: Hardening gap analysis against CIS/KSPP benchmarks, isolation boundary map, privilege escalation path enumeration (user -> kernel, container escape, IOMMU bypass), attack surface assessment.

### "Formalize security properties in TLA+"

```
> /soc-security:formalize "Formalize the TDISP state machine safety property"
```

Takes findings from any upstream skill and produces a TLA+ specification with state variables, type invariants, initial state, next-state relation, and temporal security properties. Includes TLC model checking configuration guidance.

### "Run the full advanced pipeline"

```
> /soc-security:advanced-pipeline "Full advanced analysis of our data-center SoC security subsystem"
```

Runs A0-A3 in parallel, then F0 (TLA+ formalization) with review checkpoints between stages.

### "Full original pipeline, end to end"

```
> /soc-security:pipeline "CXL Type-3 memory device security for data-center SoC"
```

Runs all 4 original stages with review checkpoints between each. You can stop and resume at any stage.

---

## Repository Structure

```
soc-security-skills/
  install.sh                           # Installer script
  CATALOG.md                           # Detailed skill catalog
  README.md                            # This file
  VERSION                              # Current version (0.2.0)
  commands/                            # Slash command definitions
    threat-model.md                    #   /soc-security:threat-model
    verify.md                          #   /soc-security:verify
    comply.md                          #   /soc-security:comply
    brief.md                           #   /soc-security:brief
    pipeline.md                        #   /soc-security:pipeline
    microarch.md                       #   /soc-security:microarch
    physical-sca.md                    #   /soc-security:physical-sca
    kernel-sec.md                      #   /soc-security:kernel-sec
    emerging-hw.md                     #   /soc-security:emerging-hw
    formalize.md                       #   /soc-security:formalize
    advanced-pipeline.md               #   /soc-security:advanced-pipeline
  threat-model-skill/                  # P0: Threat modeling (SKILL.md + references/)
  verification-scaffold-skill/         # P1: Verification scaffolding
  compliance-pipeline-skill/           # P2: Compliance mapping
  executive-brief-skill/               # P3: Executive communication
  microarch-attack-skill/              # A0: Microarchitectural attacks
  physical-sca-skill/                  # A1: Physical side-channel analysis
  kernel-security-skill/               # A2: Kernel security
  emerging-hw-security-skill/          # A3: Emerging HW security
  tlaplus-security-skill/              # F0: TLA+ formal specification
  shared-references/                   # Curated knowledge files
    soc-security/
      entity-schema.md                 # Entity type definitions
      glossary.md                      # 140+ terms
      domain-ontology/                 # Security properties, technology domains
      standards-registry/              # DICE, SPDM, TDISP, CXL, CHERI, ISO 17825, FIPS 203-205, UCIe
      threat-catalog/                  # 64+ threats across 6 categories
      verification-patterns/           # SVA templates + review checklists
      cross-cutting/                   # SoC family profiles, research currency
```

Each skill directory contains:
- `SKILL.md` — The core skill definition (methodology, process phases, quality standards, worked example)
- `references/` — Deep-dive reference files loaded on demand

---

## Technology Coverage

### Standards

| Standard | Version | Coverage |
|----------|---------|----------|
| TCG DICE | v1.2 | Layered identity, CDI derivation, certificate hierarchy, UDS protection |
| DMTF SPDM | v1.4 | Authentication, measurement, key exchange, secure session |
| PCIe TDISP | 1.0 | Device assignment, TDI states, IDE stream setup, lock/unlock flows |
| CXL Security | 3.1 | TSP, IDE for CXL, cache coherence security, memory encryption |
| RISC-V CHERI | ISA spec | Capability encoding, bounds checking, sealing, compartmentalization |
| ISO 17825 | 2016 | TVLA leakage assessment, non-specific t-test, specific t-test |
| NIST FIPS 203 | 2024 | ML-KEM (Kyber) HW implementation security |
| NIST FIPS 204 | 2024 | ML-DSA (Dilithium) HW implementation security |
| NIST FIPS 205 | 2024 | SLH-DSA (SPHINCS+) HW implementation security |
| UCIe | 1.1 | Die-to-die authentication, link integrity, chiplet trust model |

Compliance overlays: FIPS 140-3, ISO 21434, Common Criteria.

### Threat Catalog

64+ cataloged threats across 6 categories: physical attacks (fault injection, side-channel, probing), firmware attacks (boot chain, rollback, supply chain), interface attacks (PCIe TLP injection, CXL manipulation, DMA), architectural attacks (privilege escalation, TEE breakout, capability forgery), microarchitectural attacks (UARCH-001 to UARCH-020: Spectre, Meltdown, MDS, cache side-channels), kernel attacks (KERN-001 to KERN-015: privilege escalation, container escape, IOMMU bypass).

### SVA Templates

14 parameterized SVA assertion templates covering access control, FSM transitions, register locks -- with `// INTENT:` and `// DOES NOT CHECK:` annotations on every template.

---

## Cross-Family Reuse

Security IP architectures are 70-80% reusable across SoC families. What reuses: crypto engines, boot ROM flows, DICE layers, fuse controllers, debug auth FSMs, TDISP state machines, CHERI capability rules. What varies: bus integration (AXI vs CXL vs PCIe), power domain topology, clock domain crossings, compliance regime (ISO 21434 vs FIPS 140-3), interrupt routing.

The compliance pipeline tracks requirements across families with delta annotations for what changes per family (bus wrapper, compliance artifact, power domain).

---

## Knowledge Accumulation

Your analysis findings accumulate across sessions in a local knowledge base:

- **Findings ledger** (`knowledge-base/findings-ledger.md`) -- Append-only log of significant findings with SoC family, domain, standards, reusability assessment. Skills check this at session start and reference prior findings during analysis.
- **Decision log** (`knowledge-base/decision-log.md`) -- Security architecture decisions with rationale and alternatives considered.

This means your second analysis in a domain builds on your first. A vulnerability found in the automotive TDISP implementation gets flagged when you analyze the data-center variant.

---

## What These Skills Are Not

- **Not a formal verification tool.** SVA templates are candidates for review, never claimed-correct proofs. TLA+ specifications from the tlaplus-security-skill require TLC model checking -- the skill generates specifications, not proofs. Tier 3 properties (information flow, side-channel) are specification-only -- no SVA generated.
- **Not a replacement for domain expertise.** The skills are a structured reasoning assistant, not an expert. They apply frameworks systematically; you provide the judgment.
- **Not a spec database.** Embedded reference material is derived summaries (IP-clean), not verbatim spec text. Version-tagged with "last verified" dates. Always confirm against your working spec version.
- **Not connected to EDA tools.** All inputs and outputs are local Markdown/YAML files. No integration with JasperGold, VC Formal, or other tool chains.

---

## Troubleshooting

### Slash commands not found

If `/soc-security:threat-model` doesn't work:

1. **Check install location:** `ls ~/.claude/skills/soc-security/commands/threat-model.md` — the file must exist.
2. **Check directory name:** The install directory must be `~/.claude/skills/soc-security/` (not `soc-security-skills/`). The directory name determines the slash command prefix.
3. **Restart Claude Code** after installation. Skills are discovered at session start.

### Skills not auto-activating

Skills auto-activate based on keyword detection. If a skill isn't activating:

1. **Be explicit:** Instead of vague requests, mention specific terms: "threat model," "Spectre," "DPA," "kernel hardening," "TLA+."
2. **Use slash commands** for guaranteed activation: `/soc-security:microarch` always activates the microarch-attack-skill.
3. **Check installation:** `ls ~/.claude/skills/soc-security/*-skill/SKILL.md` should list 9 files.

### Skill outputs seem generic

Skills produce better results when you provide specific inputs:

- **Component description** — what the component does, its interfaces, trust boundaries
- **Spec references** — which standard version, which sections apply
- **SoC family** — compute, automotive, client, or data center (affects applicable standards)
- **Existing mitigations** — what's already in place (skills assess residual risk)

---

## Feedback and Contributing

This is v0.2.0 -- the skills are designed to be iterated on based on real usage.

### How to Give Feedback

- **Something wrong in a threat catalog entry?** Open an issue with the threat ID (e.g., `INTF-003`) and what should change.
- **Missing a standard you need?** Open an issue describing the spec, version, and which skill would use it.
- **An SVA template has a bug?** Open an issue with the template name and the correction.
- **The executive brief doesn't land with your audience?** Tell us what audience level, what domain, and what didn't work.
- **A confidence tier feels miscalibrated?** If GROUNDED findings are wrong or SPECULATIVE ones are consistently right, that's signal we need.

### How to Contribute

1. **Improve shared references.** The standards registry, threat catalog, and verification patterns are curated knowledge -- corrections and additions from practitioners are the highest-value contributions.
2. **Add a standard.** Follow the format in `shared-references/soc-security/standards-registry/` -- structured requirement extracts with IDs, derived (not verbatim) from specs.
3. **Add threat entries.** Follow the format in `shared-references/soc-security/threat-catalog/` -- ID, STRIDE category, affected domains, affected families, mitigations, verification tier.
4. **Tune skill prompts.** The SKILL.md files are the prompt engineering layer. If a methodology step consistently produces better results with a tweak, propose it.

### Report Issues

GitHub Issues: [github.com/dtsong/soc-security-skills/issues](https://github.com/dtsong/soc-security-skills/issues)

---

## Roadmap

v0.2.0 delivered the advanced pipeline and formal methods skills. Future candidates:

| Planned | Trigger | Depends On |
|---------|---------|------------|
| **EDA Tool Integration** | Users need direct JasperGold/VC Formal/VCS connectivity | SVA template adoption data |
| **Cross-Family Reuse Engine** | Multiple SoC family analyses completed | Findings ledger + traceability data |
| **Supply Chain Audit** (dedicated skill) | EU Cyber Resilience Act / US EO enforcement | Compliance Pipeline standards expansion |
| **CHERI Analysis** (dedicated skill) | CHERI projects reach production volume | Threat model CHERI knowledge pack |
| **TLC Integration** | TLA+ specs validated by engineers | tlaplus-security-skill usage data |
| **Automated Pipeline Orchestration** | Pipeline usage proves manual orchestration too slow | Advanced pipeline usage data |

---

## License

Apache-2.0. See [LICENSE](LICENSE).

---

*Built with [Claude Code](https://claude.com/claude-code) using the [Council](https://github.com/dtsong/llm-skills) multi-agent deliberation workflow.*
