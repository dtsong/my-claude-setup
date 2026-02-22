# Domain Discovery Frameworks

## Sector Question Banks

Select based on what consultant did NOT mention. Max 2 per bank.

### Government

- "Policy mandate with compliance deadline?"
- "Which competitive bidding process applies?"
- "First-of-kind acquisition or ministry has procured before?"
- "Existing framework agreements to streamline procurement?"
- "Dedicated IT unit or central agency manages tech?"
- "Connectivity at deployment locations?"
- "Existing platforms solution must integrate with?"
- "Political continuity -- administration championed this?"
- "Similar initiative failed previously?"

### Healthcare

- "Interacts with clinical workflows? Which departments?"
- "EHR system/vendor? Integration status?"
- "Involves patient data? Consent mechanisms?"
- "Qualifies as SaMD under applicable regulations?"
- "Pending regulatory changes?"
- "Driven by CMIO, CTO, or clinical head?"

### Agricultural Supply Chain

- "Perishable (cold chain) or shelf-stable crops?"
- "Geographic footprint -- single region, multiple, national?"
- "Producers: smallholders, commercial, cooperatives, mix?"
- "Connectivity at farm/aggregation levels?"
- "Target devices -- feature phones, smartphones, none?"
- "Domestic, export, or both markets?"
- "Existing traceability systems, even informal?"
- "Key intermediaries -- aggregators, cooperatives, traders?"

### Financial Services

- "Core banking platform and last upgrade?"
- "Single or multiple platforms across business lines?"
- "Cloud status -- on-premise, hybrid, cloud-first?"
- "Primary regulatory authority? Multiple regulators?"
- "Under consent orders, enhanced supervision, remediation?"
- "Pending regulatory changes affecting decision?"
- "Risk appetite for technology change?"
- "Significant tech incidents in past 2 years?"

### Energy Infrastructure

- "Vertically integrated utility, independent producer, grid operator, or regulator?"
- "Generation mix and trajectory?"
- "OT/SCADA concern or IT-side?"
- "Regulated or deregulated?"
- "Renewable standards or emissions targets driving decisions?"
- "Age profile of major assets?"
- "Interconnection queue backlog?"
- "Workforce transition challenges?"

## Client Maturity Assessment

Assess on 3 levels from conversational signals. Produces `digitization_level`.

| Dimension | Nascent | Developing | Established |
|---|---|---|---|
| Systems | Paper/spreadsheets | Standalone DB/basic ERP, siloed | Integrated, APIs, cloud |
| Technical capacity | No IT staff | Small team (1-5), maintain only | Dev/ops/security, in-house dev |
| Data | Unstructured, paper/tacit | Basic reporting, inconsistent | Governance, analytics, dashboards |
| Change mgmt | No process, high resistance | Some awareness, reactive | Structured methodology, track record |
| Vendor mgmt | Informal procurement | Basic process, limited | Structured evaluation, diversified |
| Security | No policies | Basic policies | Standards-aligned (ISO 27001/NIST) |

**Composite:** Nascent = simple + capacity building. Developing = moderate complexity, integration feasibility. Established = complex solutions viable. Mixed = tailor to gaps, flag risks.

## Problem Decomposition

### Core Question Patterns

| Consultant Says | Core Question |
|---|---|
| "Choose a technology for X" | Which technology best fits X given constraints? |
| "Evaluate whether Y is right" | Does Y meet needs within acceptable risk? |
| "Digital strategy for Z" | What tech investments to prioritize for Z? |
| "Due diligence on vendor W" | Does W present acceptable risk across all dimensions? |
| "Modernize their V" | What approach delivers best return given constraints? |

### MECE Sub-Question Template

1. **Landscape** -- What options exist?
2. **Fit** -- Which meet specific requirements and constraints?
3. **Risk** -- What risks does each carry? Acceptable?
4. **Cost** -- TCO for each? Investment justified?
5. **Implementation** -- Can the client realistically implement?
6. **Context** -- What regulatory, political, or market factors apply?

Select relevant sub-questions per engagement. Each maps to research threads.

## Constraint Elicitation

| Category | Implicit Signals | Impact |
|---|---|---|
| Budget | Govt developing country = donor-funded; startup = OpEx preferred; pilot = small initial | ROI fidelity level. Donor = compliance constraints. |
| Timeline | Political context = mandate-aligned; "urgent" = unclear deadline | < 3 months narrows scope. Political = affects phasing. |
| Technical | Developing country = limited IT; "legacy" = limited integration; rural = connectivity | Low = include support models. Integration thread. |
| Regulatory | Govt = procurement + sovereignty; healthcare = HIPAA; financial = banking + data localization | Eliminates solution categories early. |
| Political | Tech mandate = pressure; different stakeholder interests; election year | Present options not single recommendation. |

Probe when absent: budget allocated vs. needed, hard vs. flexible deadline, capacity, data residency, alignment.

## Stakeholder Identification

### Inference Patterns

| Client Type | Always-Relevant Roles |
|---|---|
| Government ministry | Perm Sec / Director General, IT/CIO, Procurement |
| Hospital / health system | CMIO / clinical leadership, CTO/IT Director, Compliance |
| Bank / financial institution | CTO/CIO, CRO, Compliance, Board (major decisions) |
| Utility | Grid Ops Director, CTO, Regulatory Affairs |
| Development project | Project Director, Donor representative, Govt counterpart |

Flag inferred stakeholders for confirmation.

### Decision Authority

| Decision | Required Authority |
|---|---|
| Technology purchase > $250K | Board or senior leadership |
| Government procurement | Procurement office mandatory |
| Clinical technology | Clinical leadership sign-off |
| Security-relevant | CISO or security function |
| Budget allocation | CFO or finance director |

## Research Thread Generation

Format: "{Action}: {topic} for {context}". Target 4-6 threads (2+ primary). Cover 6 risk axes.

### Templates by Engagement Type

**Technology Selection:** (1) Landscape scan [Primary], (2) Regulatory analysis [Primary], (3) Integration feasibility [Primary], (4) Cost analysis / TCO [Secondary], (5) Organizational readiness [Secondary], (6) Reference implementations [Secondary].

**Due Diligence:** (1) Vendor assessment [Primary], (2) Technical evaluation [Primary], (3) Regulatory compliance [Primary], (4) Customer references [Secondary], (5) Migration risk [Secondary], (6) Contractual analysis [Secondary].

**Strategic Assessment:** (1) Technology landscape [Primary], (2) Regulatory trajectory [Primary], (3) Peer benchmarking [Primary], (4) Capability gap analysis [Secondary], (5) Investment framework [Secondary], (6) Workforce analysis [Secondary].

Each thread must be self-contained: what to investigate, why, and expected output.
