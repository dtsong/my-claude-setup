# Engagement Scoping Patterns

## Scope Zones

Every scope item falls into one of three zones:

**Zone 1 -- In Scope:** Actively investigated. Must be specific (two consultants agree on boundary), connected to problem statement. Active language: "Evaluate IoT sensors for cold chain" not "Cold chain."

**Zone 2 -- Out of Scope:** Explicit exclusions of reasonable expectations. Every brief needs 1+. Common: implementation, change management, contract negotiation, training.

**Zone 3 -- Deferred:** May enter scope on trigger. Each needs trigger condition. Max 0-3; many = scope too uncertain.

## Scope Item Patterns

### In Scope

| Pattern | Example |
|---|---|
| Evaluate [tech category] for [use case] | Evaluate IoT sensors for post-harvest loss monitoring in tropical agriculture |
| Assess [product/vendor] against [criteria] | Assess TempTrack Pro against data sovereignty and integration requirements |
| Compare [options] on [dimensions] | Compare cloud-native vs. on-premise core banking on TCO, compliance, migration risk |
| Analyze [constraint] for [context] | Analyze data sovereignty requirements for cloud deployment in Ghana |
| Investigate [capability] for [need] | Investigate offline-capable mobile solutions for field-level produce tracking |

### Out of Scope

| Pattern | Example |
|---|---|
| [Adjacent topic] -- [reason] | End-user training design -- engagement assesses training needs only |
| [Broader scope] -- [boundary] | Full supply chain assessment -- focuses on post-harvest loss reduction |
| [Downstream activity] -- [phase] | Vendor contract negotiation -- produces evaluation and recommendation only |

### Deferred

| Pattern | Example |
|---|---|
| [Item] -- if [condition] | Phase 2 implementation planning -- if client approves recommended solution |
| [Item] -- pending [info] | Additional sector analysis -- pending confirmation of cross-sector scope |
| [Item] -- based on [finding] | Detailed security audit -- if risk gate flags Security at Significant or higher |

## Scope Boundary Inference

Infer from: (1) problem statement, (2) engagement type, (3) stated deliverable, (4) timeline, (5) budget. Flag inferred boundaries for confirmation.

## Success Criteria Patterns

| Pattern | Template | Example |
|---|---|---|
| Completeness | "Produces [deliverable] including [elements]" | "Evaluates 5+ solutions against all 6 risk dimensions" |
| Decision enablement | "Enables [stakeholder] to [decision]" | "Enables Perm Sec to select with clear trade-offs" |
| Coverage/depth | "Covers [scope] with [evidence standard]" | "8+ candidates scanned, 3-5 in detailed evaluation" |
| Constraint satisfaction | "Recommendations comply with [constraint]" | "All solutions comply with data sovereignty" |
| Stakeholder needs | "[Stakeholder] receives [deliverable]" | "IT receives technical appendix with architecture" |

Criteria must be evaluable, cover core question, and be achievable within timeline.

## Timeline Templates

| Type | Duration | Constraints |
|---|---|---|
| Standard | 6-8 wks | Full depth. Wk1: brief. Wk2-3: landscape. Wk4-5: assessment. Wk6-7: draft. Wk8: final. |
| Accelerated | 3-4 wks | 5-8 candidates, 3 deep dives. Single audience. Overlapping phases. |
| Extended | 10-12 wks | Client review cycles. 10-15 candidates. Multi-audience. Mid-point gates. |

Gates need clear outputs. Document external dependencies. Include 1+ review cycle.

## Scope Risk Checklist

| Risk | Warning Signs | Mitigation |
|---|---|---|
| Ambiguity | Broad terms; no exclusions; multiple expectations | Specific items; 3+ exclusions; confirm per stakeholder |
| Creep | Post-confirmation additions; broad problem statement | Explicit exclusions; deferred with triggers; re-scope protocol |
| Misalignment | Different depth expectations; no primary decision-maker | Stakeholder map; identify primary audience; layered deliverables |
| Info access | Unconfirmed client data; unsecured vendor cooperation | Early dependency ID; access deadlines; contingency approaches |
| Constraint discovery | Unfamiliar regulatory env; no constraints in intake | Prioritize regulatory questions; load industry overlay |

## Multi-Stakeholder Tensions

| Tension | Resolution |
|---|---|
| Breadth vs. depth | Layer deliverable: exec summary + technical appendix |
| Speed vs. thoroughness | Accelerated timeline, scope constraints, flag gaps as open questions |
| Recommendation vs. options | Same data, different framing per audience |
| Technical vs. business | Both threads, separate gates, layered deliverable |

## Brief Quality Gate

### Completeness

- Metadata: engagement_id, created_date, domain_tags, sensitivity_tier
- Client: organization, sector, region, digitization level, size
- Problem: 1-2 sentences describing problem (not project), no prescribed solution
- Constraints: 1+ per category (budget, timeline, technical, regulatory, political) or "TBD"
- Stakeholders: 1+ with `approve` authority; each has role, authority, depth, deliverable need
- Scope: 3+ in-scope (specific, action-oriented), 1+ out-of-scope, deferred have triggers
- Success criteria: 2+ evaluable, covering core question
- Research: 4-6 threads (2+ primary), MECE, cover risk dimensions
- Open questions: all gaps listed
- Timeline: start, deadline, milestones with outputs

### Consistency

- Sensitivity tier consistent (no name leaks in Sensitive/Restricted)
- Threads align with scope; timeline consistent with thread count

### Actionability

- Research-skill can begin without additional questions
- Threads specific enough to generate search queries
