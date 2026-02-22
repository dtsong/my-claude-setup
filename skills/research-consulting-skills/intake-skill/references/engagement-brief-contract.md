# EngagementBrief Typed Contract

## Contract Schema

```
EngagementBrief {
  metadata: {
    engagement_id: string        // Format: {YYYY-MM}-{client-sector}-{technology-area}
    created_date: string         // ISO-8601: YYYY-MM-DD
    domain_tags: string[]        // Lowercase kebab-case domain identifiers
    sensitivity_tier: string     // "open" | "sensitive" | "restricted"
  }
  client_context: {
    organization: string         // Name or [Client] if Sensitive/Restricted
    industry: string             // Canonical sector value
    size: string                 // Organization size description
    region: string               // Country/region
    regulatory_environment: string  // Key regulatory frameworks applicable
    digitization_level: string   // Assessment of current technical maturity
  }
  pain_point: {
    description: string          // 1-2 sentence problem statement
    severity: string             // "critical" | "significant" | "moderate" | "exploratory"
    current_state: string        // How the problem is currently handled
  }
  stakeholders: [{
    name: string                 // Name or role title
    role: string                 // Organizational role
    decision_authority: string   // "approve" | "recommend" | "inform"
    technical_depth: string      // "executive" | "functional" | "technical"
    deliverable_need: string     // What this stakeholder needs from the engagement
  }]
  scope: {
    in_scope: string[]           // Specific items within scope
    out_of_scope: string[]       // Explicit exclusions
    deferred: string[]           // Items that may enter scope later
    constraints: {
      budget: string             // Range, envelope, or "To be determined"
      timeline: string           // Hard deadlines or driving events
      technical_capacity: string // Client's implementation and maintenance capability
      regulatory: string         // Applicable regulations
      political: string          // Political sensitivities
    }
  }
  success_criteria: string[]     // Measurable outcomes that define engagement success
  research_plan: {
    investigation_threads: [{
      name: string               // Thread title
      description: string        // What to investigate and why
      priority: string           // "primary" | "secondary"
    }]
    anticipated_risk_dimensions: string[]  // Which 6-axis dimensions are most material
    roi_fidelity_level: string   // "full" | "structured" | "qualitative"
  }
  timeline: {
    start: string                // Date or "Upon confirmation"
    milestones: string[]         // Key milestone descriptions
    deadline: string             // Hard deadline or "Flexible"
  }
  open_questions: string[]       // Information gaps flagged for follow-up
}
```

## Contract Guarantees

The EngagementBrief provides these guarantees to downstream skills:

1. **Metadata is always complete.** `engagement_id`, `created_date`, `domain_tags`, and `sensitivity_tier` are always populated. Downstream skills can rely on these for filing and retrieval.

2. **Pain point is always present.** `pain_point.description` is always populated with a precise problem statement. This anchors all downstream research and assessment.

3. **At least one stakeholder is mapped.** The `stakeholders` array is never empty. At minimum, the consultant is listed with their role and authority level.

4. **Scope has explicit boundaries.** Both `in_scope` and `out_of_scope` are populated. Downstream skills must not investigate topics in `out_of_scope`.

5. **Research plan is actionable.** `investigation_threads` contains 4-6 threads the research-skill can begin investigating immediately. Threads are specific enough to guide a literature scan and landscape analysis.

6. **Open questions are transparent.** Information gaps are listed in `open_questions`. Downstream skills should flag when an open question affects their output quality.

7. **Sensitivity tier is enforced.** All content already complies with the sensitivity tier's handling rules. Downstream skills inherit and enforce the same tier.
