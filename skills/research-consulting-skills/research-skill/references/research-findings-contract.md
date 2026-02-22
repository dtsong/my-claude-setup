# ResearchFindings Output Contract

## Typed Definition

```
ResearchFindings {
  metadata: {
    engagement_id: string,          // Format: {YYYY-MM}-{sector}-{tech}
    research_date: string,          // ISO-8601 date
    domain_tags: string[],          // Broad domain tags for retrieval
    technology_areas: string[],     // Specific technology tags
    prior_art_checked: boolean,     // Was knowledge base consulted?
    prior_art_references: string[], // IDs of prior engagements referenced (optional)
    sensitivity_tier: enum("open", "sensitive", "restricted"),
    researcher_notes: string        // Free-form caveats (optional)
  },

  engagement_brief_ref: string,    // Path to brief or "none"

  findings: [{
    technology_or_process: string,  // Candidate name
    description: string,            // 2-3 sentence description

    sources: [{
      url: string,                  // URL or DOI
      type: enum("academic", "analyst", "standards", "industry", "vendor", "community"),
      tier: enum("A", "B", "C"),
      date: string,                 // Publication date (ISO-8601)
      verification_status: enum("verified", "unverified", "source_needed"),
      flags: string[]               // Bias flags, staleness flags, etc.
    }],

    confidence: enum("high", "medium", "low"),

    relevance_to_brief: string,     // How candidate addresses the research question

    comparison_dimensions: {
      security_posture: string,     // Rating + confidence
      vendor_viability: string,
      regulatory_alignment: string,
      integration_capability: string,
      adoption_maturity: string,
      exit_strategy: string,
      cost_structure: string,
      technical_capability: string
    },

    preliminary_risk_flags: string[] // Early risk indicators for assessment-skill
  }],

  landscape_summary: string,       // Narrative market overview

  gaps_identified: string[],       // Specific, actionable research gaps

  methodology_notes: string        // What was searched, what was not found
}
```

## YAML Template

```yaml
ResearchFindings:
  metadata:
    engagement_id: "{YYYY-MM}-{client-sector}-{technology-area}"
    research_date: "{YYYY-MM-DD}"
    domain_tags:
      - "{domain tag 1}"
      - "{domain tag 2}"
    technology_areas:
      - "{technology area 1}"
      - "{technology area 2}"
    prior_art_checked: true | false
    prior_art_references:
      - "{prior engagement_id, if any}"
    sensitivity_tier: "open | sensitive | restricted"
    researcher_notes: "{any caveats about scope, constraints, or methodology}"

  engagement_brief_ref: "{path to engagement brief or 'none - consultant-provided scope'}"

  findings:
    - technology_or_process: "{Candidate Name}"
      description: "{2-3 sentence description of what it is and does}"
      sources:
        - url: "{source URL or DOI}"
          type: "{academic | analyst | standards | industry | vendor | community}"
          tier: "A | B | C"
          date: "{YYYY-MM-DD or YYYY-MM}"
          verification_status: "verified | unverified | [SOURCE NEEDED]"
          flags: ["list of any flags, e.g., VENDOR-AUTHORED, STALE, PAYWALLED"]
      confidence: "high | medium | low"
      relevance_to_brief: "{How this candidate addresses the research question}"
      comparison_dimensions:
        security_posture: "{rating + confidence}"
        vendor_viability: "{rating + confidence}"
        regulatory_alignment: "{rating + confidence}"
        integration_capability: "{rating + confidence}"
        adoption_maturity: "{rating + confidence}"
        exit_strategy: "{rating + confidence}"
        cost_structure: "{rating + confidence}"
        technical_capability: "{rating + confidence}"
      preliminary_risk_flags:
        - "{risk flag 1}"
        - "{risk flag 2}"

  landscape_summary: |
    {Narrative summary of the technology landscape. Written for a reader
    who has not seen the engagement brief. Covers market structure,
    maturity stage, key players, notable trends, and areas of rapid change.}

  gaps_identified:
    - "{Gap 1: What you could not find and where to look}"
    - "{Gap 2: What requires consultant or client action}"

  methodology_notes: |
    {Document what was searched, in what order, and what was NOT found.
    Include search terms used, databases consulted, date range of search,
    and any access limitations encountered.}
```

## Methodology Notes Requirements

The methodology notes section is mandatory. Document:

1. **What was searched:** Every source category consulted, with specific databases, publications, or repositories named.
2. **Search terms used:** Actual queries or keywords used to discover sources.
3. **Date range:** The temporal scope of the search.
4. **What was NOT found:** Expected sources that did not exist, searches that returned no results, topics with no independent coverage.
5. **Access limitations:** Paywalled sources that could not be verified, databases requiring institutional access, information behind vendor NDA.
6. **Completeness assessment:** Honest assessment of whether the research captures the full landscape or whether significant blind spots remain.

## Preliminary Risk Flags

Identify risk signals that foreshadow what the assessment-skill will evaluate. These are signals, not scores.

Common flags:
- **Vendor concentration risk:** Market dominated by 1-2 vendors with limited alternatives
- **Maturity concerns:** Technology below TRL 7 considered for production use
- **Regulatory uncertainty:** Pending regulation that could change the compliance landscape
- **Security gaps:** Known vulnerabilities or missing certifications
- **Integration complexity:** No standard APIs or proprietary data formats
- **Community health:** Declining contributor base for open-source options
- **Cost trajectory:** Pricing model that scales unfavorably
- **Adoption plateau:** Technology losing momentum after initial adoption wave
