---
name: "Documentation Plan"
department: "chronicler"
description: "Documentation architecture with audience mapping, onboarding paths, and maintenance schedules"
version: 1
triggers:
  - "documentation"
  - "docs"
  - "README"
  - "guide"
  - "onboarding"
  - "wiki"
  - "tutorial"
  - "knowledge base"
---

# Documentation Plan

## Purpose

Design a comprehensive documentation architecture that maps content types to audiences, defines onboarding paths, and establishes maintenance schedules. Produces a documentation strategy that scales with the team and codebase.

## Inputs

- Project type and scope (library, application, platform, API)
- Target audiences (developers, API consumers, end users, operators)
- Current documentation state (what exists, what's missing, what's stale)
- Team size and growth expectations

## Process

### Step 1: Identify Documentation Audiences

Map each audience and their needs:
- **New developers**: Getting started, local setup, architecture overview, "where is X?" answers
- **Experienced team members**: API reference, design decisions, runbooks, troubleshooting guides
- **API consumers**: Authentication, endpoint reference, rate limits, SDKs, changelog
- **End users**: Feature guides, FAQs, tutorials, release notes
- **Operators/SREs**: Deployment procedures, monitoring runbooks, incident response, infrastructure docs
- For each audience, define their entry point, primary tasks, and information needs

### Step 2: Map Documentation Types Needed

Catalog required documentation:
- **Getting started**: Quick start, prerequisites, installation, "hello world" in under 5 minutes
- **API reference**: Endpoint docs, type definitions, error codes, authentication
- **Architecture overview**: System diagram, component responsibilities, data flow, key decisions
- **Runbooks**: Operational procedures, incident response, common troubleshooting steps
- **User guides**: Feature walkthroughs, best practices, common patterns
- **Tutorials**: Step-by-step learning paths, progressive complexity, working examples

### Step 3: Define Documentation Structure

Apply the Diataxis framework:
- **Tutorials**: Learning-oriented — guided lessons that teach through doing
- **How-to guides**: Task-oriented — steps to achieve a specific goal
- **Explanation**: Understanding-oriented — background, context, design rationale
- **Reference**: Information-oriented — accurate, complete technical descriptions
- Map each existing and planned document to its Diataxis category, identify gaps

### Step 4: Specify Format and Location

Define where each doc type lives:
- **In-repo markdown**: Architecture docs, ADRs, contributing guides (versioned with code)
- **Generated API docs**: Auto-generated from code/types (OpenAPI, TypeDoc, Storybook)
- **Wiki/knowledge base**: Runbooks, onboarding guides, team processes (frequently updated)
- **Inline code docs**: JSDoc/TSDoc for public APIs, README per module/package
- Establish naming conventions, directory structure, and linking strategy

### Step 5: Plan Developer Onboarding Flow

Design progressive onboarding:
- **Day 1**: Environment setup, run the app locally, make a trivial change, deploy to dev
- **Week 1**: Architecture overview, codebase tour, key abstractions, first real task
- **Month 1**: Deep-dive into owned area, understand cross-cutting concerns, contribute to docs
- Include checkpoints, mentorship touchpoints, and feedback collection
- Create an onboarding checklist that tracks progress

### Step 6: Design Documentation Testing

Ensure documentation stays accurate:
- **Link checking**: Automated broken link detection in CI
- **Code sample validation**: Test that code examples compile/run (extract and execute in CI)
- **Freshness reviews**: Flag docs not updated in N months, assign review owners
- **Screenshot/diagram validation**: Process for updating visual assets when UI changes
- **Feedback mechanism**: Easy way for readers to report issues ("Was this helpful?" + issue link)

### Step 7: Define Maintenance Schedule

Establish ongoing documentation health:
- **Review cadence**: Quarterly full review, monthly spot-checks on high-traffic docs
- **Ownership per section**: Every doc section has an owner responsible for accuracy
- **Staleness detection**: Automated alerts when docs haven't been updated alongside related code changes
- **Deprecation process**: How to mark docs as outdated, redirect to replacements, eventually remove
- **Contribution guidelines**: How to write docs, style guide, review process for doc PRs

## Output Format

```markdown
# Documentation Plan: [Project Name]

## Documentation Map

| Doc Type | Audience | Format | Location | Owner | Status |
|----------|----------|--------|----------|-------|--------|
| Getting Started | New devs | Markdown | /docs/getting-started.md | [team] | [exists/needed/stale] |
| API Reference | API consumers | Generated | /docs/api/ | [team] | ... |
| Architecture | All devs | Markdown + diagrams | /docs/architecture/ | [team] | ... |
| Runbooks | Operators | Wiki | [wiki URL] | [team] | ... |
| ... | ... | ... | ... | ... | ... |

## Diataxis Mapping

| Category | Documents | Gap Analysis |
|----------|-----------|--------------|
| Tutorials | [list] | [what's missing] |
| How-to Guides | [list] | [what's missing] |
| Explanation | [list] | [what's missing] |
| Reference | [list] | [what's missing] |

## Onboarding Path

```
Day 1: [Setup] → [Run app] → [Trivial change] → [Deploy to dev]
  ↓
Week 1: [Architecture tour] → [Codebase walkthrough] → [First task]
  ↓
Month 1: [Deep-dive] → [Cross-cutting concerns] → [Doc contribution]
```

## Maintenance Schedule

| Cadence | Activity | Owner | Automation |
|---------|----------|-------|------------|
| Per PR | Link checking | CI | Automated |
| Monthly | High-traffic doc review | Rotating | Reminder |
| Quarterly | Full doc audit | Tech lead | Staleness report |

## Ownership Matrix

| Section | Primary Owner | Backup | Last Review |
|---------|--------------|--------|-------------|
| Getting Started | [name] | [name] | [date] |
| API Reference | [name] | [name] | [date] |
| ... | ... | ... | ... |
```

## Quality Checks

- [ ] All target audiences are identified with their specific documentation needs
- [ ] Documentation types are mapped to the Diataxis framework with gap analysis
- [ ] Format and location are specified for each doc type (in-repo, generated, wiki)
- [ ] Developer onboarding path covers day 1, week 1, and month 1 milestones
- [ ] Documentation testing includes link checking and code sample validation
- [ ] Maintenance schedule defines review cadence and staleness detection
- [ ] Every documentation section has an assigned owner
- [ ] Contribution guidelines exist for writing and reviewing documentation

## Evolution Notes
<!-- Observations appended after each use -->
