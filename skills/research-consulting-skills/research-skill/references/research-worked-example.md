# Worked Example: State Government Document Management Platform

**Engagement:** A state government agency needs to evaluate document management platforms to replace a legacy system nearing end-of-support. The agency handles sensitive citizen records and must comply with state records retention law and CJIS security policy.

## Phase 1 Output (abbreviated)

**Primary question:** What document management platforms are suitable for a state government agency handling sensitive citizen records under CJIS and state records retention requirements?

**MECE sub-questions:**
1. What platforms have FedRAMP or StateRAMP authorization? (Source: FedRAMP Marketplace [Tier A])
2. Which platforms support CJIS-aligned access controls? (Source: CJIS Security Policy + vendor attestations)
3. What are the records retention automation capabilities? (Source: vendor documentation [Tier C] + analyst reviews [Tier B])
4. What are the data residency and sovereignty constraints? (Source: vendor SLAs + data processing agreements)
5. What is the migration path from the legacy system? (Source: vendor documentation + implementation case studies)
6. What are the TCO indicators over a 5-year horizon? (Source: pricing pages [Tier C] + analyst TCO models [Tier B])

**Sector overlay loaded:** Government Procurement

## Phase 2 Output (abbreviated)

**Longlist: 9 candidates identified**
- High Relevance: DocuVault Pro, GovCloud DMS, OpenText Content Server, Hyland OnBase
- Medium Relevance: M-Files, Laserfiche, SharePoint Online (with compliance add-ons)
- Low Relevance: Box for Government, Google Workspace
- Notable Absence: No open-source platform with FedRAMP authorization found [SOURCE NEEDED - expected: FedRAMP-authorized open-source DMS]

**Shortlist recommendation:** DocuVault Pro, GovCloud DMS, Hyland OnBase, Laserfiche (4 candidates)

## Phase 3 Output (one candidate abbreviated)

**DocuVault Pro - Security Posture:**

| Claim | Source | Tier | Date | Confidence | Flags |
|---|---|---|---|---|---|
| FedRAMP Moderate authorized | FedRAMP Marketplace | A | 2025-12 | High | -- |
| No StateRAMP authorization | StateRAMP registry (absence confirmed) | A | 2026-01 | High | -- |
| CJIS compliance claimed | Vendor compliance page | C | 2025-11 | Low | [VENDOR-AUTHORED] [SINGLE SOURCE - verify independently] |
| SOC 2 Type II certified | AICPA SOC report (referenced, not accessed) | B | 2025-09 | Medium | [PAYWALLED] |

## Phase 5 Output

Assembled `ResearchFindings` contract with all 4 shortlisted candidates, full evidence tables, comparison matrix, methodology notes documenting all searches including dead ends, and 6 preliminary risk flags including "CJIS compliance for DocuVault Pro is vendor-asserted only -- independent audit recommended before procurement."
