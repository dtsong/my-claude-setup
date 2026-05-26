# cover-letter.md — template

Scaffold for Alan Yu's cover letters. Fill the placeholders; do not invent content beyond `base/alan-resume.json`. Full voice rules live in `base/alan-voice.md` § "Cover letter voice" — read that section before drafting.

## Inputs
- The target JD (company, role, one concrete fact about the company)
- `base/alan-resume.json` (proof points; use only the verified-safe list in `alan-voice.md`)
- Industry calibration already agreed with Alan (if non-retail, see SKILL.md step 3)

## Output
Write to `output/Cover_Letter_[CompanyName].md`. Plain markdown, no front matter.

## Hard rules (every letter)
- 180–220 words. Count before finishing.
- First person, active voice, Alan's measured verbs (managed, led, delivered, built, implemented). Do NOT upgrade to owned/drove/spearheaded without flagging for Alan.
- Em-dash cap 0–1 across resume AND letter combined. Aim for zero. Use commas/semicolons.
- One concrete proof point per paragraph, drawn only from the verified-safe list.
- No "I am writing to apply for" opener. No "Please find my resume attached" close.
- Close with: "based in San Diego, available for in-person interviews."
- Lead with why-them before why-me.

## Structure
```
[Date]
[Hiring Manager / Hiring Team], [Company]

[OPENING — 2-3 sentences]
Why this role and why Alan. Name the company and one concrete, specific fact
about them or the role. Connect it to Alan's retail-systems track record.

[MIDDLE — 2-3 short paragraphs, one proof point each]
Map 2-3 JD priorities to verified accomplishments. Examples to pull from:
- 3 Cegid Y2 upgrades, 51 stores / 5 countries, zero downtime
- ITSM build on Jira/Confluence: 40% ticket reduction, 2 hrs/day MTTR cut
- Cegid–Salesforce integration; reconciliation time down 60%
- Ranorex: 109 automated test cases, 30% QA cycle reduction
- Vendor management / SOW review (Michaels, 1,200+ stores)
- 33% vendor cost reduction (Alexander Wang)
Reframe honestly for the JD's industry; never claim items on the "should NOT
claim" list.

[CLOSE — 1-2 sentences]
Specific interest in the company + call to action. End with the San Diego line.

Sincerely,
Alan Yu
```

## Compact example (opening + one proof, retail JD)
> Your move to unify in-store and digital inventory across all North American
> locations is exactly the kind of omnichannel work I have spent the last six
> years on at Hermès. As Americas systems lead, I supported 51 stores across
> five countries and delivered the integration connecting them to a single
> commerce platform.
>
> Reliability at scale is where I do my best work. I ran three Cegid Y2
> platform upgrades with zero deployment downtime and built the ITSM practice
> that cut ticket volume 40% and mean time to resolution by two hours a day.

## Before returning the letter
1. Recount words (180–220).
2. Grep for em-dashes; confirm 0–1 total across resume + letter.
3. Confirm every claim traces to `base/alan-resume.json`.
4. List any verb you strengthened beyond Alan's palette, for his review.
