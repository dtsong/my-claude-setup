# Task List: /council --page

1. Engine: add `--page [<slug>] [--pick]` at position 4 of the session
   management commands in Argument Parsing (execute and exit).
2. Engine: new `### --page` subsection under Session Management Commands:
   resolve via Resume Logic 1-2 (no-slug = most recent active; slug =
   fuzzy match any status; --pick = picker), rerun scribe, open, always
   print path; pre-F11 sessions get best-effort reconstruction per
   Contract item 3, friendly pointer on failure; brainstorm/no-session
   cases get explicit messages.
3. Engine: add --page to the --help SESSION MANAGEMENT block.
4. council.md: add --page to usage list (and argument-hint if present).
5. Port the same edits to agentic-council (engine + help + README modes
   table if applicable), as part of the next release.
