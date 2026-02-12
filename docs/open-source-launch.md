# Open Source Launch Checklist

Use this one-time checklist when preparing the first broad public launch.

This is separate from `docs/release-checklist.md`, which is for recurring version releases.

## Repository Settings

- [ ] repository description and topics are current
- [ ] default branch protection is configured (required checks and no force push)
- [ ] issue labels are seeded (`bug`, `enhancement`, `docs`, `question`, `good first issue`)

## Community and Policy

- [ ] `README.md` includes a safe default install and opt-in paths
- [ ] `CONTRIBUTING.md` includes validation steps and PR guidance
- [ ] `CODE_OF_CONDUCT.md` and `SECURITY.md` are reviewed and current
- [ ] issue/PR templates are reviewed for launch wording

## Technical Launch Readiness

- [ ] CI passes on pull requests and main
- [ ] secret scanning passes
- [ ] installer tested end-to-end:
  - [ ] `./install.sh --dry-run`
  - [ ] `./install.sh --preset skills`
  - [ ] `./install.sh --preset core`
  - [ ] `./install.sh --preset full`
  - [ ] `./install.sh --uninstall`

## Release and Communication

- [ ] `CHANGELOG.md` has release notes for launch tag
- [ ] launch tag created (for example, `v0.1.0`)
- [ ] GitHub release drafted with highlights and known limitations
- [ ] a short adoption guide exists (`docs/adoption.md`)
