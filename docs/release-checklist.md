# Release Checklist

Use this checklist before tagging a release.

## Pre-release

- [ ] `README.md` reflects current installer behavior and presets
- [ ] third-party notices are current (`THIRD_PARTY_NOTICES.md`)
- [ ] no local-only assumptions or paths leaked into docs

## Validation

- [ ] `bash -n install.sh` passes
- [ ] `bash -n hooks/*.sh` passes
- [ ] `bash -n scripts/*.sh` passes
- [ ] `python3 -m json.tool settings.json` passes
- [ ] `python3 -m json.tool hooks.json` passes
- [ ] install and uninstall path tested:
  - [ ] `./install.sh --dry-run`
  - [ ] `./install.sh --preset skills --conflict-policy fail`
  - [ ] `./install.sh --preset core --conflict-policy fail`
  - [ ] `./install.sh --preset full --conflict-policy fail`
  - [ ] `./install.sh --uninstall`

## Publish

- [ ] changelog notes prepared
- [ ] version tag created
- [ ] GitHub release drafted with highlights and migration notes
