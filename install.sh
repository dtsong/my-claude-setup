#!/bin/bash
# install.sh — Install this repository into a user's Claude Code config.
#
# Default behavior is intentionally minimal and safe:
# - installs skills only
# - does NOT replace ~/.claude/settings.json, ~/.claude/hooks.json, or ~/.claude/CLAUDE.md unless explicitly requested
# - does NOT overwrite regular files/directories (conflict policy defaults to fail)
set -euo pipefail

REPO_DIR="$(cd "$(dirname "$0")" && pwd)"
CLAUDE_DIR="${CLAUDE_DIR:-$HOME/.claude}"
CONFLICT_POLICY="fail"
PRESET="skills"
DRY_RUN=0

WITH_SETTINGS=0
WITH_HOOKS_JSON=0
WITH_HOOKS_SCRIPTS=0
WITH_CLAUDE_MD=0

SKILLS_CSV=""

MANAGED_DIR="$CLAUDE_DIR/.managed"
MANIFEST_PATH="$MANAGED_DIR/my-claude-setup.json"

usage() {
  cat <<EOF
Usage: ./install.sh [options]

Defaults:
  - preset: skills
  - conflict policy: fail
  - install target: $CLAUDE_DIR (override with CLAUDE_DIR=/path)

Presets:
  --preset skills   Install skills only (default)
  --preset core     Install skills + commands + agents
  --preset full     Install core + scripts + hooks scripts + workspaces

Skills:
  --list-skills              List available skill packs.
  --skills <csv>             Install only the named skill packs (directories under ./skills/).

Opt-in config:
  --with-settings            Link settings.json into ~/.claude/settings.json
  --with-hooks-json          Link hooks.json into ~/.claude/hooks.json
  --with-hooks-scripts       Link hook scripts into ~/.claude/hooks/
  --with-claude-md           Link CLAUDE.md into ~/.claude/CLAUDE.md

Safety and maintenance:
  --conflict-policy fail|skip  Behavior when a target path exists and is not a symlink.
  --dry-run                   Print planned actions without writing.
  --uninstall                 Remove symlinks created by this installer.
  -h, --help                  Show this help.
EOF
}

die() {
  echo "Error: $*" >&2
  exit 1
}

is_managed_link() {
  local link_path="$1"
  local expected_target="$2"

  if [[ ! -L "$link_path" ]]; then
    return 1
  fi

  local resolved
  resolved="$(readlink "$link_path" || true)"
  [[ "$resolved" == "$expected_target" ]]
}

list_skill_packs() {
  if [[ ! -d "$REPO_DIR/skills" ]]; then
    die "Missing skills directory: $REPO_DIR/skills"
  fi

  echo "Available skill packs"
  local any=0
  local d
  for d in "$REPO_DIR/skills"/*; do
    [[ -d "$d" ]] || continue
    [[ "$(basename "$d")" == "skills" ]] && continue
    echo "- $(basename "$d")"
    any=1
  done

  if [[ "$any" -eq 0 ]]; then
    echo "(none)"
  fi
}

split_csv() {
  local csv="$1"
  python3 - "$csv" <<'PY'
import sys

csv = sys.argv[1]
items = [s.strip() for s in csv.split(",") if s.strip()]
for item in items:
    print(item)
PY
}

collect_links_for_preset() {
  local preset="$1"
  local -a links=()

  # Base directories used by all presets.
  links+=("DIR::$CLAUDE_DIR")
  links+=("DIR::$CLAUDE_DIR/skills")

  case "$preset" in
    skills)
      ;;
    core)
      links+=("DIR::$CLAUDE_DIR/commands")
      links+=("DIR::$CLAUDE_DIR/agents")
      ;;
    full)
      links+=("DIR::$CLAUDE_DIR/commands")
      links+=("DIR::$CLAUDE_DIR/agents")
      links+=("DIR::$CLAUDE_DIR/scripts")
      links+=("DIR::$CLAUDE_DIR/hooks")
      links+=("DIR::$CLAUDE_DIR/workspaces")
      ;;
    *)
      die "Unknown preset: $preset"
      ;;
  esac

  # Skill packs
  local -a skill_packs=()
  if [[ -n "$SKILLS_CSV" ]]; then
    while IFS= read -r item; do
      skill_packs+=("$item")
    done < <(split_csv "$SKILLS_CSV")
  else
    local d
    for d in "$REPO_DIR/skills"/*; do
      [[ -d "$d" ]] || continue
      [[ "$(basename "$d")" == "skills" ]] && continue
      skill_packs+=("$(basename "$d")")
    done
  fi

  local pack
  for pack in "${skill_packs[@]}"; do
    if [[ ! -d "$REPO_DIR/skills/$pack" ]]; then
      die "Unknown skill pack: $pack (expected directory: skills/$pack)"
    fi
    links+=("LINK::$REPO_DIR/skills/$pack::$CLAUDE_DIR/skills/$pack")
  done

  # Commands / agents for core/full
  if [[ "$preset" == "core" || "$preset" == "full" ]]; then
    local f
    for f in "$REPO_DIR/commands"/*.md; do
      [[ -f "$f" ]] || continue
      links+=("LINK::$f::$CLAUDE_DIR/commands/$(basename "$f")")
    done
    for f in "$REPO_DIR/agents"/*.md; do
      [[ -f "$f" ]] || continue
      links+=("LINK::$f::$CLAUDE_DIR/agents/$(basename "$f")")
    done
  fi

  # Full preset extras
  if [[ "$preset" == "full" ]]; then
    local f
    for f in "$REPO_DIR/scripts"/*.sh; do
      [[ -f "$f" ]] || continue
      links+=("LINK::$f::$CLAUDE_DIR/scripts/$(basename "$f")")
    done
    for f in "$REPO_DIR/hooks"/*.sh; do
      [[ -f "$f" ]] || continue
      links+=("LINK::$f::$CLAUDE_DIR/hooks/$(basename "$f")")
    done

    local w
    for w in "$REPO_DIR/workspaces"/*; do
      [[ -e "$w" ]] || continue
      links+=("LINK::$w::$CLAUDE_DIR/workspaces/$(basename "$w")")
    done
  fi

  # Explicit opt-ins
  if [[ "$WITH_SETTINGS" -eq 1 ]]; then
    links+=("LINK::$REPO_DIR/settings.json::$CLAUDE_DIR/settings.json")
  fi
  if [[ "$WITH_HOOKS_JSON" -eq 1 ]]; then
    links+=("LINK::$REPO_DIR/hooks.json::$CLAUDE_DIR/hooks.json")
  fi
  if [[ "$WITH_HOOKS_SCRIPTS" -eq 1 && "$preset" != "full" ]]; then
    links+=("DIR::$CLAUDE_DIR/hooks")
    local f
    for f in "$REPO_DIR/hooks"/*.sh; do
      [[ -f "$f" ]] || continue
      links+=("LINK::$f::$CLAUDE_DIR/hooks/$(basename "$f")")
    done
  fi
  if [[ "$WITH_CLAUDE_MD" -eq 1 ]]; then
    links+=("LINK::$REPO_DIR/CLAUDE.md::$CLAUDE_DIR/CLAUDE.md")
  fi

  printf '%s\n' "${links[@]}"
}

collect_conflicts() {
  local -a plan
  plan=()
  while IFS= read -r line; do
    plan+=("$line")
  done < <(collect_links_for_preset "$PRESET")

  local -a conflicts=()
  local entry kind
  for entry in "${plan[@]}"; do
    kind="${entry%%::*}"
    if [[ "$kind" == "DIR" ]]; then
      local dir_path="${entry#DIR::}"
      if [[ -e "$dir_path" && ! -d "$dir_path" ]]; then
        conflicts+=("$dir_path")
      fi
      continue
    fi

    if [[ "$kind" == "LINK" ]]; then
      local target_path="${entry##*::}"
      if [[ -e "$target_path" && ! -L "$target_path" ]]; then
        conflicts+=("$target_path")
      fi
    fi
  done

  if [[ "${#conflicts[@]}" -eq 0 ]]; then
    return 0
  fi

  echo "Detected install path conflicts:"
  local c
  for c in "${conflicts[@]}"; do
    echo "- $c"
  done
  echo ""
  echo "Conflicts happen when files/directories already exist and are not symlinks."
  echo "Recommended: move or remove conflicting paths, then rerun ./install.sh"

  if [[ "$CONFLICT_POLICY" == "fail" ]]; then
    echo ""
    echo "Aborting install due to conflict policy: fail"
    echo "To proceed without replacing conflicting paths, rerun with:"
    echo "  ./install.sh --conflict-policy skip"
    return 1
  fi

  echo ""
  echo "Continuing with conflict policy: skip"
  echo "Only non-conflicting paths will be linked."
  return 0
}

write_manifest() {
  local preset="$1"
  shift

  mkdir -p "$MANAGED_DIR"

  local tmp
  tmp="$(mktemp)"
  printf '%s\n' "$@" > "$tmp"

  python3 - "$MANIFEST_PATH" "$REPO_DIR" "$preset" "$tmp" <<'PY'
import json
import os
import sys
from datetime import datetime, timezone

manifest_path, repo_dir, preset, pairs_path = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]

items = []
with open(pairs_path, "r", encoding="utf-8") as f:
    for line in f.read().splitlines():
        if not line.strip():
            continue
        src, dst = line.split("::", 1)
        items.append({"source": src, "path": dst})

data = {
    "version": 1,
    "repo_dir": repo_dir,
    "preset": preset,
    "installed_at": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
    "items": items,
}

os.makedirs(os.path.dirname(manifest_path), exist_ok=True)
with open(manifest_path, "w", encoding="utf-8") as f:
    json.dump(data, f, indent=2)
    f.write("\n")
PY

  rm -f "$tmp"
}

install() {
  collect_conflicts || [[ "$CONFLICT_POLICY" == "skip" ]] || exit 1

  local -a plan
  plan=()
  while IFS= read -r line; do
    plan+=("$line")
  done < <(collect_links_for_preset "$PRESET")

  echo "Install target: $CLAUDE_DIR"
  echo "Preset: $PRESET"
  if [[ -n "$SKILLS_CSV" ]]; then
    echo "Skills: $SKILLS_CSV"
  else
    echo "Skills: (all)"
  fi

  if [[ "$DRY_RUN" -eq 1 ]]; then
    echo ""
    echo "Dry run: planned actions"
  fi

  local -a installed_pairs=()
  local entry kind
  for entry in "${plan[@]}"; do
    kind="${entry%%::*}"

    if [[ "$kind" == "DIR" ]]; then
      local dir_path="${entry#DIR::}"
      if [[ "$DRY_RUN" -eq 1 ]]; then
        echo "  mkdir -p $dir_path"
      else
        mkdir -p "$dir_path"
      fi
      continue
    fi

    if [[ "$kind" == "LINK" ]]; then
      local remainder="${entry#LINK::}"
      local src="${remainder%%::*}"
      local dst="${remainder##*::}"

      if [[ -e "$dst" && ! -L "$dst" ]]; then
        if [[ "$CONFLICT_POLICY" == "skip" ]]; then
          echo "  conflict: $dst exists and is not a symlink (skipped)"
          continue
        fi
        die "Conflict: $dst exists and is not a symlink"
      fi

      if [[ "$DRY_RUN" -eq 1 ]]; then
        echo "  ln -sfn $src $dst"
      else
        mkdir -p "$(dirname "$dst")"
        ln -sfn "$src" "$dst"
      fi
      installed_pairs+=("$src::$dst")
      continue
    fi
  done

  if [[ "$DRY_RUN" -eq 1 ]]; then
    echo ""
    echo "Dry run complete. No changes made."
    return 0
  fi

  # Write manifest for safe uninstall.
  write_manifest "$PRESET" "${installed_pairs[@]}"

  echo ""
  echo "Done. Installed ${#installed_pairs[@]} link(s)."
  echo "Tip: rerun with --preset core or --preset full to adopt more of the setup."
}

uninstall() {
  echo "Uninstall target: $CLAUDE_DIR"

  local removed=0

  # Preferred path: remove only what is recorded in the manifest.
  if [[ -f "$MANIFEST_PATH" ]]; then
    while IFS= read -r path; do
      [[ -n "$path" ]] || continue
      if [[ -L "$path" ]]; then
        rm "$path"
        echo "  removed $path"
        removed=$((removed + 1))

        # Best-effort cleanup of empty parent dirs (never errors).
        rmdir "$(dirname "$path")" 2>/dev/null || true
      fi
    done < <(
      python3 - "$MANIFEST_PATH" <<'PY'
import json
import sys

data = json.load(open(sys.argv[1], "r", encoding="utf-8"))
for item in data.get("items", []):
    print(item.get("path", ""))
PY
    )

    rm "$MANIFEST_PATH"
    rmdir "$MANAGED_DIR" 2>/dev/null || true
  fi

  # Legacy cleanup: previous versions symlinked top-level directories.
  local legacy
  for legacy in CLAUDE.md settings.json hooks.json commands skills agents scripts hooks workspaces; do
    local target="$CLAUDE_DIR/$legacy"
    local expected="$REPO_DIR/$legacy"
    if is_managed_link "$target" "$expected"; then
      rm "$target"
      echo "  removed legacy $target"
      removed=$((removed + 1))
    fi
  done

  if [[ "$removed" -eq 0 ]]; then
    echo "  No managed symlinks found — nothing to remove."
  else
    echo "Done. Removed $removed symlink(s)."
  fi
}

main() {
  if [[ "${1:-}" == "--uninstall" ]]; then
    uninstall
    exit 0
  fi

  while [[ $# -gt 0 ]]; do
    case "$1" in
      --preset)
        [[ -n "${2:-}" ]] || die "--preset requires a value (skills|core|full)"
        PRESET="$2"
        shift 2
        ;;
      --conflict-policy)
        [[ -n "${2:-}" ]] || die "--conflict-policy requires a value (fail|skip)"
        [[ "$2" == "fail" || "$2" == "skip" ]] || die "Invalid conflict policy: $2"
        CONFLICT_POLICY="$2"
        shift 2
        ;;
      --dry-run)
        DRY_RUN=1
        shift
        ;;
      --skills)
        [[ -n "${2:-}" ]] || die "--skills requires a comma-separated list"
        SKILLS_CSV="$2"
        shift 2
        ;;
      --list-skills)
        list_skill_packs
        exit 0
        ;;
      --with-settings)
        WITH_SETTINGS=1
        shift
        ;;
      --with-hooks-json)
        WITH_HOOKS_JSON=1
        shift
        ;;
      --with-hooks-scripts)
        WITH_HOOKS_SCRIPTS=1
        shift
        ;;
      --with-claude-md)
        WITH_CLAUDE_MD=1
        shift
        ;;
      -h|--help)
        usage
        exit 0
        ;;
      *)
        die "Unknown option: $1"
        ;;
    esac
  done

  install
}

main "$@"
