#!/usr/bin/env bash
set -euo pipefail

# SoC Security Skills Installer
# Installs skills to ~/.claude/skills/soc-security/

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Configuration
INSTALL_DIR="$HOME/.claude/skills/soc-security"
REPO_URL="https://github.com/dtsong/soc-security-skills"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Available skills
ALL_SKILLS=(
  "threat-model-skill"
  "verification-scaffold-skill"
  "compliance-pipeline-skill"
  "executive-brief-skill"
  "microarch-attack-skill"
  "physical-sca-skill"
  "kernel-security-skill"
  "emerging-hw-security-skill"
  "tlaplus-security-skill"
)

# All skills available
AVAILABLE_SKILLS=(
  "threat-model-skill"
  "verification-scaffold-skill"
  "compliance-pipeline-skill"
  "executive-brief-skill"
  "microarch-attack-skill"
  "physical-sca-skill"
  "kernel-security-skill"
  "emerging-hw-security-skill"
  "tlaplus-security-skill"
)

# Role-based presets (bash 3.2 compatible — no associative arrays)
ALL_ROLES="full-suite soc-pipeline advanced-analyst microarch-specialist physical-security kernel-analyst emerging-hw formal-methods full-analysis threat-analyst compliance-engineer executive-communicator"

get_role_skills() {
  case "$1" in
    full-suite)             echo "threat-model-skill,verification-scaffold-skill,compliance-pipeline-skill,executive-brief-skill,microarch-attack-skill,physical-sca-skill,kernel-security-skill,emerging-hw-security-skill,tlaplus-security-skill" ;;
    soc-pipeline)           echo "threat-model-skill,verification-scaffold-skill,compliance-pipeline-skill,executive-brief-skill" ;;
    advanced-analyst)       echo "microarch-attack-skill,physical-sca-skill,kernel-security-skill,emerging-hw-security-skill" ;;
    microarch-specialist)   echo "microarch-attack-skill" ;;
    physical-security)      echo "physical-sca-skill" ;;
    kernel-analyst)         echo "kernel-security-skill" ;;
    emerging-hw)            echo "emerging-hw-security-skill" ;;
    formal-methods)         echo "tlaplus-security-skill" ;;
    full-analysis)          echo "threat-model-skill,verification-scaffold-skill,compliance-pipeline-skill,executive-brief-skill,microarch-attack-skill,physical-sca-skill,kernel-security-skill,emerging-hw-security-skill,tlaplus-security-skill" ;;
    threat-analyst)         echo "threat-model-skill,verification-scaffold-skill" ;;
    compliance-engineer)    echo "compliance-pipeline-skill" ;;
    executive-communicator) echo "executive-brief-skill" ;;
    *)                      echo "" ;;
  esac
}

# Helper functions
info() {
  echo -e "${BLUE}[INFO]${NC} $1"
}

success() {
  echo -e "${GREEN}[SUCCESS]${NC} $1"
}

warn() {
  echo -e "${YELLOW}[WARN]${NC} $1"
}

error() {
  echo -e "${RED}[ERROR]${NC} $1"
  exit 1
}

show_help() {
  cat << EOF
SoC Security Skills Installer

USAGE:
  ./install.sh [OPTIONS]

OPTIONS:
  (no options)           Install all available skills
  --role ROLE            Install role-based preset
  --skills SKILLS        Install specific skills (comma-separated)
  --list                 List available skills and roles
  --update               Update existing installation (git pull)
  --force                Force reinstall (remove and reinstall)
  --help                 Show this help message

ROLES:
  full-suite             All 9 skills (both pipelines + formal methods)
  soc-pipeline           Original 4 skills (threat model → verify → comply → brief)
  advanced-analyst       Advanced 4 skills (microarch, SCA, kernel, emerging HW)
  microarch-specialist   microarch-attack-skill only
  physical-security      physical-sca-skill only
  kernel-analyst         kernel-security-skill only
  emerging-hw            emerging-hw-security-skill only
  formal-methods         tlaplus-security-skill only
  full-analysis          All 9 skills (alias for full-suite)
  threat-analyst         threat-model-skill, verification-scaffold-skill
  compliance-engineer    compliance-pipeline-skill
  executive-communicator executive-brief-skill

SKILLS (Original Pipeline):
  threat-model-skill           Spec-grounded threat identification with STRIDE/attack-tree methodology
  verification-scaffold-skill  Tiered verification checklists and SVA assertion templates
  compliance-pipeline-skill    Requirement-to-evidence compliance mapping with gap analysis
  executive-brief-skill        4-layer abstraction for audience-calibrated executive communication

SKILLS (Advanced Pipeline):
  microarch-attack-skill       Microarchitectural attack analysis (Spectre, Meltdown, cache side-channels)
  physical-sca-skill           Physical side-channel assessment with JIL scoring and ISO 17825
  kernel-security-skill        Kernel security analysis (hardening, isolation, privilege escalation)
  emerging-hw-security-skill   Emerging HW security (PQC, chiplets, heterogeneous compute, AI accelerators)

SKILLS (Formal Methods):
  tlaplus-security-skill       TLA+ formal security property specification and model checking

EXAMPLES:
  ./install.sh
    Install all available skills

  ./install.sh --role threat-analyst
    Install threat-model-skill and verification-scaffold-skill

  ./install.sh --skills threat-model-skill,compliance-pipeline-skill
    Install only selected skills

  ./install.sh --update
    Update existing installation to latest version

  ./install.sh --list
    Show available skills and roles

NOTE: Shared references are always installed regardless of role or skill selection.

INSTALL LOCATION:
  $INSTALL_DIR

For more information, see: $REPO_URL
EOF
}

list_available() {
  echo ""
  echo -e "${BLUE}Available Skills:${NC}"
  echo ""
  for skill in "${AVAILABLE_SKILLS[@]}"; do
    echo "  - $skill"
  done
  echo ""
  echo -e "${BLUE}Available Roles:${NC}"
  echo ""
  for role in $ALL_ROLES; do
    echo "  - $role: $(get_role_skills "$role")"
  done
  echo ""
}

# Parse arguments
MODE="all"
SELECTED_SKILLS=()
UPDATE_MODE=false
FORCE_MODE=false

while [[ $# -gt 0 ]]; do
  case $1 in
    --help)
      show_help
      exit 0
      ;;
    --list)
      list_available
      exit 0
      ;;
    --force)
      FORCE_MODE=true
      shift
      ;;
    --role)
      if [[ -z "${2:-}" ]]; then
        error "Missing role name. Use --list to see available roles."
      fi
      ROLE_RESULT="$(get_role_skills "$2")"
      if [[ -z "$ROLE_RESULT" ]]; then
        error "Unknown role: $2. Use --list to see available roles."
      fi
      MODE="role"
      IFS=',' read -ra SELECTED_SKILLS <<< "$ROLE_RESULT"
      shift 2
      ;;
    --skills)
      if [[ -z "${2:-}" ]]; then
        error "Missing skills list. Use --list to see available skills."
      fi
      MODE="skills"
      IFS=',' read -ra SELECTED_SKILLS <<< "$2"
      shift 2
      ;;
    --update)
      UPDATE_MODE=true
      shift
      ;;
    *)
      error "Unknown option: $1. Use --help for usage."
      ;;
  esac
done

# Validate selected skills
if [[ "$MODE" == "skills" || "$MODE" == "role" ]]; then
  for skill in "${SELECTED_SKILLS[@]}"; do
    if [[ ! " ${AVAILABLE_SKILLS[@]} " =~ " ${skill} " ]]; then
      if [[ " ${ALL_SKILLS[@]} " =~ " ${skill} " ]]; then
        warn "Skill '$skill' is planned but not yet available. Skipping."
      else
        error "Unknown skill: $skill. Use --list to see available skills."
      fi
    fi
  done
  FILTERED_SKILLS=()
  for skill in "${SELECTED_SKILLS[@]}"; do
    if [[ " ${AVAILABLE_SKILLS[@]} " =~ " ${skill} " ]]; then
      FILTERED_SKILLS+=("$skill")
    fi
  done
  SELECTED_SKILLS=("${FILTERED_SKILLS[@]}")

  if [[ ${#SELECTED_SKILLS[@]} -eq 0 ]]; then
    error "No available skills to install."
  fi
fi

# Update mode
if [[ "$UPDATE_MODE" == true ]]; then
  if [[ ! -d "$INSTALL_DIR" ]]; then
    error "Installation not found at $INSTALL_DIR. Use ./install.sh to install first."
  fi
  info "Updating installation at $INSTALL_DIR..."
  cd "$INSTALL_DIR"
  git pull
  success "Installation updated to latest version."
  echo ""
  info "Skills will auto-activate when relevant keywords are detected."
  exit 0
fi

# Check if already installed
if [[ -d "$INSTALL_DIR" ]]; then
  if [[ "$FORCE_MODE" == true ]]; then
    warn "Removing existing installation (--force)..."
    rm -rf "$INSTALL_DIR"
  else
    success "Skills already installed at $INSTALL_DIR"
    echo ""
    info "To update to latest version:  ./install.sh --update"
    info "To force reinstall:           ./install.sh --force"
    exit 0
  fi
fi

# Create install directory
info "Creating installation directory..."
mkdir -p "$INSTALL_DIR"

# Install logic
if [[ "$MODE" == "all" ]]; then
  info "Installing all available skills to $INSTALL_DIR..."

  if [[ -f "$SCRIPT_DIR/CATALOG.md" ]]; then
    info "Installing from local repository..."
    cp -r "$SCRIPT_DIR"/* "$INSTALL_DIR/"
  else
    info "Cloning from $REPO_URL..."
    git clone "$REPO_URL" "$INSTALL_DIR"
  fi

  success "Installed all available skills:"
  for skill in "${AVAILABLE_SKILLS[@]}"; do
    echo "  - $skill"
  done

else
  info "Installing selected skills..."

  mkdir -p "$INSTALL_DIR/shared-references/soc-security"

  for skill in "${SELECTED_SKILLS[@]}"; do
    if [[ -d "$SCRIPT_DIR/$skill" ]]; then
      info "Copying $skill..."
      cp -r "$SCRIPT_DIR/$skill" "$INSTALL_DIR/"
    else
      info "Downloading $skill from $REPO_URL..."
      TEMP_DIR=$(mktemp -d)
      git clone --depth 1 --filter=blob:none --sparse "$REPO_URL" "$TEMP_DIR"
      cd "$TEMP_DIR"
      git sparse-checkout set "$skill"
      cp -r "$skill" "$INSTALL_DIR/"
      cd -
      rm -rf "$TEMP_DIR"
    fi
  done

  if [[ -d "$SCRIPT_DIR/shared-references" ]]; then
    info "Copying shared references..."
    cp -r "$SCRIPT_DIR/shared-references"/* "$INSTALL_DIR/shared-references/"
  else
    info "Downloading shared references..."
    TEMP_DIR=$(mktemp -d)
    git clone --depth 1 --filter=blob:none --sparse "$REPO_URL" "$TEMP_DIR"
    cd "$TEMP_DIR"
    git sparse-checkout set "shared-references"
    cp -r shared-references/* "$INSTALL_DIR/shared-references/"
    cd -
    rm -rf "$TEMP_DIR"
  fi

  for file in CATALOG.md README.md LICENSE; do
    if [[ -f "$SCRIPT_DIR/$file" ]]; then
      cp "$SCRIPT_DIR/$file" "$INSTALL_DIR/"
    else
      curl -sSL "https://raw.githubusercontent.com/dtsong/soc-security-skills/main/$file" -o "$INSTALL_DIR/$file" 2>/dev/null || true
    fi
  done

  success "Installed skills:"
  for skill in "${SELECTED_SKILLS[@]}"; do
    echo "  - $skill"
  done
fi

# Summary
echo ""
success "Installation complete!"
echo ""
info "Installation location: $INSTALL_DIR"
echo ""
info "Skills auto-activate when Claude detects relevant keywords:"
echo ""
echo "  Original Pipeline:"
echo "  - threat-model-skill: threat model, security requirements, STRIDE, attack surface"
echo "  - verification-scaffold-skill: verification checklist, SVA assertions, test plan"
echo "  - compliance-pipeline-skill: compliance mapping, gap analysis, FIPS, ISO 21434"
echo "  - executive-brief-skill: executive brief, security summary, risk register, board update"
echo ""
echo "  Advanced Pipeline:"
echo "  - microarch-attack-skill: Spectre, Meltdown, cache side-channel, speculative execution"
echo "  - physical-sca-skill: DPA, SPA, fault injection, JIL scoring, ISO 17825"
echo "  - kernel-security-skill: kernel hardening, IOMMU, privilege escalation, seccomp"
echo "  - emerging-hw-security-skill: PQC, chiplet, UCIe, AI accelerator, heterogeneous compute"
echo ""
echo "  Formal Methods:"
echo "  - tlaplus-security-skill: TLA+, formal verification, safety property, model checking"
echo ""
info "Pipeline flows:"
echo "  Original:  threat-model → verify → comply → brief"
echo "  Advanced:  component → microarch | physical-sca | kernel | emerging-hw (parallel)"
echo "  Formal:    any findings → tlaplus-security → FormalSecSpec"
echo ""
info "Next steps:"
echo "  1. Start a new conversation in Claude Code"
echo "  2. Describe a security analysis task (e.g., 'Threat model the TDISP device assignment flow')"
echo "  3. Skills will auto-activate based on your workflow phase"
echo ""
info "For more information:"
echo "  - Catalog: $INSTALL_DIR/CATALOG.md"
echo "  - README: $INSTALL_DIR/README.md"
echo "  - GitHub: $REPO_URL"
echo ""
