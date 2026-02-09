#!/bin/bash
# pokemon-hook.sh — Pokemon battle-themed Claude Code hook dispatcher
# Handles: Notification (permission_prompt, idle_prompt), Stop, TaskCompleted
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SOUND_DIR="$SCRIPT_DIR/sounds/pokemon"

# Read JSON from stdin (hooks always pipe JSON)
INPUT="$(cat)"

# ── ANSI color codes ─────────────────────────────────────────────────────────
RESET='\033[0m'
BOLD='\033[1m'
RED='\033[31m'
GREEN='\033[32m'
YELLOW='\033[33m'
BLUE='\033[34m'
MAGENTA='\033[35m'
WHITE='\033[37m'
BG_RED='\033[41m'
BG_BLUE='\033[44m'
BG_YELLOW='\033[43m'
BG_MAGENTA='\033[45m'
BLACK='\033[30m'

# ── Parse fields from JSON without jq ────────────────────────────────────────
get_json_string() {
  echo "$INPUT" | grep -o "\"$1\"[[:space:]]*:[[:space:]]*\"[^\"]*\"" | head -1 | sed 's/.*:[[:space:]]*"\([^"]*\)"/\1/' || true
}

HOOK_EVENT="$(get_json_string hook_event_name)"
TOOL_NAME="$(get_json_string tool_name)"
NOTIFICATION_TYPE="$(get_json_string notification_type)"

# Extract tool_input.command (nested)
TOOL_COMMAND=""
if echo "$INPUT" | grep -q '"tool_input"' 2>/dev/null; then
  TOOL_COMMAND="$(echo "$INPUT" | grep -o '"command"[[:space:]]*:[[:space:]]*"[^"]*"' | head -1 | sed 's/.*:[[:space:]]*"\([^"]*\)"/\1/' || true)"
fi

# ── Sound debounce ───────────────────────────────────────────────────────────
DEBOUNCE_FILE="/tmp/claude-pokemon-sound-last"
DEBOUNCE_MS=1500

can_play() {
  local now
  now=$(python3 -c 'import time; print(int(time.time()*1000))' 2>/dev/null || date +%s000)
  local last
  last=$(cat "$DEBOUNCE_FILE" 2>/dev/null || echo 0)
  if (( now - last >= DEBOUNCE_MS )); then
    echo "$now" > "$DEBOUNCE_FILE"
    return 0
  fi
  return 1
}

# ── Sound playback helper ────────────────────────────────────────────────────
play_sound() {
  local sound_file="$SOUND_DIR/$1"
  local volume="${2:-0.5}"
  if [[ -f "$sound_file" ]] && can_play; then
    afplay -v "$volume" "$sound_file" 2>/dev/null &
  fi
}

# ── macOS notification helper ────────────────────────────────────────────────
notify() {
  osascript -e "display notification \"$2\" with title \"$1\"" 2>/dev/null &
}

# ── stderr message helper ────────────────────────────────────────────────────
msg() {
  echo -e "$1" >&2
}

# ── Pokeball ASCII art ───────────────────────────────────────────────────────
pokeball_art() {
  case "$1" in
    pokeball)
      msg "  ${RED}${BOLD}    ┌─ Pokeball ─┐${RESET}"
      msg "  ${RED}      ╭────────╮${RESET}"
      msg "  ${RED}     ╱ ${BG_RED}${WHITE}▓▓▓▓▓▓▓▓${RESET}${RED} ╲${RESET}"
      msg "  ${RED}    │ ${BG_RED}${WHITE}▓▓▓▓▓▓▓▓▓▓${RESET}${RED} │${RESET}"
      msg "  ${WHITE}    ├────⚪────┤${RESET}"
      msg "  ${WHITE}    │ ░░░░░░░░░░ │${RESET}"
      msg "  ${WHITE}     ╲ ░░░░░░░░ ╱${RESET}"
      msg "  ${WHITE}      ╰────────╯${RESET}" ;;
    greatball)
      msg "  ${BLUE}${BOLD}    ┌─ Great Ball ─┐${RESET}"
      msg "  ${BLUE}      ╭────────╮${RESET}"
      msg "  ${BLUE}     ╱ ${BG_BLUE}${WHITE}▓▓▒▒▓▓▒▒${RESET}${BLUE} ╲${RESET}"
      msg "  ${BLUE}    │ ${BG_BLUE}${WHITE}▓▓▒▒▓▓▒▒▓▓${RESET}${BLUE} │${RESET}"
      msg "  ${RED}    ├───${WHITE}─⚪─${RED}───┤${RESET}"
      msg "  ${WHITE}    │ ░░░░░░░░░░ │${RESET}"
      msg "  ${WHITE}     ╲ ░░░░░░░░ ╱${RESET}"
      msg "  ${WHITE}      ╰────────╯${RESET}" ;;
    ultraball)
      msg "  ${YELLOW}${BOLD}    ┌─ Ultra Ball ─┐${RESET}"
      msg "  ${YELLOW}      ╭────────╮${RESET}"
      msg "  ${BLACK}${BG_YELLOW}     ╱ ████████ ╲${RESET}"
      msg "  ${BLACK}${BG_YELLOW}    │ ██████████ │${RESET}"
      msg "  ${YELLOW}    ├───${WHITE}─⚪─${YELLOW}───┤${RESET}"
      msg "  ${BLACK}    │ ██████████ │${RESET}"
      msg "  ${BLACK}     ╲ ████████ ╱${RESET}"
      msg "  ${BLACK}      ╰────────╯${RESET}" ;;
    masterball)
      msg "  ${MAGENTA}${BOLD}  ┌─ Master Ball ── ⚠ DANGER ⚠ ─┐${RESET}"
      msg "  ${MAGENTA}      ╭────────╮${RESET}"
      msg "  ${MAGENTA}     ╱ ${BG_MAGENTA}${WHITE}▓▓▓${BOLD}M${RESET}${BG_MAGENTA}${WHITE}▓▓▓▓${RESET}${MAGENTA} ╲${RESET}"
      msg "  ${MAGENTA}    │ ${BG_MAGENTA}${WHITE}▓▓▓▓${BOLD}MM${RESET}${BG_MAGENTA}${WHITE}▓▓▓▓${RESET}${MAGENTA} │${RESET}"
      msg "  ${MAGENTA}${BOLD}    ├───${WHITE}─⚪─${MAGENTA}───┤${RESET}"
      msg "  ${MAGENTA}    │ ${BG_MAGENTA}${WHITE}░░░░░░░░░░${RESET}${MAGENTA} │${RESET}"
      msg "  ${MAGENTA}     ╲ ${BG_MAGENTA}${WHITE}░░░░░░░░${RESET}${MAGENTA} ╱${RESET}"
      msg "  ${MAGENTA}      ╰────────╯${RESET}" ;;
  esac
}

# ── Classify Pokeball tier based on tool + command ───────────────────────────
classify_tier() {
  local tool="$1" cmd="$2"

  # Master Ball: dangerous commands
  if [[ "$tool" == "Bash" && -n "$cmd" ]]; then
    if echo "$cmd" | grep -qiE 'rm -rf|rm -fr|--force|force.push|push --force|push -f|sudo |docker (rm|rmi|prune|stop|kill)|deploy|DROP TABLE|DROP DATABASE|DELETE FROM|truncate|mkfs|dd if=|:\(\)\{ :|shutdown|reboot|systemctl (stop|disable)' 2>/dev/null; then
      echo "masterball"; return
    fi
  fi

  # Ultra Ball: system operations
  case "$tool" in
    Bash|Task|TaskCreate|SendMessage|TeamCreate|Skill) echo "ultraball"; return ;;
  esac

  # Great Ball: edit operations
  case "$tool" in
    Edit|Write|NotebookEdit) echo "greatball"; return ;;
  esac

  # Pokeball: everything else
  echo "pokeball"
}

# ── Tier → sound file mapping ────────────────────────────────────────────────
tier_sound() {
  case "$1" in
    pokeball)   echo "move-select.wav" ;;
    greatball)  echo "super-effective.wav" ;;
    ultraball)  echo "critical-hit.wav" ;;
    masterball) echo "explosion.wav" ;;
  esac
}

tier_label() {
  case "$1" in
    pokeball)   echo "Pokeball" ;;
    greatball)  echo "Great Ball" ;;
    ultraball)  echo "Ultra Ball" ;;
    masterball) echo "Master Ball - DANGER" ;;
  esac
}

tier_emoji() {
  case "$1" in
    pokeball)   echo "🔴" ;;
    greatball)  echo "🔵" ;;
    ultraball)  echo "🟡" ;;
    masterball) echo "🟣" ;;
  esac
}

# ══════════════════════════════════════════════════════════════════════════════
# Main event routing
# ══════════════════════════════════════════════════════════════════════════════
case "$HOOK_EVENT" in

  Stop)
    play_sound "your-turn.wav" 0.3
    ;;

  TaskCompleted)
    play_sound "pokemon-caught.wav" 0.5
    notify "Gotcha!" "Pokemon caught! Task completed!"
    msg "  ${GREEN}${BOLD}⭐ Gotcha! Task completed!${RESET}"
    ;;

  Notification)
    case "$NOTIFICATION_TYPE" in
      permission_prompt)
        TIER="$(classify_tier "$TOOL_NAME" "$TOOL_COMMAND")"
        play_sound "$(tier_sound "$TIER")" 0.5

        TOOL_DESC="$TOOL_NAME"
        if [[ -n "$TOOL_COMMAND" ]]; then
          [[ ${#TOOL_COMMAND} -gt 80 ]] && TOOL_COMMAND="${TOOL_COMMAND:0:77}..."
          TOOL_DESC="$TOOL_NAME: $TOOL_COMMAND"
        fi

        notify "$(tier_emoji "$TIER") $(tier_label "$TIER")" "Claude wants to use: $TOOL_DESC"
        pokeball_art "$TIER"
        ;;
      idle_prompt)
        play_sound "low-hp.wav" 0.4
        notify "Low HP!" "Claude is waiting for your input..."
        ;;
    esac
    ;;
esac

exit 0
