#!/bin/bash
# notify-complete.sh - Send completion notification for agent tasks
# Usage: notify-complete.sh <branch-name> [task-summary]

BRANCH="${1:-unknown}"
SUMMARY="${2:-Task completed}"

# Detect OS
if [[ "$OSTYPE" == "darwin"* ]]; then
    # macOS - use osascript for notification
    osascript -e "display notification \"$SUMMARY\" with title \"Claude Agent Complete\" subtitle \"$BRANCH\""

    # Play completion sound
    afplay /System/Library/Sounds/Glass.aiff 2>/dev/null &

elif [[ "$OSTYPE" == "linux-gnu"* ]]; then
    # Linux - try notify-send
    if command -v notify-send &> /dev/null; then
        notify-send "Claude Agent Complete" "$BRANCH: $SUMMARY"
    fi

    # Try to play sound
    if command -v paplay &> /dev/null; then
        paplay /usr/share/sounds/freedesktop/stereo/complete.oga 2>/dev/null &
    elif command -v aplay &> /dev/null; then
        aplay /usr/share/sounds/alsa/Front_Center.wav 2>/dev/null &
    fi
fi

echo "Notification sent: $BRANCH - $SUMMARY"
