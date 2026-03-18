#!/usr/bin/env bash
set -euo pipefail

# Check security headers for a URL
# Usage: security-headers-check.sh <url>

URL="${1:?URL required. Usage: security-headers-check.sh https://example.com}"

# Validate URL format
if [[ ! "$URL" =~ ^https?:// ]]; then
  echo "ERROR: URL must start with http:// or https://"
  exit 1
fi

echo "Checking security headers for: $URL"
echo ""

HEADERS=$(curl -sI -o /dev/null -w '%header{strict-transport-security}|%header{x-content-type-options}|%header{x-frame-options}|%header{content-security-policy}|%header{x-xss-protection}|%header{referrer-policy}|%header{permissions-policy}' "$URL" 2>/dev/null || curl -sI "$URL" 2>/dev/null)

# Fallback: parse headers manually
RESPONSE=$(curl -sI "$URL" 2>/dev/null)

check_header() {
  local name="$1"
  local value
  value=$(echo "$RESPONSE" | grep -i "^${name}:" | head -1 | sed 's/^[^:]*: //' | tr -d '\r')
  if [[ -n "$value" ]]; then
    echo "PASS: $name: $value"
  else
    echo "FAIL: $name: MISSING"
  fi
}

echo "=== Required Headers ==="
check_header "Strict-Transport-Security"
check_header "X-Content-Type-Options"
check_header "X-Frame-Options"
check_header "Content-Security-Policy"

echo ""
echo "=== Recommended Headers ==="
check_header "Referrer-Policy"
check_header "Permissions-Policy"
check_header "X-XSS-Protection"

echo ""
echo "Done."
