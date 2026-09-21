#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
manifest="$root/tools/prove2me-mcp-readonly/UPSTREAM.toml"

test -f "$manifest"
test "$(sed -n 's/^enabled = //p' "$manifest")" = false

for capability in \
  allows_write_operations \
  allows_agent_supplied_credentials \
  allows_agent_supplied_urls \
  allows_agent_supplied_http_methods \
  allows_agent_supplied_headers
do
  test "$(sed -n "s/^${capability} = //p" "$manifest")" = false
done

if rg -n --hidden --glob '!README.md' \
    '(PROVE2ME_API_KEY|Bearer[[:space:]]|https?://)' \
    "$root/tools/prove2me-mcp-readonly"
then
  echo "forbidden secret or endpoint material in read-only helper boundary" >&2
  exit 1
fi

echo "prove2me read-only boundary: fail-closed"
