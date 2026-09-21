# `prove2me-mcp-readonly` integration boundary

This directory is intentionally separate from the ANTIGRAV Lean package.  It
records the auxiliary tool expected for Prove2Me inspection, but does **not**
vendor or impersonate the upstream project: the repository was not publicly
resolvable during this iteration.

## Fail-closed installation

1. Obtain the authoritative, reviewed `prove2me-mcp-readonly` source out of band.
2. Pin its reviewed commit in `UPSTREAM.toml`.
3. Install it outside this repository and outside the Lean build.
4. Run `tests/audit_prove2me_readonly.sh` before enabling the MCP server.

Until those steps are possible, DAG lookup is **UNIMPLEMENTED** and the bridge
in `Prove2MeBridge.lean` remains conditional.

## Frozen capability boundary

The integrated tool must expose only fixed read operations.  No tool input may
accept credentials, arbitrary URLs, arbitrary HTTP methods, arbitrary headers,
or mutation payloads.  The tool must not expose publish, create, update, delete,
or generic-request operations.  Secrets must be injected only by the trusted
runtime boundary, never by an agent-controlled argument or versioned file.

No Prove2Me credential is required or stored by this repository.
