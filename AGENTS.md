# AGENTS.md — PCA Construction Rules

## Scope
This file governs any coding agent working on PCA inside ANTIGRAV.

PCA is a modular pseudo-imperative machine inspired by BASIC-style explicit `GOTO` control flow.

> **FAIL FIRST.**

When correctness, authority, semantics, or state validity cannot be established, stop before mutating state or fabricating meaning.

## Authority
- `Main.lean` is the mathematical authority.
- `pca.lean` is a derived, manipulable PCA image of that corpus.
- Never silently weaken, strengthen, reinterpret, or replace `Main.lean`.
- A generated `pca.lean` should record source provenance: source file, source hash, generator version, PCA format version.

## Architecture
Preserve the current modular separation:

```text
Antigrav/PCA/
  Core/
  Rom/
  Compiler/
  Engine/
  Interface/
```

Conceptually:

```text
Interface → Compiler → CompiledQuery → Engine/vCPU → ROM → Lean authority
```

Do not collapse layers without an explicit architectural task.

## Pseudo-Imperative Paradigm
Preferred conceptual form:

```text
0100 SET ...
0110 COMPUTE ...
0120 IF condition THEN GOTO 0200
0130 GOTO 0300
0200 ...
9999 STOP
```

Rules:
1. Labels are persistent semantic addresses, not source lines.
2. Numeric order does not define control flow.
3. `GOTO` moves only to an explicit mapped address.
4. Branches require an explicit evaluator.
5. `STOP` halts execution; it does not prove or refute a target.
6. Control-flow success never creates mathematical authority.

## FAIL FIRST — Construction
Use this loop:

```text
1 problem
→ 1 minimal patch
→ build
→ test
→ audit invariants
→ stop
```

Do not continue automatically to the next architectural task.

## FAIL FIRST — Runtime
Before state mutation:

```text
VALIDATE
IF invalid THEN FAULT
ONLY THEN MUTATE
```

Runtime faults must be atomic:

```text
FAULT ⇒ NO PARTIAL STATE MUTATION
```

Unimplemented semantics fail closed.

Forbidden substitutions:
- unknown branch → guessed branch
- missing computation → dummy value
- missing proof → placeholder evidence
- missing authorization → sealed result

## Mathematical Authority
Agents, compiler, runtime and vCPU may parse, route, schedule, transform representations and request verification.

They may not invent mathematical authority.

Formal authority must follow an explicit chain:

```text
REQUEST
→ FORMAL VERIFICATION
→ VERIFIED EVIDENCE
→ COMMIT
→ PROOF STORE
→ AUTHORIZED RESULT
```

Verification ≠ commitment.
Commitment ≠ result sealing.
STOP ≠ proof.

## State Discipline
Keep separate:
- machine state
- trace/logs
- data writes
- proof writes
- result writes

A result must not become `proved` or `refuted` merely because execution reached a convenient address.

## ROM Discipline
A valid ROM must support checks for:
- entry exists
- all referenced addresses exist
- no duplicate addresses
- terminal exists
- terminal decodes as STOP
- ROM version known
- source provenance known

## ROM-BIOS
Prefer a small boot self-test before execution:

```text
POWER_ON
VERIFY ARCHITECTURE
VERIFY RUNTIME
VERIFY ROM
VERIFY TERMINAL
VERIFY BASIC ISA
VERIFY STATE ATOMICITY
IF any check fails THEN BOOT_FAULT
GOTO ENTRY
```

ROM-BIOS is the operational root of trust.
Lean remains the mathematical root of trust.

## Derived `pca.lean`
Target role:

```text
pca.lean
  ├── provenance header
  ├── mathematical corpus image
  ├── semantic labels
  ├── PCA ROM/control nodes
  └── consistency/build checks
```

The first goal is not to translate every Lean proof into imperative instructions.
The first goal is to build a faithful control image over the existing corpus.

## Agent Work Protocol
For every task:

```text
READ TASK
READ AGENTS.md
READ RELEVANT ARCHITECTURE / INVARIANTS
INSPECT CURRENT CODE
IDENTIFY ONE MINIMAL CHANGE
IMPLEMENT
BUILD
TEST
REPORT
STOP
```

If a requested change conflicts with a frozen invariant, report the conflict and stop.

## Reporting
Report:
- task
- files changed
- behavior added/removed
- build result
- test result
- invariants checked
- open problems

Distinguish clearly:
`COMPILES`, `TESTED`, `FORMALLY VERIFIED`, `ASSUMED`, `UNIMPLEMENTED`.

## Global Rule

```text
FAIL FIRST.
EXPLICIT STATE.
EXPLICIT CONTROL.
EXPLICIT AUTHORITY.
ONE STEP AT A TIME.
```
