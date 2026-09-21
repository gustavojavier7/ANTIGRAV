# ANTIGRAV / Prove2Me integration — iteration 1

## Status vocabulary

- **COMPILES:** checked by Lean 4.33.1 in this repository.
- **TESTED:** exercised by a command listed below.
- **FORMALLY VERIFIED:** proved by Lean without `sorry`.
- **ASSUMED:** conditional input, not authority produced by ANTIGRAV.
- **UNIMPLEMENTED:** intentionally fail-closed pending authoritative data.

No theorem was published and no Prove2Me write operation was enabled.

## Minimal port strategy

The repository previously selected the Lean 4.34.0 release candidate.  The
minimum port changes the project to stable Lean 4.33.1 and mathlib `v4.33.1`.
Using mathlib `v4.33.0` was tested first and rejected: it pins Lean 4.33.0, so
its compiled cache cannot be used by Lean 4.33.1.

Rather than port all of `main.lean`, two independent modules were extracted:

1. `Antigrav.Prove2Me.Accelerated` contains only `v2`, `collatzExponent`, and
   `Tstar`, which are needed to state the future Syracuse bridge.
2. `Antigrav.Prove2Me.AffineCore` contains the selected affine/parity kernel.

`main.lean` imports both modules, so there is one Lean declaration for each
extracted result rather than a copied second theorem.  Its pre-extraction
SHA-256 is recorded in `AffineCore.lean`.  The dedicated `Prove2MeCore` Lake
target does not import `main` or `RhinBridge`.

## Selected theorem/declaration dependency closure

The following is the minimal logical closure relevant to the requested names
(documentation and examples in the extracted source are not dependencies):

- `AffineDescriptor`: `Nat` fields only.
- `AffineRealizes`: `AffineDescriptor`.
- `parityCodeDescriptor`: `ParityCode`, `parityBitDescriptor`, `affineId`,
  and `affineCompose`.
- `parityCodeDescriptor_lift_high`: `AffineRealizes`,
  `parityCodeDescriptor`, `parityOnes`, `affineRealizes_lift_high`,
  `parityCodeDescriptor_pow2`, and `parityCodeDescriptor_pow3`.
- `parityCodeDescriptor_injective`: `parityCodeDescriptor`,
  `parityCodeDescriptor_pow2_eq_zero_iff`,
  `parityCodeDescriptor_correction_even_iff_head_false`,
  `correction_cons_false_even`, `correction_cons_true_odd`, and
  `parityBitDescriptor_left_cancel`.
- `ExactParityState`: `Nat` fields only.
- `refineExactParityState`: `ExactParityState` and `exactLiftValue`.
- `refineExactParityState_affineRealizes`:
  `exactStateOfParity`, `refineExactParityState`, `parityLiftBit`,
  `exactNextBool`, `parityCodeDescriptor_lift_bit_exact`,
  `refineExactParityState_parityStep`, `parityStep_affineRealizes`,
  `parityCodeDescriptor_append`, and `affineCompose_realizes`.  Their closure
  includes the lift/power lemmas above plus `exactNextBit`,
  `refineExactParityState_value_mul_two`, `ParityStep`, and the descriptor
  constructors.

All are **COMPILES** under the dedicated target.  The named results and their
proof dependencies are **FORMALLY VERIFIED**; no `sorry` was introduced.

## Dependence on `RhinBridge`

The selected kernel has **zero Lean import dependence** on `RhinBridge`:
`Accelerated.lean` and `AffineCore.lean` import only `Mathlib`, and
`Prove2MeBridge.lean` imports only those two modules.  The original full
`main.lean` still imports `RhinBridge`, because removing that unrelated
analytic dependency is outside this one-step task.

## Prove2Me boundary and blocker

The exact Prove2Me Syracuse declaration, namespace, normalization (one ordinary
step versus an accelerated odd step), domain, and orientation were unavailable.
The public source location for `prove2me-mcp-readonly` was also unresolved.
Accordingly:

- `Prove2MeSyracuseSpec` is an explicit **ASSUMED** interface obligation;
- `tstar_eq_prove2me_syracuse_of_spec` is a conditional, **FORMALLY VERIFIED**
  bridge and not a publication-ready identification;
- importing the actual Prove2Me declaration and discharging that obligation is
  **UNIMPLEMENTED**;
- DAG lookup, theorem-ID resolution, and comparison against existing Prove2Me
  results are blocked on reviewed read-only DAG/API access;
- publishing and every mutation operation remain disabled.

The auxiliary-tool boundary is recorded under
`tools/prove2me-mcp-readonly/`.  It is disabled until an authoritative commit
can be pinned and audited.  Its manifest denies agent-supplied credentials,
URLs, HTTP methods, headers, and all write operations.

## Reproduction

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake update mathlib
lake build Prove2MeCore
lake build Antigrav
lake env lean main.lean
bash tests/audit_prove2me_readonly.sh
```

## Next concrete theorem

After importing the authoritative Prove2Me module, formalize exactly one
unconditional theorem replacing the temporary obligation:

```lean
theorem tstar_eq_prove2me_syracuse (m : ℕ) (hm : Odd m) :
    Tstar m = Prove2Me.<authoritative_syracuse_name> m := by
  -- unfold only the authoritative Prove2Me definition and Tstar;
  -- prove the normalization equality without a new axiom.
```

The theorem must be adjusted rather than forced if the DAG shows a different
domain or iteration convention.  Only after that theorem compiles should a
second bridge be selected.
