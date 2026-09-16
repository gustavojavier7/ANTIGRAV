import Mathlib

/-!
# Vendored minimal Rhin phase-gap interface

This file reproduces the interface used by `RhinBridge.lean` from the
ProofAtlas checked source for `Erdos1135.ND.PhaseGap`, pinned at commit
`a7e937d2c87047b2275323c5f186e6e8bdefceb3`.

It intentionally contains only the three declarations consumed by ANTIGRAV:
`logTwoThree`, `nearestIntegerNorm`, and `PhaseGap`.

## Vendor status (FAIL FIRST)

Target endpoint (not present in this repository):

```lean
Erdos1135.ND.existsPhaseGapRhin :
  ∃ c : ℝ, Erdos1135.ND.PhaseGap c (143 / 10 : ℝ)
```

Attempted source:
* ProofAtlas formalization page historically at
  `proofatlas.ai/formalizations/rhin-phase-gap-log2-three/`
* package commit pin `a7e937d2c87047b2275323c5f186e6e8bdefceb3`
* expected closure shape (secondary notes only): ~40 first-party files /
  ~8926 lines; `Erdos1135/NumberTheory/Rhin/` ~14 files / ~5960 lines
  including `LargeHeight.lean`; surface theorem file often cited as
  `RhinPhaseGap.lean`

**First real blocker:** the pinned ProofAtlas Rhin Lean sources are not
retrievable from this environment.

* `proofatlas.ai` / `www.proofatlas.ai` do not resolve (DNS NXDOMAIN /
  refused).
* Commit `a7e937d2c87047b2275323c5f186e6e8bdefceb3` is not hosted on any
  searchable public Git repository found during this attempt.
* No public mirror of `RhinPhaseGap.lean`, `Erdos1135/NumberTheory/Rhin/*`,
  or the Rhin source ZIP was located (GitHub code search, Lech Mazur public
  Lean repos, third-party notes under `senamakel/math-superagent` and
  `Moatazg/proofatlas-notes` — notes only, no Lean bodies).
* Therefore the dependency closure of `existsPhaseGapRhin` cannot be
  vendored, adapted, or checked.

FAIL FIRST response: stop before inventing a proof, axiom, `sorry`, or
`admit`. Keep this interface-only file. Do not connect OneBlockGap here.

The checked ProofAtlas endpoint `Erdos1135.ND.existsPhaseGapRhin` is NOT
asserted here and no axiom is introduced.
-/

namespace Erdos1135
namespace ND

/-- `log_2 3`, represented with natural logarithms. -/
noncomputable def logTwoThree : ℝ :=
  Real.log 3 / Real.log 2

/-- Distance from a real number to the nearest integer. -/
noncomputable def nearestIntegerNorm (x : ℝ) : ℝ :=
  |x - (round x : ℝ)|

/-- Power-law phase-gap interface. -/
structure PhaseGap (c kappa : ℝ) : Prop where
  c_pos : 0 < c
  c_le_one : c ≤ 1
  two_lt_kappa : 2 < kappa
  gap : ∀ q : ℕ, 0 < q →
    c * Real.rpow (q : ℝ) (1 - kappa) ≤
      nearestIntegerNorm ((q : ℝ) * logTwoThree)

end ND
end Erdos1135
