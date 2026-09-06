import Mathlib

/-!
# Vendored minimal Rhin phase-gap interface

This file reproduces the interface used by `RhinBridge.lean` from the
ProofAtlas checked source for `Erdos1135.ND.PhaseGap`, pinned at commit
`a7e937d2c87047b2275323c5f186e6e8bdefceb3`.

It intentionally contains only the three declarations consumed by ANTIGRAV:
`logTwoThree`, `nearestIntegerNorm`, and `PhaseGap`.

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
