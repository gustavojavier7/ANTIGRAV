import Mathlib

/-- Critical logarithmic phase for the Collatz/Syracuse block comparison. -/
def alpha : ℝ := logTwoThree - 1

/-- Identification of `alpha` with the base-2 logarithm of `3 / 2`. -/
theorem alpha_eq_log_two_three_halves :
    alpha = Real.log (3 / 2) / Real.log 2 := by
  unfold alpha
  rw [show logTwoThree = Real.log 3 / Real.log 2 by rfl]
  rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)]
  ring

/-- 3. Multiplying the critical phase by a natural number and subtracting that
integer does not change its distance to the nearest integer. -/
theorem nearestIntegerNorm_mul_alpha (r : ℕ) :
    nearestIntegerNorm ((r : ℝ) * alpha) =
      nearestIntegerNorm ((r : ℝ) * logTwoThree) := by
  unfold nearestIntegerNorm alpha
  rw [mul_sub, mul_one, round_sub_natCast]
  push_cast
  congr 1 <;> ring

/-- 4. Rhin's phase gap transferred from `logTwoThree` to the ANTIGRAV
critical phase `alpha = log₂(3/2)`. -/
theorem rhin_phase_gap_alpha
    {c : ℝ}
    (hgap : PhaseGap c (143 / 10 : ℝ))
    {r : ℕ}
    (hr : 0 < r) :
    c * Real.rpow (r : ℝ) (-(133 / 10 : ℝ)) ≤
      nearestIntegerNorm ((r : ℝ) * alpha) := by
  sorry

/-- 5. Distance to the nearest integer is bounded above by the distance to the
ceiling. -/
theorem nearestIntegerNorm_le_ceil_gap (x : ℝ) :
    nearestIntegerNorm x ≤ (Int.ceil x : ℝ) - x := by
  sorry

/-- 6. Rhin's polynomial phase gap gives a lower bound for the critical
ceiling gap used by ANTIGRAV. -/
theorem rhin_le_critical_ceil_gap
    {c : ℝ}
    (hgap : PhaseGap c (143 / 10 : ℝ))
    {r : ℕ}
    (hr : 0 < r) :
    c * Real.rpow (r : ℝ) (-(133 / 10 : ℝ)) ≤
      (Int.ceil ((r : ℝ) * alpha) : ℝ) - (r : ℝ) * alpha := by
  sorry

/-- 7. The exponentially small correction `-log₂(1 - 2⁻ʳ)` is eventually
smaller than any positive Rhin polynomial phase gap. -/
theorem exp_error_eventually_lt_power_gap
    {c : ℝ}
    (hc : 0 < c) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r →
      -(Real.log (1 - (2 : ℝ) ^ (-(r : ℤ))) / Real.log 2) <
        c * Real.rpow (r : ℝ) (-(133 / 10 : ℝ)) := by
  sorry

/-- 8. Eventually the ceiling gap above `r * alpha` dominates the correction
needed to compensate the factor `1 - 2⁻ʳ`. -/
theorem critical_gap_eventually
    {c : ℝ}
    (hc : 0 < c)
    (hgap : PhaseGap c (143 / 10 : ℝ)) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r → 0 < r →
      -(Real.log (1 - (2 : ℝ) ^ (-(r : ℤ))) / Real.log 2) <
        (Int.ceil ((r : ℝ) * alpha) : ℝ) - (r : ℝ) * alpha := by
  sorry

/-- 9. Eventual arithmetic gap: the power of two selected by the critical
ceiling strictly dominates the Collatz block threshold. -/
theorem pow_gap_eventually
    {c : ℝ}
    (hc : 0 < c)
    (hgap : PhaseGap c (143 / 10 : ℝ)) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r → 0 < r →
      3 ^ r <
        2 ^ (Int.toNat (Int.ceil ((r : ℝ) * alpha))) * (2 ^ r - 1) := by
  sorry
