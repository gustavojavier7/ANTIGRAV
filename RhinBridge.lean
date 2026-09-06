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
