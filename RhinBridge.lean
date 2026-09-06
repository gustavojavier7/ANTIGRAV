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
  have h := hgap.gap r hr
  rw [← nearestIntegerNorm_mul_alpha r] at h
  convert h using 1 <;> norm_num

/-- 5. Distance to the nearest integer is bounded above by the distance to the
ceiling. -/
theorem nearestIntegerNorm_le_ceil_gap (x : ℝ) :
    nearestIntegerNorm x ≤ (Int.ceil x : ℝ) - x := by
  unfold nearestIntegerNorm
  calc
    |x - (round x : ℝ)| ≤ |x - (Int.ceil x : ℝ)| :=
      round_le x (Int.ceil x)
    _ = (Int.ceil x : ℝ) - x := by
      rw [abs_of_nonneg]
      · ring
      · linarith [Int.le_ceil x]

/-- 6. Rhin's polynomial phase gap gives a lower bound for the critical
ceiling gap used by ANTIGRAV. -/
theorem rhin_le_critical_ceil_gap
    {c : ℝ}
    (hgap : PhaseGap c (143 / 10 : ℝ))
    {r : ℕ}
    (hr : 0 < r) :
    c * Real.rpow (r : ℝ) (-(133 / 10 : ℝ)) ≤
      (Int.ceil ((r : ℝ) * alpha) : ℝ) - (r : ℝ) * alpha := by
  exact le_trans
    (rhin_phase_gap_alpha hgap hr)
    (nearestIntegerNorm_le_ceil_gap ((r : ℝ) * alpha))

/-- Auxiliary logarithmic estimate for lemma 7. For `0 ≤ x ≤ 1/2`, the
base-2 correction `-log₂(1-x)` is bounded by a linear multiple of `x`. -/
theorem neg_log_one_sub_div_log_two_le
    {x : ℝ}
    (hx0 : 0 ≤ x)
    (hxhalf : x ≤ (1 / 2 : ℝ)) :
    -(Real.log (1 - x) / Real.log 2) ≤
      (2 / Real.log 2) * x := by
  have hy : 0 < 1 - x := by linarith
  have hlog : 1 - (1 - x)⁻¹ ≤ Real.log (1 - x) :=
    Real.one_sub_inv_le_log_of_pos hy
  have hlin : -2 * x ≤ 1 - (1 - x)⁻¹ := by
    have hprod : x ≤ 2 * x * (1 - x) := by
      nlinarith [mul_nonneg hx0 (by linarith : 0 ≤ 1 - 2 * x)]
    rw [show 1 - (1 - x)⁻¹ = (-x) / (1 - x) by
      field_simp
      ring]
    exact (le_div_iff₀ hy).2 (by nlinarith)
  have hneg : -Real.log (1 - x) ≤ 2 * x := by
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv := (div_le_div_iff_of_pos_right hlog2).2 hneg
  convert hdiv using 1 <;> ring

/-- Auxiliary exponential-vs-polynomial estimate for lemma 7. The dyadic
factor `2⁻ʳ` eventually beats the Rhin polynomial scale `r⁻¹³·³`. -/
theorem two_neg_nat_eventually_lt_rhin_power
    {c : ℝ}
    (hc : 0 < c) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r →
      (2 / Real.log 2) * (2 : ℝ) ^ (-(r : ℤ)) <
        c * Real.rpow (r : ℝ) (-(133 / 10 : ℝ)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let ε : ℝ := c * Real.log 2 / 4
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have ho :=
    is_o_exp_neg_mul_rpow_at_top hlog2 (-(133 / 10 : ℝ))
  have hb := ho.bound hε
  rcases Filter.eventually_atTop.1 hb with ⟨X, hX⟩
  obtain ⟨R, hXR⟩ := exists_nat_ge X
  refine ⟨max 1 R, ?_⟩
  intro r hr
  have hr1 : 1 ≤ r := le_trans (Nat.le_max_left 1 R) hr
  have hRr : R ≤ r := le_trans (Nat.le_max_right 1 R) hr
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr1
  have hXr : X ≤ (r : ℝ) := by
    exact le_trans hXR (by exact_mod_cast hRr)
  have hbound := hX (r : ℝ) hXr
  have hzpow :
      (2 : ℝ) ^ (-(r : ℤ)) =
        Real.exp (-Real.log 2 * (r : ℝ)) := by
    rw [← Real.rpow_intCast]
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    push_cast
    congr 1
    ring
  have hrpowpos : 0 < Real.rpow (r : ℝ) (-(133 / 10 : ℝ)) :=
    Real.rpow_pos_of_pos hrpos _
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Real.norm_eq_abs, abs_of_pos hrpowpos] at hbound
  rw [hzpow]
  have hscaled :
      (2 / Real.log 2) * Real.exp (-Real.log 2 * (r : ℝ)) ≤
        (c / 2) * Real.rpow (r : ℝ) (-(133 / 10 : ℝ)) := by
    have hfac : 0 < 2 / Real.log 2 := by positivity
    have := mul_le_mul_of_nonneg_left hbound (le_of_lt hfac)
    dsimp [ε] at this
    convert this using 1 <;> field_simp [ne_of_gt hlog2] <;> ring
  have hhalf : c / 2 < c := by linarith
  have hstrict :
      (c / 2) * Real.rpow (r : ℝ) (-(133 / 10 : ℝ)) <
        c * Real.rpow (r : ℝ) (-(133 / 10 : ℝ)) := by
    exact mul_lt_mul_of_pos_right hhalf hrpowpos
  exact lt_of_le_of_lt hscaled hstrict

/-- 7. The exponentially small correction `-log₂(1 - 2⁻ʳ)` is eventually
smaller than any positive Rhin polynomial phase gap. -/
theorem exp_error_eventually_lt_power_gap
    {c : ℝ}
    (hc : 0 < c) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r →
      -(Real.log (1 - (2 : ℝ) ^ (-(r : ℤ))) / Real.log 2) <
        c * Real.rpow (r : ℝ) (-(133 / 10 : ℝ)) := by
  obtain ⟨R, hR⟩ := two_neg_nat_eventually_lt_rhin_power hc
  refine ⟨max 1 R, ?_⟩
  intro r hr
  have hr1 : 1 ≤ r := le_trans (Nat.le_max_left 1 R) hr
  have hRr : R ≤ r := le_trans (Nat.le_max_right 1 R) hr
  have hx0 : 0 ≤ (2 : ℝ) ^ (-(r : ℤ)) := by positivity
  have hxhalf : (2 : ℝ) ^ (-(r : ℤ)) ≤ (1 / 2 : ℝ) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hr1
    subst r
    rw [show -(((1 + k : ℕ) : ℤ)) = -(1 : ℤ) - (k : ℤ) by
      push_cast
      ring]
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
    exact inv_le_one₀.mpr (by positivity)
  have hlog := neg_log_one_sub_div_log_two_le hx0 hxhalf
  have hdom := hR r hRr
  exact lt_of_le_of_lt hlog hdom

/-- 8. Eventually the ceiling gap above `r * alpha` dominates the correction
needed to compensate the factor `1 - 2⁻ʳ`. -/
theorem critical_gap_eventually
    {c : ℝ}
    (hc : 0 < c)
    (hgap : PhaseGap c (143 / 10 : ℝ)) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r → 0 < r →
      -(Real.log (1 - (2 : ℝ) ^ (-(r : ℤ))) / Real.log 2) <
        (Int.ceil ((r : ℝ) * alpha) : ℝ) - (r : ℝ) * alpha := by
  obtain ⟨R, hR⟩ := exp_error_eventually_lt_power_gap hc
  refine ⟨R, ?_⟩
  intro r hr hpos
  have hsmall := hR r hr
  have hbig := rhin_le_critical_ceil_gap hgap hpos
  exact lt_of_lt_of_le hsmall hbig

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
