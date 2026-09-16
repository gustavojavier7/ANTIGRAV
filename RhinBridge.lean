import Mathlib
import Erdos1135.ND.PhaseGap

open Erdos1135.ND
open Asymptotics Filter

/-- Critical logarithmic phase for the Collatz/Syracuse block comparison. -/
noncomputable def alpha : ℝ := logTwoThree - 1

/-- Identification of `alpha` with the base-2 logarithm of `3 / 2`. -/
theorem alpha_eq_log_two_three_halves :
    alpha = Real.log (3 / 2) / Real.log 2 := by
  unfold alpha
  rw [show logTwoThree = Real.log 3 / Real.log 2 by rfl]
  rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  field_simp [Real.log_ne_zero_of_pos_of_ne_one
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)]

/-- 3. Multiplying the critical phase by a natural number and subtracting that
integer does not change its distance to the nearest integer. -/
theorem nearestIntegerNorm_mul_alpha (r : ℕ) :
    nearestIntegerNorm ((r : ℝ) * alpha) =
      nearestIntegerNorm ((r : ℝ) * logTwoThree) := by
  unfold nearestIntegerNorm alpha
  rw [mul_sub, mul_one, round_sub_natCast]
  push_cast
  congr 1
  ring

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
  convert h using 1
  norm_num

/-- 5. Distance to the nearest integer is bounded above by the distance to the
ceiling. -/
theorem nearestIntegerNorm_le_ceil_gap (x : ℝ) :
    nearestIntegerNorm x ≤ (Int.ceil x : ℝ) - x := by
  unfold nearestIntegerNorm
  calc
    |x - (round x : ℝ)| ≤ |x - (Int.ceil x : ℝ)| :=
      round_le x (Int.ceil x)
    _ = |(Int.ceil x : ℝ) - x| := by
      rw [abs_sub_comm]
    _ = (Int.ceil x : ℝ) - x := by
      rw [abs_of_nonneg]
      linarith [Int.le_ceil x]

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
    have hform : 1 - (1 - x)⁻¹ = (-x) / (1 - x) := by
      field_simp
      ring
    rw [hform]
    exact (le_div_iff₀ hy).2 (by nlinarith)
  have hneg : -Real.log (1 - x) ≤ 2 * x := by
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv := (div_le_div_iff_of_pos_right hlog2).2 hneg
  have hgoal :
      -Real.log (1 - x) / Real.log 2 ≤ 2 * x / Real.log 2 := hdiv
  have hrhs : 2 * x / Real.log 2 = (2 / Real.log 2) * x := by
    field_simp
  rw [← hrhs]
  simpa [neg_div] using hgoal

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
  have ho :
      (fun x : ℝ => Real.exp (-Real.log 2 * x)) =o[atTop]
        fun x : ℝ => x ^ (-(133 / 10 : ℝ)) :=
    isLittleO_exp_neg_mul_rpow_atTop hlog2 (-(133 / 10 : ℝ))
  have hb : ∀ᶠ x in atTop,
      ‖Real.exp (-Real.log 2 * x)‖ ≤
        ε * ‖x ^ (-(133 / 10 : ℝ))‖ :=
    ho.bound hε
  rcases eventually_atTop.1 hb with ⟨X, hX⟩
  obtain ⟨R, hXR⟩ := exists_nat_ge X
  refine ⟨max 1 R, ?_⟩
  intro r hr
  have hr1 : 1 ≤ r := le_trans (Nat.le_max_left 1 R) hr
  have hRr : R ≤ r := le_trans (Nat.le_max_right 1 R) hr
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr1
  have hXr : X ≤ (r : ℝ) :=
    le_trans hXR (by exact_mod_cast hRr)
  have hbound := hX (r : ℝ) hXr
  have hzpow :
      (2 : ℝ) ^ (-(r : ℤ)) =
        Real.exp (-Real.log 2 * (r : ℝ)) := by
    rw [← Real.rpow_intCast,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    push_cast
    congr 1
    ring
  have hrpowpos : 0 < Real.rpow (r : ℝ) (-(133 / 10 : ℝ)) :=
    Real.rpow_pos_of_pos hrpos _
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Real.norm_eq_abs, abs_of_pos (by simpa using hrpowpos)] at hbound
  rw [hzpow]
  have hscaled :
      (2 / Real.log 2) * Real.exp (-Real.log 2 * (r : ℝ)) ≤
        (c / 2) * Real.rpow (r : ℝ) (-(133 / 10 : ℝ)) := by
    have hfac : 0 ≤ 2 / Real.log 2 := le_of_lt (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hbound hfac
    dsimp [ε] at hmul
    have hconst :
        (2 / Real.log 2) * (c * Real.log 2 / 4) = c / 2 := by
      field_simp [ne_of_gt hlog2]
      ring
    calc
      (2 / Real.log 2) * Real.exp (-Real.log 2 * (r : ℝ))
          ≤ (2 / Real.log 2) *
              ((c * Real.log 2 / 4) *
                Real.rpow (r : ℝ) (-(133 / 10 : ℝ))) := by
                  simpa [mul_assoc] using hmul
      _ = ((2 / Real.log 2) * (c * Real.log 2 / 4)) *
            Real.rpow (r : ℝ) (-(133 / 10 : ℝ)) := by ring
      _ = (c / 2) * Real.rpow (r : ℝ) (-(133 / 10 : ℝ)) := by
            rw [hconst]
  have hhalf : c / 2 < c := by linarith
  have hstrict :
      (c / 2) * Real.rpow (r : ℝ) (-(133 / 10 : ℝ)) <
        c * Real.rpow (r : ℝ) (-(133 / 10 : ℝ)) :=
    mul_lt_mul_of_pos_right hhalf hrpowpos
  exact lt_of_le_of_lt hscaled hstrict

/-- Dyadic `2⁻ʳ` is at most `1/2` for every positive natural `r`. -/
private theorem two_zpow_neg_le_half {r : ℕ} (hr1 : 1 ≤ r) :
    (2 : ℝ) ^ (-(r : ℤ)) ≤ (1 / 2 : ℝ) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hr1
  subst r
  have hform : (-(((1 + k : ℕ) : ℤ))) = -(1 : ℤ) - (k : ℤ) := by
    push_cast
    ring
  rw [hform, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ k :=
    one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hinv : ((2 : ℝ) ^ k)⁻¹ ≤ (1 : ℝ) :=
    inv_le_one_of_one_le₀ hpow
  have h2 : (2 : ℝ) ^ (-(1 : ℤ)) = (1 / 2 : ℝ) := by norm_num
  rw [h2, div_eq_mul_inv]
  have hhalf0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hle := mul_le_mul_of_nonneg_left hinv hhalf0
  -- (1/2) * (2^k)⁻¹ ≤ (1/2) * 1 = 1/2
  simpa using hle

/-- Elementary critical-error bound used by Astra: for `s ≥ 1`,
`-log₂(1 - 2⁻ˢ) ≤ 1`. -/
theorem critical_error_le_one
    {s : ℕ}
    (hs : 1 ≤ s) :
    - Real.log (1 - (2 : ℝ) ^ (-(s : ℤ))) / Real.log 2 ≤ 1 := by
  have hx : (2 : ℝ) ^ (-(s : ℤ)) ≤ (1 / 2 : ℝ) := two_zpow_neg_le_half hs
  have hhalf_le : (1 / 2 : ℝ) ≤ 1 - (2 : ℝ) ^ (-(s : ℤ)) := by linarith
  have hlog :
      Real.log (1 / 2 : ℝ) ≤ Real.log (1 - (2 : ℝ) ^ (-(s : ℤ))) :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hhalf_le
  have hlog_half : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_one, zero_sub]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hneg : -Real.log (1 - (2 : ℝ) ^ (-(s : ℤ))) ≤ Real.log 2 := by
    linarith [hlog, hlog_half]
  have hdiv := (div_le_div_iff_of_pos_right hlog2).2 hneg
  have hone : Real.log 2 / Real.log 2 = (1 : ℝ) := div_self (ne_of_gt hlog2)
  simpa [hone] using hdiv

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
  have hxhalf : (2 : ℝ) ^ (-(r : ℤ)) ≤ (1 / 2 : ℝ) :=
    two_zpow_neg_le_half hr1
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
  obtain ⟨R, hR⟩ := critical_gap_eventually hc hgap
  refine ⟨R, ?_⟩
  intro r hr hpos
  let v : ℤ := Int.ceil ((r : ℝ) * alpha)
  have hcrit := hR r hr hpos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have halpha : 0 < alpha := by
    rw [alpha_eq_log_two_three_halves]
    have hnum : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
    exact div_pos hnum hlog2
  have hr0 : 0 ≤ (r : ℝ) := by positivity
  have hv0 : 0 ≤ v := by
    dsimp [v]
    exact Int.ceil_nonneg (mul_nonneg hr0 (le_of_lt halpha))
  have hv_toNat : ((Int.toNat v : ℕ) : ℤ) = v :=
    Int.toNat_of_nonneg hv0
  have hxhalf : (2 : ℝ) ^ (-(r : ℤ)) ≤ (1 / 2 : ℝ) :=
    two_zpow_neg_le_half hpos
  have hone : 0 < 1 - (2 : ℝ) ^ (-(r : ℤ)) := by
    linarith
  have hcrit' :
      -Real.log (1 - (2 : ℝ) ^ (-(r : ℤ))) <
        (((v : ℤ) : ℝ) - (r : ℝ) * alpha) * Real.log 2 := by
    have htmp :
        (-Real.log (1 - (2 : ℝ) ^ (-(r : ℤ)))) / Real.log 2 <
          ((v : ℤ) : ℝ) - (r : ℝ) * alpha := by
      simpa [v, neg_div] using hcrit
    exact (div_lt_iff₀ hlog2).1 htmp
  have hlog_form :
      (r : ℝ) * Real.log (3 / 2 : ℝ) -
          Real.log (1 - (2 : ℝ) ^ (-(r : ℤ))) <
        ((v : ℤ) : ℝ) * Real.log 2 := by
    rw [alpha_eq_log_two_three_halves] at hcrit'
    field_simp [ne_of_gt hlog2] at hcrit'
    linarith
  have hexp0 := Real.exp_lt_exp.mpr hlog_form
  have hpow2 :
      Real.exp (((v : ℤ) : ℝ) * Real.log 2) =
        (2 : ℝ) ^ (Int.toNat v) := by
    rw [← Real.rpow_natCast,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    have hvR : ((v : ℤ) : ℝ) = (Int.toNat v : ℝ) := by
      exact_mod_cast hv_toNat.symm
    rw [hvR]
    ring
  have hpow3 :
      Real.exp ((r : ℝ) * Real.log (3 / 2 : ℝ)) =
        (3 / 2 : ℝ) ^ r := by
    rw [← Real.rpow_natCast,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    congr 1
    ring
  have hleft :
      Real.exp ((r : ℝ) * Real.log (3 / 2 : ℝ) -
        Real.log (1 - (2 : ℝ) ^ (-(r : ℤ)))) =
        (3 / 2 : ℝ) ^ r /
          (1 - (2 : ℝ) ^ (-(r : ℤ))) := by
    rw [Real.exp_sub, hpow3, Real.exp_log hone]
  have hexp : (3 / 2 : ℝ) ^ r / (1 - (2 : ℝ) ^ (-(r : ℤ))) <
      (2 : ℝ) ^ (Int.toNat v) := by
    rw [← hleft, ← hpow2]
    exact hexp0
  have hzpow : (2 : ℝ) ^ (-(r : ℤ)) = ((2 : ℝ) ^ r)⁻¹ := by
    rw [zpow_neg]
    simp
  have hexp' :
      (3 / 2 : ℝ) ^ r / (1 - ((2 : ℝ) ^ r)⁻¹) <
        (2 : ℝ) ^ (Int.toNat v) := by
    simpa [hzpow] using hexp
  have hden : 0 < 1 - ((2 : ℝ) ^ r)⁻¹ := by
    rw [← hzpow]
    exact hone
  have hmul :
      (3 / 2 : ℝ) ^ r <
        (2 : ℝ) ^ (Int.toNat v) * (1 - ((2 : ℝ) ^ r)⁻¹) :=
    (div_lt_iff₀ hden).1 hexp'
  have h2rpos : 0 < (2 : ℝ) ^ r := by positivity
  have hmul2 :
      (3 / 2 : ℝ) ^ r * (2 : ℝ) ^ r <
        (2 : ℝ) ^ (Int.toNat v) *
          ((1 - ((2 : ℝ) ^ r)⁻¹) * (2 : ℝ) ^ r) := by
    have h := mul_lt_mul_of_pos_right hmul h2rpos
    -- h : (3/2)^r * 2^r < 2^v * (1 - inv) * 2^r
    -- goal right factor is (1-inv)*2^r; left is same
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have hrewrite :
      (3 / 2 : ℝ) ^ r * (2 : ℝ) ^ r = (3 : ℝ) ^ r := by
    rw [← mul_pow]
    norm_num
  have hfactor :
      (1 - ((2 : ℝ) ^ r)⁻¹) * (2 : ℝ) ^ r = (2 : ℝ) ^ r - 1 := by
    field_simp
  have hreal :
      (3 : ℝ) ^ r <
        (2 : ℝ) ^ (Int.toNat v) * ((2 : ℝ) ^ r - 1) := by
    rw [← hrewrite, ← hfactor]
    exact hmul2
  have h1 : (1 : ℕ) ≤ 2 ^ r :=
    Nat.one_le_pow r 2 (by decide : 0 < 2)
  have hcast :
      ((3 ^ r : ℕ) : ℝ) <
        ((2 ^ Int.toNat v : ℕ) : ℝ) * ((2 ^ r - 1 : ℕ) : ℝ) := by
    have hsub : ((2 ^ r - 1 : ℕ) : ℝ) = (2 : ℝ) ^ r - 1 := by
      rw [Nat.cast_sub h1]
      norm_cast
    simpa [Nat.cast_pow, hsub] using hreal
  exact_mod_cast hcast

/-- Bridge lemma. A pure power comparison `3 ^ s < 2 ^ (a + s)` forces the
critical ceiling bound
`Int.toNat (Int.ceil ((s : ℝ) * alpha)) ≤ a`
with `alpha = log₂(3/2)`.

Mathematical chain (exact, no numerical approximation):
`3^s < 2^(a+s)`
→ `s · log 3 < (a+s) · log 2`
→ `s · log(3/2) < a · log 2`
→ `s · alpha < a`
→ `⌈s · alpha⌉ ≤ a`
→ `toNat(⌈s · alpha⌉) ≤ a`. -/
theorem oneBlockGap_ceil_alpha_le_a
    {a s : ℕ}
    (_ha : 1 ≤ a)
    (_hs : 1 ≤ s)
    (hpow : 3 ^ s < 2 ^ (a + s)) :
    Int.toNat (Int.ceil ((s : ℝ) * alpha)) ≤ a := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlt : (3 : ℝ) ^ s < (2 : ℝ) ^ (a + s) := by
    exact_mod_cast hpow
  have hlog :=
    Real.log_lt_log (by positivity : 0 < (3 : ℝ) ^ s) hlt
  rw [Real.log_pow, Real.log_pow] at hlog
  -- hlog : ↑s * log 3 < ↑(a + s) * log 2
  have hlog' :
      (s : ℝ) * Real.log 3 - (s : ℝ) * Real.log 2 <
        (a : ℝ) * Real.log 2 := by
    push_cast at hlog
    linarith
  have hlog_half :
      (s : ℝ) * Real.log (3 / 2 : ℝ) < (a : ℝ) * Real.log 2 := by
    have hdiff :
        Real.log 3 - Real.log 2 = Real.log (3 / 2 : ℝ) :=
      (Real.log_div (by norm_num : (3 : ℝ) ≠ 0)
        (by norm_num : (2 : ℝ) ≠ 0)).symm
    have hrewrite :
        (s : ℝ) * Real.log 3 - (s : ℝ) * Real.log 2 =
          (s : ℝ) * Real.log (3 / 2 : ℝ) := by
      rw [← mul_sub, hdiff]
    rwa [← hrewrite]
  have hmul : (s : ℝ) * alpha < (a : ℝ) := by
    rw [alpha_eq_log_two_three_halves, ← mul_div_assoc]
    exact (div_lt_iff₀ hlog2).2 hlog_half
  have halpha : 0 < alpha := by
    rw [alpha_eq_log_two_three_halves]
    exact div_pos
      (Real.log_pos (by norm_num : (1 : ℝ) < 3 / 2)) hlog2
  have hv0 : 0 ≤ Int.ceil ((s : ℝ) * alpha) :=
    Int.ceil_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (le_of_lt halpha))
  have hceil : Int.ceil ((s : ℝ) * alpha) ≤ (a : ℤ) :=
    (Int.ceil_le).2 (le_of_lt hmul)
  have hcoe :
      ((Int.toNat (Int.ceil ((s : ℝ) * alpha)) : ℕ) : ℤ) ≤
        (a : ℤ) := by
    rwa [Int.toNat_of_nonneg hv0]
  exact_mod_cast hcoe
