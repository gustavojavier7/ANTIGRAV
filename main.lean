import Mathlib




def v2 (n : ℕ) : ℕ :=
  padicValNat 2 n




theorem pow_v2_dvd {n : ℕ} (hn : n ≠ 0) :
    2 ^ v2 n ∣ n := by
  rw [v2, padicValNat_dvd_iff_le hn]




theorem pow_dvd_iff_le_v2 {n k : ℕ} (hn : n ≠ 0) :
    2 ^ k ∣ n ↔ k ≤ v2 n := by
  simpa [v2] using (padicValNat_dvd_iff_le (p := 2) (a := n) (n := k) hn)




def collatzExponent (m : ℕ) : ℕ :=
  v2 (3 * m + 1)




def Tstar (m : ℕ) : ℕ :=
  (3 * m + 1) / 2 ^ collatzExponent m




def runLength (m : ℕ) : ℕ :=
  v2 (m + 1)




def IsBlue (m : ℕ) : Prop :=
  collatzExponent m = 1




def IsRed (m : ℕ) : Prop :=
  2 ≤ collatzExponent m




theorem three_mul_add_one_pos (m : ℕ) :
    0 < 3 * m + 1 := by
  omega




theorem collatz_pow_dvd (m : ℕ) :
    2 ^ collatzExponent m ∣ 3 * m + 1 := by
  apply pow_v2_dvd
  omega




theorem Tstar_pos (m : ℕ) :
    0 < Tstar m := by
  unfold Tstar
  apply Nat.div_pos
  · exact Nat.le_of_dvd (three_mul_add_one_pos m) (collatz_pow_dvd m)
  · positivity




theorem div_pow_v2_odd {n : ℕ} (hn : n ≠ 0) :
    Odd (n / 2 ^ v2 n) := by
  have hdvd : 2 ^ v2 n ∣ n := pow_v2_dvd hn
  have hqpos : 0 < n / 2 ^ v2 n := by
    apply Nat.div_pos
    · exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
    · positivity
  have hdvd' : 2 ^ padicValNat 2 n ∣ n := by
    simpa [v2] using hdvd
  have hvzero : padicValNat 2 (n / 2 ^ v2 n) = 0 := by
    change padicValNat 2 (n / 2 ^ padicValNat 2 n) = 0
    rw [padicValNat.div_pow hdvd']
    exact Nat.sub_self _
  have hnotdvd : ¬ 2 ∣ n / 2 ^ v2 n := by
    rcases (padicValNat.eq_zero_iff.mp hvzero) with h | h | h
    · omega
    · exact ((Nat.ne_of_gt hqpos) h).elim
    · exact h
  apply Nat.not_even_iff_odd.mp
  intro heven
  rcases heven with ⟨a, ha⟩
  apply hnotdvd
  refine ⟨a, ?_⟩
  omega




theorem Tstar_odd (m : ℕ) :
    Odd (Tstar m) := by
  unfold Tstar collatzExponent
  apply div_pow_v2_odd
  omega




/-- Counterexample to the proposed universal claim
    `Odd m → runLength m = 1`: take `m = 3`. -/
theorem runLength_three :
    runLength 3 = 2 := by
  native_decide




theorem four_dvd_succ_iff_mod_eq_three (m : ℕ) :
    4 ∣ m + 1 ↔ m % 4 = 3 := by
  omega




theorem runLength_ge_one {m : ℕ} (hm : Odd m) :
    1 ≤ runLength m := by
  rw [runLength, ← pow_dvd_iff_le_v2 (n := m + 1) (k := 1) (by omega)]
  norm_num
  rcases hm with ⟨a, ha⟩
  refine ⟨a + 1, ?_⟩
  omega




theorem runLength_ge_two_iff_mod_four_eq_three {m : ℕ} (_hm : Odd m) :
    2 ≤ runLength m ↔ m % 4 = 3 := by
  rw [runLength, ← pow_dvd_iff_le_v2 (n := m + 1) (k := 2) (by omega)]
  norm_num
  exact four_dvd_succ_iff_mod_eq_three m




theorem runLength_eq_one_iff_mod_four_eq_one {m : ℕ} (hm : Odd m) :
    runLength m = 1 ↔ m % 4 = 1 := by
  have hge1 : 1 ≤ runLength m := runLength_ge_one hm
  have hge2 := runLength_ge_two_iff_mod_four_eq_three (m := m) hm
  rcases hm with ⟨a, ha⟩
  constructor
  · intro hr
    have hnot3 : m % 4 ≠ 3 := by
      intro h3
      have : 2 ≤ runLength m := hge2.mpr h3
      omega
    omega
  · intro hmod
    have hnotge2 : ¬ 2 ≤ runLength m := by
      intro h
      have h3 : m % 4 = 3 := hge2.mp h
      omega
    omega




theorem four_dvd_three_mul_add_one_iff_mod_eq_one (m : ℕ) :
    4 ∣ 3 * m + 1 ↔ m % 4 = 1 := by
  omega




theorem collatzExponent_ge_one {m : ℕ} (hm : Odd m) :
    1 ≤ collatzExponent m := by
  rw [collatzExponent, ← pow_dvd_iff_le_v2
    (n := 3 * m + 1) (k := 1) (by omega)]
  norm_num
  rcases hm with ⟨a, ha⟩
  refine ⟨3 * a + 2, ?_⟩
  omega




theorem collatzExponent_ge_two_iff_mod_four_eq_one
    {m : ℕ} (_hm : Odd m) :
    2 ≤ collatzExponent m ↔ m % 4 = 1 := by
  rw [collatzExponent, ← pow_dvd_iff_le_v2
    (n := 3 * m + 1) (k := 2) (by omega)]
  norm_num
  exact four_dvd_three_mul_add_one_iff_mod_eq_one m




theorem collatzExponent_eq_one_iff_mod_four_eq_three
    {m : ℕ} (hm : Odd m) :
    collatzExponent m = 1 ↔ m % 4 = 3 := by
  have hge1 : 1 ≤ collatzExponent m := collatzExponent_ge_one hm
  have hge2 := collatzExponent_ge_two_iff_mod_four_eq_one (m := m) hm
  rcases hm with ⟨a, ha⟩
  constructor
  · intro hk
    have hnot1 : m % 4 ≠ 1 := by
      intro h1
      have : 2 ≤ collatzExponent m := hge2.mpr h1
      omega
    omega
  · intro hmod
    have hnotge2 : ¬ 2 ≤ collatzExponent m := by
      intro h
      have h1 : m % 4 = 1 := hge2.mp h
      omega
    omega




theorem L1 {m : ℕ} (hm : Odd m) :
    collatzExponent m = 1 ↔ 2 ≤ runLength m := by
  rw [collatzExponent_eq_one_iff_mod_four_eq_three hm,
    runLength_ge_two_iff_mod_four_eq_three hm]




theorem L2 {m : ℕ} (hm : Odd m) :
    IsRed m ↔ runLength m = 1 := by
  rw [IsRed, collatzExponent_ge_two_iff_mod_four_eq_one hm,
    runLength_eq_one_iff_mod_four_eq_one hm]








theorem Tstar_eq_half_of_exponent_one
    {m : ℕ}
    (hk : collatzExponent m = 1) :
    Tstar m = (3 * m + 1) / 2 := by
  simp [Tstar, hk]




theorem Tstar_add_one_eq
    {m : ℕ}
    (hm : Odd m)
    (hk : collatzExponent m = 1) :
    Tstar m + 1 = 3 * ((m + 1) / 2) := by
  rw [Tstar_eq_half_of_exponent_one hk]
  rcases hm with ⟨a, ha⟩
  omega




theorem v2_div_two
    {n : ℕ}
    (_hn : n ≠ 0)
    (heven : 2 ∣ n) :
    v2 (n / 2) = v2 n - 1 := by
  simpa [v2] using (padicValNat.div (p := 2) (b := n) heven)




theorem v2_three_mul
    {n : ℕ}
    (hn : n ≠ 0) :
    v2 (3 * n) = v2 n := by
  unfold v2
  rw [padicValNat.mul (p := 2) (a := 3) (b := n) (by norm_num) hn]
  rw [padicValNat_primes (p := 2) (q := 3) (by norm_num)]
  omega




theorem runLength_Tstar_of_ge_two
    {m : ℕ}
    (hm : Odd m)
    (hr : 2 ≤ runLength m) :
    runLength (Tstar m) = runLength m - 1 := by
  have hk : collatzExponent m = 1 :=
    (L1 hm).2 hr
  have hT : Tstar m + 1 = 3 * ((m + 1) / 2) :=
    Tstar_add_one_eq hm hk
  have hnonzero : m + 1 ≠ 0 := by
    omega
  have heven : 2 ∣ m + 1 := by
    rcases hm with ⟨a, ha⟩
    refine ⟨a + 1, ?_⟩
    omega
  have hhalf : (m + 1) / 2 ≠ 0 := by
    rcases hm with ⟨a, ha⟩
    omega
  calc
    runLength (Tstar m) = v2 (Tstar m + 1) := rfl
    _ = v2 (3 * ((m + 1) / 2)) := congrArg v2 hT
    _ = v2 ((m + 1) / 2) := v2_three_mul hhalf
    _ = v2 (m + 1) - 1 := v2_div_two hnonzero heven
    _ = runLength m - 1 := rfl




example : runLength 3 = 2 := by native_decide
example : Tstar 3 = 5 := by native_decide
example : runLength 5 = 1 := by native_decide




example : runLength 7 = 3 := by native_decide
example : Tstar 7 = 11 := by native_decide
example : runLength 11 = 2 := by native_decide
example : Tstar 11 = 17 := by native_decide
example : runLength 17 = 1 := by native_decide








def oddOrbit (m j : ℕ) : ℕ :=
  Tstar^[j] m




@[simp]
theorem oddOrbit_zero (m : ℕ) :
    oddOrbit m 0 = m := by
  simp [oddOrbit]




theorem oddOrbit_succ (m j : ℕ) :
    oddOrbit m (j + 1) = Tstar (oddOrbit m j) := by
  simpa [oddOrbit] using
    (Function.iterate_succ_apply' Tstar j m)




theorem oddOrbit_odd
    {m j : ℕ}
    (hm : Odd m) :
    Odd (oddOrbit m j) := by
  induction j with
  | zero =>
      simpa using hm
  | succ j _ =>
      rw [oddOrbit_succ]
      exact Tstar_odd (oddOrbit m j)




theorem runLength_oddOrbit
    {m j : ℕ}
    (hm : Odd m)
    (hj : j < runLength m) :
    runLength (oddOrbit m j) = runLength m - j := by
  induction j with
  | zero =>
      simp
  | succ j ih =>
      have hj' : j < runLength m := by
        omega
      have hIH :
          runLength (oddOrbit m j) = runLength m - j :=
        ih hj'
      have hr : 2 ≤ runLength (oddOrbit m j) := by
        omega
      have hodd : Odd (oddOrbit m j) :=
        oddOrbit_odd hm
      calc
        runLength (oddOrbit m (j + 1))
            = runLength (Tstar (oddOrbit m j)) := by
                rw [oddOrbit_succ]
        _ = runLength (oddOrbit m j) - 1 :=
              runLength_Tstar_of_ge_two hodd hr
        _ = (runLength m - j) - 1 := by
              rw [hIH]
        _ = runLength m - (j + 1) := by
              omega








example : runLength 7 = 3 := by native_decide
example : oddOrbit 7 0 = 7 := by native_decide
example : oddOrbit 7 1 = 11 := by native_decide
example : oddOrbit 7 2 = 17 := by native_decide
example : runLength (oddOrbit 7 0) = 3 := by native_decide
example : runLength (oddOrbit 7 1) = 2 := by native_decide
example : runLength (oddOrbit 7 2) = 1 := by native_decide




example : runLength 15 = 4 := by native_decide
example : oddOrbit 15 0 = 15 := by native_decide
example : oddOrbit 15 1 = 23 := by native_decide
example : oddOrbit 15 2 = 35 := by native_decide
example : oddOrbit 15 3 = 53 := by native_decide
example : runLength (oddOrbit 15 0) = 4 := by native_decide
example : runLength (oddOrbit 15 1) = 3 := by native_decide
example : runLength (oddOrbit 15 2) = 2 := by native_decide
example : runLength (oddOrbit 15 3) = 1 := by native_decide




def symbolWord (m j : ℕ) : ℕ :=
  collatzExponent (oddOrbit m j)




theorem L3_blue_prefix
    {m j : ℕ}
    (hm : Odd m)
    (hj : j < runLength m - 1) :
    symbolWord m j = 1 := by
  have hrpos : 1 ≤ runLength m :=
    runLength_ge_one hm
  have hjr : j < runLength m := by
    omega
  have hcount :
      runLength (oddOrbit m j) = runLength m - j :=
    runLength_oddOrbit hm hjr
  have hge : 2 ≤ runLength (oddOrbit m j) := by
    omega
  have hodd : Odd (oddOrbit m j) :=
    oddOrbit_odd hm
  unfold symbolWord
  exact (L1 hodd).2 hge




theorem L4_block_closes
    {m : ℕ}
    (hm : Odd m) :
    2 ≤ symbolWord m (runLength m - 1) := by
  have hrpos : 1 ≤ runLength m :=
    runLength_ge_one hm
  have hindex : runLength m - 1 < runLength m := by
    omega
  have hcount :=
    runLength_oddOrbit
      (m := m)
      (j := runLength m - 1)
      hm
      hindex
  have hone :
      runLength (oddOrbit m (runLength m - 1)) = 1 := by
    omega
  have hodd :
      Odd (oddOrbit m (runLength m - 1)) :=
    oddOrbit_odd hm
  have hred :
      IsRed (oddOrbit m (runLength m - 1)) :=
    (L2 hodd).2 hone
  simpa [IsRed, symbolWord] using hred




theorem first_block_spec
    {m : ℕ}
    (hm : Odd m) :
    (∀ j, j < runLength m - 1 →
       symbolWord m j = 1) ∧
    2 ≤ symbolWord m (runLength m - 1) := by
  constructor
  · intro j hj
    exact L3_blue_prefix hm hj
  · exact L4_block_closes hm




example : symbolWord 7 0 = 1 := by native_decide
example : symbolWord 7 1 = 1 := by native_decide
example : symbolWord 7 2 = 2 := by native_decide




example : symbolWord 15 0 = 1 := by native_decide
example : symbolWord 15 1 = 1 := by native_decide
example : symbolWord 15 2 = 1 := by native_decide
example : symbolWord 15 3 = 5 := by native_decide








def U (m : ℕ) : ℕ :=
  (3 * m + 1) / 2




theorem Tstar_eq_U_of_exponent_one
    {m : ℕ}
    (hk : collatzExponent m = 1) :
    Tstar m = U m := by
  simpa [U] using Tstar_eq_half_of_exponent_one hk




theorem Tstar_eq_U_of_blue
    {m : ℕ}
    (hblue : IsBlue m) :
    Tstar m = U m := by
  exact Tstar_eq_U_of_exponent_one hblue




theorem oddOrbit_eq_iterate_U_of_lt_runLength
    {m j : ℕ}
    (hm : Odd m)
    (hj : j < runLength m) :
    oddOrbit m j = U^[j] m := by
  induction j with
  | zero =>
      simp
  | succ j ih =>
      have hj' : j < runLength m := by
        omega
      have hIH : oddOrbit m j = U^[j] m :=
        ih hj'
      have hcount :
          runLength (oddOrbit m j) = runLength m - j :=
        runLength_oddOrbit hm hj'
      have hr : 2 ≤ runLength (oddOrbit m j) := by
        omega
      have hodd : Odd (oddOrbit m j) :=
        oddOrbit_odd hm
      have hk : collatzExponent (oddOrbit m j) = 1 :=
        (L1 hodd).2 hr
      have hstep :
          Tstar (oddOrbit m j) = U (oddOrbit m j) :=
        Tstar_eq_U_of_exponent_one hk
      calc
        oddOrbit m (j + 1)
            = Tstar (oddOrbit m j) := oddOrbit_succ m j
        _ = U (oddOrbit m j) := hstep
        _ = U (U^[j] m) := by rw [hIH]
        _ = U^[j + 1] m := by
              simpa using
                (Function.iterate_succ_apply' U j m).symm




def closingExponent (m : ℕ) : ℕ :=
  symbolWord m (runLength m - 1)




theorem closingExponent_ge_two
    {m : ℕ}
    (hm : Odd m) :
    2 ≤ closingExponent m := by
  simpa [closingExponent] using L4_block_closes hm




theorem v2_U_eq_collatzExponent_sub_one
    {x : ℕ}
    (hx : Odd x) :
    v2 (U x) = collatzExponent x - 1 := by
  have hn : 3 * x + 1 ≠ 0 := by
    omega
  have heven : 2 ∣ 3 * x + 1 := by
    rcases hx with ⟨a, ha⟩
    refine ⟨3 * a + 2, ?_⟩
    omega
  simpa [U, collatzExponent] using
    v2_div_two hn heven








theorem v2_U_iterate_eq_closingExponent_sub_one
    {m : ℕ}
    (hm : Odd m) :
    v2 (U^[runLength m] m) =
      closingExponent m - 1 := by
  have hrpos : 1 ≤ runLength m :=
    runLength_ge_one hm
  have hindex :
      runLength m - 1 < runLength m := by
    omega
  have horbit :
      oddOrbit m (runLength m - 1) =
        U^[runLength m - 1] m :=
    oddOrbit_eq_iterate_U_of_lt_runLength hm hindex
  have hxodd :
      Odd (oddOrbit m (runLength m - 1)) :=
    oddOrbit_odd hm
  have hv :=
    v2_U_eq_collatzExponent_sub_one hxodd
  have hsucc :
      (runLength m - 1) + 1 = runLength m := by
    omega
  have hUx :
      U (oddOrbit m (runLength m - 1)) =
        U^[runLength m] m := by
    calc
      U (oddOrbit m (runLength m - 1))
          = U (U^[runLength m - 1] m) := by
              rw [horbit]
      _ = U^[(runLength m - 1) + 1] m := by
            simpa using
              (Function.iterate_succ_apply'
                U (runLength m - 1) m).symm
      _ = U^[runLength m] m := by
            rw [hsucc]
  rw [← hUx]
  simpa [closingExponent, symbolWord] using hv




theorem closingExponent_eq_v2_U_iterate_add_one
    {m : ℕ}
    (hm : Odd m) :
    closingExponent m =
      v2 (U^[runLength m] m) + 1 := by
  have hv :=
    v2_U_iterate_eq_closingExponent_sub_one hm
  have hc : 2 ≤ closingExponent m :=
    closingExponent_ge_two hm
  omega








structure Block where
  ones    : ℕ
  closing : ℕ
deriving DecidableEq, Repr




def predictiveBlock (m : ℕ) : Block :=
  {
    ones := runLength m - 1
    closing := closingExponent m
  }




@[simp]
theorem predictiveBlock_ones (m : ℕ) :
    (predictiveBlock m).ones = runLength m - 1 := by
  rfl




@[simp]
theorem predictiveBlock_closing (m : ℕ) :
    (predictiveBlock m).closing = closingExponent m := by
  rfl




theorem predictiveBlock_closing_ge_two
    {m : ℕ}
    (hm : Odd m) :
    2 ≤ (predictiveBlock m).closing := by
  simpa using closingExponent_ge_two hm




def blockNext (m : ℕ) : ℕ :=
  oddOrbit m (runLength m)




theorem blockNext_odd
    {m : ℕ}
    (hm : Odd m) :
    Odd (blockNext m) := by
  exact oddOrbit_odd hm




example : blockNext 0 = 0 := by
  native_decide




example : ¬ 0 < blockNext 0 := by
  native_decide




theorem blockNext_pos_of_odd
    {m : ℕ}
    (hm : Odd m) :
    0 < blockNext m := by
  have hodd : Odd (blockNext m) :=
    blockNext_odd hm
  rcases hodd with ⟨a, ha⟩
  omega




theorem blockNext_eq_Tstar_closing_state
    {m : ℕ}
    (hm : Odd m) :
    blockNext m =
      Tstar (oddOrbit m (runLength m - 1)) := by
  have hrpos : 1 ≤ runLength m :=
    runLength_ge_one hm
  have hsucc :
      (runLength m - 1) + 1 = runLength m := by
    omega
  calc
    blockNext m = oddOrbit m (runLength m) := rfl
    _ = oddOrbit m ((runLength m - 1) + 1) := by
          rw [hsucc]
    _ = Tstar (oddOrbit m (runLength m - 1)) :=
          oddOrbit_succ m (runLength m - 1)








theorem Tstar_eq_U_div_v2
    {x : ℕ}
    (hx : Odd x) :
    Tstar x = U x / 2 ^ v2 (U x) := by
  have hc : 1 ≤ collatzExponent x :=
    collatzExponent_ge_one hx
  have hpow :
      2 ^ collatzExponent x =
        2 * 2 ^ (collatzExponent x - 1) := by
    calc
      2 ^ collatzExponent x
          = 2 ^ ((collatzExponent x - 1) + 1) := by
              rw [Nat.sub_add_cancel hc]
      _ = 2 ^ (collatzExponent x - 1) * 2 := by
            rw [pow_succ]
      _ = 2 * 2 ^ (collatzExponent x - 1) := by
            omega
  rw [Tstar, v2_U_eq_collatzExponent_sub_one hx]
  rw [U]
  rw [Nat.div_div_eq_div_mul]
  rw [← hpow]








theorem blockNext_eq_U_iterate_div
    {m : ℕ}
    (hm : Odd m) :
    blockNext m =
      (U^[runLength m] m) /
        2 ^ v2 (U^[runLength m] m) := by
  have hrpos : 1 ≤ runLength m :=
    runLength_ge_one hm
  have hindex :
      runLength m - 1 < runLength m := by
    omega
  have horbit :
      oddOrbit m (runLength m - 1) =
        U^[runLength m - 1] m :=
    oddOrbit_eq_iterate_U_of_lt_runLength hm hindex
  have hxodd :
      Odd (oddOrbit m (runLength m - 1)) :=
    oddOrbit_odd hm
  have hsucc :
      (runLength m - 1) + 1 = runLength m := by
    omega
  have hUx :
      U (oddOrbit m (runLength m - 1)) =
        U^[runLength m] m := by
    calc
      U (oddOrbit m (runLength m - 1))
          = U (U^[runLength m - 1] m) := by
              rw [horbit]
      _ = U^[(runLength m - 1) + 1] m := by
            simpa using
              (Function.iterate_succ_apply'
                U (runLength m - 1) m).symm
      _ = U^[runLength m] m := by
            rw [hsucc]
  calc
    blockNext m
        = Tstar (oddOrbit m (runLength m - 1)) :=
          blockNext_eq_Tstar_closing_state hm
    _ = U (oddOrbit m (runLength m - 1)) /
          2 ^ v2 (U (oddOrbit m (runLength m - 1))) :=
          Tstar_eq_U_div_v2 hxodd
    _ = (U^[runLength m] m) /
          2 ^ v2 (U^[runLength m] m) := by
          rw [hUx]




theorem predictiveBlock_spec
    {m : ℕ}
    (hm : Odd m) :
    (∀ j, j < (predictiveBlock m).ones →
       symbolWord m j = 1) ∧
    2 ≤ (predictiveBlock m).closing ∧
    (predictiveBlock m).closing =
      v2 (U^[runLength m] m) + 1 := by
  constructor
  · intro j hj
    apply L3_blue_prefix hm
    simpa using hj
  · constructor
    · exact predictiveBlock_closing_ge_two hm
    · simpa using
        closingExponent_eq_v2_U_iterate_add_one hm




example : (predictiveBlock 7).ones = 2 := by
  native_decide




example : (predictiveBlock 7).closing = 2 := by
  native_decide




example : blockNext 7 = 13 := by
  native_decide




example : (predictiveBlock 15).ones = 3 := by
  native_decide




example : (predictiveBlock 15).closing = 5 := by
  native_decide




example : blockNext 15 = 5 := by
  native_decide




example : closingExponent 15 = 5 := by
  native_decide




example : v2 (U^[runLength 15] 15) = 4 := by
  native_decide








theorem U_iterate_closed_form
    {m r q : ℕ}
    (hfactor : m + 1 = 2 ^ r * q) :
    U^[r] m = 3 ^ r * q - 1 := by
  induction r generalizing m q with
  | zero =>
      simp at hfactor ⊢
      omega
  | succ r ih =>
      have hfactor' :
          m + 1 = 2 * (2 ^ r * q) := by
        calc
          m + 1 = 2 ^ (r + 1) * q := hfactor
          _ = 2 * (2 ^ r * q) := by ring
      let a : ℕ := 2 ^ r * q
      have ha : m + 1 = 2 * a := by
        simpa [a] using hfactor'
      have hapos : 1 ≤ a := by omega
      have hnum :
          3 * m + 1 = 2 * (3 * a - 1) := by
        omega
      have hU : U m = 3 * a - 1 := by
        rw [U, hnum]
        omega
      have hnext :
          U m + 1 = 2 ^ r * (3 * q) := by
        calc
          U m + 1 = (3 * a - 1) + 1 := by rw [hU]
          _ = 3 * a := by omega
          _ = 2 ^ r * (3 * q) := by
                simp [a]
                ring
      calc
        U^[r + 1] m = U^[r] (U m) := by
          simp
        _ = 3 ^ r * (3 * q) - 1 :=
          ih (m := U m) (q := 3 * q) hnext
        _ = 3 ^ (r + 1) * q - 1 := by ring_nf








theorem blockNext_closed_form
    {m r q : ℕ}
    (hm : Odd m)
    (hr : r = runLength m)
    (hfactor : m + 1 = 2 ^ r * q) :
    blockNext m =
      (3 ^ r * q - 1) /
        2 ^ v2 (3 ^ r * q - 1) := by
  subst r
  rw [blockNext_eq_U_iterate_div hm]
  rw [U_iterate_closed_form hfactor]




theorem blockNext_closed_form_runLength
    {m q : ℕ}
    (hm : Odd m)
    (hfactor : m + 1 = 2 ^ runLength m * q) :
    blockNext m =
      (3 ^ runLength m * q - 1) /
        2 ^ v2 (3 ^ runLength m * q - 1) := by
  exact blockNext_closed_form hm rfl hfactor




example : U^[4] 15 = 3 ^ 4 * 1 - 1 := by
  apply U_iterate_closed_form
  native_decide




example :
    blockNext 15 =
      (3 ^ 4 * 1 - 1) / 2 ^ v2 (3 ^ 4 * 1 - 1) := by
  apply blockNext_closed_form (m := 15) (r := 4) (q := 1)
  · native_decide
  · native_decide
  · native_decide








def blockQuotient (m : ℕ) : ℕ :=
  (m + 1) / 2 ^ runLength m




theorem blockQuotient_factorization
    {m : ℕ}
    (_hm : Odd m) :
    m + 1 =
      2 ^ runLength m * blockQuotient m := by
  have hn : m + 1 ≠ 0 := by omega
  have hd : 2 ^ runLength m ∣ m + 1 := by
    simpa [runLength] using pow_v2_dvd hn
  simpa [blockQuotient] using (Nat.mul_div_cancel' hd).symm




theorem blockQuotient_odd
    {m : ℕ}
    (_hm : Odd m) :
    Odd (blockQuotient m) := by
  have hn : m + 1 ≠ 0 := by omega
  simpa [blockQuotient, runLength] using
    div_pow_v2_odd hn




theorem blockQuotient_pos
    {m : ℕ}
    (hm : Odd m) :
    0 < blockQuotient m := by
  rcases blockQuotient_odd hm with ⟨a, ha⟩
  omega




theorem runLength_pos
    {m : ℕ}
    (hm : Odd m) :
    0 < runLength m := by
  have h := runLength_ge_one hm
  omega




theorem blockNext_closed_form_canonical
    {m : ℕ}
    (hm : Odd m) :
    blockNext m =
      (3 ^ runLength m * blockQuotient m - 1) /
        2 ^ v2
          (3 ^ runLength m * blockQuotient m - 1) := by
  exact blockNext_closed_form_runLength hm
    (blockQuotient_factorization hm)




theorem closingExponent_closed_form_canonical
    {m : ℕ}
    (hm : Odd m) :
    closingExponent m =
      v2
        (3 ^ runLength m * blockQuotient m - 1) + 1 := by
  rw [closingExponent_eq_v2_U_iterate_add_one hm]
  rw [U_iterate_closed_form (blockQuotient_factorization hm)]








structure BlockCoord where
  r : ℕ
  q : ℕ
deriving DecidableEq, Repr




def BlockCoord.Valid (c : BlockCoord) : Prop :=
  1 ≤ c.r ∧ Odd c.q




def encodeBlockCoord (m : ℕ) : BlockCoord :=
  { r := runLength m
    q := blockQuotient m }




theorem encodeBlockCoord_valid
    {m : ℕ}
    (hm : Odd m) :
    (encodeBlockCoord m).Valid := by
  constructor
  · exact runLength_ge_one hm
  · exact blockQuotient_odd hm




def decodeBlockCoord (c : BlockCoord) : ℕ :=
  2 ^ c.r * c.q - 1




theorem valid_coord_q_pos
    {c : BlockCoord}
    (hc : c.Valid) :
    0 < c.q := by
  rcases hc.2 with ⟨a, ha⟩
  omega




theorem valid_coord_product_ge_two
    {c : BlockCoord}
    (hc : c.Valid) :
    2 ≤ 2 ^ c.r * c.q := by
  have hrge : 1 ≤ c.r := hc.1
  obtain ⟨r, hr⟩ : ∃ r, c.r = r + 1 :=
    ⟨c.r - 1, by omega⟩
  have hpow : 2 ≤ 2 ^ c.r := by
    rw [hr, pow_succ]
    have hp : 0 < 2 ^ r := pow_pos (by omega) r
    omega
  have hq : 1 ≤ c.q := by
    exact valid_coord_q_pos hc
  have hmul : 2 ^ c.r ≤ 2 ^ c.r * c.q := by
    simpa using Nat.mul_le_mul_left (2 ^ c.r) hq
  exact hpow.trans hmul




theorem decodeBlockCoord_add_one
    {c : BlockCoord}
    (hc : c.Valid) :
    decodeBlockCoord c + 1 =
      2 ^ c.r * c.q := by
  unfold decodeBlockCoord
  have h := valid_coord_product_ge_two hc
  omega




theorem decodeBlockCoord_pos
    {c : BlockCoord}
    (hc : c.Valid) :
    0 < decodeBlockCoord c := by
  unfold decodeBlockCoord
  have h := valid_coord_product_ge_two hc
  omega




theorem decodeBlockCoord_odd
    {c : BlockCoord}
    (hc : c.Valid) :
    Odd (decodeBlockCoord c) := by
  have hrge : 1 ≤ c.r := hc.1
  obtain ⟨r, hr⟩ : ∃ r, c.r = r + 1 :=
    ⟨c.r - 1, by omega⟩
  have hq : 0 < c.q := valid_coord_q_pos hc
  have hp : 0 < 2 ^ r * c.q :=
    Nat.mul_pos (pow_pos (by omega) r) hq
  have heven :
      2 ^ c.r * c.q = 2 * (2 ^ r * c.q) := by
    rw [hr, pow_succ]
    ring
  refine ⟨2 ^ r * c.q - 1, ?_⟩
  unfold decodeBlockCoord
  rw [heven]
  omega








theorem v2_odd_eq_zero
    {q : ℕ}
    (hq : Odd q) :
    v2 q = 0 := by
  rw [v2, padicValNat.eq_zero_iff]
  right
  right
  intro hd
  rcases hd with ⟨a, ha⟩
  rcases hq with ⟨b, hb⟩
  omega




theorem v2_pow_two_mul_odd
    {r q : ℕ}
    (hq : Odd q) :
    v2 (2 ^ r * q) = r := by
  have hpowne : 2 ^ r ≠ 0 := by positivity
  have hqne : q ≠ 0 := by
    rcases hq with ⟨a, ha⟩
    omega
  rw [v2, padicValNat.mul hpowne hqne,
      padicValNat.pow]
  change r * v2 2 + v2 q = r
  have htwo : v2 2 = 1 := by native_decide
  rw [htwo, v2_odd_eq_zero hq]
  omega




theorem runLength_decodeBlockCoord
    {c : BlockCoord}
    (hc : c.Valid) :
    runLength (decodeBlockCoord c) = c.r := by
  rw [runLength, decodeBlockCoord_add_one hc]
  exact v2_pow_two_mul_odd hc.2




theorem blockQuotient_decodeBlockCoord
    {c : BlockCoord}
    (hc : c.Valid) :
    blockQuotient (decodeBlockCoord c) = c.q := by
  rw [blockQuotient, decodeBlockCoord_add_one hc,
      runLength_decodeBlockCoord hc]
  exact Nat.mul_div_cancel_left c.q (by positivity)




theorem decode_encodeBlockCoord
    {m : ℕ}
    (hm : Odd m) :
    decodeBlockCoord (encodeBlockCoord m) = m := by
  change
    2 ^ runLength m * blockQuotient m - 1 = m
  rw [← blockQuotient_factorization hm]
  omega




theorem encode_decodeBlockCoord
    {c : BlockCoord}
    (hc : c.Valid) :
    encodeBlockCoord (decodeBlockCoord c) = c := by
  cases c with
  | mk r q =>
      change
        ({ r := runLength (decodeBlockCoord { r := r, q := q })
           q := blockQuotient (decodeBlockCoord { r := r, q := q }) } :
          BlockCoord) = { r := r, q := q }
      rw [runLength_decodeBlockCoord hc,
          blockQuotient_decodeBlockCoord hc]








theorem block_factorization_unique
    {m r q : ℕ}
    (_hm : Odd m)
    (_hr : 1 ≤ r)
    (hq : Odd q)
    (hfactor : m + 1 = 2 ^ r * q) :
    r = runLength m ∧ q = blockQuotient m := by
  have hv : v2 (m + 1) = r := by
    rw [hfactor]
    exact v2_pow_two_mul_odd hq
  have hr' : r = runLength m := by
    rw [runLength]
    exact hv.symm
  constructor
  · exact hr'
  · rw [blockQuotient, hfactor, ← hr']
    exact (Nat.mul_div_cancel_left q (by positivity)).symm




theorem blockNext_of_encoded_coord
    {m : ℕ}
    (hm : Odd m) :
    blockNext m =
      (3 ^ (encodeBlockCoord m).r *
           (encodeBlockCoord m).q - 1) /
      2 ^ v2
        (3 ^ (encodeBlockCoord m).r *
             (encodeBlockCoord m).q - 1) := by
  simpa [encodeBlockCoord] using
    blockNext_closed_form_canonical hm




example : runLength 15 = 4 := by native_decide
example : blockQuotient 15 = 1 := by native_decide
example : encodeBlockCoord 15 = { r := 4, q := 1 } := by
  native_decide
example : decodeBlockCoord { r := 4, q := 1 } = 15 := by
  native_decide




example : runLength 7 = 3 := by native_decide
example : blockQuotient 7 = 1 := by native_decide
example : encodeBlockCoord 7 = { r := 3, q := 1 } := by
  native_decide
example : decodeBlockCoord { r := 3, q := 1 } = 7 := by
  native_decide




example : runLength 11 = 2 := by native_decide
example : blockQuotient 11 = 3 := by native_decide
example : encodeBlockCoord 11 = { r := 2, q := 3 } := by
  native_decide
example : decodeBlockCoord { r := 2, q := 3 } = 11 := by
  native_decide








def coordNumerator (c : BlockCoord) : ℕ :=
  3 ^ c.r * c.q - 1




def coordClosingValuation (c : BlockCoord) : ℕ :=
  v2 (coordNumerator c)




def coordNextValue (c : BlockCoord) : ℕ :=
  coordNumerator c /
    2 ^ coordClosingValuation c




theorem coordNextValue_eq_blockNext_decode
    {c : BlockCoord}
    (hc : c.Valid) :
    coordNextValue c =
      blockNext (decodeBlockCoord c) := by
  have h :=
    blockNext_closed_form_canonical
      (decodeBlockCoord_odd hc)
  rw [runLength_decodeBlockCoord hc,
      blockQuotient_decodeBlockCoord hc] at h
  simpa [coordNextValue, coordClosingValuation,
    coordNumerator] using h.symm




theorem coordNextValue_odd
    {c : BlockCoord}
    (hc : c.Valid) :
    Odd (coordNextValue c) := by
  rw [coordNextValue_eq_blockNext_decode hc]
  exact blockNext_odd (decodeBlockCoord_odd hc)




theorem coordNextValue_pos
    {c : BlockCoord}
    (hc : c.Valid) :
    0 < coordNextValue c := by
  rw [coordNextValue_eq_blockNext_decode hc]
  exact blockNext_pos_of_odd (decodeBlockCoord_odd hc)




def nextCoord (c : BlockCoord) : BlockCoord :=
  encodeBlockCoord
    (blockNext (decodeBlockCoord c))




theorem nextCoord_valid
    {c : BlockCoord}
    (hc : c.Valid) :
    (nextCoord c).Valid := by
  apply encodeBlockCoord_valid
  exact blockNext_odd (decodeBlockCoord_odd hc)




theorem decode_nextCoord
    {c : BlockCoord}
    (hc : c.Valid) :
    decodeBlockCoord (nextCoord c) =
      blockNext (decodeBlockCoord c) := by
  unfold nextCoord
  apply decode_encodeBlockCoord
  exact blockNext_odd (decodeBlockCoord_odd hc)




theorem nextCoord_encode
    {m : ℕ}
    (hm : Odd m) :
    nextCoord (encodeBlockCoord m) =
      encodeBlockCoord (blockNext m) := by
  unfold nextCoord
  rw [decode_encodeBlockCoord hm]




theorem nextCoord_eq_encode_coordNextValue
    {c : BlockCoord}
    (hc : c.Valid) :
    nextCoord c =
      encodeBlockCoord (coordNextValue c) := by
  unfold nextCoord
  rw [coordNextValue_eq_blockNext_decode hc]




theorem nextCoord_r
    {c : BlockCoord}
    (hc : c.Valid) :
    (nextCoord c).r =
      runLength (coordNextValue c) := by
  rw [nextCoord_eq_encode_coordNextValue hc]
  rfl




theorem nextCoord_r_closed_form
    {c : BlockCoord}
    (hc : c.Valid) :
    (nextCoord c).r =
      v2 (coordNextValue c + 1) := by
  rw [nextCoord_r hc]
  rfl




theorem nextCoord_r_expanded
    {c : BlockCoord}
    (hc : c.Valid) :
    (nextCoord c).r =
      v2
        ((3 ^ c.r * c.q - 1) /
            2 ^ v2 (3 ^ c.r * c.q - 1) + 1) := by
  rw [nextCoord_r_closed_form hc]
  rfl




theorem nextCoord_q
    {c : BlockCoord}
    (hc : c.Valid) :
    (nextCoord c).q =
      blockQuotient (coordNextValue c) := by
  rw [nextCoord_eq_encode_coordNextValue hc]
  rfl




theorem nextCoord_q_closed_form
    {c : BlockCoord}
    (hc : c.Valid) :
    (nextCoord c).q =
      (coordNextValue c + 1) /
        2 ^ (nextCoord c).r := by
  rw [nextCoord_q hc]
  unfold blockQuotient
  rw [nextCoord_r hc]




theorem nextCoord_spec
    {c : BlockCoord}
    (hc : c.Valid) :
    (nextCoord c).Valid ∧
    decodeBlockCoord (nextCoord c) =
      coordNextValue c ∧
    (nextCoord c).r =
      runLength (coordNextValue c) ∧
    (nextCoord c).q =
      blockQuotient (coordNextValue c) := by
  constructor
  · exact nextCoord_valid hc
  · constructor
    · rw [decode_nextCoord hc]
      exact (coordNextValue_eq_blockNext_decode hc).symm
    · constructor
      · exact nextCoord_r hc
      · exact nextCoord_q hc








def coordOrbit (c : BlockCoord) (n : ℕ) : BlockCoord :=
  nextCoord^[n] c




@[simp]
theorem coordOrbit_zero (c : BlockCoord) :
    coordOrbit c 0 = c := by
  rfl




theorem coordOrbit_succ (c : BlockCoord) (n : ℕ) :
    coordOrbit c (n + 1) =
      nextCoord (coordOrbit c n) := by
  exact Function.iterate_succ_apply' nextCoord n c




theorem coordOrbit_valid
    {c : BlockCoord}
    (hc : c.Valid)
    (n : ℕ) :
    (coordOrbit c n).Valid := by
  induction n with
  | zero =>
      exact hc
  | succ n ih =>
      rw [coordOrbit_succ]
      exact nextCoord_valid ih




theorem decode_coordOrbit
    {c : BlockCoord}
    (hc : c.Valid)
    (n : ℕ) :
    decodeBlockCoord (coordOrbit c n) =
      blockNext^[n] (decodeBlockCoord c) := by
  induction n with
  | zero =>
      simp [coordOrbit]
  | succ n ih =>
      calc
        decodeBlockCoord (coordOrbit c (n + 1)) =
            decodeBlockCoord (nextCoord (coordOrbit c n)) := by
              rw [coordOrbit_succ]
        _ = blockNext (decodeBlockCoord (coordOrbit c n)) :=
              decode_nextCoord (coordOrbit_valid hc n)
        _ = blockNext (blockNext^[n] (decodeBlockCoord c)) := by
              rw [ih]
        _ = blockNext^[n + 1] (decodeBlockCoord c) := by
              exact
                (Function.iterate_succ_apply'
                  blockNext n (decodeBlockCoord c)).symm




theorem blockNext_iterate_odd
    {m : ℕ}
    (hm : Odd m)
    (n : ℕ) :
    Odd (blockNext^[n] m) := by
  induction n with
  | zero =>
      exact hm
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact blockNext_odd ih




theorem coordOrbit_encode
    {m : ℕ}
    (hm : Odd m)
    (n : ℕ) :
    coordOrbit (encodeBlockCoord m) n =
      encodeBlockCoord (blockNext^[n] m) := by
  have hc : (encodeBlockCoord m).Valid :=
    encodeBlockCoord_valid hm
  have horbit :
      (coordOrbit (encodeBlockCoord m) n).Valid :=
    coordOrbit_valid hc n
  calc
    coordOrbit (encodeBlockCoord m) n =
        encodeBlockCoord
          (decodeBlockCoord
            (coordOrbit (encodeBlockCoord m) n)) :=
      (encode_decodeBlockCoord horbit).symm
    _ = encodeBlockCoord (blockNext^[n] m) := by
      rw [decode_coordOrbit hc n,
          decode_encodeBlockCoord hm]








def oneCoord : BlockCoord :=
  encodeBlockCoord 1




theorem oneCoord_valid :
    oneCoord.Valid := by
  unfold oneCoord
  apply encodeBlockCoord_valid
  native_decide




theorem oneCoord_eq :
    oneCoord = { r := 1, q := 1 } := by
  native_decide




theorem blockNext_one :
    blockNext 1 = 1 := by
  native_decide




theorem nextCoord_one :
    nextCoord oneCoord = oneCoord := by
  unfold oneCoord
  rw [nextCoord_encode (by native_decide), blockNext_one]




def ReachesOneByBlocks (m : ℕ) : Prop :=
  ∃ n : ℕ, blockNext^[n] m = 1




def ReachesOneByCoords (c : BlockCoord) : Prop :=
  ∃ n : ℕ, coordOrbit c n = oneCoord




theorem encodeBlockCoord_injective_on_odd
    {x y : ℕ}
    (hx : Odd x)
    (hy : Odd y)
    (h : encodeBlockCoord x = encodeBlockCoord y) :
    x = y := by
  have hd := congrArg decodeBlockCoord h
  rw [decode_encodeBlockCoord hx,
      decode_encodeBlockCoord hy] at hd
  exact hd




theorem reachesOne_coords_iff_blocks
    {m : ℕ}
    (hm : Odd m) :
    ReachesOneByCoords (encodeBlockCoord m) ↔
      ReachesOneByBlocks m := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply encodeBlockCoord_injective_on_odd
      (blockNext_iterate_odd hm n) (by native_decide)
    have horbit := coordOrbit_encode hm n
    rw [hn] at horbit
    simpa [oneCoord] using horbit.symm
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [coordOrbit_encode hm n, hn]
    rfl




theorem coord_reachability_reduction
    {m : ℕ}
    (hm : Odd m) :
    ReachesOneByBlocks m ↔
      ReachesOneByCoords (encodeBlockCoord m) := by
  exact (reachesOne_coords_iff_blocks hm).symm




example : oneCoord = { r := 1, q := 1 } := by
  native_decide




example : nextCoord oneCoord = oneCoord := by
  native_decide




example : encodeBlockCoord 7 = { r := 3, q := 1 } := by
  native_decide




example : blockNext 7 = 13 := by
  native_decide




example : encodeBlockCoord 13 = { r := 1, q := 7 } := by
  native_decide




example :
    nextCoord { r := 3, q := 1 } =
      encodeBlockCoord 13 := by
  native_decide




example : encodeBlockCoord 15 = { r := 4, q := 1 } := by
  native_decide




example : blockNext 15 = 5 := by
  native_decide




example : encodeBlockCoord 5 = { r := 1, q := 3 } := by
  native_decide




example :
    nextCoord { r := 4, q := 1 } =
      encodeBlockCoord 5 := by
  native_decide








theorem coordNumerator_pos
    {c : BlockCoord}
    (hc : c.Valid) :
    0 < coordNumerator c := by
  have hrge : 1 ≤ c.r := hc.1
  obtain ⟨r, hr⟩ : ∃ r, c.r = r + 1 :=
    ⟨c.r - 1, by omega⟩
  have hpow : 3 ≤ 3 ^ c.r := by
    rw [hr, pow_succ]
    have hp : 0 < 3 ^ r := pow_pos (by omega) r
    omega
  have hq : 1 ≤ c.q := by
    exact valid_coord_q_pos hc
  have hmul : 3 ^ c.r ≤ 3 ^ c.r * c.q := by
    simpa using Nat.mul_le_mul_left (3 ^ c.r) hq
  unfold coordNumerator
  omega




theorem coordNumerator_ne_zero
    {c : BlockCoord}
    (hc : c.Valid) :
    coordNumerator c ≠ 0 := by
  exact Nat.ne_of_gt (coordNumerator_pos hc)




theorem closingExponent_decode_eq
    {c : BlockCoord}
    (hc : c.Valid) :
    closingExponent (decodeBlockCoord c) =
      coordClosingValuation c + 1 := by
  have h :=
    closingExponent_closed_form_canonical
      (decodeBlockCoord_odd hc)
  rw [runLength_decodeBlockCoord hc,
      blockQuotient_decodeBlockCoord hc] at h
  simpa [coordClosingValuation, coordNumerator] using h




theorem coordClosingValuation_pos
    {c : BlockCoord}
    (hc : c.Valid) :
    0 < coordClosingValuation c := by
  have hclose :=
    closingExponent_ge_two (decodeBlockCoord_odd hc)
  rw [closingExponent_decode_eq hc] at hclose
  omega




theorem coordNumerator_factorization
    {c : BlockCoord}
    (hc : c.Valid) :
    coordNumerator c =
      2 ^ coordClosingValuation c *
        coordNextValue c := by
  have hn : coordNumerator c ≠ 0 :=
    coordNumerator_ne_zero hc
  have hd :
      2 ^ coordClosingValuation c ∣ coordNumerator c := by
    simpa [coordClosingValuation] using pow_v2_dvd hn
  simpa [coordNextValue] using
    (Nat.mul_div_cancel' hd).symm




theorem coordNextValue_add_one_factorization
    {c : BlockCoord}
    (hc : c.Valid) :
    coordNextValue c + 1 =
      2 ^ (nextCoord c).r *
        (nextCoord c).q := by
  calc
    coordNextValue c + 1 =
        2 ^ runLength (coordNextValue c) *
          blockQuotient (coordNextValue c) :=
      blockQuotient_factorization (coordNextValue_odd hc)
    _ = 2 ^ (nextCoord c).r * (nextCoord c).q := by
      rw [nextCoord_r hc, nextCoord_q hc]




def coordBridgeNumerator (c : BlockCoord) : ℕ :=
  coordNumerator c +
    2 ^ coordClosingValuation c




theorem coordBridgeNumerator_eq
    {c : BlockCoord}
    (hc : c.Valid) :
    coordBridgeNumerator c =
      2 ^ coordClosingValuation c *
        (coordNextValue c + 1) := by
  unfold coordBridgeNumerator
  rw [coordNumerator_factorization hc]
  ring




theorem coord_bridge_equation
    {c : BlockCoord}
    (hc : c.Valid) :
    coordBridgeNumerator c =
      2 ^
        (coordClosingValuation c + (nextCoord c).r) *
        (nextCoord c).q := by
  rw [coordBridgeNumerator_eq hc,
      coordNextValue_add_one_factorization hc]
  simp [pow_add, mul_assoc]




theorem coord_bridge_equation_expanded
    {c : BlockCoord}
    (hc : c.Valid) :
    3 ^ c.r * c.q - 1 +
        2 ^ v2 (3 ^ c.r * c.q - 1) =
      2 ^
        (v2 (3 ^ c.r * c.q - 1) +
          (nextCoord c).r) *
        (nextCoord c).q := by
  simpa [coordBridgeNumerator, coordNumerator,
    coordClosingValuation] using coord_bridge_equation hc








theorem v2_coordBridgeNumerator
    {c : BlockCoord}
    (hc : c.Valid) :
    v2 (coordBridgeNumerator c) =
      coordClosingValuation c +
        (nextCoord c).r := by
  rw [coord_bridge_equation hc]
  exact v2_pow_two_mul_odd (nextCoord_valid hc).2




theorem closingValuation_add_nextRunLength
    {c : BlockCoord}
    (hc : c.Valid) :
    coordClosingValuation c +
        (nextCoord c).r =
      v2
        (3 ^ c.r * c.q - 1 +
          2 ^ coordClosingValuation c) := by
  simpa [coordBridgeNumerator, coordNumerator] using
    (v2_coordBridgeNumerator hc).symm




theorem nextCoord_q_from_bridge
    {c : BlockCoord}
    (hc : c.Valid) :
    (nextCoord c).q =
      coordBridgeNumerator c /
        2 ^
          (coordClosingValuation c +
            (nextCoord c).r) := by
  rw [coord_bridge_equation hc]
  exact
    (Nat.mul_div_cancel_left (nextCoord c).q
      (by positivity)).symm




theorem nextCoord_q_from_bridge_v2
    {c : BlockCoord}
    (hc : c.Valid) :
    (nextCoord c).q =
      coordBridgeNumerator c /
        2 ^ v2 (coordBridgeNumerator c) := by
  rw [v2_coordBridgeNumerator hc]
  exact nextCoord_q_from_bridge hc




theorem coordClosing_pow_dvd_numerator
    {c : BlockCoord}
    (hc : c.Valid) :
    2 ^ coordClosingValuation c ∣
      coordNumerator c := by
  refine ⟨coordNextValue c, ?_⟩
  exact coordNumerator_factorization hc




theorem coordClosing_next_pow_not_dvd_numerator
    {c : BlockCoord}
    (hc : c.Valid) :
    ¬ 2 ^ (coordClosingValuation c + 1) ∣
        coordNumerator c := by
  intro hd
  have hle :=
    (pow_dvd_iff_le_v2 (coordNumerator_ne_zero hc)).1 hd
  change
    coordClosingValuation c + 1 ≤
      coordClosingValuation c at hle
  omega




theorem bridge_pow_dvd
    {c : BlockCoord}
    (hc : c.Valid) :
    2 ^
      (coordClosingValuation c +
        (nextCoord c).r) ∣
      coordBridgeNumerator c := by
  refine ⟨(nextCoord c).q, ?_⟩
  exact coord_bridge_equation hc




theorem coordBridgeNumerator_ne_zero
    {c : BlockCoord}
    (hc : c.Valid) :
    coordBridgeNumerator c ≠ 0 := by
  rw [coord_bridge_equation hc]
  have hq : 0 < (nextCoord c).q :=
    valid_coord_q_pos (nextCoord_valid hc)
  positivity




theorem bridge_next_pow_not_dvd
    {c : BlockCoord}
    (hc : c.Valid) :
    ¬ 2 ^
        (coordClosingValuation c +
          (nextCoord c).r + 1) ∣
        coordBridgeNumerator c := by
  intro hd
  have hle :=
    (pow_dvd_iff_le_v2
      (coordBridgeNumerator_ne_zero hc)).1 hd
  rw [v2_coordBridgeNumerator hc] at hle
  omega




theorem two_block_arithmetic_spec
    {c : BlockCoord}
    (hc : c.Valid) :
    0 < coordClosingValuation c ∧
    coordNumerator c =
      2 ^ coordClosingValuation c *
        coordNextValue c ∧
    coordBridgeNumerator c =
      2 ^
        (coordClosingValuation c +
          (nextCoord c).r) *
        (nextCoord c).q ∧
    v2 (coordBridgeNumerator c) =
      coordClosingValuation c +
        (nextCoord c).r ∧
    Odd (nextCoord c).q := by
  constructor
  · exact coordClosingValuation_pos hc
  · constructor
    · exact coordNumerator_factorization hc
    · constructor
      · exact coord_bridge_equation hc
      · constructor
        · exact v2_coordBridgeNumerator hc
        · exact (nextCoord_valid hc).2








example :
    coordNumerator { r := 3, q := 1 } = 26 := by
  native_decide




example :
    coordClosingValuation { r := 3, q := 1 } = 1 := by
  native_decide




example :
    coordNextValue { r := 3, q := 1 } = 13 := by
  native_decide




example :
    nextCoord { r := 3, q := 1 } =
      { r := 1, q := 7 } := by
  native_decide




example :
    coordBridgeNumerator { r := 3, q := 1 } = 28 := by
  native_decide




example : v2 28 = 2 := by
  native_decide




example : (1 : ℕ) + 1 = 2 := by
  native_decide




example : (28 : ℕ) = 2 ^ 2 * 7 := by
  native_decide




example :
    coordNumerator { r := 4, q := 1 } = 80 := by
  native_decide




example :
    coordClosingValuation { r := 4, q := 1 } = 4 := by
  native_decide




example :
    coordNextValue { r := 4, q := 1 } = 5 := by
  native_decide




example :
    nextCoord { r := 4, q := 1 } =
      { r := 1, q := 3 } := by
  native_decide




example :
    coordBridgeNumerator { r := 4, q := 1 } = 96 := by
  native_decide




example : v2 96 = 5 := by
  native_decide




example : (4 : ℕ) + 1 = 5 := by
  native_decide




example : (96 : ℕ) = 2 ^ 5 * 3 := by
  native_decide




example :
    coordNumerator { r := 2, q := 3 } = 26 := by
  native_decide




example :
    coordClosingValuation { r := 2, q := 3 } = 1 := by
  native_decide




example :
    coordNextValue { r := 2, q := 3 } = 13 := by
  native_decide




example :
    nextCoord { r := 2, q := 3 } =
      { r := 1, q := 7 } := by
  native_decide




example :
    coordBridgeNumerator { r := 2, q := 3 } = 28 := by
  native_decide








def localPairModulus (a b : ℕ) : ℕ :=
  2 ^ (a + b + 1)




def localPairRHS (a b : ℕ) : ℕ :=
  1 + 2 ^ (a + b)




def LocalPairResidue
    (r q a b : ℕ) : Prop :=
  (3 ^ r * q + 2 ^ a) %
      localPairModulus a b =
    localPairRHS a b




instance instDecidableLocalPairResidue
    (r q a b : ℕ) :
    Decidable (LocalPairResidue r q a b) := by
  unfold LocalPairResidue
  infer_instance




theorem localPairRHS_lt_modulus
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    localPairRHS a b <
      localPairModulus a b := by
  unfold localPairRHS localPairModulus
  rw [show a + b + 1 = (a + b) + 1 by omega, pow_succ]
  have hpow : 2 ≤ 2 ^ (a + b) := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (a + b) := by
        gcongr <;> omega
  omega




theorem localPairRHS_pos
    (a b : ℕ) :
    0 < localPairRHS a b := by
  unfold localPairRHS
  positivity




theorem localPairResidue_of_coord
    {c : BlockCoord}
    (hc : c.Valid) :
    LocalPairResidue
      c.r
      c.q
      (coordClosingValuation c)
      (nextCoord c).r := by
  have hbridge := coord_bridge_equation hc
  have hnumpos := coordNumerator_pos hc
  have ha : 1 ≤ coordClosingValuation c :=
    coordClosingValuation_pos hc
  have hb : 1 ≤ (nextCoord c).r :=
    (nextCoord_valid hc).1
  rcases (nextCoord_valid hc).2 with ⟨k, hk⟩
  unfold coordBridgeNumerator at hbridge
  unfold coordNumerator at hbridge hnumpos
  have hexact :
      3 ^ c.r * c.q +
          2 ^ coordClosingValuation c =
        1 +
          2 ^ (coordClosingValuation c + (nextCoord c).r) +
          2 ^ (coordClosingValuation c + (nextCoord c).r + 1) * k := by
    rw [show coordClosingValuation c + (nextCoord c).r + 1 =
          (coordClosingValuation c + (nextCoord c).r) + 1 by omega,
        pow_succ]
    rw [show
        1 + 2 ^ (coordClosingValuation c + (nextCoord c).r) +
            2 ^ (coordClosingValuation c + (nextCoord c).r) * 2 * k =
          1 + 2 ^ (coordClosingValuation c + (nextCoord c).r) *
            (2 * k + 1) by ring]
    rw [hk] at hbridge
    omega
  unfold LocalPairResidue localPairModulus localPairRHS
  rw [hexact]
  have hlt := localPairRHS_lt_modulus ha hb
  unfold localPairRHS localPairModulus at hlt
  simp [Nat.add_mod, Nat.mod_eq_of_lt hlt]




theorem localPairResidue_decomposition
    {r q a b : ℕ}
    (_ha : 1 ≤ a)
    (_hb : 1 ≤ b)
    (hres : LocalPairResidue r q a b) :
    ∃ k : ℕ,
      3 ^ r * q + 2 ^ a =
        1 + 2 ^ (a + b) +
          2 ^ (a + b + 1) * k := by
  refine ⟨(3 ^ r * q + 2 ^ a) /
      localPairModulus a b, ?_⟩
  have hdiv :=
    Nat.mod_add_div
      (3 ^ r * q + 2 ^ a)
      (localPairModulus a b)
  unfold LocalPairResidue at hres
  rw [hres] at hdiv
  simpa [localPairModulus, localPairRHS,
    Nat.add_assoc] using hdiv.symm








theorem coordNumerator_factorization_of_localResidue
    {r q a b : ℕ}
    (hr : 1 ≤ r)
    (hq : Odd q)
    (ha : 1 ≤ a)
    (hb : 1 ≤ b)
    (hres : LocalPairResidue r q a b) :
    ∃ t : ℕ,
      Odd t ∧
      coordNumerator { r := r, q := q } =
        2 ^ a * t := by
  rcases localPairResidue_decomposition ha hb hres with
    ⟨k, hdecomp⟩
  have hc : ({ r := r, q := q } : BlockCoord).Valid :=
    ⟨hr, hq⟩
  have hnumpos := coordNumerator_pos hc
  cases b with
  | zero => omega
  | succ d =>
      let u := 2 ^ d * (2 * k + 1)
      let z := 2 ^ (d + 1) * (2 * k + 1)
      have huz : z = 2 * u := by
        simp [u, z, pow_succ]
        ring
      have hu : 0 < u := by
        dsimp [u]
        positivity
      have hsum :
          3 ^ r * q + 2 ^ a =
            1 + 2 ^ a * z := by
        calc
          3 ^ r * q + 2 ^ a =
              1 + 2 ^ (a + (d + 1)) +
                2 ^ (a + (d + 1) + 1) * k := hdecomp
          _ = 1 + 2 ^ a * z := by
            simp [z, pow_add, pow_succ]
            ring
      refine ⟨z - 1, ?_, ?_⟩
      · rw [huz]
        refine ⟨u - 1, ?_⟩
        omega
      · unfold coordNumerator at hnumpos ⊢
        rw [Nat.mul_sub_left_distrib]
        simp only [mul_one]
        omega




theorem coordClosingValuation_eq_of_localResidue
    {r q a b : ℕ}
    (hr : 1 ≤ r)
    (hq : Odd q)
    (ha : 1 ≤ a)
    (hb : 1 ≤ b)
    (hres : LocalPairResidue r q a b) :
    coordClosingValuation { r := r, q := q } = a := by
  rcases
      coordNumerator_factorization_of_localResidue
        hr hq ha hb hres with
    ⟨t, htodd, hfactor⟩
  unfold coordClosingValuation
  rw [hfactor]
  exact v2_pow_two_mul_odd htodd




theorem prescribed_bridge_factorization
    {r q a b : ℕ}
    (hr : 1 ≤ r)
    (hq : Odd q)
    (ha : 1 ≤ a)
    (hb : 1 ≤ b)
    (hres : LocalPairResidue r q a b) :
    ∃ k : ℕ,
      coordNumerator { r := r, q := q } + 2 ^ a =
        2 ^ (a + b) * (2 * k + 1) := by
  rcases localPairResidue_decomposition ha hb hres with
    ⟨k, hdecomp⟩
  have hc : ({ r := r, q := q } : BlockCoord).Valid :=
    ⟨hr, hq⟩
  have hnumpos := coordNumerator_pos hc
  refine ⟨k, ?_⟩
  have hsum :
      3 ^ r * q + 2 ^ a =
        1 + 2 ^ (a + b) * (2 * k + 1) := by
    calc
      3 ^ r * q + 2 ^ a =
          1 + 2 ^ (a + b) +
            2 ^ (a + b + 1) * k := hdecomp
      _ = 1 + 2 ^ (a + b) * (2 * k + 1) := by
        rw [show a + b + 1 = (a + b) + 1 by omega,
          pow_succ]
        ring
  unfold coordNumerator at hnumpos ⊢
  change 0 < 3 ^ r * q - 1 at hnumpos
  change 3 ^ r * q - 1 + 2 ^ a =
    2 ^ (a + b) * (2 * k + 1)
  omega




theorem bridge_v2_eq_of_localResidue
    {r q a b : ℕ}
    (hr : 1 ≤ r)
    (hq : Odd q)
    (ha : 1 ≤ a)
    (hb : 1 ≤ b)
    (hres : LocalPairResidue r q a b) :
    v2
      (coordNumerator { r := r, q := q } +
        2 ^ a) =
      a + b := by
  rcases
      prescribed_bridge_factorization
        hr hq ha hb hres with
    ⟨k, hfactor⟩
  rw [hfactor]
  exact v2_pow_two_mul_odd ⟨k, rfl⟩








theorem localPairResidue_sufficient
    {r q a b : ℕ}
    (hr : 1 ≤ r)
    (hq : Odd q)
    (ha : 1 ≤ a)
    (hb : 1 ≤ b)
    (hres : LocalPairResidue r q a b) :
    coordClosingValuation { r := r, q := q } = a ∧
    (nextCoord { r := r, q := q }).r = b := by
  have hclose :=
    coordClosingValuation_eq_of_localResidue
      hr hq ha hb hres
  refine ⟨hclose, ?_⟩
  have hc : ({ r := r, q := q } : BlockCoord).Valid :=
    ⟨hr, hq⟩
  have hvactual := v2_coordBridgeNumerator hc
  unfold coordBridgeNumerator at hvactual
  rw [hclose] at hvactual
  have hvprescribed :=
    bridge_v2_eq_of_localResidue
      hr hq ha hb hres
  omega




theorem localPairResidue_iff
    {r q a b : ℕ}
    (hr : 1 ≤ r)
    (hq : Odd q)
    (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    LocalPairResidue r q a b ↔
      (coordClosingValuation
          { r := r, q := q } = a ∧
       (nextCoord
          { r := r, q := q }).r = b) := by
  constructor
  · exact localPairResidue_sufficient hr hq ha hb
  · intro hpair
    have hc : ({ r := r, q := q } : BlockCoord).Valid :=
      ⟨hr, hq⟩
    have hres := localPairResidue_of_coord hc
    rw [hpair.1, hpair.2] at hres
    exact hres








def localPairTarget (a b : ℕ) : ℕ :=
  1 + 2 ^ (a + b) - 2 ^ a




theorem localPairTarget_add_pow
    {a b : ℕ}
    (hb : 1 ≤ b) :
    localPairTarget a b + 2 ^ a =
      localPairRHS a b := by
  have hle : 2 ^ a ≤ 2 ^ (a + b) := by
    gcongr <;> omega
  unfold localPairTarget localPairRHS
  omega




theorem localPairTarget_pos
    {a b : ℕ}
    (hb : 1 ≤ b) :
    0 < localPairTarget a b := by
  have hadd := localPairTarget_add_pow (a := a) hb
  have hle : 2 ^ a ≤ 2 ^ (a + b) := by
    gcongr <;> omega
  unfold localPairRHS at hadd
  omega




theorem localPairTarget_lt_modulus
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    localPairTarget a b <
      localPairModulus a b := by
  have hadd := localPairTarget_add_pow (a := a) hb
  have hrhs := localPairRHS_lt_modulus ha hb
  have hlt :
      localPairTarget a b < localPairRHS a b := by
    have hpow : 0 < 2 ^ a := by positivity
    omega
  exact hlt.trans hrhs




theorem localPairResidue_of_modEq_target
    {r q a b : ℕ}
    (ha : 1 ≤ a)
    (hb : 1 ≤ b)
    (hmod :
      Nat.ModEq
        (localPairModulus a b)
        (3 ^ r * q)
        (localPairTarget a b)) :
    LocalPairResidue r q a b := by
  unfold LocalPairResidue
  change
    (3 ^ r * q) % localPairModulus a b =
      localPairTarget a b % localPairModulus a b at hmod
  calc
    (3 ^ r * q + 2 ^ a) % localPairModulus a b =
        ((3 ^ r * q) % localPairModulus a b +
          (2 ^ a) % localPairModulus a b) %
            localPairModulus a b := Nat.add_mod _ _ _
    _ =
        (localPairTarget a b % localPairModulus a b +
          (2 ^ a) % localPairModulus a b) %
            localPairModulus a b := by rw [hmod]
    _ =
        (localPairTarget a b + 2 ^ a) %
          localPairModulus a b :=
            (Nat.add_mod _ _ _).symm
    _ = localPairRHS a b := by
      rw [localPairTarget_add_pow hb]
      exact Nat.mod_eq_of_lt
        (localPairRHS_lt_modulus ha hb)




theorem odd_q_of_localPairResidue
    {r q a b : ℕ}
    (ha : 1 ≤ a)
    (hb : 1 ≤ b)
    (hres : LocalPairResidue r q a b) :
    Odd q := by
  apply Nat.not_even_iff_odd.mp
  intro hqeven
  rcases hqeven with ⟨j, hj⟩
  rcases localPairResidue_decomposition ha hb hres with
    ⟨k, hdecomp⟩
  cases a with
  | zero => omega
  | succ d =>
      rw [hj] at hdecomp
      simp only [pow_succ] at hdecomp
      ring_nf at hdecomp
      omega




theorem three_pow_coprime_localPairModulus
    (r a b : ℕ) :
    Nat.Coprime
      (3 ^ r)
      (localPairModulus a b) := by
  unfold localPairModulus
  exact
    Nat.Coprime.pow_right (a + b + 1)
      (Nat.Coprime.pow_left r (by norm_num))




theorem exists_odd_q_localPairResidue
    {r a b : ℕ}
    (_hr : 1 ≤ r)
    (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    ∃ q : ℕ,
      Odd q ∧
      LocalPairResidue r q a b := by
  let M := localPairModulus a b
  have hM : NeZero M := ⟨by
    dsimp [M, localPairModulus]
    positivity⟩
  have hu :
      IsUnit (((3 ^ r : ℕ) : ZMod M)) := by
    apply
      (ZMod.isUnit_iff_coprime (3 ^ r) M).2
    simpa [M] using
      three_pow_coprime_localPairModulus r a b
  rcases hu with ⟨u, huval⟩
  let x : ZMod M :=
    ((u⁻¹ : (ZMod M)ˣ) : ZMod M) *
      ((localPairTarget a b : ℕ) : ZMod M)
  let q : ℕ := @ZMod.val M x
  have hqcast : ((q : ℕ) : ZMod M) = x := by
    dsimp [q]
    exact @ZMod.natCast_zmod_val M hM x
  have hzx :
      ((3 ^ r : ℕ) : ZMod M) * x =
        ((localPairTarget a b : ℕ) : ZMod M) := by
    rw [← huval]
    dsimp [x]
    simp [← mul_assoc]
  have hcast :
      ((3 ^ r * q : ℕ) : ZMod M) =
        ((localPairTarget a b : ℕ) : ZMod M) := by
    rw [Nat.cast_mul, hqcast]
    exact hzx
  have hmod :
      Nat.ModEq M
        (3 ^ r * q)
        (localPairTarget a b) :=
    (ZMod.natCast_eq_natCast_iff
      (3 ^ r * q)
      (localPairTarget a b)
      M).mp hcast
  have hres : LocalPairResidue r q a b := by
    exact localPairResidue_of_modEq_target ha hb
      (by simpa [M] using hmod)
  exact ⟨q, odd_q_of_localPairResidue ha hb hres, hres⟩








theorem every_positive_local_pair_realizable
    {r a b : ℕ}
    (hr : 1 ≤ r)
    (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    ∃ q : ℕ,
      Odd q ∧
      coordClosingValuation
        { r := r, q := q } = a ∧
      (nextCoord
        { r := r, q := q }).r = b := by
  rcases exists_odd_q_localPairResidue hr ha hb with
    ⟨q, hq, hres⟩
  rcases localPairResidue_sufficient hr hq ha hb hres with
    ⟨hclose, hnext⟩
  exact ⟨q, hq, hclose, hnext⟩




theorem every_positive_local_pair_realizable_coord
    {r a b : ℕ}
    (hr : 1 ≤ r)
    (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    ∃ c : BlockCoord,
      c.Valid ∧
      c.r = r ∧
      coordClosingValuation c = a ∧
      (nextCoord c).r = b := by
  rcases every_positive_local_pair_realizable hr ha hb with
    ⟨q, hq, hclose, hnext⟩
  refine ⟨{ r := r, q := q }, ?_⟩
  exact ⟨⟨hr, hq⟩, rfl, hclose, hnext⟩




theorem no_positive_closing_nextRunLength_pair_is_forbidden
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    ∃ c : BlockCoord,
      c.Valid ∧
      coordClosingValuation c = a ∧
      (nextCoord c).r = b := by
  rcases
      every_positive_local_pair_realizable_coord
        (r := 1) (by norm_num) ha hb with
    ⟨c, hc, _hr, hclose, hnext⟩
  exact ⟨c, hc, hclose, hnext⟩




example :
    Odd 1 ∧
    coordClosingValuation { r := 1, q := 1 } = 1 ∧
    (nextCoord { r := 1, q := 1 }).r = 1 ∧
    LocalPairResidue 1 1 1 1 := by
  constructor
  · exact ⟨0, rfl⟩
  · constructor
    · native_decide
    · constructor
      · native_decide
      · native_decide




example :
    Odd 13 ∧
    coordClosingValuation { r := 1, q := 13 } = 1 ∧
    (nextCoord { r := 1, q := 13 }).r = 2 ∧
    LocalPairResidue 1 13 1 2 := by
  constructor
  · exact ⟨6, rfl⟩
  · constructor
    · native_decide
    · constructor
      · native_decide
      · native_decide




example :
    Odd 7 ∧
    coordClosingValuation { r := 1, q := 7 } = 2 ∧
    (nextCoord { r := 1, q := 7 }).r = 1 ∧
    LocalPairResidue 1 7 2 1 := by
  constructor
  · exact ⟨3, rfl⟩
  · constructor
    · native_decide
    · constructor
      · native_decide
      · native_decide




example :
    Odd 23 ∧
    coordClosingValuation { r := 2, q := 23 } = 1 ∧
    (nextCoord { r := 2, q := 23 }).r = 3 ∧
    LocalPairResidue 2 23 1 3 := by
  constructor
  · exact ⟨11, rfl⟩
  · constructor
    · native_decide
    · constructor
      · native_decide
      · native_decide




example :
    Odd 35 ∧
    coordClosingValuation { r := 3, q := 35 } = 4 ∧
    (nextCoord { r := 3, q := 35 }).r = 2 ∧
    LocalPairResidue 3 35 4 2 := by
  constructor
  · exact ⟨17, rfl⟩
  · constructor
    · native_decide
    · constructor
      · native_decide
      · native_decide








theorem localPair_q_modEq_unique
    {r q₁ q₂ a b : ℕ}
    (hr : 1 ≤ r)
    (hq₁ : Odd q₁)
    (hq₂ : Odd q₂)
    (ha : 1 ≤ a)
    (hb : 1 ≤ b)
    (h₁ :
      coordClosingValuation
          { r := r, q := q₁ } = a ∧
        (nextCoord
          { r := r, q := q₁ }).r = b)
    (h₂ :
      coordClosingValuation
          { r := r, q := q₂ } = a ∧
        (nextCoord
          { r := r, q := q₂ }).r = b) :
    Nat.ModEq
      (localPairModulus a b)
      q₁ q₂ := by
  have hres₁ :
      LocalPairResidue r q₁ a b :=
    (localPairResidue_iff hr hq₁ ha hb).2 h₁
  have hres₂ :
      LocalPairResidue r q₂ a b :=
    (localPairResidue_iff hr hq₂ ha hb).2 h₂
  have hadd :
      Nat.ModEq
        (localPairModulus a b)
        (3 ^ r * q₁ + 2 ^ a)
        (3 ^ r * q₂ + 2 ^ a) := by
    change
      (3 ^ r * q₁ + 2 ^ a) % localPairModulus a b =
        (3 ^ r * q₂ + 2 ^ a) % localPairModulus a b
    unfold LocalPairResidue at hres₁ hres₂
    rw [hres₁, hres₂]
  have hcastAdd :
      (((3 ^ r * q₁ + 2 ^ a : ℕ) :
          ZMod (localPairModulus a b))) =
        (((3 ^ r * q₂ + 2 ^ a : ℕ) :
          ZMod (localPairModulus a b))) :=
    (ZMod.natCast_eq_natCast_iff
      (3 ^ r * q₁ + 2 ^ a)
      (3 ^ r * q₂ + 2 ^ a)
      (localPairModulus a b)).2 hadd
  have hmul :
      ((3 : ZMod (localPairModulus a b)) ^ r) *
          ((q₁ : ℕ) : ZMod (localPairModulus a b)) =
        ((3 : ZMod (localPairModulus a b)) ^ r) *
          ((q₂ : ℕ) : ZMod (localPairModulus a b)) := by
    push_cast at hcastAdd
    exact add_right_cancel hcastAdd
  have hu :
      IsUnit
        (((3 ^ r : ℕ) :
          ZMod (localPairModulus a b))) := by
    exact
      (ZMod.isUnit_iff_coprime
        (3 ^ r) (localPairModulus a b)).2
        (three_pow_coprime_localPairModulus r a b)
  rcases hu with ⟨u, huval⟩
  push_cast at huval
  rw [← huval] at hmul
  have hqcast :
      ((q₁ : ℕ) : ZMod (localPairModulus a b)) =
        ((q₂ : ℕ) : ZMod (localPairModulus a b)) := by
    apply_fun
      (fun z : ZMod (localPairModulus a b) =>
        ((u⁻¹ : (ZMod (localPairModulus a b))ˣ) :
          ZMod (localPairModulus a b)) * z) at hmul
    simpa [← mul_assoc] using hmul
  exact
    (ZMod.natCast_eq_natCast_iff
      q₁ q₂ (localPairModulus a b)).mp hqcast








theorem three_pow_mul_three
    (r t : ℕ) :
    3 ^ r * (3 * t) =
      3 ^ (r + 1) * t := by
  rw [pow_succ]
  ring




theorem coordNumerator_three_shift
    (r t : ℕ) :
    coordNumerator { r := r, q := 3 * t } =
      coordNumerator { r := r + 1, q := t } := by
  unfold coordNumerator
  rw [three_pow_mul_three]




theorem coordClosingValuation_three_shift
    (r t : ℕ) :
    coordClosingValuation { r := r, q := 3 * t } =
      coordClosingValuation { r := r + 1, q := t } := by
  unfold coordClosingValuation
  rw [coordNumerator_three_shift]




theorem coordNextValue_three_shift
    (r t : ℕ) :
    coordNextValue { r := r, q := 3 * t } =
      coordNextValue { r := r + 1, q := t } := by
  unfold coordNextValue
  rw [coordNumerator_three_shift,
      coordClosingValuation_three_shift]




theorem coordBridgeNumerator_three_shift
    (r t : ℕ) :
    coordBridgeNumerator { r := r, q := 3 * t } =
      coordBridgeNumerator { r := r + 1, q := t } := by
  unfold coordBridgeNumerator
  rw [coordNumerator_three_shift,
      coordClosingValuation_three_shift]




theorem three_shift_left_valid
    {r t : ℕ}
    (hr : 1 ≤ r)
    (ht : Odd t) :
    ({ r := r, q := 3 * t } : BlockCoord).Valid := by
  refine ⟨hr, ?_⟩
  rcases ht with ⟨k, hk⟩
  refine ⟨3 * k + 1, ?_⟩
  rw [hk]
  ring




theorem three_shift_right_valid
    {r t : ℕ}
    (ht : Odd t) :
    ({ r := r + 1, q := t } : BlockCoord).Valid := by
  constructor
  · change 1 ≤ r + 1
    omega
  · exact ht




theorem nextCoord_three_shift
    {r t : ℕ}
    (hr : 1 ≤ r)
    (ht : Odd t) :
    nextCoord { r := r, q := 3 * t } =
      nextCoord { r := r + 1, q := t } := by
  have hleft := three_shift_left_valid hr ht
  have hright := three_shift_right_valid (r := r) ht
  rw [nextCoord_eq_encode_coordNextValue hleft,
      nextCoord_eq_encode_coordNextValue hright,
      coordNextValue_three_shift]




theorem nextCoord_r_three_shift
    {r t : ℕ}
    (hr : 1 ≤ r)
    (ht : Odd t) :
    (nextCoord { r := r, q := 3 * t }).r =
      (nextCoord { r := r + 1, q := t }).r := by
  exact congrArg BlockCoord.r
    (nextCoord_three_shift hr ht)




theorem nextCoord_q_three_shift
    {r t : ℕ}
    (hr : 1 ≤ r)
    (ht : Odd t) :
    (nextCoord { r := r, q := 3 * t }).q =
      (nextCoord { r := r + 1, q := t }).q := by
  exact congrArg BlockCoord.q
    (nextCoord_three_shift hr ht)




theorem blockNext_decode_three_shift
    {r t : ℕ}
    (hr : 1 ≤ r)
    (ht : Odd t) :
    blockNext
        (decodeBlockCoord { r := r, q := 3 * t }) =
      blockNext
        (decodeBlockCoord { r := r + 1, q := t }) := by
  have hleft := three_shift_left_valid hr ht
  have hright := three_shift_right_valid (r := r) ht
  rw [← coordNextValue_eq_blockNext_decode hleft,
      ← coordNextValue_eq_blockNext_decode hright,
      coordNextValue_three_shift]




theorem coordOrbit_three_shift_after_one
    {r t n : ℕ}
    (hr : 1 ≤ r)
    (ht : Odd t) :
    coordOrbit { r := r, q := 3 * t } (n + 1) =
      coordOrbit { r := r + 1, q := t } (n + 1) := by
  induction n with
  | zero =>
      simpa [coordOrbit_succ] using
        nextCoord_three_shift hr ht
  | succ n ih =>
      calc
        coordOrbit { r := r, q := 3 * t } ((n + 1) + 1) =
            nextCoord
              (coordOrbit { r := r, q := 3 * t } (n + 1)) :=
          coordOrbit_succ _ (n + 1)
        _ = nextCoord
              (coordOrbit { r := r + 1, q := t } (n + 1)) :=
          congrArg nextCoord ih
        _ = coordOrbit { r := r + 1, q := t } ((n + 1) + 1) :=
          (coordOrbit_succ _ (n + 1)).symm




theorem blockNext_iterate_decode_three_shift_after_one
    {r t n : ℕ}
    (hr : 1 ≤ r)
    (ht : Odd t) :
    blockNext^[n + 1]
        (decodeBlockCoord { r := r, q := 3 * t }) =
      blockNext^[n + 1]
        (decodeBlockCoord { r := r + 1, q := t }) := by
  have hleft := three_shift_left_valid hr ht
  have hright := three_shift_right_valid (r := r) ht
  calc
    blockNext^[n + 1]
        (decodeBlockCoord { r := r, q := 3 * t }) =
      decodeBlockCoord
        (coordOrbit { r := r, q := 3 * t } (n + 1)) :=
          (decode_coordOrbit hleft (n + 1)).symm
    _ = decodeBlockCoord
        (coordOrbit { r := r + 1, q := t } (n + 1)) := by
          rw [coordOrbit_three_shift_after_one hr ht]
    _ = blockNext^[n + 1]
        (decodeBlockCoord { r := r + 1, q := t }) :=
          decode_coordOrbit hright (n + 1)




theorem decodeBlockCoord_three_shift_lt
    {r t : ℕ}
    (_hr : 1 ≤ r)
    (ht : Odd t) :
    decodeBlockCoord { r := r + 1, q := t } <
      decodeBlockCoord { r := r, q := 3 * t } := by
  have htpos : 0 < t := by
    rcases ht with ⟨k, hk⟩
    omega
  have hx : 0 < 2 ^ r * t := by positivity
  have hleft :
      2 ^ (r + 1) * t =
        2 * (2 ^ r * t) := by
    rw [pow_succ]
    ring
  have hright :
      2 ^ r * (3 * t) =
        3 * (2 ^ r * t) := by ring
  unfold decodeBlockCoord
  rw [hleft, hright]
  omega




theorem nextCoord_not_injective :
    ¬ Function.Injective nextCoord := by
  intro hinj
  have heq :=
    nextCoord_three_shift
      (r := 2) (t := 1)
      (by norm_num)
      (by exact ⟨0, rfl⟩)
  have hne :
      ({ r := 2, q := 3 } : BlockCoord) ≠
        ({ r := 3, q := 1 } : BlockCoord) := by
    native_decide
  exact hne (hinj heq)








theorem coordNumerator_three_pow_shift
    (r k t : ℕ) :
    coordNumerator { r := r, q := 3 ^ k * t } =
      coordNumerator { r := r + k, q := t } := by
  unfold coordNumerator
  simp [pow_add, mul_assoc]




theorem odd_three_pow_mul
    {k t : ℕ}
    (ht : Odd t) :
    Odd (3 ^ k * t) := by
  exact (Odd.pow (by norm_num : Odd 3)).mul ht




theorem nextCoord_three_pow_shift
    {r k t : ℕ}
    (hr : 1 ≤ r)
    (ht : Odd t) :
    nextCoord { r := r, q := 3 ^ k * t } =
      nextCoord { r := r + k, q := t } := by
  have hleft :
      ({ r := r, q := 3 ^ k * t } : BlockCoord).Valid :=
    ⟨hr, odd_three_pow_mul ht⟩
  have hright :
      ({ r := r + k, q := t } : BlockCoord).Valid := by
    constructor
    · change 1 ≤ r + k
      omega
    · exact ht
  have hnum :=
    coordNumerator_three_pow_shift r k t
  have hclose :
      coordClosingValuation
          { r := r, q := 3 ^ k * t } =
        coordClosingValuation
          { r := r + k, q := t } := by
    unfold coordClosingValuation
    rw [hnum]
  have hnext :
      coordNextValue
          { r := r, q := 3 ^ k * t } =
        coordNextValue
          { r := r + k, q := t } := by
    unfold coordNextValue
    rw [hnum, hclose]
  rw [nextCoord_eq_encode_coordNextValue hleft,
      nextCoord_eq_encode_coordNextValue hright,
      hnext]




theorem coordOrbit_three_pow_shift_after_one
    {r k t n : ℕ}
    (hr : 1 ≤ r)
    (ht : Odd t) :
    coordOrbit { r := r, q := 3 ^ k * t } (n + 1) =
      coordOrbit { r := r + k, q := t } (n + 1) := by
  induction n with
  | zero =>
      simpa [coordOrbit_succ] using
        nextCoord_three_pow_shift hr ht
  | succ n ih =>
      calc
        coordOrbit { r := r, q := 3 ^ k * t } ((n + 1) + 1) =
            nextCoord
              (coordOrbit
                { r := r, q := 3 ^ k * t } (n + 1)) :=
          coordOrbit_succ _ (n + 1)
        _ = nextCoord
              (coordOrbit
                { r := r + k, q := t } (n + 1)) :=
          congrArg nextCoord ih
        _ = coordOrbit
              { r := r + k, q := t } ((n + 1) + 1) :=
          (coordOrbit_succ _ (n + 1)).symm




theorem three_factor_fusion_spec
    {r t : ℕ}
    (hr : 1 ≤ r)
    (ht : Odd t) :
    coordNumerator { r := r, q := 3 * t } =
        coordNumerator { r := r + 1, q := t }
    ∧
    coordClosingValuation { r := r, q := 3 * t } =
        coordClosingValuation { r := r + 1, q := t }
    ∧
    coordNextValue { r := r, q := 3 * t } =
        coordNextValue { r := r + 1, q := t }
    ∧
    nextCoord { r := r, q := 3 * t } =
        nextCoord { r := r + 1, q := t } := by
  exact
    ⟨coordNumerator_three_shift r t,
     coordClosingValuation_three_shift r t,
     coordNextValue_three_shift r t,
     nextCoord_three_shift hr ht⟩




example :
    decodeBlockCoord { r := 2, q := 3 } = 11 ∧
    decodeBlockCoord { r := 3, q := 1 } = 7 ∧
    coordNumerator { r := 2, q := 3 } = 26 ∧
    coordNumerator { r := 3, q := 1 } = 26 ∧
    coordClosingValuation { r := 2, q := 3 } = 1 ∧
    coordClosingValuation { r := 3, q := 1 } = 1 ∧
    coordNextValue { r := 2, q := 3 } = 13 ∧
    coordNextValue { r := 3, q := 1 } = 13 ∧
    nextCoord { r := 2, q := 3 } = { r := 1, q := 7 } ∧
    nextCoord { r := 3, q := 1 } = { r := 1, q := 7 } := by
  native_decide




example :
    coordNumerator { r := 1, q := 15 } =
      coordNumerator { r := 2, q := 5 } ∧
    coordNextValue { r := 1, q := 15 } =
      coordNextValue { r := 2, q := 5 } ∧
    nextCoord { r := 1, q := 15 } =
      nextCoord { r := 2, q := 5 } := by
  native_decide




example :
    nextCoord { r := 1, q := 45 } =
      nextCoord { r := 3, q := 5 } := by
  native_decide








def v3 (n : ℕ) : ℕ :=
  padicValNat 3 n




theorem pow_v3_dvd
    {n : ℕ}
    (hn : n ≠ 0) :
    3 ^ v3 n ∣ n := by
  rw [v3, padicValNat_dvd_iff_le hn]




theorem pow_three_dvd_iff_le_v3
    {n k : ℕ}
    (hn : n ≠ 0) :
    3 ^ k ∣ n ↔ k ≤ v3 n := by
  simpa [v3] using
    (padicValNat_dvd_iff_le
      (p := 3) (a := n) (n := k) hn)




def threeFreePart (q : ℕ) : ℕ :=
  q / 3 ^ v3 q




theorem threeFreePart_factorization
    {q : ℕ}
    (hq : q ≠ 0) :
    q = 3 ^ v3 q * threeFreePart q := by
  have hd : 3 ^ v3 q ∣ q :=
    pow_v3_dvd hq
  simpa [threeFreePart] using
    (Nat.mul_div_cancel' hd).symm




theorem threeFreePart_pos
    {q : ℕ}
    (hq : q ≠ 0) :
    0 < threeFreePart q := by
  have hfactor := threeFreePart_factorization hq
  have hpow : 0 < 3 ^ v3 q := by positivity
  by_contra hnot
  have hzero : threeFreePart q = 0 := by omega
  rw [hzero, mul_zero] at hfactor
  exact hq hfactor




theorem three_not_dvd_threeFreePart
    {q : ℕ}
    (hq : q ≠ 0) :
    ¬ 3 ∣ threeFreePart q := by
  intro hd
  rcases hd with ⟨d, hd⟩
  have hfactor := threeFreePart_factorization hq
  have hpow :
      3 ^ (v3 q + 1) ∣ q := by
    refine ⟨d, ?_⟩
    calc
      q = 3 ^ v3 q * threeFreePart q := hfactor
      _ = 3 ^ v3 q * (3 * d) := by rw [hd]
      _ = 3 ^ (v3 q + 1) * d := by
        rw [pow_succ]
        ring
  have hle :=
    (pow_three_dvd_iff_le_v3 hq).1 hpow
  omega




theorem v3_threeFreePart_eq_zero
    {q : ℕ}
    (hq : q ≠ 0) :
    v3 (threeFreePart q) = 0 := by
  rw [v3, padicValNat.eq_zero_iff]
  right
  right
  exact three_not_dvd_threeFreePart hq




theorem threeFreePart_odd
    {q : ℕ}
    (hq : Odd q) :
    Odd (threeFreePart q) := by
  have hqne : q ≠ 0 := by
    rcases hq with ⟨k, hk⟩
    omega
  have hfactor := threeFreePart_factorization hqne
  by_contra hnotodd
  have heven : Even (threeFreePart q) := by
    by_contra hnoteven
    exact hnotodd (Nat.not_even_iff_odd.mp hnoteven)
  rcases hq with ⟨k, hk⟩
  rcases heven with ⟨d, hd⟩
  have hparity :
      2 * k + 1 =
        3 ^ v3 q * (d + d) := by
    calc
      2 * k + 1 = q := hk.symm
      _ = 3 ^ v3 q * threeFreePart q := hfactor
      _ = 3 ^ v3 q * (d + d) := by rw [hd]
  ring_nf at hparity
  omega




theorem v3_pos_iff_three_dvd
    {q : ℕ}
    (hq : q ≠ 0) :
    0 < v3 q ↔ 3 ∣ q := by
  constructor
  · intro hv
    exact
      (pow_three_dvd_iff_le_v3 (k := 1) hq).2
        (by omega)
  · intro hd
    have hle :=
      (pow_three_dvd_iff_le_v3 (k := 1) hq).1
        (by simpa using hd)
    omega




def normalizeCoord (c : BlockCoord) : BlockCoord :=
  {
    r := c.r + v3 c.q
    q := threeFreePart c.q
  }




theorem normalizeCoord_valid
    {c : BlockCoord}
    (hc : c.Valid) :
    (normalizeCoord c).Valid := by
  constructor
  · have hr := hc.1
    change 1 ≤ c.r at hr
    change 1 ≤ c.r + v3 c.q
    omega
  · exact threeFreePart_odd hc.2




theorem normalizeCoord_three_free
    {c : BlockCoord}
    (hc : c.Valid) :
    ¬ 3 ∣ (normalizeCoord c).q := by
  apply three_not_dvd_threeFreePart
  exact Nat.ne_of_gt (valid_coord_q_pos hc)




theorem normalizeCoord_v3_q_eq_zero
    {c : BlockCoord}
    (hc : c.Valid) :
    v3 (normalizeCoord c).q = 0 := by
  apply v3_threeFreePart_eq_zero
  exact Nat.ne_of_gt (valid_coord_q_pos hc)




theorem threeFreePart_of_v3_eq_zero
    {q : ℕ}
    (h : v3 q = 0) :
    threeFreePart q = q := by
  unfold threeFreePart
  rw [h]
  simp




theorem normalizeCoord_idempotent
    {c : BlockCoord}
    (hc : c.Valid) :
    normalizeCoord (normalizeCoord c) =
      normalizeCoord c := by
  have hv := normalizeCoord_v3_q_eq_zero hc
  unfold normalizeCoord at hv ⊢
  rw [hv, threeFreePart_of_v3_eq_zero hv]
  simp




theorem normalizeCoord_eq_self_of_three_free
    {c : BlockCoord}
    (_hc : c.Valid)
    (h3 : ¬ 3 ∣ c.q) :
    normalizeCoord c = c := by
  have hv : v3 c.q = 0 := by
    rw [v3, padicValNat.eq_zero_iff]
    right
    right
    exact h3
  unfold normalizeCoord
  rw [hv, threeFreePart_of_v3_eq_zero hv]
  simp




theorem normalizeCoord_eq_self_iff
    {c : BlockCoord}
    (hc : c.Valid) :
    normalizeCoord c = c ↔ ¬ 3 ∣ c.q := by
  constructor
  · intro hself
    have hr := congrArg BlockCoord.r hself
    change c.r + v3 c.q = c.r at hr
    have hv : v3 c.q = 0 := by omega
    rw [v3, padicValNat.eq_zero_iff] at hv
    rcases hv with hbad | hbad | hgood
    · norm_num at hbad
    · exact False.elim
        (Nat.ne_of_gt (valid_coord_q_pos hc) hbad)
    · exact hgood
  · exact normalizeCoord_eq_self_of_three_free hc




theorem q_eq_three_pow_v3_mul_threeFreePart
    {c : BlockCoord}
    (hc : c.Valid) :
    c.q =
      3 ^ v3 c.q * threeFreePart c.q := by
  exact threeFreePart_factorization
    (Nat.ne_of_gt (valid_coord_q_pos hc))




theorem coordNumerator_normalize
    {c : BlockCoord}
    (hc : c.Valid) :
    coordNumerator (normalizeCoord c) =
      coordNumerator c := by
  have hfactor :=
    q_eq_three_pow_v3_mul_threeFreePart hc
  have hshift :=
    coordNumerator_three_pow_shift
      c.r (v3 c.q) (threeFreePart c.q)
  change
    coordNumerator
        { r := c.r + v3 c.q,
          q := threeFreePart c.q } =
      coordNumerator c
  calc
    coordNumerator
        { r := c.r + v3 c.q,
          q := threeFreePart c.q } =
      coordNumerator
        { r := c.r,
          q := 3 ^ v3 c.q * threeFreePart c.q } :=
        hshift.symm
    _ = coordNumerator c := by rw [← hfactor]




theorem coordClosingValuation_normalize
    {c : BlockCoord}
    (hc : c.Valid) :
    coordClosingValuation (normalizeCoord c) =
      coordClosingValuation c := by
  unfold coordClosingValuation
  rw [coordNumerator_normalize hc]




theorem coordNextValue_normalize
    {c : BlockCoord}
    (hc : c.Valid) :
    coordNextValue (normalizeCoord c) =
      coordNextValue c := by
  unfold coordNextValue
  rw [coordNumerator_normalize hc,
      coordClosingValuation_normalize hc]




theorem nextCoord_normalize
    {c : BlockCoord}
    (hc : c.Valid) :
    nextCoord (normalizeCoord c) =
      nextCoord c := by
  have hfactor :=
    q_eq_three_pow_v3_mul_threeFreePart hc
  have hshift :=
    nextCoord_three_pow_shift
      (r := c.r)
      (k := v3 c.q)
      (t := threeFreePart c.q)
      hc.1
      (threeFreePart_odd hc.2)
  change
    nextCoord
        { r := c.r + v3 c.q,
          q := threeFreePart c.q } =
      nextCoord c
  calc
    nextCoord
        { r := c.r + v3 c.q,
          q := threeFreePart c.q } =
      nextCoord
        { r := c.r,
          q := 3 ^ v3 c.q * threeFreePart c.q } :=
        hshift.symm
    _ = nextCoord c := by rw [← hfactor]




theorem coordOrbit_normalize_after_one
    {c : BlockCoord}
    (hc : c.Valid)
    (n : ℕ) :
    coordOrbit (normalizeCoord c) (n + 1) =
      coordOrbit c (n + 1) := by
  induction n with
  | zero =>
      simpa [coordOrbit_succ] using
        nextCoord_normalize hc
  | succ n ih =>
      calc
        coordOrbit (normalizeCoord c) ((n + 1) + 1) =
            nextCoord
              (coordOrbit (normalizeCoord c) (n + 1)) :=
          coordOrbit_succ _ (n + 1)
        _ = nextCoord
              (coordOrbit c (n + 1)) :=
          congrArg nextCoord ih
        _ = coordOrbit c ((n + 1) + 1) :=
          (coordOrbit_succ _ (n + 1)).symm








theorem decodeCoord_add_one_factorized
    {c : BlockCoord}
    (hc : c.Valid) :
    decodeBlockCoord c + 1 =
      2 ^ c.r *
        (3 ^ v3 c.q * threeFreePart c.q) := by
  calc
    decodeBlockCoord c + 1 =
        2 ^ c.r * c.q :=
      decodeBlockCoord_add_one hc
    _ = 2 ^ c.r *
        (3 ^ v3 c.q * threeFreePart c.q) :=
      congrArg (fun q => 2 ^ c.r * q)
        (q_eq_three_pow_v3_mul_threeFreePart hc)




theorem decodeNormalize_add_one
    {c : BlockCoord}
    (hc : c.Valid) :
    decodeBlockCoord (normalizeCoord c) + 1 =
      2 ^ (c.r + v3 c.q) *
        threeFreePart c.q := by
  simpa [normalizeCoord] using
    decodeBlockCoord_add_one (normalizeCoord_valid hc)




theorem two_pow_le_three_pow
    (k : ℕ) :
    2 ^ k ≤ 3 ^ k := by
  gcongr
  norm_num




theorem two_pow_lt_three_pow
    {k : ℕ}
    (hk : 0 < k) :
    2 ^ k < 3 ^ k := by
  cases k with
  | zero => omega
  | succ k =>
      rw [pow_succ, pow_succ]
      have hle := two_pow_le_three_pow k
      have hp : 0 < 2 ^ k := by positivity
      omega




theorem decode_normalize_le
    {c : BlockCoord}
    (hc : c.Valid) :
    decodeBlockCoord (normalizeCoord c) ≤
      decodeBlockCoord c := by
  have hnorm := decodeNormalize_add_one hc
  have horig := decodeCoord_add_one_factorized hc
  have hpow := two_pow_le_three_pow (v3 c.q)
  have hleft :=
    Nat.mul_le_mul_left (2 ^ c.r) hpow
  have hprod :=
    Nat.mul_le_mul_right
      (threeFreePart c.q) hleft
  have hproduct :
      2 ^ (c.r + v3 c.q) *
          threeFreePart c.q ≤
        2 ^ c.r *
          (3 ^ v3 c.q * threeFreePart c.q) := by
    simpa [pow_add, mul_assoc] using hprod
  omega




theorem decode_normalize_lt_of_v3_pos
    {c : BlockCoord}
    (hc : c.Valid)
    (hk : 0 < v3 c.q) :
    decodeBlockCoord (normalizeCoord c) <
      decodeBlockCoord c := by
  have hnorm := decodeNormalize_add_one hc
  have horig := decodeCoord_add_one_factorized hc
  have hpow := two_pow_lt_three_pow hk
  have hleft :=
    Nat.mul_lt_mul_of_pos_left hpow
      (by positivity : 0 < 2 ^ c.r)
  have htpos :
      0 < threeFreePart c.q :=
    threeFreePart_pos
      (Nat.ne_of_gt (valid_coord_q_pos hc))
  have hprod :=
    Nat.mul_lt_mul_of_pos_right hleft htpos
  have hproduct :
      2 ^ (c.r + v3 c.q) *
          threeFreePart c.q <
        2 ^ c.r *
          (3 ^ v3 c.q * threeFreePart c.q) := by
    simpa [pow_add, mul_assoc] using hprod
  omega




theorem decode_normalize_lt_of_three_dvd
    {c : BlockCoord}
    (hc : c.Valid)
    (h3 : 3 ∣ c.q) :
    decodeBlockCoord (normalizeCoord c) <
      decodeBlockCoord c := by
  apply decode_normalize_lt_of_v3_pos hc
  exact
    (v3_pos_iff_three_dvd
      (Nat.ne_of_gt (valid_coord_q_pos hc))).2 h3




theorem decode_normalize_eq_of_three_free
    {c : BlockCoord}
    (hc : c.Valid)
    (h3 : ¬ 3 ∣ c.q) :
    decodeBlockCoord (normalizeCoord c) =
      decodeBlockCoord c := by
  rw [normalizeCoord_eq_self_of_three_free hc h3]




theorem decode_normalize_lt_iff
    {c : BlockCoord}
    (hc : c.Valid) :
    decodeBlockCoord (normalizeCoord c) <
        decodeBlockCoord c
      ↔
    3 ∣ c.q := by
  constructor
  · intro hlt
    by_contra hnot
    have heq :=
      decode_normalize_eq_of_three_free hc hnot
    omega
  · exact decode_normalize_lt_of_three_dvd hc




theorem decode_normalize_lt_iff_v3_pos
    {c : BlockCoord}
    (hc : c.Valid) :
    decodeBlockCoord (normalizeCoord c) <
        decodeBlockCoord c
      ↔
    0 < v3 c.q := by
  rw [decode_normalize_lt_iff hc]
  exact
    (v3_pos_iff_three_dvd
      (Nat.ne_of_gt (valid_coord_q_pos hc))).symm




theorem normalizeCoord_spec
    {c : BlockCoord}
    (hc : c.Valid) :
    (normalizeCoord c).Valid
    ∧
    ¬ 3 ∣ (normalizeCoord c).q
    ∧
    nextCoord (normalizeCoord c) = nextCoord c
    ∧
    decodeBlockCoord (normalizeCoord c) ≤
      decodeBlockCoord c := by
  exact
    ⟨normalizeCoord_valid hc,
     normalizeCoord_three_free hc,
     nextCoord_normalize hc,
     decode_normalize_le hc⟩




theorem normalized_and_original_same_future
    {c : BlockCoord}
    (hc : c.Valid)
    (n : ℕ) :
    coordOrbit (normalizeCoord c) (n + 1) =
      coordOrbit c (n + 1) := by
  exact coordOrbit_normalize_after_one hc n




example : v3 45 = 2 := by
  native_decide




example :
    normalizeCoord { r := 2, q := 3 } =
      { r := 3, q := 1 } := by
  native_decide




example :
    normalizeCoord { r := 1, q := 15 } =
      { r := 2, q := 5 } := by
  native_decide




example :
    normalizeCoord { r := 1, q := 45 } =
      { r := 3, q := 5 } := by
  native_decide




example :
    normalizeCoord { r := 3, q := 5 } =
      { r := 3, q := 5 } := by
  native_decide




example :
    nextCoord (normalizeCoord { r := 1, q := 45 }) =
      nextCoord { r := 1, q := 45 } := by
  native_decide




example :
    decodeBlockCoord { r := 2, q := 3 } = 11 ∧
    decodeBlockCoord (normalizeCoord { r := 2, q := 3 }) = 7 := by
  native_decide




example :
    decodeBlockCoord { r := 1, q := 45 } = 89 ∧
    decodeBlockCoord (normalizeCoord { r := 1, q := 45 }) = 39 ∧
    decodeBlockCoord (normalizeCoord { r := 1, q := 45 }) <
      decodeBlockCoord { r := 1, q := 45 } := by
  native_decide








theorem normalizeCoord_one :
    normalizeCoord oneCoord = oneCoord := by
  apply normalizeCoord_eq_self_of_three_free oneCoord_valid
  rw [oneCoord_eq]
  norm_num




theorem reachesOne_normalize_iff (c : BlockCoord) (hc : c.Valid) :
    ReachesOneByCoords (normalizeCoord c) ↔ ReachesOneByCoords c := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero =>
        have hnormeq : normalizeCoord c = oneCoord := by
          simpa using hn
        refine ⟨1, ?_⟩
        rw [coordOrbit_succ]
        simp only [coordOrbit_zero]
        have hnext := nextCoord_normalize hc
        rw [hnormeq, nextCoord_one] at hnext
        exact hnext.symm
    | succ n =>
        refine ⟨n + 1, ?_⟩
        rw [← coordOrbit_normalize_after_one hc n]
        simpa using hn
  · rintro ⟨n, hn⟩
    cases n with
    | zero =>
        have hcOne : c = oneCoord := by
          simpa using hn
        refine ⟨0, ?_⟩
        simp [hcOne, normalizeCoord_one]
    | succ n =>
        refine ⟨n + 1, ?_⟩
        rw [coordOrbit_normalize_after_one hc n]
        simpa using hn








/-!
## Reducción universal al subespacio normalizado




La alcanzabilidad universal de oneCoord en todo el espacio válido
equivale exactamente a la alcanzabilidad universal restringida a
coordenadas con q impar y no divisible por 3.
-/




def BlockCoord.Normalized (c : BlockCoord) : Prop :=
  c.Valid ∧ ¬ 3 ∣ c.q




theorem normalizeCoord_normalized
    {c : BlockCoord}
    (hc : c.Valid) :
    (normalizeCoord c).Normalized := by
  exact
    ⟨normalizeCoord_valid hc,
     normalizeCoord_three_free hc⟩




theorem normalized_iff_normalize_eq_self
    {c : BlockCoord}
    (hc : c.Valid) :
    c.Normalized ↔ normalizeCoord c = c := by
  constructor
  · intro hnorm
    exact (normalizeCoord_eq_self_iff hc).2 hnorm.2
  · intro hself
    exact
      ⟨hc,
       (normalizeCoord_eq_self_iff hc).1 hself⟩




def AllValidCoordsReachOne : Prop :=
  ∀ c : BlockCoord,
    c.Valid →
    ReachesOneByCoords c




def AllNormalizedCoordsReachOne : Prop :=
  ∀ c : BlockCoord,
    c.Normalized →
    ReachesOneByCoords c




theorem all_valid_implies_all_normalized :
    AllValidCoordsReachOne →
    AllNormalizedCoordsReachOne := by
  intro hall c hc
  exact hall c hc.1




theorem all_normalized_implies_all_valid :
    AllNormalizedCoordsReachOne →
    AllValidCoordsReachOne := by
  intro hall c hc
  have hnorm :
      (normalizeCoord c).Normalized :=
    normalizeCoord_normalized hc
  have hreach :
      ReachesOneByCoords (normalizeCoord c) :=
    hall (normalizeCoord c) hnorm
  exact (reachesOne_normalize_iff c hc).1 hreach




theorem normalized_global_reachability_iff :
    AllValidCoordsReachOne ↔
    AllNormalizedCoordsReachOne := by
  exact
    ⟨all_valid_implies_all_normalized,
     all_normalized_implies_all_valid⟩




theorem normalized_global_reachability_iff_expanded :
    (∀ c : BlockCoord,
        c.Valid →
        ReachesOneByCoords c)
    ↔
    (∀ c : BlockCoord,
        c.Valid →
        ¬ 3 ∣ c.q →
        ReachesOneByCoords c) := by
  simpa only
      [AllValidCoordsReachOne,
       AllNormalizedCoordsReachOne,
       BlockCoord.Normalized,
       and_imp] using
    normalized_global_reachability_iff




def AllOddReachOneByBlocks : Prop :=
  ∀ m : ℕ,
    Odd m →
    ReachesOneByBlocks m




theorem all_valid_coords_iff_all_odd_blocks :
    AllValidCoordsReachOne ↔
    AllOddReachOneByBlocks := by
  constructor
  · intro hcoords m hm
    have hreach :
        ReachesOneByCoords (encodeBlockCoord m) :=
      hcoords (encodeBlockCoord m)
        (encodeBlockCoord_valid hm)
    exact (reachesOne_coords_iff_blocks hm).1 hreach
  · intro hblocks c hc
    have hmOdd : Odd (decodeBlockCoord c) :=
      decodeBlockCoord_odd hc
    have hmReach :
        ReachesOneByBlocks (decodeBlockCoord c) :=
      hblocks (decodeBlockCoord c) hmOdd
    have hencoded :
        ReachesOneByCoords
          (encodeBlockCoord (decodeBlockCoord c)) :=
      (reachesOne_coords_iff_blocks hmOdd).2 hmReach
    rw [encode_decodeBlockCoord hc] at hencoded
    exact hencoded




theorem all_odd_blocks_iff_all_normalized_coords :
    AllOddReachOneByBlocks ↔
    AllNormalizedCoordsReachOne := by
  constructor
  · intro hblocks
    exact
      normalized_global_reachability_iff.1
        (all_valid_coords_iff_all_odd_blocks.2 hblocks)
  · intro hnorm
    exact
      all_valid_coords_iff_all_odd_blocks.1
        (normalized_global_reachability_iff.2 hnorm)




theorem all_odd_blocks_iff_three_free_coords :
    (∀ m : ℕ,
        Odd m →
        ReachesOneByBlocks m)
    ↔
    (∀ c : BlockCoord,
        c.Valid →
        ¬ 3 ∣ c.q →
        ReachesOneByCoords c) := by
  simpa only
      [AllOddReachOneByBlocks,
       AllNormalizedCoordsReachOne,
       BlockCoord.Normalized,
       and_imp] using
    all_odd_blocks_iff_all_normalized_coords




/-!
## Fallos y contraejemplos mínimos en coordenadas
-/




def FailsToReachOneByCoords (c : BlockCoord) : Prop :=
  c.Valid ∧ ¬ ReachesOneByCoords c




theorem fails_normalize_iff
    {c : BlockCoord}
    (hc : c.Valid) :
    FailsToReachOneByCoords (normalizeCoord c) ↔
      FailsToReachOneByCoords c := by
  constructor
  · rintro ⟨_, hnot⟩
    exact
      ⟨hc, fun hreach =>
        hnot ((reachesOne_normalize_iff c hc).2 hreach)⟩
  · rintro ⟨_, hnot⟩
    exact
      ⟨normalizeCoord_valid hc, fun hreach =>
        hnot ((reachesOne_normalize_iff c hc).1 hreach)⟩




theorem failing_coord_reduces_if_three_dvd
    {c : BlockCoord}
    (hfail : FailsToReachOneByCoords c)
    (h3 : 3 ∣ c.q) :
    FailsToReachOneByCoords (normalizeCoord c)
    ∧
    decodeBlockCoord (normalizeCoord c) <
      decodeBlockCoord c := by
  exact
    ⟨(fails_normalize_iff hfail.1).2 hfail,
     decode_normalize_lt_of_three_dvd hfail.1 h3⟩




def IsMinimalCoordCounterexample
    (c : BlockCoord) : Prop :=
  FailsToReachOneByCoords c ∧
  ∀ d : BlockCoord,
    d.Valid →
    decodeBlockCoord d < decodeBlockCoord c →
    ReachesOneByCoords d




theorem minimal_coord_counterexample_three_free
    {c : BlockCoord}
    (hmin : IsMinimalCoordCounterexample c) :
    ¬ 3 ∣ c.q := by
  intro h3
  have hc : c.Valid := hmin.1.1
  have hnormValid : (normalizeCoord c).Valid :=
    normalizeCoord_valid hc
  have hlt :
      decodeBlockCoord (normalizeCoord c) <
        decodeBlockCoord c :=
    decode_normalize_lt_of_three_dvd hc h3
  have hnormReach :
      ReachesOneByCoords (normalizeCoord c) :=
    hmin.2 (normalizeCoord c) hnormValid hlt
  have hcReach : ReachesOneByCoords c :=
    (reachesOne_normalize_iff c hc).1 hnormReach
  exact hmin.1.2 hcReach




theorem minimal_coord_counterexample_is_normalized
    {c : BlockCoord}
    (hmin : IsMinimalCoordCounterexample c) :
    c.Normalized := by
  exact
    ⟨hmin.1.1,
     minimal_coord_counterexample_three_free hmin⟩




theorem normalize_minimal_coord_counterexample
    {c : BlockCoord}
    (hmin : IsMinimalCoordCounterexample c) :
    normalizeCoord c = c := by
  exact
    normalizeCoord_eq_self_of_three_free
      hmin.1.1
      (minimal_coord_counterexample_three_free hmin)








/-!
## Contraejemplos condicionales en la dinámica por bloques
-/




def FailsToReachOneByBlocks (m : ℕ) : Prop :=
  Odd m ∧ ¬ ReachesOneByBlocks m




def IsMinimalBlockCounterexample (m : ℕ) : Prop :=
  FailsToReachOneByBlocks m ∧
  ∀ n : ℕ,
    Odd n →
    n < m →
    ReachesOneByBlocks n




def normalizeOddState (m : ℕ) : ℕ :=
  decodeBlockCoord
    (normalizeCoord (encodeBlockCoord m))




theorem normalizeOddState_odd
    {m : ℕ}
    (hm : Odd m) :
    Odd (normalizeOddState m) := by
  exact
    decodeBlockCoord_odd
      (normalizeCoord_valid
        (encodeBlockCoord_valid hm))




theorem normalizeOddState_le
    {m : ℕ}
    (hm : Odd m) :
    normalizeOddState m ≤ m := by
  have hle :=
    decode_normalize_le
      (encodeBlockCoord_valid hm)
  rw [decode_encodeBlockCoord hm] at hle
  exact hle




theorem normalizeOddState_lt_iff
    {m : ℕ}
    (hm : Odd m) :
    normalizeOddState m < m ↔
      3 ∣ blockQuotient m := by
  have hlt :=
    decode_normalize_lt_iff
      (encodeBlockCoord_valid hm)
  rw [decode_encodeBlockCoord hm] at hlt
  simpa only [normalizeOddState, encodeBlockCoord] using hlt




theorem encode_normalizeOddState
    {m : ℕ}
    (hm : Odd m) :
    encodeBlockCoord (normalizeOddState m) =
      normalizeCoord (encodeBlockCoord m) := by
  exact
    encode_decodeBlockCoord
      (normalizeCoord_valid
        (encodeBlockCoord_valid hm))




theorem reachesOne_normalizeOddState_iff
    {m : ℕ}
    (hm : Odd m) :
    ReachesOneByBlocks (normalizeOddState m) ↔
      ReachesOneByBlocks m := by
  have hencValid : (encodeBlockCoord m).Valid :=
    encodeBlockCoord_valid hm
  have hnormOdd : Odd (normalizeOddState m) :=
    normalizeOddState_odd hm
  constructor
  · intro hnormBlocks
    have hnormCoords :
        ReachesOneByCoords
          (encodeBlockCoord (normalizeOddState m)) :=
      (reachesOne_coords_iff_blocks hnormOdd).2
        hnormBlocks
    rw [encode_normalizeOddState hm] at hnormCoords
    have hcoords :
        ReachesOneByCoords (encodeBlockCoord m) :=
      (reachesOne_normalize_iff
        (encodeBlockCoord m) hencValid).1 hnormCoords
    exact
      (reachesOne_coords_iff_blocks hm).1 hcoords
  · intro hblocks
    have hcoords :
        ReachesOneByCoords (encodeBlockCoord m) :=
      (reachesOne_coords_iff_blocks hm).2 hblocks
    have hnormCoords :
        ReachesOneByCoords
          (normalizeCoord (encodeBlockCoord m)) :=
      (reachesOne_normalize_iff
        (encodeBlockCoord m) hencValid).2 hcoords
    have hencodedNorm :
        ReachesOneByCoords
          (encodeBlockCoord (normalizeOddState m)) := by
      rw [encode_normalizeOddState hm]
      exact hnormCoords
    exact
      (reachesOne_coords_iff_blocks hnormOdd).1
        hencodedNorm




theorem failing_odd_state_reduces_if_three_dvd
    {m : ℕ}
    (hfail : FailsToReachOneByBlocks m)
    (h3 : 3 ∣ blockQuotient m) :
    FailsToReachOneByBlocks (normalizeOddState m)
    ∧
    normalizeOddState m < m := by
  constructor
  · exact
      ⟨normalizeOddState_odd hfail.1,
       fun hreach =>
         hfail.2
           ((reachesOne_normalizeOddState_iff
             hfail.1).1 hreach)⟩
  · exact
      (normalizeOddState_lt_iff hfail.1).2 h3




theorem minimal_block_counterexample_three_free
    {m : ℕ}
    (hmin : IsMinimalBlockCounterexample m) :
    ¬ 3 ∣ blockQuotient m := by
  intro h3
  have hreduced :=
    failing_odd_state_reduces_if_three_dvd
      hmin.1 h3
  have hreach :
      ReachesOneByBlocks (normalizeOddState m) :=
    hmin.2
      (normalizeOddState m)
      hreduced.1.1
      hreduced.2
  exact hreduced.1.2 hreach




theorem minimal_block_counterexample_quotient_two_three_free
    {m : ℕ}
    (hmin : IsMinimalBlockCounterexample m) :
    Odd (blockQuotient m) ∧
    ¬ 3 ∣ blockQuotient m := by
  exact
    ⟨blockQuotient_odd hmin.1.1,
     minimal_block_counterexample_three_free hmin⟩




/-! Regression tests for the total normalization map. -/




example : normalizeOddState 11 = 7 := by
  native_decide




example : normalizeOddState 29 = 19 := by
  native_decide




example : normalizeOddState 89 = 39 := by
  native_decide




example : normalizeOddState 7 = 7 := by
  native_decide




example : normalizeOddState 39 = 39 := by
  native_decide




example : 3 ∣ blockQuotient 11 := by
  native_decide




example : ¬ 3 ∣ blockQuotient 7 := by
  native_decide




theorem normalized_reduction_spec :
    AllValidCoordsReachOne ↔
      AllNormalizedCoordsReachOne := by
  exact normalized_global_reachability_iff




theorem minimal_counterexample_restriction
    {m : ℕ}
    (hmin : IsMinimalBlockCounterexample m) :
    Odd m ∧
    ¬ ReachesOneByBlocks m ∧
    ¬ 3 ∣ blockQuotient m := by
  exact
    ⟨hmin.1.1,
     hmin.1.2,
     minimal_block_counterexample_three_free hmin⟩








theorem minimal_block_counterexample_quotient_coprime_six
    {m : ℕ}
    (hmin : IsMinimalBlockCounterexample m) :
    Nat.Coprime (blockQuotient m) 6 := by
  have hcoprimeTwo :
      Nat.Coprime (blockQuotient m) 2 :=
    Nat.coprime_two_right.2
      (blockQuotient_odd hmin.1.1)
  have hcoprimeThree :
      Nat.Coprime (blockQuotient m) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd
      Nat.prime_three).2
      (minimal_block_counterexample_three_free hmin)).symm
  simpa using hcoprimeTwo.mul_right hcoprimeThree








/-!
## Cuatro clases modulares de coordenadas normalizadas




Aquí tres-libre para una coordenada significa que 3 no divide c.q.
No debe confundirse con que 3 no divida decodeBlockCoord c: por ejemplo,
la coordenada (2, 1) está normalizada y decodifica al valor 3.
-/




theorem normalized_q_mod_six_cases
    {c : BlockCoord}
    (hc : c.Normalized) :
    c.q % 6 = 1 ∨ c.q % 6 = 5 := by
  rcases hc.1.2 with ⟨k, hk⟩
  have hnotThreeMod : c.q % 3 ≠ 0 := by
    intro hzero
    exact hc.2 (Nat.dvd_of_mod_eq_zero hzero)
  omega




theorem r_mod_two_cases
    (r : ℕ) :
    r % 2 = 0 ∨ r % 2 = 1 := by
  omega




theorem normalized_four_rq_cases
    {c : BlockCoord}
    (hc : c.Normalized) :
    (c.r % 2 = 1 ∧ c.q % 6 = 1) ∨
    (c.r % 2 = 1 ∧ c.q % 6 = 5) ∨
    (c.r % 2 = 0 ∧ c.q % 6 = 1) ∨
    (c.r % 2 = 0 ∧ c.q % 6 = 5) := by
  rcases r_mod_two_cases c.r with hr | hr
  · rcases normalized_q_mod_six_cases hc with hq | hq
    · exact Or.inr (Or.inr (Or.inl ⟨hr, hq⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hr, hq⟩))
  · rcases normalized_q_mod_six_cases hc with hq | hq
    · exact Or.inl ⟨hr, hq⟩
    · exact Or.inr (Or.inl ⟨hr, hq⟩)




theorem two_pow_mod_three_of_even
    {r : ℕ}
    (hr : r % 2 = 0) :
    2 ^ r % 3 = 1 := by
  have hd : 2 ∣ r :=
    Nat.dvd_of_mod_eq_zero hr
  rcases hd with ⟨k, rfl⟩
  have hbase : Nat.ModEq 3 4 1 := by
    norm_num [Nat.ModEq]
  have hp := hbase.pow k
  simpa [Nat.ModEq, pow_mul] using hp




theorem two_pow_mod_three_of_odd
    {r : ℕ}
    (hr : r % 2 = 1) :
    2 ^ r % 3 = 2 := by
  let k := r / 2
  have hdecomp := Nat.mod_add_div r 2
  have hrEq : r = 2 * k + 1 := by
    dsimp [k]
    omega
  have heven :
      2 ^ (2 * k) % 3 = 1 :=
    two_pow_mod_three_of_even (by omega)
  rw [hrEq, pow_add, Nat.mul_mod, heven]
  norm_num




theorem two_pow_mod_two_of_pos
    {r : ℕ}
    (hr : 1 ≤ r) :
    2 ^ r % 2 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 :=
    ⟨r - 1, by omega⟩
  simp [pow_succ]




theorem two_pow_mod_six_of_odd
    {r : ℕ}
    (hrPos : 1 ≤ r)
    (hr : r % 2 = 1) :
    2 ^ r % 6 = 2 := by
  have hmodTwo := two_pow_mod_two_of_pos hrPos
  have hmodThree := two_pow_mod_three_of_odd hr
  omega




theorem two_pow_mod_six_of_even
    {r : ℕ}
    (hrPos : 1 ≤ r)
    (hr : r % 2 = 0) :
    2 ^ r % 6 = 4 := by
  have hmodTwo := two_pow_mod_two_of_pos hrPos
  have hmodThree := two_pow_mod_three_of_even hr
  omega




theorem decode_mod_six_odd_r_q_one
    {c : BlockCoord}
    (hc : c.Valid)
    (hr : c.r % 2 = 1)
    (hq : c.q % 6 = 1) :
    decodeBlockCoord c % 6 = 1 := by
  have hpow :=
    two_pow_mod_six_of_odd hc.1 hr
  have hproduct :
      (2 ^ c.r * c.q) % 6 = 2 := by
    rw [Nat.mul_mod, hpow, hq]
  have hlarge := valid_coord_product_ge_two hc
  unfold decodeBlockCoord
  omega




theorem decode_mod_six_odd_r_q_five
    {c : BlockCoord}
    (hc : c.Valid)
    (hr : c.r % 2 = 1)
    (hq : c.q % 6 = 5) :
    decodeBlockCoord c % 6 = 3 := by
  have hpow :=
    two_pow_mod_six_of_odd hc.1 hr
  have hproduct :
      (2 ^ c.r * c.q) % 6 = 4 := by
    rw [Nat.mul_mod, hpow, hq]
  have hlarge := valid_coord_product_ge_two hc
  unfold decodeBlockCoord
  omega




theorem decode_mod_six_even_r_q_one
    {c : BlockCoord}
    (hc : c.Valid)
    (hr : c.r % 2 = 0)
    (hq : c.q % 6 = 1) :
    decodeBlockCoord c % 6 = 3 := by
  have hpow :=
    two_pow_mod_six_of_even hc.1 hr
  have hproduct :
      (2 ^ c.r * c.q) % 6 = 4 := by
    rw [Nat.mul_mod, hpow, hq]
  have hlarge := valid_coord_product_ge_two hc
  unfold decodeBlockCoord
  omega




theorem decode_mod_six_even_r_q_five
    {c : BlockCoord}
    (hc : c.Valid)
    (hr : c.r % 2 = 0)
    (hq : c.q % 6 = 5) :
    decodeBlockCoord c % 6 = 1 := by
  have hpow :=
    two_pow_mod_six_of_even hc.1 hr
  have hproduct :
      (2 ^ c.r * c.q) % 6 = 2 := by
    rw [Nat.mul_mod, hpow, hq]
  have hlarge := valid_coord_product_ge_two hc
  unfold decodeBlockCoord
  omega




theorem decode_normalized_mod_six_eq_one_iff
    {c : BlockCoord}
    (hc : c.Normalized) :
    decodeBlockCoord c % 6 = 1 ↔
      ((c.r % 2 = 1 ∧ c.q % 6 = 1) ∨
       (c.r % 2 = 0 ∧ c.q % 6 = 5)) := by
  constructor
  · intro hdecode
    rcases normalized_four_rq_cases hc with
        h11 | h15 | h01 | h05
    · exact Or.inl h11
    · have hthree :=
        decode_mod_six_odd_r_q_five
          hc.1 h15.1 h15.2
      omega
    · have hthree :=
        decode_mod_six_even_r_q_one
          hc.1 h01.1 h01.2
      omega
    · exact Or.inr h05
  · rintro (h11 | h05)
    · exact
        decode_mod_six_odd_r_q_one
          hc.1 h11.1 h11.2
    · exact
        decode_mod_six_even_r_q_five
          hc.1 h05.1 h05.2




theorem decode_normalized_mod_six_eq_three_iff
    {c : BlockCoord}
    (hc : c.Normalized) :
    decodeBlockCoord c % 6 = 3 ↔
      ((c.r % 2 = 1 ∧ c.q % 6 = 5) ∨
       (c.r % 2 = 0 ∧ c.q % 6 = 1)) := by
  constructor
  · intro hdecode
    rcases normalized_four_rq_cases hc with
        h11 | h15 | h01 | h05
    · have hone :=
        decode_mod_six_odd_r_q_one
          hc.1 h11.1 h11.2
      omega
    · exact Or.inl h15
    · exact Or.inr h01
    · have hone :=
        decode_mod_six_even_r_q_five
          hc.1 h05.1 h05.2
      omega
  · rintro (h15 | h01)
    · exact
        decode_mod_six_odd_r_q_five
          hc.1 h15.1 h15.2
    · exact
        decode_mod_six_even_r_q_one
          hc.1 h01.1 h01.2








/-!
## Ley módulo 6 del siguiente estado impar
-/




theorem coordNumerator_mod_three
    {c : BlockCoord}
    (hc : c.Valid) :
    coordNumerator c % 3 = 2 := by
  have hrPos : 1 ≤ c.r := hc.1
  obtain ⟨k, hk⟩ : ∃ k, c.r = k + 1 :=
    ⟨c.r - 1, by omega⟩
  have hpow : 3 ^ c.r % 3 = 0 := by
    rw [hk, pow_succ, Nat.mul_mod]
    simp
  have hproduct :
      (3 ^ c.r * c.q) % 3 = 0 := by
    rw [Nat.mul_mod, hpow]
    simp
  have hpositive := coordNumerator_pos hc
  unfold coordNumerator at hpositive ⊢
  omega




theorem coordNextValue_mod_three_of_closing_odd
    {c : BlockCoord}
    (hc : c.Valid)
    (ha : coordClosingValuation c % 2 = 1) :
    coordNextValue c % 3 = 1 := by
  have hnumerator := coordNumerator_mod_three hc
  have hfactor := coordNumerator_factorization hc
  have hpow :=
    two_pow_mod_three_of_odd ha
  have hproduct :
      (2 ^ coordClosingValuation c *
          coordNextValue c) % 3 = 2 := by
    rw [← hfactor]
    exact hnumerator
  rw [Nat.mul_mod, hpow] at hproduct
  omega




theorem coordNextValue_mod_three_of_closing_even
    {c : BlockCoord}
    (hc : c.Valid)
    (ha : coordClosingValuation c % 2 = 0) :
    coordNextValue c % 3 = 2 := by
  have hnumerator := coordNumerator_mod_three hc
  have hfactor := coordNumerator_factorization hc
  have hpow :=
    two_pow_mod_three_of_even ha
  have hproduct :
      (2 ^ coordClosingValuation c *
          coordNextValue c) % 3 = 2 := by
    rw [← hfactor]
    exact hnumerator
  rw [Nat.mul_mod, hpow] at hproduct
  omega




theorem coordNextValue_mod_six_of_closing_odd
    {c : BlockCoord}
    (hc : c.Valid)
    (ha : coordClosingValuation c % 2 = 1) :
    coordNextValue c % 6 = 1 := by
  rcases coordNextValue_odd hc with ⟨k, hk⟩
  have hmodThree :=
    coordNextValue_mod_three_of_closing_odd hc ha
  omega




theorem coordNextValue_mod_six_of_closing_even
    {c : BlockCoord}
    (hc : c.Valid)
    (ha : coordClosingValuation c % 2 = 0) :
    coordNextValue c % 6 = 5 := by
  rcases coordNextValue_odd hc with ⟨k, hk⟩
  have hmodThree :=
    coordNextValue_mod_three_of_closing_even hc ha
  omega




theorem coordNextValue_coprime_six
    {c : BlockCoord}
    (hc : c.Valid) :
    Nat.Coprime (coordNextValue c) 6 := by
  have hodd : Odd (coordNextValue c) :=
    coordNextValue_odd hc
  have hcoprimeTwo :
      Nat.Coprime (coordNextValue c) 2 :=
    Nat.coprime_two_right.2 hodd
  have hmodCases :
      coordNextValue c % 3 = 1 ∨
      coordNextValue c % 3 = 2 := by
    rcases r_mod_two_cases
        (coordClosingValuation c) with ha | ha
    · exact Or.inr
        (coordNextValue_mod_three_of_closing_even hc ha)
    · exact Or.inl
        (coordNextValue_mod_three_of_closing_odd hc ha)
  have hnotThree : ¬ 3 ∣ coordNextValue c := by
    intro hdiv
    have hzero := Nat.mod_eq_zero_of_dvd hdiv
    omega
  have hcoprimeThree :
      Nat.Coprime (coordNextValue c) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd
      Nat.prime_three).2 hnotThree).symm
  simpa using hcoprimeTwo.mul_right hcoprimeThree




theorem blockNext_coprime_six
    {m : ℕ}
    (hm : Odd m) :
    Nat.Coprime (blockNext m) 6 := by
  have hc : (encodeBlockCoord m).Valid :=
    encodeBlockCoord_valid hm
  have hcoprime :=
    coordNextValue_coprime_six hc
  rw [coordNextValue_eq_blockNext_decode hc,
      decode_encodeBlockCoord hm] at hcoprime
  exact hcoprime








/-!
## Información modular conservada por la coordenada siguiente
-/




theorem three_not_dvd_two_pow
    (r : ℕ) :
    ¬ 3 ∣ 2 ^ r := by
  intro hdiv
  have hzero := Nat.mod_eq_zero_of_dvd hdiv
  rcases r_mod_two_cases r with hr | hr
  · have hone := two_pow_mod_three_of_even hr
    omega
  · have htwo := two_pow_mod_three_of_odd hr
    omega




theorem three_dvd_nextCoord_q_iff_closing_even
    {c : BlockCoord}
    (hc : c.Valid) :
    (3 ∣ (nextCoord c).q) ↔
      coordClosingValuation c % 2 = 0 := by
  constructor
  · intro hq
    have hfactor :=
      coordNextValue_add_one_factorization hc
    have hsumDiv :
        3 ∣ coordNextValue c + 1 := by
      rcases hq with ⟨k, hk⟩
      refine ⟨2 ^ (nextCoord c).r * k, ?_⟩
      rw [hfactor, hk]
      ring
    rcases r_mod_two_cases
        (coordClosingValuation c) with ha | ha
    · exact ha
    · have hsmod :=
        coordNextValue_mod_six_of_closing_odd hc ha
      have hsumZero :=
        Nat.mod_eq_zero_of_dvd hsumDiv
      omega
  · intro ha
    have hsmod :=
      coordNextValue_mod_six_of_closing_even hc ha
    have hsumMod :
        (coordNextValue c + 1) % 3 = 0 := by
      omega
    have hsumDiv :
        3 ∣ coordNextValue c + 1 :=
      Nat.dvd_of_mod_eq_zero hsumMod
    have hfactor :=
      coordNextValue_add_one_factorization hc
    have hproductDiv :
        3 ∣
          2 ^ (nextCoord c).r *
            (nextCoord c).q := by
      rw [← hfactor]
      exact hsumDiv
    have hcases :=
      (Nat.Prime.dvd_mul Nat.prime_three).1
        hproductDiv
    exact hcases.resolve_left
      (three_not_dvd_two_pow (nextCoord c).r)




theorem nextCoord_normalized_iff_closing_odd
    {c : BlockCoord}
    (hc : c.Valid) :
    (nextCoord c).Normalized ↔
      coordClosingValuation c % 2 = 1 := by
  constructor
  · intro hnorm
    rcases r_mod_two_cases
        (coordClosingValuation c) with ha | ha
    · exact False.elim
        (hnorm.2
          ((three_dvd_nextCoord_q_iff_closing_even hc).2 ha))
    · exact ha
  · intro ha
    refine ⟨nextCoord_valid hc, ?_⟩
    intro hdiv
    have heven :=
      (three_dvd_nextCoord_q_iff_closing_even hc).1
        hdiv
    omega




theorem nextCoord_q_mod_six_of_closing_even
    {c : BlockCoord}
    (hc : c.Valid)
    (ha : coordClosingValuation c % 2 = 0) :
    (nextCoord c).q % 6 = 3 := by
  have hodd : Odd (nextCoord c).q :=
    (nextCoord_valid hc).2
  have hdiv : 3 ∣ (nextCoord c).q :=
    (three_dvd_nextCoord_q_iff_closing_even hc).2 ha
  rcases hodd with ⟨k, hk⟩
  rcases hdiv with ⟨j, hj⟩
  omega




theorem nextCoord_q_mod_six_of_closing_odd_next_r_odd
    {c : BlockCoord}
    (hc : c.Valid)
    (ha : coordClosingValuation c % 2 = 1)
    (hr' : (nextCoord c).r % 2 = 1) :
    (nextCoord c).q % 6 = 1 := by
  have hnorm :
      (nextCoord c).Normalized :=
    (nextCoord_normalized_iff_closing_odd hc).2 ha
  have hqCases :=
    normalized_q_mod_six_cases hnorm
  have hsmod :=
    coordNextValue_mod_six_of_closing_odd hc ha
  have hsumMod :
      (coordNextValue c + 1) % 6 = 2 := by
    omega
  have hfactor :=
    coordNextValue_add_one_factorization hc
  have hproductMod :
      (2 ^ (nextCoord c).r *
          (nextCoord c).q) % 6 = 2 := by
    rw [← hfactor]
    exact hsumMod
  have hpow :=
    two_pow_mod_six_of_odd
      (nextCoord_valid hc).1 hr'
  rcases hqCases with hq | hq
  · exact hq
  · have hcontr :
        (2 ^ (nextCoord c).r *
            (nextCoord c).q) % 6 = 4 := by
      rw [Nat.mul_mod, hpow, hq]
    omega




theorem nextCoord_q_mod_six_of_closing_odd_next_r_even
    {c : BlockCoord}
    (hc : c.Valid)
    (ha : coordClosingValuation c % 2 = 1)
    (hr' : (nextCoord c).r % 2 = 0) :
    (nextCoord c).q % 6 = 5 := by
  have hnorm :
      (nextCoord c).Normalized :=
    (nextCoord_normalized_iff_closing_odd hc).2 ha
  have hqCases :=
    normalized_q_mod_six_cases hnorm
  have hsmod :=
    coordNextValue_mod_six_of_closing_odd hc ha
  have hsumMod :
      (coordNextValue c + 1) % 6 = 2 := by
    omega
  have hfactor :=
    coordNextValue_add_one_factorization hc
  have hproductMod :
      (2 ^ (nextCoord c).r *
          (nextCoord c).q) % 6 = 2 := by
    rw [← hfactor]
    exact hsumMod
  have hpow :=
    two_pow_mod_six_of_even
      (nextCoord_valid hc).1 hr'
  rcases hqCases with hq | hq
  · have hcontr :
        (2 ^ (nextCoord c).r *
            (nextCoord c).q) % 6 = 4 := by
      rw [Nat.mul_mod, hpow, hq]
    omega
  · exact hq




theorem next_block_mod_six_spec
    {c : BlockCoord}
    (hc : c.Valid) :
    (coordClosingValuation c % 2 = 0 →
      coordNextValue c % 6 = 5 ∧
      (nextCoord c).q % 6 = 3)
    ∧
    (coordClosingValuation c % 2 = 1 →
      coordNextValue c % 6 = 1 ∧
      (nextCoord c).Normalized) := by
  constructor
  · intro ha
    exact
      ⟨coordNextValue_mod_six_of_closing_even hc ha,
       nextCoord_q_mod_six_of_closing_even hc ha⟩
  · intro ha
    exact
      ⟨coordNextValue_mod_six_of_closing_odd hc ha,
       (nextCoord_normalized_iff_closing_odd hc).2 ha⟩








/-!
Las cuatro clases dadas por (r mod 2, q mod 6) determinan
decodeBlockCoord c mod 6, pero no determinan la paridad de
coordClosingValuation c. Información adicional a módulo 2
es necesaria para determinar la clase módulo 6 del siguiente impar.
-/




def AllCoprimeSixOddReachOneByBlocks : Prop :=
  ∀ m : ℕ,
    Odd m →
    Nat.Coprime m 6 →
    ReachesOneByBlocks m




theorem all_odd_blocks_iff_all_coprime_six_blocks :
    AllOddReachOneByBlocks ↔
      AllCoprimeSixOddReachOneByBlocks := by
  constructor
  · intro hall m hm _
    exact hall m hm
  · intro hrestricted m hm
    have hnextOdd : Odd (blockNext m) :=
      blockNext_odd hm
    have hnextCoprime :
        Nat.Coprime (blockNext m) 6 :=
      blockNext_coprime_six hm
    rcases hrestricted
        (blockNext m) hnextOdd hnextCoprime with
      ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    simpa [Function.iterate_succ_apply] using hn




/-! Regresiones: cada clase admite ambas paridades del cierre. -/




example :
    let c : BlockCoord := { r := 1, q := 1 }
    c.Normalized ∧
    c.r % 2 = 1 ∧
    c.q % 6 = 1 ∧
    coordClosingValuation c = 1 ∧
    coordNextValue c % 6 = 1 := by
  dsimp
  constructor
  · norm_num [BlockCoord.Normalized, BlockCoord.Valid, Odd]
  · native_decide




example :
    let c : BlockCoord := { r := 1, q := 7 }
    c.Normalized ∧
    c.r % 2 = 1 ∧
    c.q % 6 = 1 ∧
    coordClosingValuation c = 2 ∧
    coordNextValue c % 6 = 5 := by
  dsimp
  constructor
  · norm_num [BlockCoord.Normalized, BlockCoord.Valid, Odd]
  · native_decide




example :
    let c : BlockCoord := { r := 1, q := 5 }
    c.Normalized ∧
    c.r % 2 = 1 ∧
    c.q % 6 = 5 ∧
    coordClosingValuation c = 1 ∧
    coordNextValue c % 6 = 1 := by
  dsimp
  constructor
  · norm_num [BlockCoord.Normalized, BlockCoord.Valid, Odd]
    refine ⟨2, by norm_num⟩
  · native_decide




example :
    let c : BlockCoord := { r := 1, q := 23 }
    c.Normalized ∧
    c.r % 2 = 1 ∧
    c.q % 6 = 5 ∧
    coordClosingValuation c = 2 ∧
    coordNextValue c % 6 = 5 := by
  dsimp
  constructor
  · norm_num [BlockCoord.Normalized, BlockCoord.Valid, Odd]
    refine ⟨11, by norm_num⟩
  · native_decide




example :
    let c : BlockCoord := { r := 2, q := 1 }
    c.Normalized ∧
    c.r % 2 = 0 ∧
    c.q % 6 = 1 ∧
    coordClosingValuation c = 3 ∧
    coordNextValue c % 6 = 1 := by
  dsimp
  constructor
  · norm_num [BlockCoord.Normalized, BlockCoord.Valid, Odd]
  · native_decide




example :
    let c : BlockCoord := { r := 2, q := 13 }
    c.Normalized ∧
    c.r % 2 = 0 ∧
    c.q % 6 = 1 ∧
    coordClosingValuation c = 2 ∧
    coordNextValue c % 6 = 5 := by
  dsimp
  constructor
  · norm_num [BlockCoord.Normalized, BlockCoord.Valid, Odd]
  · native_decide




example :
    let c : BlockCoord := { r := 2, q := 11 }
    c.Normalized ∧
    c.r % 2 = 0 ∧
    c.q % 6 = 5 ∧
    coordClosingValuation c = 1 ∧
    coordNextValue c % 6 = 1 := by
  dsimp
  constructor
  · norm_num [BlockCoord.Normalized, BlockCoord.Valid, Odd]
  · native_decide




example :
    let c : BlockCoord := { r := 2, q := 5 }
    c.Normalized ∧
    c.r % 2 = 0 ∧
    c.q % 6 = 5 ∧
    coordClosingValuation c = 2 ∧
    coordNextValue c % 6 = 5 := by
  dsimp
  constructor
  · norm_num [BlockCoord.Normalized, BlockCoord.Valid, Odd]
  · native_decide








/-!
## Transición normalizada




La función G toma el sucesor bruto y elige su representante
normalizado canónico. No expande la definición de la valuación
tres-ádica ni la fórmula interna de nextCoord.
-/




def normalizedNextCoord (c : BlockCoord) : BlockCoord :=
  normalizeCoord (nextCoord c)




theorem normalizedNextCoord_normalized
    {c : BlockCoord}
    (hc : c.Valid) :
    (normalizedNextCoord c).Normalized := by
  exact normalizeCoord_normalized (nextCoord_valid hc)




theorem normalizedNextCoord_valid
    {c : BlockCoord}
    (hc : c.Valid) :
    (normalizedNextCoord c).Valid := by
  exact (normalizedNextCoord_normalized hc).1




theorem nextCoord_normalizedNextCoord
    {c : BlockCoord}
    (hc : c.Valid) :
    nextCoord (normalizedNextCoord c) =
      nextCoord (nextCoord c) := by
  exact nextCoord_normalize (nextCoord_valid hc)




def nextNormalizationExponent (c : BlockCoord) : ℕ :=
  v3 (nextCoord c).q




theorem normalizedNextCoord_r
    (c : BlockCoord) :
    (normalizedNextCoord c).r =
      (nextCoord c).r + nextNormalizationExponent c := by
  rfl




theorem normalizedNextCoord_q
    (c : BlockCoord) :
    (normalizedNextCoord c).q =
      threeFreePart (nextCoord c).q := by
  rfl




theorem nextNormalizationExponent_pos_iff_closing_even
    {c : BlockCoord}
    (hc : c.Valid) :
    0 < nextNormalizationExponent c ↔
      coordClosingValuation c % 2 = 0 := by
  have hqNe :
      (nextCoord c).q ≠ 0 :=
    Nat.ne_of_gt
      (valid_coord_q_pos (nextCoord_valid hc))
  unfold nextNormalizationExponent
  rw [v3_pos_iff_three_dvd hqNe]
  exact three_dvd_nextCoord_q_iff_closing_even hc




theorem nextNormalizationExponent_eq_zero_iff_closing_odd
    {c : BlockCoord}
    (hc : c.Valid) :
    nextNormalizationExponent c = 0 ↔
      coordClosingValuation c % 2 = 1 := by
  constructor
  · intro hk
    rcases r_mod_two_cases
        (coordClosingValuation c) with ha | ha
    · have hpos :=
        (nextNormalizationExponent_pos_iff_closing_even hc).2 ha
      omega
    · exact ha
  · intro ha
    by_contra hk
    have hpos : 0 < nextNormalizationExponent c :=
      Nat.pos_of_ne_zero hk
    have heven :=
      (nextNormalizationExponent_pos_iff_closing_even hc).1
        hpos
    omega




theorem normalizedNextCoord_eq_nextCoord_of_closing_odd
    {c : BlockCoord}
    (hc : c.Valid)
    (ha : coordClosingValuation c % 2 = 1) :
    normalizedNextCoord c = nextCoord c := by
  have hnorm :
      (nextCoord c).Normalized :=
    (nextCoord_normalized_iff_closing_odd hc).2 ha
  unfold normalizedNextCoord
  exact
    (normalizeCoord_eq_self_iff
      (nextCoord_valid hc)).2 hnorm.2




theorem normalizedNextCoord_eq_nextCoord_iff
    {c : BlockCoord}
    (hc : c.Valid) :
    normalizedNextCoord c = nextCoord c ↔
      coordClosingValuation c % 2 = 1 := by
  constructor
  · intro hself
    have hthreeFree :
        ¬ 3 ∣ (nextCoord c).q :=
      (normalizeCoord_eq_self_iff
        (nextCoord_valid hc)).1 hself
    exact
      (nextCoord_normalized_iff_closing_odd hc).1
        ⟨nextCoord_valid hc, hthreeFree⟩
  · exact normalizedNextCoord_eq_nextCoord_of_closing_odd hc




theorem normalizedNextCoord_decode_lt_raw_of_closing_even
    {c : BlockCoord}
    (hc : c.Valid)
    (ha : coordClosingValuation c % 2 = 0) :
    decodeBlockCoord (normalizedNextCoord c) <
      coordNextValue c := by
  have hthree :
      3 ∣ (nextCoord c).q :=
    (three_dvd_nextCoord_q_iff_closing_even hc).2 ha
  have hlt :=
    decode_normalize_lt_of_three_dvd
      (nextCoord_valid hc) hthree
  rw [(nextCoord_spec hc).2.1] at hlt
  exact hlt




theorem normalizedNextCoord_decode_lt_raw_iff
    {c : BlockCoord}
    (hc : c.Valid) :
    decodeBlockCoord (normalizedNextCoord c) <
        coordNextValue c
      ↔
    coordClosingValuation c % 2 = 0 := by
  unfold normalizedNextCoord
  rw [← (nextCoord_spec hc).2.1]
  exact
    (decode_normalize_lt_iff (nextCoord_valid hc)).trans
      (three_dvd_nextCoord_q_iff_closing_even hc)




theorem normalizedNextCoord_add_one_exact_raw
    {c : BlockCoord}
    (hc : c.Valid) :
    3 ^ nextNormalizationExponent c *
        (decodeBlockCoord (normalizedNextCoord c) + 1)
      =
    2 ^ nextNormalizationExponent c *
        (decodeBlockCoord (nextCoord c) + 1) := by
  have hd : (nextCoord c).Valid :=
    nextCoord_valid hc
  have hnorm := decodeNormalize_add_one hd
  have hraw := decodeCoord_add_one_factorized hd
  unfold normalizedNextCoord nextNormalizationExponent
  rw [hnorm, hraw, pow_add]
  ac_rfl




theorem normalizedNextCoord_add_one_exact
    {c : BlockCoord}
    (hc : c.Valid) :
    3 ^ nextNormalizationExponent c *
        (decodeBlockCoord (normalizedNextCoord c) + 1)
      =
    2 ^ nextNormalizationExponent c *
        (coordNextValue c + 1) := by
  rw [← (nextCoord_spec hc).2.1]
  exact normalizedNextCoord_add_one_exact_raw hc




/-!
La cota siguiente compara el representante normalizado con el
sucesor bruto coordNextValue c, no con decodeBlockCoord c.
-/




theorem normalizedNextCoord_two_thirds_bound_of_closing_even
    {c : BlockCoord}
    (hc : c.Valid)
    (ha : coordClosingValuation c % 2 = 0) :
    3 * (decodeBlockCoord (normalizedNextCoord c) + 1) ≤
      2 * (coordNextValue c + 1) := by
  have hd : (nextCoord c).Valid :=
    nextCoord_valid hc
  have hnorm := decodeNormalize_add_one hd
  have hraw := decodeCoord_add_one_factorized hd
  have hkPos :
      0 < nextNormalizationExponent c :=
    (nextNormalizationExponent_pos_iff_closing_even hc).2 ha
  obtain ⟨j, hj⟩ :
      ∃ j, nextNormalizationExponent c = j + 1 :=
    ⟨nextNormalizationExponent c - 1, by omega⟩
  have hpow := two_pow_le_three_pow j
  have hmul :=
    Nat.mul_le_mul_left
      (6 * 2 ^ (nextCoord c).r *
        threeFreePart (nextCoord c).q) hpow
  rw [← (nextCoord_spec hc).2.1]
  unfold normalizedNextCoord nextNormalizationExponent at *
  rw [hnorm, hraw, hj]
  simp only [pow_add, pow_succ]
  convert hmul using 1 <;> ring




theorem normalizedNextCoord_exact_two_thirds_of_k_eq_one
    {c : BlockCoord}
    (hc : c.Valid)
    (hk : nextNormalizationExponent c = 1) :
    3 * (decodeBlockCoord (normalizedNextCoord c) + 1) =
      2 * (coordNextValue c + 1) := by
  simpa [hk] using normalizedNextCoord_add_one_exact hc




theorem normalizedNextCoord_spec
    {c : BlockCoord}
    (hc : c.Valid) :
    (normalizedNextCoord c).Normalized
    ∧
    nextCoord (normalizedNextCoord c) =
        nextCoord (nextCoord c)
    ∧
    (0 < nextNormalizationExponent c ↔
      coordClosingValuation c % 2 = 0) := by
  exact
    ⟨normalizedNextCoord_normalized hc,
     nextCoord_normalizedNextCoord hc,
     nextNormalizationExponent_pos_iff_closing_even hc⟩








/-!
## Órbita reducida inducida por G
-/




def reducedCoordOrbit
    (c : BlockCoord) (n : ℕ) : BlockCoord :=
  normalizedNextCoord^[n] c




@[simp]
theorem reducedCoordOrbit_zero (c : BlockCoord) :
    reducedCoordOrbit c 0 = c := by
  rfl




theorem reducedCoordOrbit_succ
    (c : BlockCoord) (n : ℕ) :
    reducedCoordOrbit c (n + 1) =
      normalizedNextCoord (reducedCoordOrbit c n) := by
  exact Function.iterate_succ_apply'
    normalizedNextCoord n c




theorem reducedCoordOrbit_valid
    {c : BlockCoord}
    (hc : c.Valid)
    (n : ℕ) :
    (reducedCoordOrbit c n).Valid := by
  induction n with
  | zero =>
      exact hc
  | succ n ih =>
      rw [reducedCoordOrbit_succ]
      exact normalizedNextCoord_valid ih




theorem reducedCoordOrbit_normalized_after_one
    {c : BlockCoord}
    (hc : c.Valid)
    (n : ℕ) :
    (reducedCoordOrbit c (n + 1)).Normalized := by
  rw [reducedCoordOrbit_succ]
  exact
    normalizedNextCoord_normalized
      (reducedCoordOrbit_valid hc n)




theorem reducedCoordOrbit_normalized
    {c : BlockCoord}
    (hc : c.Normalized)
    (n : ℕ) :
    (reducedCoordOrbit c n).Normalized := by
  cases n with
  | zero =>
      simpa using hc
  | succ n =>
      exact reducedCoordOrbit_normalized_after_one hc.1 n




theorem reducedCoordOrbit_eq_normalize_coordOrbit_after_one
    {c : BlockCoord}
    (hc : c.Valid)
    (n : ℕ) :
    reducedCoordOrbit c (n + 1) =
      normalizeCoord (coordOrbit c (n + 1)) := by
  induction n with
  | zero =>
      simp [reducedCoordOrbit_succ,
        normalizedNextCoord, coordOrbit_succ]
  | succ n ih =>
      calc
        reducedCoordOrbit c ((n + 1) + 1) =
            normalizedNextCoord
              (reducedCoordOrbit c (n + 1)) :=
          reducedCoordOrbit_succ _ (n + 1)
        _ = normalizeCoord
              (nextCoord
                (normalizeCoord
                  (coordOrbit c (n + 1)))) := by
          rw [ih]
          rfl
        _ = normalizeCoord
              (nextCoord (coordOrbit c (n + 1))) := by
          rw [nextCoord_normalize
            (coordOrbit_valid hc (n + 1))]
        _ = normalizeCoord
              (coordOrbit c ((n + 1) + 1)) :=
          congrArg normalizeCoord
            (coordOrbit_succ c (n + 1)).symm




theorem reducedCoordOrbit_eq_normalize_coordOrbit
    {c : BlockCoord}
    (hc : c.Normalized)
    (n : ℕ) :
    reducedCoordOrbit c n =
      normalizeCoord (coordOrbit c n) := by
  cases n with
  | zero =>
      have hself :
          normalizeCoord c = c :=
        (normalized_iff_normalize_eq_self hc.1).1 hc
      simpa using hself.symm
  | succ n =>
      exact
        reducedCoordOrbit_eq_normalize_coordOrbit_after_one
          hc.1 n




theorem nextCoord_reducedCoordOrbit
    {c : BlockCoord}
    (hc : c.Valid)
    (n : ℕ) :
    nextCoord (reducedCoordOrbit c n) =
      coordOrbit c (n + 1) := by
  cases n with
  | zero =>
      simp [coordOrbit_succ]
  | succ n =>
      calc
        nextCoord (reducedCoordOrbit c (n + 1)) =
            nextCoord
              (normalizeCoord
                (coordOrbit c (n + 1))) := by
          rw [reducedCoordOrbit_eq_normalize_coordOrbit_after_one
            hc n]
        _ = nextCoord (coordOrbit c (n + 1)) :=
          nextCoord_normalize
            (coordOrbit_valid hc (n + 1))
        _ = coordOrbit c ((n + 1) + 1) :=
          (coordOrbit_succ _ (n + 1)).symm




def ReachesOneByReducedCoords (c : BlockCoord) : Prop :=
  ∃ n : ℕ, reducedCoordOrbit c n = oneCoord




theorem reachesOne_reduced_iff_coords
    {c : BlockCoord}
    (hc : c.Normalized) :
    ReachesOneByReducedCoords c ↔
      ReachesOneByCoords c := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    have hnext := congrArg nextCoord hn
    rw [nextCoord_reducedCoordOrbit hc.1 n,
        nextCoord_one] at hnext
    exact hnext
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [reducedCoordOrbit_eq_normalize_coordOrbit hc n,
        hn, normalizeCoord_one]




def AllNormalizedReachOneByReducedCoords : Prop :=
  ∀ c : BlockCoord,
    c.Normalized →
    ReachesOneByReducedCoords c




theorem all_normalized_reduced_iff_original :
    AllNormalizedReachOneByReducedCoords ↔
      AllNormalizedCoordsReachOne := by
  constructor
  · intro hreduce c hc
    exact (reachesOne_reduced_iff_coords hc).1
      (hreduce c hc)
  · intro horiginal c hc
    exact (reachesOne_reduced_iff_coords hc).2
      (horiginal c hc)




theorem all_odd_blocks_iff_reduced_normalized :
    AllOddReachOneByBlocks ↔
      AllNormalizedReachOneByReducedCoords := by
  constructor
  · intro hblocks
    exact
      all_normalized_reduced_iff_original.2
        (all_odd_blocks_iff_all_normalized_coords.1
          hblocks)
  · intro hreduced
    exact
      all_odd_blocks_iff_all_normalized_coords.2
        (all_normalized_reduced_iff_original.1
          hreduced)




theorem normalizedNextCoord_one :
    normalizedNextCoord oneCoord = oneCoord := by
  unfold normalizedNextCoord
  rw [nextCoord_one, normalizeCoord_one]




theorem reducedCoordOrbit_one
    (n : ℕ) :
    reducedCoordOrbit oneCoord n = oneCoord := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [reducedCoordOrbit_succ, ih,
          normalizedNextCoord_one]








/-!
normalizedNextCoord c no es, en general, el sucesor real blockNext
del natural decodificado. Es el representante normalizado canónico
del sucesor real. Puede ser estrictamente menor que ese sucesor,
pero comparte con él el mismo futuro desde el bloque siguiente.




Por tanto, decodeBlockCoord (normalizedNextCoord c) y
coordNextValue c sólo coinciden necesariamente en el caso de cierre
impar. La contracción demostrada compara G(c) con el sucesor bruto,
no afirma descenso universal respecto del estado inicial.
-/




/-! Cierre impar: no hay renormalización. -/




example :
    let c : BlockCoord := { r := 3, q := 1 }
    coordClosingValuation c = 1 ∧
    nextCoord c = { r := 1, q := 7 } ∧
    normalizedNextCoord c = { r := 1, q := 7 } ∧
    nextNormalizationExponent c = 0 := by
  native_decide




/-! Cierre par y exactamente un factor de tres. -/




example :
    let c : BlockCoord := { r := 4, q := 1 }
    coordClosingValuation c = 4 ∧
    coordNextValue c = 5 ∧
    nextCoord c = { r := 1, q := 3 } ∧
    nextNormalizationExponent c = 1 ∧
    normalizedNextCoord c = { r := 2, q := 1 } ∧
    decodeBlockCoord (normalizedNextCoord c) = 3 ∧
    3 * (3 + 1) = 2 * (5 + 1) := by
  native_decide




/-! Dos factores de tres producen una contracción más fuerte. -/




example :
    let c : BlockCoord := { r := 1, q := 23 }
    coordClosingValuation c = 2 ∧
    coordNextValue c = 17 ∧
    nextCoord c = { r := 1, q := 9 } ∧
    nextNormalizationExponent c = 2 ∧
    normalizedNextCoord c = { r := 3, q := 1 } ∧
    decodeBlockCoord (normalizedNextCoord c) = 7 ∧
    3 ^ 2 * (7 + 1) = 2 ^ 2 * (17 + 1) := by
  native_decide




/-! Tres factores de tres. -/




example :
    let c : BlockCoord := { r := 1, q := 71 }
    nextCoord c = { r := 1, q := 27 } ∧
    nextNormalizationExponent c = 3 ∧
    normalizedNextCoord c = { r := 4, q := 1 } := by
  native_decide








/-!
Comparación exacta del tamaño natural del sucesor normalizado.
-/




theorem normalizedNextCoord_master_size_bridge
    {c : BlockCoord}
    (hc : c.Valid) :
    3 ^ nextNormalizationExponent c *
        2 ^ coordClosingValuation c *
        (decodeBlockCoord (normalizedNextCoord c) + 1)
      =
    2 ^ nextNormalizationExponent c *
        coordBridgeNumerator c := by
  rw [coordBridgeNumerator_eq hc]
  have h := normalizedNextCoord_add_one_exact hc
  calc
    3 ^ nextNormalizationExponent c *
          2 ^ coordClosingValuation c *
          (decodeBlockCoord (normalizedNextCoord c) + 1)
        =
      2 ^ coordClosingValuation c *
        (3 ^ nextNormalizationExponent c *
          (decodeBlockCoord (normalizedNextCoord c) + 1)) := by
            ring
    _ =
      2 ^ coordClosingValuation c *
        (2 ^ nextNormalizationExponent c *
          (coordNextValue c + 1)) := by
            rw [h]
    _ =
      2 ^ nextNormalizationExponent c *
        (2 ^ coordClosingValuation c *
          (coordNextValue c + 1)) := by
            ring




theorem normalizedNextCoord_master_size_expanded
    {c : BlockCoord}
    (hc : c.Valid) :
    3 ^ nextNormalizationExponent c *
        2 ^ coordClosingValuation c *
        (decodeBlockCoord (normalizedNextCoord c) + 1)
      =
    2 ^ nextNormalizationExponent c *
      (3 ^ c.r * c.q - 1 +
        2 ^ coordClosingValuation c) := by
  simpa [coordBridgeNumerator, coordNumerator] using
    normalizedNextCoord_master_size_bridge hc




theorem reduced_size_multiplier_pos (c : BlockCoord) :
    0 <
      3 ^ nextNormalizationExponent c *
        2 ^ coordClosingValuation c := by
  positivity




theorem normalizedNextCoord_descends_iff_bridge
    {c : BlockCoord}
    (hc : c.Valid) :
    decodeBlockCoord (normalizedNextCoord c) <
        decodeBlockCoord c
      ↔
    2 ^ nextNormalizationExponent c *
        coordBridgeNumerator c
      <
    3 ^ nextNormalizationExponent c *
        2 ^ coordClosingValuation c *
        (decodeBlockCoord c + 1) := by
  constructor
  · intro h
    have hAdd :
        decodeBlockCoord (normalizedNextCoord c) + 1 <
          decodeBlockCoord c + 1 := by
      omega
    have hMul :=
      (Nat.mul_lt_mul_left (reduced_size_multiplier_pos c)).2 hAdd
    rw [normalizedNextCoord_master_size_bridge hc] at hMul
    exact hMul
  · intro h
    rw [← normalizedNextCoord_master_size_bridge hc] at h
    have hAdd := Nat.lt_of_mul_lt_mul_left h
    omega








theorem normalizedNextCoord_descends_iff_rakq
    {c : BlockCoord}
    (hc : c.Valid) :
    decodeBlockCoord (normalizedNextCoord c) <
        decodeBlockCoord c
      ↔
    2 ^ nextNormalizationExponent c *
      (3 ^ c.r * c.q - 1 +
        2 ^ coordClosingValuation c)
      <
    3 ^ nextNormalizationExponent c *
      2 ^ (coordClosingValuation c + c.r) *
      c.q := by
  simpa [coordBridgeNumerator, coordNumerator,
    decodeBlockCoord_add_one hc, pow_add,
    mul_assoc, mul_left_comm, mul_comm] using
      normalizedNextCoord_descends_iff_bridge hc




theorem normalizedNextCoord_same_size_iff_bridge
    {c : BlockCoord}
    (hc : c.Valid) :
    decodeBlockCoord (normalizedNextCoord c) =
        decodeBlockCoord c
      ↔
    2 ^ nextNormalizationExponent c *
        coordBridgeNumerator c
      =
    3 ^ nextNormalizationExponent c *
        2 ^ coordClosingValuation c *
        (decodeBlockCoord c + 1) := by
  constructor
  · intro h
    have hAdd :
        decodeBlockCoord (normalizedNextCoord c) + 1 =
          decodeBlockCoord c + 1 := by
      omega
    have hMul := congrArg
      (fun n =>
        (3 ^ nextNormalizationExponent c *
          2 ^ coordClosingValuation c) * n) hAdd
    rw [normalizedNextCoord_master_size_bridge hc] at hMul
    exact hMul
  · intro h
    rw [← normalizedNextCoord_master_size_bridge hc] at h
    have hAdd :=
      Nat.mul_left_cancel (reduced_size_multiplier_pos c) h
    omega




theorem normalizedNextCoord_same_size_iff_rakq
    {c : BlockCoord}
    (hc : c.Valid) :
    decodeBlockCoord (normalizedNextCoord c) =
        decodeBlockCoord c
      ↔
    2 ^ nextNormalizationExponent c *
      (3 ^ c.r * c.q - 1 +
        2 ^ coordClosingValuation c)
      =
    3 ^ nextNormalizationExponent c *
      2 ^ (coordClosingValuation c + c.r) *
      c.q := by
  simpa [coordBridgeNumerator, coordNumerator,
    decodeBlockCoord_add_one hc, pow_add,
    mul_assoc, mul_left_comm, mul_comm] using
      normalizedNextCoord_same_size_iff_bridge hc




theorem normalizedNextCoord_grows_iff_bridge
    {c : BlockCoord}
    (hc : c.Valid) :
    decodeBlockCoord c <
        decodeBlockCoord (normalizedNextCoord c)
      ↔
    3 ^ nextNormalizationExponent c *
        2 ^ coordClosingValuation c *
        (decodeBlockCoord c + 1)
      <
    2 ^ nextNormalizationExponent c *
        coordBridgeNumerator c := by
  constructor
  · intro h
    have hAdd :
        decodeBlockCoord c + 1 <
          decodeBlockCoord (normalizedNextCoord c) + 1 := by
      omega
    have hMul :=
      (Nat.mul_lt_mul_left (reduced_size_multiplier_pos c)).2 hAdd
    rw [normalizedNextCoord_master_size_bridge hc] at hMul
    exact hMul
  · intro h
    rw [← normalizedNextCoord_master_size_bridge hc] at h
    have hAdd := Nat.lt_of_mul_lt_mul_left h
    omega




theorem normalizedNextCoord_grows_iff_rakq
    {c : BlockCoord}
    (hc : c.Valid) :
    decodeBlockCoord c <
        decodeBlockCoord (normalizedNextCoord c)
      ↔
    3 ^ nextNormalizationExponent c *
      2 ^ (coordClosingValuation c + c.r) *
      c.q
      <
    2 ^ nextNormalizationExponent c *
      (3 ^ c.r * c.q - 1 +
        2 ^ coordClosingValuation c) := by
  simpa [coordBridgeNumerator, coordNumerator,
    decodeBlockCoord_add_one hc, pow_add,
    mul_assoc, mul_left_comm, mul_comm] using
      normalizedNextCoord_grows_iff_bridge hc




def reducedStepExpansionTerm (c : BlockCoord) : ℕ :=
  2 ^ nextNormalizationExponent c * 3 ^ c.r




def reducedStepContractionTerm (c : BlockCoord) : ℕ :=
  3 ^ nextNormalizationExponent c *
    2 ^ (coordClosingValuation c + c.r)




def reducedStepCorrection (c : BlockCoord) : ℕ :=
  2 ^ nextNormalizationExponent c *
    (2 ^ coordClosingValuation c - 1)




theorem reducedStepCorrection_pos
    {c : BlockCoord}
    (hc : c.Valid) :
    0 < reducedStepCorrection c := by
  have ha : 0 < coordClosingValuation c :=
    coordClosingValuation_pos hc
  obtain ⟨a, haEq⟩ :
      ∃ a, coordClosingValuation c = a + 1 :=
    ⟨coordClosingValuation c - 1, by omega⟩
  unfold reducedStepCorrection
  rw [haEq, pow_succ]
  have hp : 0 < 2 ^ a := by
    positivity
  have hs : 0 < 2 ^ a * 2 - 1 := by
    omega
  exact Nat.mul_pos (by positivity) hs




theorem reducedStep_weighted_bridge_decomposition
    {c : BlockCoord}
    (hc : c.Valid) :
    2 ^ nextNormalizationExponent c *
      (3 ^ c.r * c.q - 1 +
        2 ^ coordClosingValuation c)
      =
    reducedStepExpansionTerm c * c.q +
      reducedStepCorrection c := by
  have hn : 0 < 3 ^ c.r * c.q - 1 := by
    simpa [coordNumerator] using coordNumerator_pos hc
  have hp : 0 < 2 ^ coordClosingValuation c := by
    positivity
  have hshift :
      3 ^ c.r * c.q - 1 +
          2 ^ coordClosingValuation c
        =
      3 ^ c.r * c.q +
          (2 ^ coordClosingValuation c - 1) := by
    omega
  rw [hshift]
  unfold reducedStepExpansionTerm reducedStepCorrection
  ring








theorem normalizedNextCoord_descends_iff_terms
    {c : BlockCoord}
    (hc : c.Valid) :
    decodeBlockCoord (normalizedNextCoord c) <
        decodeBlockCoord c
      ↔
    reducedStepExpansionTerm c * c.q +
        reducedStepCorrection c
      <
    reducedStepContractionTerm c * c.q := by
  simpa [reducedStepContractionTerm,
    reducedStep_weighted_bridge_decomposition hc] using
      normalizedNextCoord_descends_iff_rakq hc




theorem normalizedNextCoord_same_size_iff_terms
    {c : BlockCoord}
    (hc : c.Valid) :
    decodeBlockCoord (normalizedNextCoord c) =
        decodeBlockCoord c
      ↔
    reducedStepExpansionTerm c * c.q +
        reducedStepCorrection c
      =
    reducedStepContractionTerm c * c.q := by
  simpa [reducedStepContractionTerm,
    reducedStep_weighted_bridge_decomposition hc] using
      normalizedNextCoord_same_size_iff_rakq hc




theorem normalizedNextCoord_grows_iff_terms
    {c : BlockCoord}
    (hc : c.Valid) :
    decodeBlockCoord c <
        decodeBlockCoord (normalizedNextCoord c)
      ↔
    reducedStepContractionTerm c * c.q
      <
    reducedStepExpansionTerm c * c.q +
        reducedStepCorrection c := by
  simpa [reducedStepContractionTerm,
    reducedStep_weighted_bridge_decomposition hc] using
      normalizedNextCoord_grows_iff_rakq hc




def ReducedStepExponentContracts
    (c : BlockCoord) : Prop :=
  reducedStepExpansionTerm c +
      reducedStepCorrection c <
    reducedStepContractionTerm c




theorem exponent_condition_implies_reduced_descent
    {c : BlockCoord}
    (hc : c.Valid)
    (hcontract : ReducedStepExponentContracts c) :
    decodeBlockCoord (normalizedNextCoord c) <
      decodeBlockCoord c := by
  have hqPos : 0 < c.q :=
    valid_coord_q_pos hc
  have hq : 1 ≤ c.q := hqPos
  have hC :
      reducedStepCorrection c ≤
        reducedStepCorrection c * c.q := by
    simpa using
      Nat.mul_le_mul_left (reducedStepCorrection c) hq
  have hToProduct :
      reducedStepExpansionTerm c * c.q +
          reducedStepCorrection c
        ≤
      (reducedStepExpansionTerm c +
          reducedStepCorrection c) * c.q := by
    calc
      reducedStepExpansionTerm c * c.q +
            reducedStepCorrection c
          ≤
        reducedStepExpansionTerm c * c.q +
            reducedStepCorrection c * c.q :=
        Nat.add_le_add_left hC _
      _ =
        (reducedStepExpansionTerm c +
            reducedStepCorrection c) * c.q := by
          ring
  have hStrict :
      (reducedStepExpansionTerm c +
          reducedStepCorrection c) * c.q
        <
      reducedStepContractionTerm c * c.q :=
    Nat.mul_lt_mul_of_pos_right hcontract hqPos
  exact (normalizedNextCoord_descends_iff_terms hc).2
    (hToProduct.trans_lt hStrict)




theorem exponent_condition_expanded
    (c : BlockCoord) :
    ReducedStepExponentContracts c ↔
      2 ^ nextNormalizationExponent c *
        (3 ^ c.r +
          2 ^ coordClosingValuation c - 1)
      <
      3 ^ nextNormalizationExponent c *
        2 ^ (coordClosingValuation c + c.r) := by
  have hThree : 0 < 3 ^ c.r := by
    positivity
  have hTwo : 0 < 2 ^ coordClosingValuation c := by
    positivity
  have hshift :
      3 ^ c.r + 2 ^ coordClosingValuation c - 1
        =
      3 ^ c.r +
        (2 ^ coordClosingValuation c - 1) := by
    omega
  have hleft :
      reducedStepExpansionTerm c +
          reducedStepCorrection c
        =
      2 ^ nextNormalizationExponent c *
        (3 ^ c.r +
          2 ^ coordClosingValuation c - 1) := by
    unfold reducedStepExpansionTerm reducedStepCorrection
    rw [hshift]
    ring
  unfold ReducedStepExponentContracts
  rw [hleft]
  rfl




def ReducedStepCoreExpands
    (c : BlockCoord) : Prop :=
  reducedStepContractionTerm c ≤
    reducedStepExpansionTerm c




theorem core_expansion_implies_reduced_growth
    {c : BlockCoord}
    (hc : c.Valid)
    (hexpand : ReducedStepCoreExpands c) :
    decodeBlockCoord c <
      decodeBlockCoord (normalizedNextCoord c) := by
  have hDq :
      reducedStepContractionTerm c * c.q ≤
        reducedStepExpansionTerm c * c.q :=
    Nat.mul_le_mul_right c.q hexpand
  have hCorrection :
      0 < reducedStepCorrection c :=
    reducedStepCorrection_pos hc
  have hEq :
      reducedStepExpansionTerm c * c.q <
        reducedStepExpansionTerm c * c.q +
          reducedStepCorrection c := by
    omega
  exact (normalizedNextCoord_grows_iff_terms hc).2
    (hDq.trans_lt hEq)




theorem reduced_descent_iff_correction_lt_margin
    {c : BlockCoord}
    (hc : c.Valid)
    (hmargin :
      reducedStepExpansionTerm c <
        reducedStepContractionTerm c) :
    decodeBlockCoord (normalizedNextCoord c) <
        decodeBlockCoord c
      ↔
    reducedStepCorrection c <
      (reducedStepContractionTerm c -
        reducedStepExpansionTerm c) * c.q := by
  rw [normalizedNextCoord_descends_iff_terms hc,
    Nat.sub_mul]
  have hProduct :
      reducedStepExpansionTerm c * c.q ≤
        reducedStepContractionTerm c * c.q :=
    Nat.mul_le_mul_right c.q (Nat.le_of_lt hmargin)
  omega




theorem reduced_step_size_spec
    {c : BlockCoord}
    (hc : c.Valid) :
    3 ^ nextNormalizationExponent c *
        2 ^ coordClosingValuation c *
        (decodeBlockCoord (normalizedNextCoord c) + 1)
      =
    2 ^ nextNormalizationExponent c *
        coordBridgeNumerator c
    ∧
    (decodeBlockCoord (normalizedNextCoord c) <
        decodeBlockCoord c
      ↔
      reducedStepExpansionTerm c * c.q +
          reducedStepCorrection c <
        reducedStepContractionTerm c * c.q) := by
  exact ⟨normalizedNextCoord_master_size_bridge hc,
    normalizedNextCoord_descends_iff_terms hc⟩








/-!
El triple (r,a,k) no determina por sí solo el signo
en toda situación frontera. q controla si el margen
multiplicativo absorbe el término correctivo.
-/




example :
    let c : BlockCoord := { r := 1, q := 1 }
    c.Normalized ∧
    coordClosingValuation c = 1 ∧
    nextNormalizationExponent c = 0 ∧
    normalizedNextCoord c = c := by
  dsimp
  constructor
  · norm_num [BlockCoord.Normalized, BlockCoord.Valid, Odd]
  · native_decide




example :
    let c : BlockCoord := { r := 1, q := 5 }
    c.Normalized ∧
    coordClosingValuation c = 1 ∧
    nextNormalizationExponent c = 0 ∧
    decodeBlockCoord (normalizedNextCoord c) <
      decodeBlockCoord c := by
  dsimp
  constructor
  · norm_num [BlockCoord.Normalized, BlockCoord.Valid, Odd]
  · native_decide




/-! Regresión: región de crecimiento garantizado. -/




example :
    let c : BlockCoord := { r := 3, q := 1 }
    coordClosingValuation c = 1 ∧
    nextNormalizationExponent c = 0 ∧
    decodeBlockCoord c = 7 ∧
    decodeBlockCoord (normalizedNextCoord c) = 13 ∧
    ReducedStepCoreExpands c := by
  dsimp
  unfold ReducedStepCoreExpands
  native_decide




/-! Regresión: contracción exponencial fuerte. -/




example :
    let c : BlockCoord := { r := 4, q := 1 }
    coordClosingValuation c = 4 ∧
    nextNormalizationExponent c = 1 ∧
    decodeBlockCoord c = 15 ∧
    decodeBlockCoord (normalizedNextCoord c) = 3 ∧
    ReducedStepExponentContracts c := by
  dsimp
  unfold ReducedStepExponentContracts
  native_decide




/-! Regresión: contracción con dos factores de tres. -/




example :
    let c : BlockCoord := { r := 1, q := 23 }
    coordClosingValuation c = 2 ∧
    nextNormalizationExponent c = 2 ∧
    decodeBlockCoord c = 45 ∧
    decodeBlockCoord (normalizedNextCoord c) = 7 ∧
    ReducedStepExponentContracts c := by
  dsimp
  unfold ReducedStepExponentContracts
  native_decide








/-!
Cierre de la capa de tricotomía exacta del paso reducido.
-/




theorem reduced_step_trichotomy
    {c : BlockCoord}
    (_hc : c.Valid) :
    decodeBlockCoord (normalizedNextCoord c) <
        decodeBlockCoord c
    ∨
    decodeBlockCoord (normalizedNextCoord c) =
        decodeBlockCoord c
    ∨
    decodeBlockCoord c <
        decodeBlockCoord (normalizedNextCoord c) := by
  exact lt_trichotomy
    (decodeBlockCoord (normalizedNextCoord c))
    (decodeBlockCoord c)




theorem reduced_step_terms_trichotomy
    {c : BlockCoord}
    (_hc : c.Valid) :
    reducedStepExpansionTerm c * c.q +
        reducedStepCorrection c
      <
    reducedStepContractionTerm c * c.q
    ∨
    reducedStepExpansionTerm c * c.q +
        reducedStepCorrection c
      =
    reducedStepContractionTerm c * c.q
    ∨
    reducedStepContractionTerm c * c.q
      <
    reducedStepExpansionTerm c * c.q +
        reducedStepCorrection c := by
  exact lt_trichotomy
    (reducedStepExpansionTerm c * c.q +
      reducedStepCorrection c)
    (reducedStepContractionTerm c * c.q)




theorem reduced_step_trichotomy_iff_terms
    {c : BlockCoord}
    (hc : c.Valid) :
    (
      decodeBlockCoord (normalizedNextCoord c) <
          decodeBlockCoord c
      ∨
      decodeBlockCoord (normalizedNextCoord c) =
          decodeBlockCoord c
      ∨
      decodeBlockCoord c <
          decodeBlockCoord (normalizedNextCoord c)
    )
    ↔
    (
      reducedStepExpansionTerm c * c.q +
          reducedStepCorrection c
        <
      reducedStepContractionTerm c * c.q
      ∨
      reducedStepExpansionTerm c * c.q +
          reducedStepCorrection c
        =
      reducedStepContractionTerm c * c.q
      ∨
      reducedStepContractionTerm c * c.q
        <
      reducedStepExpansionTerm c * c.q +
          reducedStepCorrection c
    ) := by
  constructor
  · intro h
    rcases h with hDescends | hSame | hGrows
    · exact Or.inl
        ((normalizedNextCoord_descends_iff_terms hc).1 hDescends)
    · exact Or.inr (Or.inl
        ((normalizedNextCoord_same_size_iff_terms hc).1 hSame))
    · exact Or.inr (Or.inr
        ((normalizedNextCoord_grows_iff_terms hc).1 hGrows))
  · intro h
    rcases h with hDescends | hSame | hGrows
    · exact Or.inl
        ((normalizedNextCoord_descends_iff_terms hc).2 hDescends)
    · exact Or.inr (Or.inl
        ((normalizedNextCoord_same_size_iff_terms hc).2 hSame))
    · exact Or.inr (Or.inr
        ((normalizedNextCoord_grows_iff_terms hc).2 hGrows))




theorem reduced_step_cases_mutually_exclusive
    {c : BlockCoord}
    (_hc : c.Valid) :
    ¬ (
      decodeBlockCoord (normalizedNextCoord c) <
        decodeBlockCoord c
      ∧
      decodeBlockCoord (normalizedNextCoord c) =
        decodeBlockCoord c
    )
    ∧
    ¬ (
      decodeBlockCoord (normalizedNextCoord c) <
        decodeBlockCoord c
      ∧
      decodeBlockCoord c <
        decodeBlockCoord (normalizedNextCoord c)
    )
    ∧
    ¬ (
      decodeBlockCoord (normalizedNextCoord c) =
        decodeBlockCoord c
      ∧
      decodeBlockCoord c <
        decodeBlockCoord (normalizedNextCoord c)
    ) := by
  constructor
  · rintro ⟨hDescends, hSame⟩
    omega
  · constructor
    · rintro ⟨hDescends, hGrows⟩
      omega
    · rintro ⟨hSame, hGrows⟩
      omega




theorem reduced_step_trichotomy_spec
    {c : BlockCoord}
    (hc : c.Valid) :
    (
      decodeBlockCoord (normalizedNextCoord c) <
          decodeBlockCoord c
      ∨
      decodeBlockCoord (normalizedNextCoord c) =
          decodeBlockCoord c
      ∨
      decodeBlockCoord c <
          decodeBlockCoord (normalizedNextCoord c)
    )
    ∧
    (
      (decodeBlockCoord (normalizedNextCoord c) <
          decodeBlockCoord c
        ↔
        reducedStepExpansionTerm c * c.q +
            reducedStepCorrection c <
          reducedStepContractionTerm c * c.q)
    )
    ∧
    (
      (decodeBlockCoord (normalizedNextCoord c) =
          decodeBlockCoord c
        ↔
        reducedStepExpansionTerm c * c.q +
            reducedStepCorrection c =
          reducedStepContractionTerm c * c.q)
    )
    ∧
    (
      (decodeBlockCoord c <
          decodeBlockCoord (normalizedNextCoord c)
        ↔
        reducedStepContractionTerm c * c.q <
          reducedStepExpansionTerm c * c.q +
            reducedStepCorrection c)
    ) := by
  exact
    ⟨reduced_step_trichotomy hc,
     normalizedNextCoord_descends_iff_terms hc,
     normalizedNextCoord_same_size_iff_terms hc,
     normalizedNextCoord_grows_iff_terms hc⟩








/-!
Puntos fijos del paso reducido y reducción exacta a la banda exponencial.
-/




theorem normalizedNextCoord_same_size_iff_fixed
    {c : BlockCoord}
    (hc : c.Valid) :
    decodeBlockCoord (normalizedNextCoord c) =
        decodeBlockCoord c
      ↔
    normalizedNextCoord c = c := by
  constructor
  · intro h
    have hEncoded := congrArg encodeBlockCoord h
    rw [encode_decodeBlockCoord (normalizedNextCoord_valid hc),
        encode_decodeBlockCoord hc] at hEncoded
    exact hEncoded
  · intro h
    rw [h]




theorem normalizedNextCoord_fixed_iff_terms
    {c : BlockCoord}
    (hc : c.Valid) :
    normalizedNextCoord c = c
      ↔
    reducedStepExpansionTerm c * c.q +
        reducedStepCorrection c
      =
    reducedStepContractionTerm c * c.q := by
  constructor
  · intro hFixed
    exact (normalizedNextCoord_same_size_iff_terms hc).1
      ((normalizedNextCoord_same_size_iff_fixed hc).2 hFixed)
  · intro hTerms
    exact (normalizedNextCoord_same_size_iff_fixed hc).1
      ((normalizedNextCoord_same_size_iff_terms hc).2 hTerms)




theorem oneCoord_normalized :
    oneCoord.Normalized := by
  rw [oneCoord_eq]
  norm_num [BlockCoord.Normalized, BlockCoord.Valid, Odd]




theorem reduced_fixed_implies_expansion_lt_contraction
    {c : BlockCoord}
    (hc : c.Valid)
    (hfix : normalizedNextCoord c = c) :
    reducedStepExpansionTerm c <
      reducedStepContractionTerm c := by
  have hEq :=
    (normalizedNextCoord_fixed_iff_terms hc).1 hfix
  have hCorrection :
      0 < reducedStepCorrection c :=
    reducedStepCorrection_pos hc
  by_contra hNot
  have hDE :
      reducedStepContractionTerm c ≤
        reducedStepExpansionTerm c :=
    Nat.le_of_not_gt hNot
  have hDEq :
      reducedStepContractionTerm c * c.q ≤
        reducedStepExpansionTerm c * c.q :=
    Nat.mul_le_mul_right c.q hDE
  omega








theorem reduced_fixed_margin_equation
    {c : BlockCoord}
    (hc : c.Valid)
    (hfix : normalizedNextCoord c = c) :
    (reducedStepContractionTerm c -
        reducedStepExpansionTerm c) * c.q
      =
    reducedStepCorrection c := by
  have hLT :=
    reduced_fixed_implies_expansion_lt_contraction hc hfix
  have hLE :
      reducedStepExpansionTerm c ≤
        reducedStepContractionTerm c :=
    Nat.le_of_lt hLT
  have hEq :=
    (normalizedNextCoord_fixed_iff_terms hc).1 hfix
  have hSub :=
    Nat.sub_add_cancel hLE
  have hDecomp :
      reducedStepContractionTerm c =
        reducedStepExpansionTerm c +
          (reducedStepContractionTerm c -
            reducedStepExpansionTerm c) := by
    omega
  have hProduct := congrArg (fun n => n * c.q) hDecomp
  rw [add_mul] at hProduct
  omega




theorem reduced_fixed_implies_exponential_gap
    {c : BlockCoord}
    (hc : c.Valid)
    (hfix : normalizedNextCoord c = c) :
    reducedStepExpansionTerm c <
        reducedStepContractionTerm c
    ∧
    reducedStepContractionTerm c ≤
        reducedStepExpansionTerm c +
          reducedStepCorrection c := by
  have hLT :=
    reduced_fixed_implies_expansion_lt_contraction hc hfix
  have hMargin :=
    reduced_fixed_margin_equation hc hfix
  have hq : 1 ≤ c.q :=
    valid_coord_q_pos hc
  have hGapMul :
      reducedStepContractionTerm c -
          reducedStepExpansionTerm c
        ≤
      (reducedStepContractionTerm c -
          reducedStepExpansionTerm c) * c.q := by
    simpa using
      Nat.mul_le_mul_left
        (reducedStepContractionTerm c -
          reducedStepExpansionTerm c) hq
  rw [hMargin] at hGapMul
  have hSub :=
    Nat.sub_add_cancel (Nat.le_of_lt hLT)
  constructor
  · exact hLT
  · omega




theorem reduced_fixed_q_le_correction
    {c : BlockCoord}
    (hc : c.Valid)
    (hfix : normalizedNextCoord c = c) :
    c.q ≤ reducedStepCorrection c := by
  have hLT :=
    reduced_fixed_implies_expansion_lt_contraction hc hfix
  have hGapPos :
      0 <
        reducedStepContractionTerm c -
          reducedStepExpansionTerm c := by
    omega
  have hGapOne :
      1 ≤
        reducedStepContractionTerm c -
          reducedStepExpansionTerm c := hGapPos
  have hqMul :
      c.q ≤
        (reducedStepContractionTerm c -
          reducedStepExpansionTerm c) * c.q := by
    have h :=
      Nat.mul_le_mul_right c.q hGapOne
    simpa [mul_comm] using h
  rw [reduced_fixed_margin_equation hc hfix] at hqMul
  exact hqMul








theorem boundary_triple_fixed_iff_q_one
    {c : BlockCoord}
    (hc : c.Valid)
    (hr : c.r = 1)
    (ha : coordClosingValuation c = 1)
    (hk : nextNormalizationExponent c = 0) :
    normalizedNextCoord c = c ↔ c.q = 1 := by
  rw [normalizedNextCoord_fixed_iff_terms hc]
  unfold reducedStepExpansionTerm
    reducedStepContractionTerm
    reducedStepCorrection
  rw [hr, ha, hk]
  norm_num
  omega




theorem boundary_triple_fixed_iff_oneCoord
    {c : BlockCoord}
    (hc : c.Valid)
    (hr : c.r = 1)
    (ha : coordClosingValuation c = 1)
    (hk : nextNormalizationExponent c = 0) :
    normalizedNextCoord c = c ↔ c = oneCoord := by
  constructor
  · intro hfix
    have hq :=
      (boundary_triple_fixed_iff_q_one hc hr ha hk).1 hfix
    cases c with
    | mk r q =>
        dsimp at hr hq
        subst r
        subst q
        exact oneCoord_eq.symm
  · intro hOne
    subst c
    exact normalizedNextCoord_one




/-!
Todo punto fijo válido de G satisface E < D ≤ E+C.
El triple frontera (r,a,k)=(1,1,0) tiene un único punto fijo,
q=1, es decir oneCoord.
La unicidad global de oneCoord requiere todavía clasificar
la banda exponencial E < D ≤ E+C.
-/




example :
    normalizedNextCoord oneCoord = oneCoord := by
  exact normalizedNextCoord_one




example :
    decodeBlockCoord (normalizedNextCoord oneCoord) =
      decodeBlockCoord oneCoord := by
  rw [normalizedNextCoord_one]




example :
    let c : BlockCoord := { r := 1, q := 5 }
    c.r = 1 ∧
    coordClosingValuation c = 1 ∧
    nextNormalizationExponent c = 0 ∧
    normalizedNextCoord c ≠ c := by
  native_decide




theorem reduced_fixed_point_spec
    {c : BlockCoord}
    (hc : c.Valid) :
    (
      decodeBlockCoord (normalizedNextCoord c) =
          decodeBlockCoord c
      ↔
      normalizedNextCoord c = c
    )
    ∧
    (
      normalizedNextCoord c = c →
      reducedStepExpansionTerm c <
          reducedStepContractionTerm c
      ∧
      reducedStepContractionTerm c ≤
          reducedStepExpansionTerm c +
            reducedStepCorrection c
    ) := by
  exact
    ⟨normalizedNextCoord_same_size_iff_fixed hc,
     reduced_fixed_implies_exponential_gap hc⟩








/-!
Reducción de puntos fijos reducidos a ciclos brutos de un bloque.
-/




theorem reduced_fixed_implies_raw_successor_fixed
    {c : BlockCoord}
    (hc : c.Valid)
    (hfix : normalizedNextCoord c = c) :
    nextCoord (nextCoord c) = nextCoord c := by
  have h := nextCoord_normalizedNextCoord hc
  rw [hfix] at h
  exact h.symm




theorem raw_fixed_coordNextValue_eq_decode
    {d : BlockCoord}
    (hd : d.Valid)
    (hfix : nextCoord d = d) :
    coordNextValue d = decodeBlockCoord d := by
  have h := (nextCoord_spec hd).2.1
  rw [hfix] at h
  exact h.symm




theorem raw_fixed_diophantine_equation
    {d : BlockCoord}
    (hd : d.Valid)
    (hfix : nextCoord d = d) :
    (2 ^ (coordClosingValuation d + d.r) -
       3 ^ d.r) * d.q
      =
    2 ^ coordClosingValuation d - 1 := by
  have hBridge := coord_bridge_equation_expanded hd
  rw [hfix] at hBridge
  have hRaw :
      3 ^ d.r * d.q - 1 +
          2 ^ coordClosingValuation d
        =
      2 ^ (coordClosingValuation d + d.r) * d.q := by
    simpa [coordClosingValuation, coordNumerator] using hBridge
  have hqPos : 0 < d.q :=
    valid_coord_q_pos hd
  have hMainPos : 0 < 3 ^ d.r * d.q :=
    Nat.mul_pos (by positivity) hqPos
  have haPos : 0 < coordClosingValuation d :=
    coordClosingValuation_pos hd
  obtain ⟨a, haEq⟩ :
      ∃ a, coordClosingValuation d = a + 1 :=
    ⟨coordClosingValuation d - 1, by omega⟩
  have hPowGt : 1 < 2 ^ coordClosingValuation d := by
    rw [haEq, pow_succ]
    have hp : 0 < 2 ^ a := by
      positivity
    omega
  have hLeftGt :
      3 ^ d.r * d.q <
        3 ^ d.r * d.q - 1 +
          2 ^ coordClosingValuation d := by
    omega
  have hGap :
      3 ^ d.r <
        2 ^ (coordClosingValuation d + d.r) := by
    by_contra hNot
    have hLE :
        2 ^ (coordClosingValuation d + d.r) ≤
          3 ^ d.r :=
      Nat.le_of_not_gt hNot
    have hMul :
        2 ^ (coordClosingValuation d + d.r) * d.q ≤
          3 ^ d.r * d.q :=
      Nat.mul_le_mul_right d.q hLE
    omega
  have hShift :
      3 ^ d.r * d.q - 1 +
          2 ^ coordClosingValuation d
        =
      3 ^ d.r * d.q +
          (2 ^ coordClosingValuation d - 1) := by
    omega
  have hRawAdd :
      3 ^ d.r * d.q +
          (2 ^ coordClosingValuation d - 1)
        =
      2 ^ (coordClosingValuation d + d.r) * d.q := by
    omega
  have hSub :=
    Nat.sub_add_cancel (Nat.le_of_lt hGap)
  have hDecomp :
      2 ^ (coordClosingValuation d + d.r)
        =
      3 ^ d.r +
        (2 ^ (coordClosingValuation d + d.r) -
          3 ^ d.r) := by
    omega
  have hProduct := congrArg (fun n => n * d.q) hDecomp
  rw [add_mul] at hProduct
  omega




theorem raw_fixed_gap_pos
    {d : BlockCoord}
    (hd : d.Valid)
    (hfix : nextCoord d = d) :
    3 ^ d.r <
      2 ^ (coordClosingValuation d + d.r) := by
  have hEq :=
    raw_fixed_diophantine_equation hd hfix
  have haPos : 0 < coordClosingValuation d :=
    coordClosingValuation_pos hd
  obtain ⟨a, haEq⟩ :
      ∃ a, coordClosingValuation d = a + 1 :=
    ⟨coordClosingValuation d - 1, by omega⟩
  have hMersenne :
      0 < 2 ^ coordClosingValuation d - 1 := by
    rw [haEq, pow_succ]
    have hp : 0 < 2 ^ a := by
      positivity
    omega
  by_contra hNot
  have hLE :
      2 ^ (coordClosingValuation d + d.r) ≤
        3 ^ d.r :=
    Nat.le_of_not_gt hNot
  have hZero :
      2 ^ (coordClosingValuation d + d.r) -
          3 ^ d.r = 0 :=
    Nat.sub_eq_zero_of_le hLE
  rw [hZero] at hEq
  simp at hEq
  omega




theorem raw_fixed_gap_dvd_mersenne
    {d : BlockCoord}
    (hd : d.Valid)
    (hfix : nextCoord d = d) :
    2 ^ (coordClosingValuation d + d.r) -
        3 ^ d.r
      ∣
    2 ^ coordClosingValuation d - 1 := by
  refine ⟨d.q, ?_⟩
  exact (raw_fixed_diophantine_equation hd hfix).symm




theorem raw_fixed_gap_le_mersenne
    {d : BlockCoord}
    (hd : d.Valid)
    (hfix : nextCoord d = d) :
    2 ^ (coordClosingValuation d + d.r) -
        3 ^ d.r
      ≤
    2 ^ coordClosingValuation d - 1 := by
  have hq : 1 ≤ d.q :=
    valid_coord_q_pos hd
  have hMul :
      2 ^ (coordClosingValuation d + d.r) -
          3 ^ d.r
        ≤
      (2 ^ (coordClosingValuation d + d.r) -
          3 ^ d.r) * d.q := by
    simpa using
      Nat.mul_le_mul_left
        (2 ^ (coordClosingValuation d + d.r) -
          3 ^ d.r) hq
  rw [raw_fixed_diophantine_equation hd hfix] at hMul
  exact hMul








theorem raw_fixed_power_squeeze
    {d : BlockCoord}
    (hd : d.Valid)
    (hfix : nextCoord d = d) :
    2 ^ coordClosingValuation d *
        (2 ^ d.r - 1)
      <
    3 ^ d.r
    ∧
    3 ^ d.r
      <
    2 ^ coordClosingValuation d *
        2 ^ d.r := by
  have hGap :=
    raw_fixed_gap_pos hd hfix
  have hGapLe :=
    raw_fixed_gap_le_mersenne hd hfix
  rw [pow_add] at hGap hGapLe
  have hPowPos :
      0 < 2 ^ coordClosingValuation d := by
    positivity
  have hThreePos : 0 < 3 ^ d.r := by
    positivity
  constructor
  · rw [Nat.mul_sub_left_distrib]
    simp only [mul_one]
    omega
  · exact hGap








theorem raw_fixed_power_div
    {d : BlockCoord}
    (hd : d.Valid)
    (hfix : nextCoord d = d) :
    3 ^ d.r / 2 ^ coordClosingValuation d =
      2 ^ d.r - 1 := by
  have hSqueeze :=
    raw_fixed_power_squeeze hd hfix
  have hPowPos : 0 < 2 ^ d.r := by
    positivity
  have hPowOne : 1 ≤ 2 ^ d.r := hPowPos
  apply Nat.div_eq_of_lt_le
  · have hLo := Nat.le_of_lt hSqueeze.1
    simpa [mul_comm] using hLo
  · simpa [Nat.sub_add_cancel hPowOne, mul_comm] using
      hSqueeze.2




def OneBlockGapRigidity : Prop :=
  ∀ a s : ℕ,
    1 ≤ a →
    1 ≤ s →
    0 < 2 ^ (a + s) - 3 ^ s →
    (2 ^ (a + s) - 3 ^ s) ∣ 2 ^ a - 1 →
    a = 1 ∧ s = 1




theorem oneBlockGapRigidity_implies_unique_reduced_fixed
    (hR : OneBlockGapRigidity)
    {c : BlockCoord}
    (hc : c.Valid)
    (hfix : normalizedNextCoord c = c) :
    c = oneCoord := by
  let d := nextCoord c
  have hd : d.Valid := by
    simpa [d] using nextCoord_valid hc
  have hraw : nextCoord d = d := by
    simpa [d] using
      reduced_fixed_implies_raw_successor_fixed hc hfix
  have hGapDiff :
      0 <
        2 ^ (coordClosingValuation d + d.r) -
          3 ^ d.r := by
    have hGap := raw_fixed_gap_pos hd hraw
    omega
  have hDiv :
      2 ^ (coordClosingValuation d + d.r) -
          3 ^ d.r
        ∣
      2 ^ coordClosingValuation d - 1 :=
    raw_fixed_gap_dvd_mersenne hd hraw
  have hRigid :=
    hR (coordClosingValuation d) d.r
      (coordClosingValuation_pos hd)
      hd.1 hGapDiff hDiv
  rcases hRigid with ⟨ha, hs⟩
  have hEq :=
    raw_fixed_diophantine_equation hd hraw
  rw [ha, hs] at hEq
  norm_num at hEq
  have hq : d.q = 1 := hEq
  have hdOne : d = oneCoord := by
    cases hD : d with
    | mk r q =>
        have hr : r = 1 := by
          simpa [hD] using hs
        have hqField : q = 1 := by
          simpa [hD] using hq
        rw [hr, hqField]
        exact oneCoord_eq.symm
  have hNextOne : nextCoord c = oneCoord := by
    simpa [d] using hdOne
  have hNormalizedOne :
      normalizedNextCoord c = oneCoord := by
    unfold normalizedNextCoord
    rw [hNextOne, normalizeCoord_one]
  exact hfix.symm.trans hNormalizedOne




theorem reduced_fixed_to_one_block_gap_spec
    {c : BlockCoord}
    (hc : c.Valid)
    (hfix : normalizedNextCoord c = c) :
    let d := nextCoord c
    nextCoord d = d
    ∧
    (2 ^ (coordClosingValuation d + d.r) -
        3 ^ d.r) * d.q
      =
    2 ^ coordClosingValuation d - 1
    ∧
    3 ^ d.r <
      2 ^ (coordClosingValuation d + d.r)
    ∧
    (2 ^ (coordClosingValuation d + d.r) -
        3 ^ d.r)
      ∣
    2 ^ coordClosingValuation d - 1
    ∧
    (
      2 ^ coordClosingValuation d *
          (2 ^ d.r - 1)
        <
      3 ^ d.r
      ∧
      3 ^ d.r <
        2 ^ coordClosingValuation d * 2 ^ d.r
    ) := by
  let d := nextCoord c
  change
    nextCoord d = d
    ∧
    (2 ^ (coordClosingValuation d + d.r) -
        3 ^ d.r) * d.q
      =
    2 ^ coordClosingValuation d - 1
    ∧
    3 ^ d.r <
      2 ^ (coordClosingValuation d + d.r)
    ∧
    (2 ^ (coordClosingValuation d + d.r) -
        3 ^ d.r)
      ∣
    2 ^ coordClosingValuation d - 1
    ∧
    (
      2 ^ coordClosingValuation d *
          (2 ^ d.r - 1)
        <
      3 ^ d.r
      ∧
      3 ^ d.r <
        2 ^ coordClosingValuation d * 2 ^ d.r
    )
  have hd : d.Valid := by
    simpa [d] using nextCoord_valid hc
  have hraw : nextCoord d = d := by
    simpa [d] using
      reduced_fixed_implies_raw_successor_fixed hc hfix
  exact
    ⟨hraw,
     raw_fixed_diophantine_equation hd hraw,
     raw_fixed_gap_pos hd hraw,
     raw_fixed_gap_dvd_mersenne hd hraw,
     raw_fixed_power_squeeze hd hraw⟩
noncomputable def steinerAlpha : ℝ :=
  Real.log 3 / Real.log 2




theorem log_two_pos :
    0 < Real.log 2 := by
  exact Real.log_pos (by norm_num)




theorem log_three_pos :
    0 < Real.log 3 := by
  exact Real.log_pos (by norm_num)




theorem two_thirds_lt_log_two :
    (2 : ℝ) / 3 < Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith




theorem oneBlockGap_le_mersenne
    {a s : ℕ}
    (ha : 1 ≤ a)
    (_hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1) :
    2 ^ (a + s) - 3 ^ s ≤ 2 ^ a - 1 := by
  have hMersenne :
      0 < 2 ^ a - 1 := by
    obtain ⟨a₀, rfl⟩ : ∃ a₀, a = a₀ + 1 :=
      ⟨a - 1, by omega⟩
    rw [pow_succ]
    have hp : 0 < 2 ^ a₀ := by
      positivity
    omega
  exact Nat.le_of_dvd hMersenne hdvd




theorem oneBlockGap_power_squeeze
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1) :
    2 ^ a * (2 ^ s - 1) < 3 ^ s
    ∧
    3 ^ s < 2 ^ (a + s) := by
  have hGapLe :=
    oneBlockGap_le_mersenne ha hs hgap hdvd
  rw [pow_add] at hgap hGapLe
  have hPowPos : 0 < 2 ^ a := by
    positivity
  have hThreePos : 0 < 3 ^ s := by
    positivity
  constructor
  · rw [Nat.mul_sub_left_distrib]
    simp only [mul_one]
    omega
  · simpa [pow_add] using hgap




theorem oneBlockGap_log_linear_pos
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1) :
    0 <
      ((a + s : ℕ) : ℝ) * Real.log 2 -
        (s : ℝ) * Real.log 3 := by
  have hltNat :=
    (oneBlockGap_power_squeeze ha hs hgap hdvd).2
  have hltReal :
      (3 : ℝ) ^ s < (2 : ℝ) ^ (a + s) := by
    exact_mod_cast hltNat
  have hlog :=
    Real.strictMonoOn_log
      (by positivity : 0 < (3 : ℝ) ^ s)
      (by positivity : 0 < (2 : ℝ) ^ (a + s))
      hltReal
  rw [Real.log_pow, Real.log_pow] at hlog
  linarith




theorem oneBlockGap_log_linear_lt
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1) :
    ((a + s : ℕ) : ℝ) * Real.log 2 -
        (s : ℝ) * Real.log 3
      <
    1 / (((2 : ℝ) ^ s) - 1) := by
  have hSqueeze :=
    oneBlockGap_power_squeeze ha hs hgap hdvd
  have hGapLe :=
    oneBlockGap_le_mersenne ha hs hgap hdvd
  have hGapNatLe :
      3 ^ s ≤ 2 ^ (a + s) :=
    Nat.le_of_lt hSqueeze.2
  have hPowAOne : 1 ≤ 2 ^ a := by
    have hp : 0 < 2 ^ a := by positivity
    omega
  have hPowSOne : 1 ≤ 2 ^ s := by
    have hp : 0 < 2 ^ s := by positivity
    omega
  have hGapCast :
      ((2 ^ (a + s) - 3 ^ s : ℕ) : ℝ)
        =
      (2 : ℝ) ^ (a + s) - (3 : ℝ) ^ s := by
    rw [Nat.cast_sub hGapNatLe]
    norm_num
  have hGapLeReal :
      ((2 ^ (a + s) - 3 ^ s : ℕ) : ℝ)
        ≤
      (2 : ℝ) ^ a - 1 := by
    exact_mod_cast hGapLe
  have hGapLtPowA :
      ((2 ^ (a + s) - 3 ^ s : ℕ) : ℝ)
        <
      (2 : ℝ) ^ a := by
    linarith
  have hThreePos : 0 < (3 : ℝ) ^ s := by
    positivity
  have hTwoPos : 0 < (2 : ℝ) ^ (a + s) := by
    positivity
  have hDenPos : 0 < (2 : ℝ) ^ s - 1 := by
    have hsPos : 0 < s := by omega
    have hsPow : (1 : ℝ) < 2 ^ s := by
      exact one_lt_pow₀ (by norm_num) (by omega : s ≠ 0)
    linarith
  have hRatioPos :
      0 < (2 : ℝ) ^ (a + s) / (3 : ℝ) ^ s :=
    div_pos hTwoPos hThreePos
  have hLogLe :=
    Real.log_le_sub_one_of_pos hRatioPos
  have hLinearEq :
      ((a + s : ℕ) : ℝ) * Real.log 2 -
          (s : ℝ) * Real.log 3
        =
      Real.log
        ((2 : ℝ) ^ (a + s) / (3 : ℝ) ^ s) := by
    rw [Real.log_div (ne_of_gt hTwoPos) (ne_of_gt hThreePos),
      Real.log_pow, Real.log_pow]
  have hRatioSub :
      (2 : ℝ) ^ (a + s) / (3 : ℝ) ^ s - 1
        =
      ((2 ^ (a + s) - 3 ^ s : ℕ) : ℝ) /
        (3 : ℝ) ^ s := by
    rw [hGapCast]
    field_simp
  have hGapDivLt :
      ((2 ^ (a + s) - 3 ^ s : ℕ) : ℝ) /
          (3 : ℝ) ^ s
        <
      (2 : ℝ) ^ a / (3 : ℝ) ^ s :=
    (div_lt_div_iff_of_pos_right hThreePos).2 hGapLtPowA
  have hLowerReal :
      (2 : ℝ) ^ a * ((2 : ℝ) ^ s - 1)
        <
      (3 : ℝ) ^ s := by
    exact_mod_cast hSqueeze.1
  have hPowDivLt :
      (2 : ℝ) ^ a / (3 : ℝ) ^ s
        <
      1 / ((2 : ℝ) ^ s - 1) := by
    apply (div_lt_div_iff₀ hThreePos hDenPos).2
    simpa using hLowerReal
  rw [hLinearEq]
  calc
    Real.log ((2 : ℝ) ^ (a + s) / (3 : ℝ) ^ s)
        ≤ (2 : ℝ) ^ (a + s) / (3 : ℝ) ^ s - 1 := hLogLe
    _ = ((2 ^ (a + s) - 3 ^ s : ℕ) : ℝ) /
          (3 : ℝ) ^ s := hRatioSub
    _ < (2 : ℝ) ^ a / (3 : ℝ) ^ s := hGapDivLt
    _ < 1 / ((2 : ℝ) ^ s - 1) := hPowDivLt




theorem oneBlockGap_steiner_approx
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1) :
    0 <
      (((a + s : ℕ) : ℝ) / (s : ℝ)) -
        steinerAlpha
    ∧
    (((a + s : ℕ) : ℝ) / (s : ℝ)) -
        steinerAlpha
      <
    1 /
      ((s : ℝ) * Real.log 2 *
        (((2 : ℝ) ^ s) - 1)) := by
  have hsReal : 0 < (s : ℝ) := by
    exact_mod_cast (show 0 < s by omega)
  have hLogPos := log_two_pos
  have hDenPos :
      0 < (s : ℝ) * Real.log 2 :=
    mul_pos hsReal hLogPos
  have hPowSubPos :
      0 < (2 : ℝ) ^ s - 1 := by
    have hsPow : (1 : ℝ) < 2 ^ s :=
      one_lt_pow₀ (by norm_num) (by omega : s ≠ 0)
    linarith
  have hIdentity :
      (((a + s : ℕ) : ℝ) / (s : ℝ)) -
          steinerAlpha
        =
      (((a + s : ℕ) : ℝ) * Real.log 2 -
          (s : ℝ) * Real.log 3) /
        ((s : ℝ) * Real.log 2) := by
    unfold steinerAlpha
    field_simp [ne_of_gt hsReal, ne_of_gt hLogPos]
  have hLinearPos :=
    oneBlockGap_log_linear_pos ha hs hgap hdvd
  have hLinearLt :=
    oneBlockGap_log_linear_lt ha hs hgap hdvd
  constructor
  · rw [hIdentity]
    exact div_pos hLinearPos hDenPos
  · rw [hIdentity]
    calc
      (((a + s : ℕ) : ℝ) * Real.log 2 -
          (s : ℝ) * Real.log 3) /
          ((s : ℝ) * Real.log 2)
        <
      (1 / ((2 : ℝ) ^ s - 1)) /
          ((s : ℝ) * Real.log 2) :=
        (div_lt_div_iff_of_pos_right hDenPos).2 hLinearLt
      _ =
        1 /
          ((s : ℝ) * Real.log 2 *
            ((2 : ℝ) ^ s - 1)) := by
        field_simp




theorem three_mul_lt_two_pow_sub_one
    {s : ℕ}
    (hs : 4 ≤ s) :
    3 * s < 2 ^ s - 1 := by
  have hMain : 3 * s + 1 < 2 ^ s := by
    induction s, hs using Nat.le_induction with
    | base =>
        norm_num
    | succ n hn ih =>
        rw [pow_succ]
        omega
  omega




theorem steiner_log_denominator_gt
    {s : ℕ}
    (hs : 4 ≤ s) :
    2 * (s : ℝ) <
      Real.log 2 * (((2 : ℝ) ^ s) - 1) := by
  have hGrowth :=
    three_mul_lt_two_pow_sub_one hs
  have hPowOneNat : 1 ≤ 2 ^ s := by
    have hp : 0 < 2 ^ s := by positivity
    omega
  have hGrowthCast :
      ((3 * s : ℕ) : ℝ) < ((2 ^ s - 1 : ℕ) : ℝ) := by
    exact_mod_cast hGrowth
  have hGrowthReal :
      3 * (s : ℝ) < (2 : ℝ) ^ s - 1 := by
    rw [Nat.cast_sub hPowOneNat] at hGrowthCast
    norm_num at hGrowthCast ⊢
    exact hGrowthCast
  have hSubPos : 0 < (2 : ℝ) ^ s - 1 := by
    have hsPos : 0 < (s : ℝ) := by
      exact_mod_cast (show 0 < s by omega)
    linarith
  have hScaled :
      (2 / 3 : ℝ) * ((2 : ℝ) ^ s - 1)
        <
      Real.log 2 * ((2 : ℝ) ^ s - 1) :=
    mul_lt_mul_of_pos_right two_thirds_lt_log_two hSubPos
  nlinarith




theorem oneBlockGap_legendre_bound
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 4 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1) :
    0 <
      (((a + s : ℕ) : ℝ) / (s : ℝ)) -
        steinerAlpha
    ∧
    (((a + s : ℕ) : ℝ) / (s : ℝ)) -
        steinerAlpha
      <
    1 / (2 * (s : ℝ) ^ 2) := by
  have hsOne : 1 ≤ s := by omega
  have hApprox :=
    oneBlockGap_steiner_approx ha hsOne hgap hdvd
  have hsReal : 0 < (s : ℝ) := by
    exact_mod_cast (show 0 < s by omega)
  have hLogDen :=
    steiner_log_denominator_gt hs
  have hSubPos : 0 < (2 : ℝ) ^ s - 1 := by
    have hsPow : (1 : ℝ) < 2 ^ s :=
      one_lt_pow₀ (by norm_num) (by omega : s ≠ 0)
    linarith
  have hAnalyticPos :
      0 <
        (s : ℝ) * Real.log 2 *
          ((2 : ℝ) ^ s - 1) :=
    mul_pos (mul_pos hsReal log_two_pos) hSubPos
  have hQuadPos :
      0 < 2 * (s : ℝ) ^ 2 := by
    positivity
  have hDenOrder :
      2 * (s : ℝ) ^ 2
        <
      (s : ℝ) * Real.log 2 *
        ((2 : ℝ) ^ s - 1) := by
    have hScaled :=
      mul_lt_mul_of_pos_left hLogDen hsReal
    nlinarith
  have hRecip :
      1 /
          ((s : ℝ) * Real.log 2 *
            ((2 : ℝ) ^ s - 1))
        <
      1 / (2 * (s : ℝ) ^ 2) := by
    apply (div_lt_div_iff₀ hAnalyticPos hQuadPos).2
    simpa using hDenOrder
  exact ⟨hApprox.1, lt_trans hApprox.2 hRecip⟩




theorem oneBlockGap_legendre_abs
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 4 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1) :
    abs (
      steinerAlpha -
        (((a + s : ℕ) : ℝ) / (s : ℝ))
    )
      <
    1 / (2 * (s : ℝ) ^ 2) := by
  have h :=
    oneBlockGap_legendre_bound ha hs hgap hdvd
  rw [abs_of_neg (by linarith)]
  linarith




def steinerSlopeRat (a s : ℕ) : ℚ :=
  Rat.divInt (Int.ofNat (a + s)) (Int.ofNat s)




theorem steinerSlopeRat_cast
    {a s : ℕ}
    (_hs : 1 ≤ s) :
    ((steinerSlopeRat a s : ℚ) : ℝ)
      =
    ((a + s : ℕ) : ℝ) / (s : ℝ) := by
  rw [steinerSlopeRat, Rat.cast_divInt]
  norm_num




theorem steinerSlopeRat_den_le
    {a s : ℕ}
    (hs : 1 ≤ s) :
    (steinerSlopeRat a s).den ≤ s := by
  have hDenDvdInt :
      ((steinerSlopeRat a s).den : ℤ) ∣ (s : ℤ) := by
    simpa [steinerSlopeRat] using
      Rat.den_dvd (Int.ofNat (a + s)) (Int.ofNat s)
  have hDenDvdNat :
      (steinerSlopeRat a s).den ∣ s :=
    Int.natCast_dvd_natCast.mp hDenDvdInt
  exact Nat.le_of_dvd (by omega) hDenDvdNat




theorem oneBlockGap_legendre_den_bound
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 4 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1) :
    abs (
      steinerAlpha -
        ((steinerSlopeRat a s : ℚ) : ℝ)
    )
      <
    1 /
      (2 * ((steinerSlopeRat a s).den : ℝ) ^ 2) := by
  have hsOne : 1 ≤ s := by omega
  have hAbs :=
    oneBlockGap_legendre_abs ha hs hgap hdvd
  rw [← steinerSlopeRat_cast hsOne] at hAbs
  have hDenLe :=
    steinerSlopeRat_den_le (a := a) hsOne
  have hDenPosNat :
      0 < (steinerSlopeRat a s).den :=
    Rat.den_pos _
  have hDenPosReal :
      0 < ((steinerSlopeRat a s).den : ℝ) := by
    exact_mod_cast hDenPosNat
  have hsReal : 0 < (s : ℝ) := by
    exact_mod_cast (show 0 < s by omega)
  have hDenLeReal :
      ((steinerSlopeRat a s).den : ℝ) ≤ (s : ℝ) := by
    exact_mod_cast hDenLe
  have hSmallDenPos :
      0 <
        2 * ((steinerSlopeRat a s).den : ℝ) ^ 2 := by
    positivity
  have hLargeDenPos :
      0 < 2 * (s : ℝ) ^ 2 := by
    positivity
  have hSquareLe :
      2 * ((steinerSlopeRat a s).den : ℝ) ^ 2
        ≤
      2 * (s : ℝ) ^ 2 := by
    nlinarith
  have hRecipLe :
      1 / (2 * (s : ℝ) ^ 2)
        ≤
      1 /
        (2 * ((steinerSlopeRat a s).den : ℝ) ^ 2) := by
    apply (div_le_div_iff₀ hLargeDenPos hSmallDenPos).2
    simpa using hSquareLe
  exact lt_of_lt_of_le hAbs hRecipLe




theorem oneBlockGap_slope_is_convergent
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 4 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1) :
    ∃ n : ℕ,
      steinerSlopeRat a s =
        steinerAlpha.convergent n := by
  apply Real.exists_rat_eq_convergent
  exact oneBlockGap_legendre_den_bound ha hs hgap hdvd




/-
La cota de Legendre se aplica aquí solamente para s ≥ 4.
Los casos s < 4 se estudiarán después mediante aritmética exacta.
-/




theorem raw_fixed_slope_is_convergent
    {d : BlockCoord}
    (hd : d.Valid)
    (hfix : nextCoord d = d)
    (hs : 4 ≤ d.r) :
    ∃ n : ℕ,
      steinerSlopeRat
          (coordClosingValuation d)
          d.r
        =
      steinerAlpha.convergent n := by
  have ha : 1 ≤ coordClosingValuation d :=
    coordClosingValuation_pos hd
  have hgap :
      0 <
        2 ^ (coordClosingValuation d + d.r) -
          3 ^ d.r :=
    Nat.sub_pos_of_lt (raw_fixed_gap_pos hd hfix)
  exact
    oneBlockGap_slope_is_convergent
      ha hs hgap
      (raw_fixed_gap_dvd_mersenne hd hfix)




theorem reduced_fixed_raw_slope_is_convergent
    {c : BlockCoord}
    (hc : c.Valid)
    (hfix : normalizedNextCoord c = c)
    (hs : 4 ≤ (nextCoord c).r) :
    ∃ n : ℕ,
      steinerSlopeRat
          (coordClosingValuation (nextCoord c))
          (nextCoord c).r
        =
      steinerAlpha.convergent n := by
  exact
    raw_fixed_slope_is_convergent
      (nextCoord_valid hc)
      (reduced_fixed_implies_raw_successor_fixed hc hfix)
      hs




theorem oneBlockGap_logarithmic_spec
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 4 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1) :
    0 <
      (((a + s : ℕ) : ℝ) / (s : ℝ)) -
        steinerAlpha
    ∧
    (((a + s : ℕ) : ℝ) / (s : ℝ)) -
        steinerAlpha
      <
    1 / (2 * (s : ℝ) ^ 2) := by
  exact oneBlockGap_legendre_bound ha hs hgap hdvd




theorem oneBlockGap_continued_fraction_spec
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 4 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1) :
    ∃ n : ℕ,
      steinerSlopeRat a s =
        steinerAlpha.convergent n := by
  exact oneBlockGap_slope_is_convergent ha hs hgap hdvd




theorem four_le_two_pow_of_two_le
    {a : ℕ}
    (ha : 2 ≤ a) :
    4 ≤ 2 ^ a := by
  induction a, ha using Nat.le_induction with
  | base =>
      norm_num
  | succ n hn ih =>
      rw [pow_succ]
      omega




theorem oneBlockGap_s_one
    {a : ℕ}
    (ha : 1 ≤ a)
    (hgap :
      0 < 2 ^ (a + 1) - 3)
    (hdvd :
      2 ^ (a + 1) - 3 ∣
        2 ^ a - 1) :
    a = 1 := by
  have hle :=
    oneBlockGap_le_mersenne
      ha (by norm_num : 1 ≤ 1) hgap hdvd
  by_contra hne
  have haTwo : 2 ≤ a := by omega
  have hFour := four_le_two_pow_of_two_le haTwo
  rw [pow_succ] at hle
  omega




theorem oneBlockGap_s_two_impossible
    {a : ℕ}
    (ha : 1 ≤ a)
    (hgap :
      0 < 2 ^ (a + 2) - 3 ^ 2)
    (hdvd :
      2 ^ (a + 2) - 3 ^ 2 ∣
        2 ^ a - 1) :
    False := by
  have haNe : a ≠ 1 := by
    intro haOne
    subst a
    norm_num at hgap
  have haTwo : 2 ≤ a := by omega
  have hFour := four_le_two_pow_of_two_le haTwo
  have hle :=
    oneBlockGap_le_mersenne
      ha (by norm_num : 1 ≤ 2) hgap hdvd
  rw [pow_add] at hle
  norm_num at hle
  omega




theorem oneBlockGap_s_three_impossible
    {a : ℕ}
    (ha : 1 ≤ a)
    (hgap :
      0 < 2 ^ (a + 3) - 3 ^ 3)
    (hdvd :
      2 ^ (a + 3) - 3 ^ 3 ∣
        2 ^ a - 1) :
    False := by
  have haNe : a ≠ 1 := by
    intro haOne
    subst a
    norm_num at hgap
  have haTwo : 2 ≤ a := by omega
  have hFour := four_le_two_pow_of_two_le haTwo
  have hle :=
    oneBlockGap_le_mersenne
      ha (by norm_num : 1 ≤ 3) hgap hdvd
  rw [pow_add] at hle
  norm_num at hle
  omega




theorem oneBlockGap_small_s_classification
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hspos : 1 ≤ s)
    (hs : s ≤ 3)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1) :
    a = 1 ∧ s = 1 := by
  have hcases : s = 1 ∨ s = 2 ∨ s = 3 := by
    omega
  rcases hcases with hsOne | hsTwo | hsThree
  · subst s
    exact ⟨oneBlockGap_s_one ha hgap hdvd, rfl⟩
  · subst s
    exact (oneBlockGap_s_two_impossible ha hgap hdvd).elim
  · subst s
    exact (oneBlockGap_s_three_impossible ha hgap hdvd).elim




theorem oneBlockGap_nontrivial_four_le_s
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1)) :
    4 ≤ s := by
  by_contra hFour
  have hsThree : s ≤ 3 := by omega
  exact hne
    (oneBlockGap_small_s_classification
      ha hs hsThree hgap hdvd)




theorem oneBlockGap_nontrivial_slope_is_convergent
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1)) :
    ∃ n : ℕ,
      steinerSlopeRat a s =
        steinerAlpha.convergent n := by
  have hsFour :=
    oneBlockGap_nontrivial_four_le_s
      ha hs hgap hdvd hne
  exact
    oneBlockGap_slope_is_convergent
      ha hsFour hgap hdvd




theorem oneBlockGap_trivial_or_convergent
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1) :
    (a = 1 ∧ s = 1)
    ∨
    ∃ n : ℕ,
      4 ≤ s ∧
      steinerSlopeRat a s =
        steinerAlpha.convergent n := by
  by_cases h : a = 1 ∧ s = 1
  · exact Or.inl h
  · right
    have hsFour :=
      oneBlockGap_nontrivial_four_le_s
        ha hs hgap hdvd h
    obtain ⟨n, hn⟩ :=
      oneBlockGap_nontrivial_slope_is_convergent
        ha hs hgap hdvd h
    exact ⟨n, hsFour, hn⟩




theorem raw_fixed_small_r_eq_oneCoord
    {d : BlockCoord}
    (hd : d.Valid)
    (hfix : nextCoord d = d)
    (hr : d.r ≤ 3) :
    d = oneCoord := by
  have hgap :
      0 <
        2 ^ (coordClosingValuation d + d.r) -
          3 ^ d.r :=
    Nat.sub_pos_of_lt (raw_fixed_gap_pos hd hfix)
  obtain ⟨haOne, hrOne⟩ :=
    oneBlockGap_small_s_classification
      (coordClosingValuation_pos hd)
      hd.1
      hr
      hgap
      (raw_fixed_gap_dvd_mersenne hd hfix)
  have hEq :=
    raw_fixed_diophantine_equation hd hfix
  rw [haOne, hrOne] at hEq
  norm_num at hEq
  have hqOne : d.q = 1 := by
    omega
  rw [oneCoord_eq]
  cases d
  simp_all




theorem raw_fixed_oneCoord_or_convergent
    {d : BlockCoord}
    (hd : d.Valid)
    (hfix : nextCoord d = d) :
    d = oneCoord
    ∨
    ∃ n : ℕ,
      4 ≤ d.r ∧
      steinerSlopeRat
          (coordClosingValuation d)
          d.r
        =
      steinerAlpha.convergent n := by
  by_cases hr : d.r ≤ 3
  · left
    exact raw_fixed_small_r_eq_oneCoord hd hfix hr
  · right
    have hrFour : 4 ≤ d.r := by omega
    obtain ⟨n, hn⟩ :=
      raw_fixed_slope_is_convergent hd hfix hrFour
    exact ⟨n, hrFour, hn⟩




theorem reduced_fixed_oneCoord_or_raw_convergent
    {c : BlockCoord}
    (hc : c.Valid)
    (hfix : normalizedNextCoord c = c) :
    c = oneCoord
    ∨
    ∃ n : ℕ,
      4 ≤ (nextCoord c).r ∧
      steinerSlopeRat
          (coordClosingValuation (nextCoord c))
          (nextCoord c).r
        =
      steinerAlpha.convergent n := by
  let d := nextCoord c
  have hd : d.Valid := by
    simpa [d] using nextCoord_valid hc
  have hdfix : nextCoord d = d := by
    simpa [d] using
      reduced_fixed_implies_raw_successor_fixed hc hfix
  rcases raw_fixed_oneCoord_or_convergent hd hdfix with
      hdOne | hConvergent
  · left
    have hnext : nextCoord c = oneCoord := by
      simpa [d] using hdOne
    have hnorm :
        normalizedNextCoord c = oneCoord := by
      unfold normalizedNextCoord
      rw [hnext, normalizeCoord_one]
    exact hfix.symm.trans hnorm
  · right
    simpa [d] using hConvergent




theorem reduced_fixed_nontrivial_raw_convergent
    {c : BlockCoord}
    (hc : c.Valid)
    (hfix : normalizedNextCoord c = c)
    (hne : c ≠ oneCoord) :
    ∃ n : ℕ,
      4 ≤ (nextCoord c).r ∧
      steinerSlopeRat
          (coordClosingValuation (nextCoord c))
          (nextCoord c).r
        =
      steinerAlpha.convergent n := by
  rcases
      reduced_fixed_oneCoord_or_raw_convergent hc hfix with
    hOne | hConvergent
  · exact (hne hOne).elim
  · exact hConvergent




theorem oneBlockGap_small_and_large_spec
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1) :
    (
      s ≤ 3 →
      a = 1 ∧ s = 1
    )
    ∧
    (
      ¬ (a = 1 ∧ s = 1) →
      ∃ n : ℕ,
        4 ≤ s ∧
        steinerSlopeRat a s =
          steinerAlpha.convergent n
    ) := by
  constructor
  · intro hsThree
    exact
      oneBlockGap_small_s_classification
        ha hs hsThree hgap hdvd
  · intro hne
    have hsFour :=
      oneBlockGap_nontrivial_four_le_s
        ha hs hgap hdvd hne
    obtain ⟨n, hn⟩ :=
      oneBlockGap_nontrivial_slope_is_convergent
        ha hs hgap hdvd hne
    exact ⟨n, hsFour, hn⟩




example :
    0 < 2 ^ (1 + 1) - 3 ^ 1 ∧
    (2 ^ (1 + 1) - 3 ^ 1) ∣
      2 ^ 1 - 1 := by
  norm_num




def steinerScale (a s : ℕ) : ℕ :=
  Nat.gcd a s




def steinerReducedA (a s : ℕ) : ℕ :=
  a / steinerScale a s




def steinerReducedS (a s : ℕ) : ℕ :=
  s / steinerScale a s




theorem steinerScale_pos
    {a s : ℕ}
    (ha : 1 ≤ a)
    (_hs : 1 ≤ s) :
    0 < steinerScale a s := by
  exact Nat.gcd_pos_of_pos_left s (by omega)




theorem steinerScale_mul_reducedA
    {a s : ℕ}
    (_ha : 1 ≤ a)
    (_hs : 1 ≤ s) :
    steinerScale a s * steinerReducedA a s = a := by
  exact
    Nat.mul_div_cancel' (Nat.gcd_dvd_left a s)




theorem steinerScale_mul_reducedS
    {a s : ℕ}
    (_ha : 1 ≤ a)
    (_hs : 1 ≤ s) :
    steinerScale a s * steinerReducedS a s = s := by
  exact
    Nat.mul_div_cancel' (Nat.gcd_dvd_right a s)




theorem steinerReducedA_pos
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s) :
    0 < steinerReducedA a s := by
  have hrec :=
    steinerScale_mul_reducedA ha hs
  have hg := steinerScale_pos ha hs
  by_contra hnot
  have hz : steinerReducedA a s = 0 :=
    Nat.eq_zero_of_not_pos hnot
  rw [hz, mul_zero] at hrec
  omega




theorem steinerReducedS_pos
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s) :
    0 < steinerReducedS a s := by
  have hrec :=
    steinerScale_mul_reducedS ha hs
  have hg := steinerScale_pos ha hs
  by_contra hnot
  have hz : steinerReducedS a s = 0 :=
    Nat.eq_zero_of_not_pos hnot
  rw [hz, mul_zero] at hrec
  omega




theorem steinerReduced_coprime
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s) :
    Nat.Coprime
      (steinerReducedA a s)
      (steinerReducedS a s) := by
  simpa [steinerReducedA, steinerReducedS, steinerScale] using
    Nat.coprime_div_gcd_div_gcd
      (steinerScale_pos ha hs)




theorem steinerReduced_sum_coprime_right
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s) :
    Nat.Coprime
      (steinerReducedA a s +
        steinerReducedS a s)
      (steinerReducedS a s) := by
  exact Nat.coprime_add_self_left.mpr
    (steinerReduced_coprime ha hs)




theorem steiner_reduced_slope_real
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s) :
    (((a + s : ℕ) : ℝ) / (s : ℝ))
      =
    ((steinerReducedA a s +
        steinerReducedS a s : ℕ) : ℝ) /
      (steinerReducedS a s : ℝ) := by
  have hAReal :
      (a : ℝ) =
        (steinerScale a s : ℝ) *
          (steinerReducedA a s : ℝ) := by
    exact_mod_cast
      (steinerScale_mul_reducedA ha hs).symm
  have hSReal :
      (s : ℝ) =
        (steinerScale a s : ℝ) *
          (steinerReducedS a s : ℝ) := by
    exact_mod_cast
      (steinerScale_mul_reducedS ha hs).symm
  have hgReal : 0 < (steinerScale a s : ℝ) := by
    exact_mod_cast steinerScale_pos ha hs
  have hvReal : 0 < (steinerReducedS a s : ℝ) := by
    exact_mod_cast steinerReducedS_pos ha hs
  rw [Nat.cast_add, Nat.cast_add, hAReal, hSReal]
  field_simp [ne_of_gt hgReal, ne_of_gt hvReal]




theorem steinerSlopeRat_reduced
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s) :
    steinerSlopeRat a s =
      Rat.divInt
        (Int.ofNat
          (steinerReducedA a s +
           steinerReducedS a s))
        (Int.ofNat
          (steinerReducedS a s)) := by
  apply Rat.cast_injective (α := ℝ)
  rw [steinerSlopeRat_cast hs, Rat.cast_divInt]
  norm_num
  simpa only [Nat.cast_add] using
    steiner_reduced_slope_real ha hs




theorem steinerSlopeRat_den_eq_reducedS
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s) :
    (steinerSlopeRat a s).den =
      steinerReducedS a s := by
  rw [steinerSlopeRat_reduced ha hs, Rat.den_divInt]
  have hvPos := steinerReducedS_pos ha hs
  have hCoprime :=
    steinerReduced_coprime ha hs
  have hGcd :
      Nat.gcd
        (steinerReducedS a s)
        (steinerReducedA a s) = 1 :=
    (Nat.coprime_comm.mp hCoprime).gcd_eq_one
  simp [ne_of_gt hvPos, hGcd]




theorem steinerSlopeRat_den_eq_div_gcd
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s) :
    (steinerSlopeRat a s).den =
      s / Nat.gcd a s := by
  simpa [steinerReducedS, steinerScale] using
    steinerSlopeRat_den_eq_reducedS ha hs




theorem oneBlockGap_scaled_equation
    {a s Q : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (heq :
      (2 ^ (a + s) - 3 ^ s) * Q =
        2 ^ a - 1) :
    (
      2 ^
        (steinerScale a s *
          (steinerReducedA a s +
           steinerReducedS a s))
      -
      3 ^
        (steinerScale a s *
          steinerReducedS a s)
    ) * Q
      =
    2 ^
        (steinerScale a s *
          steinerReducedA a s) - 1 := by
  rw [mul_add,
    steinerScale_mul_reducedA ha hs,
    steinerScale_mul_reducedS ha hs]
  exact heq




theorem oneBlockGap_scaled_power_equation
    {a s Q : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (heq :
      (2 ^ (a + s) - 3 ^ s) * Q =
        2 ^ a - 1) :
    (
      (2 ^
        (steinerReducedA a s +
         steinerReducedS a s)) ^
          steinerScale a s
      -
      (3 ^ steinerReducedS a s) ^
          steinerScale a s
    ) * Q
      =
    (2 ^ steinerReducedA a s) ^
        steinerScale a s - 1 := by
  rw [← pow_mul, ← pow_mul, ← pow_mul]
  simpa [mul_comm] using
    oneBlockGap_scaled_equation ha hs heq




theorem oneBlockGap_reduced_scale_bound
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1)) :
    abs (
      steinerAlpha -
        ((steinerReducedA a s +
            steinerReducedS a s : ℕ) : ℝ) /
          (steinerReducedS a s : ℝ)
    )
      <
    1 /
      (
        2 *
        (steinerScale a s : ℝ) ^ 2 *
        (steinerReducedS a s : ℝ) ^ 2
      ) := by
  have hsFour :=
    oneBlockGap_nontrivial_four_le_s
      ha hs hgap hdvd hne
  have hBound :=
    oneBlockGap_legendre_abs
      ha hsFour hgap hdvd
  have hSReal :
      (s : ℝ) =
        (steinerScale a s : ℝ) *
          (steinerReducedS a s : ℝ) := by
    exact_mod_cast
      (steinerScale_mul_reducedS ha hs).symm
  rw [← steiner_reduced_slope_real ha hs, hSReal]
  rw [hSReal] at hBound
  simpa [Nat.cast_add, mul_pow, mul_assoc] using hBound




theorem oneBlockGap_scale_den_bound
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1)) :
    abs (
      steinerAlpha -
        ((steinerSlopeRat a s : ℚ) : ℝ)
    )
      <
    1 /
      (
        2 *
        (steinerScale a s : ℝ) ^ 2 *
        ((steinerSlopeRat a s).den : ℝ) ^ 2
      ) := by
  rw [steinerSlopeRat_den_eq_reducedS ha hs]
  rw [steinerSlopeRat_cast hs]
  rw [steiner_reduced_slope_real ha hs]
  exact
    oneBlockGap_reduced_scale_bound
      ha hs hgap hdvd hne




theorem oneBlockGap_nontrivial_convergent_with_scale
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1)) :
    ∃ n : ℕ,
      steinerSlopeRat a s =
        steinerAlpha.convergent n
      ∧
      (steinerAlpha.convergent n).den =
        steinerReducedS a s
      ∧
      abs (
        steinerAlpha -
          ((steinerAlpha.convergent n : ℚ) : ℝ)
      )
        <
      1 /
        (
          2 *
          (steinerScale a s : ℝ) ^ 2 *
          ((steinerAlpha.convergent n).den : ℝ) ^ 2
        ) := by
  obtain ⟨n, hn⟩ :=
    oneBlockGap_nontrivial_slope_is_convergent
      ha hs hgap hdvd hne
  refine ⟨n, hn, ?_, ?_⟩
  · rw [← hn]
    exact steinerSlopeRat_den_eq_reducedS ha hs
  · rw [← hn]
    exact oneBlockGap_scale_den_bound
      ha hs hgap hdvd hne




theorem oneBlockGap_gcd_reduction_spec
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s) :
    0 < steinerScale a s
    ∧
    0 < steinerReducedA a s
    ∧
    0 < steinerReducedS a s
    ∧
    Nat.Coprime
      (steinerReducedA a s)
      (steinerReducedS a s)
    ∧
    steinerScale a s *
        steinerReducedA a s = a
    ∧
    steinerScale a s *
        steinerReducedS a s = s
    ∧
    (steinerSlopeRat a s).den =
        steinerReducedS a s := by
  exact
    ⟨steinerScale_pos ha hs,
     steinerReducedA_pos ha hs,
     steinerReducedS_pos ha hs,
     steinerReduced_coprime ha hs,
     steinerScale_mul_reducedA ha hs,
     steinerScale_mul_reducedS ha hs,
     steinerSlopeRat_den_eq_reducedS ha hs⟩




theorem raw_fixed_nontrivial_params_nontrivial
    {d : BlockCoord}
    (hd : d.Valid)
    (hfix : nextCoord d = d)
    (hne : d ≠ oneCoord) :
    ¬ (
      coordClosingValuation d = 1 ∧
      d.r = 1
    ) := by
  rintro ⟨haOne, hrOne⟩
  have hEq :=
    raw_fixed_diophantine_equation hd hfix
  rw [haOne, hrOne] at hEq
  norm_num at hEq
  have hqOne : d.q = 1 := by
    omega
  apply hne
  rw [oneCoord_eq]
  cases d
  simp_all




theorem raw_fixed_nontrivial_gcd_convergent_spec
    {d : BlockCoord}
    (hd : d.Valid)
    (hfix : nextCoord d = d)
    (hne : d ≠ oneCoord) :
    ∃ n : ℕ,
      steinerSlopeRat
          (coordClosingValuation d)
          d.r
        =
      steinerAlpha.convergent n
    ∧
      (steinerAlpha.convergent n).den =
        steinerReducedS
          (coordClosingValuation d)
          d.r
    ∧
      abs (
        steinerAlpha -
          ((steinerAlpha.convergent n : ℚ) : ℝ)
      )
        <
      1 /
        (
          2 *
          (steinerScale
            (coordClosingValuation d)
            d.r : ℝ) ^ 2 *
          ((steinerAlpha.convergent n).den : ℝ) ^ 2
        ) := by
  have ha : 1 ≤ coordClosingValuation d :=
    coordClosingValuation_pos hd
  have hgap :
      0 <
        2 ^ (coordClosingValuation d + d.r) -
          3 ^ d.r :=
    Nat.sub_pos_of_lt (raw_fixed_gap_pos hd hfix)
  exact
    oneBlockGap_nontrivial_convergent_with_scale
      ha hd.1 hgap
      (raw_fixed_gap_dvd_mersenne hd hfix)
      (raw_fixed_nontrivial_params_nontrivial hd hfix hne)




example :
    steinerScale 1 1 = 1
    ∧
    steinerReducedA 1 1 = 1
    ∧
    steinerReducedS 1 1 = 1
    ∧
    (steinerSlopeRat 1 1).den = 1 := by
  norm_num [steinerScale, steinerReducedA,
    steinerReducedS, steinerSlopeRat, Rat.den_divInt]












/-!
Lower bound local para convergentes y salto de denominadores.
La prueba usa sólo no terminación en el índice concreto; no presupone
irracionalidad global de steinerAlpha.
-/




noncomputable def steinerConvDen (n : ℕ) : ℕ :=
  (steinerAlpha.convergent n).den




theorem steinerConvDen_pos (n : ℕ) :
    0 < steinerConvDen n := by
  exact Rat.den_pos _




theorem steinerConvDen_cast_pos (n : ℕ) :
    (0 : ℝ) < (steinerConvDen n : ℝ) := by
  exact_mod_cast steinerConvDen_pos n




theorem steiner_gcf_convs_eq_convergent
    (n : ℕ) :
    (GenContFract.of steinerAlpha).convs n =
      ((steinerAlpha.convergent n : ℚ) : ℝ) := by
  exact Real.convs_eq_convergent steinerAlpha n




theorem gcf_not_terminatedAt_of_ne_convergent
    {x : ℝ} {n : ℕ}
    (hne :
      x ≠ (GenContFract.of x).convs n) :
    ¬ (GenContFract.of x).TerminatedAt n := by
  intro hterm
  exact hne (GenContFract.of_correctness_of_terminatedAt hterm)




theorem exists_stream_data_of_ne_convergent
    {x : ℝ} {n : ℕ}
    (hne :
      x ≠ (GenContFract.of x).convs n) :
    ∃ ifp : GenContFract.IntFractPair ℝ,
      GenContFract.IntFractPair.stream x n =
        some ifp
      ∧
      ifp.fr ≠ 0 := by
  have hnot :=
    gcf_not_terminatedAt_of_ne_convergent hne
  have hsucc :
      GenContFract.IntFractPair.stream x (n + 1) ≠ none := by
    intro hnone
    exact hnot
      ((GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none).2
        hnone)
  cases hs :
      GenContFract.IntFractPair.stream x n with
  | none =>
      exfalso
      apply hsucc
      exact (GenContFract.IntFractPair.stream_isSeq x) hs
  | some ifp =>
      refine ⟨ifp, rfl, ?_⟩
      intro hfr
      apply hsucc
      simp only [GenContFract.IntFractPair.stream]
      rw [hs]
      simp [hfr]




theorem gcf_den_pos_of_ne_convergent
    {x : ℝ} {n : ℕ}
    (hne :
      x ≠ (GenContFract.of x).convs n) :
    0 < (GenContFract.of x).dens n := by
  have hnot :=
    gcf_not_terminatedAt_of_ne_convergent hne
  have hhyp :
      n = 0 ∨
        ¬ (GenContFract.of x).TerminatedAt (n - 1) := by
    by_cases hn : n = 0
    · exact Or.inl hn
    · right
      intro hterm
      exact hnot
        (GenContFract.terminated_stable
          (Nat.sub_le n 1) hterm)
  have hFib :=
    GenContFract.succ_nth_fib_le_of_nth_den
      (v := x) hhyp
  have hFibPos :
      (0 : ℝ) < Nat.fib (n + 1) := by
    exact_mod_cast (Nat.fib_pos.mpr (by omega : 0 < n + 1))
  linarith












theorem gcf_dens_succ_eq_floor_recurrence
    {x : ℝ} {n : ℕ}
    {ifp : GenContFract.IntFractPair ℝ}
    (hs :
      GenContFract.IntFractPair.stream x n =
        some ifp)
    (hfr : ifp.fr ≠ 0) :
    (GenContFract.of x).dens (n + 1) =
      ((GenContFract.IntFractPair.of ifp.fr⁻¹).b : ℝ) *
        (GenContFract.of x).dens n +
      ((GenContFract.of x).contsAux n).b := by
  have hget :=
    GenContFract.get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero
      hs hfr
  change
    ((GenContFract.of x).contsAux (n + 2)).b =
      ((GenContFract.IntFractPair.of ifp.fr⁻¹).b : ℝ) *
        ((GenContFract.of x).contsAux (n + 1)).b +
      ((GenContFract.of x).contsAux n).b
  rw [show n + 2 = Nat.succ (Nat.succ n) by omega]
  simp only [GenContFract.contsAux]
  rw [hget]
  simp [GenContFract.nextConts, GenContFract.nextDen]












theorem gcf_convergent_error_lower
    {x : ℝ} {n : ℕ}
    (hne :
      x ≠ (GenContFract.of x).convs n) :
    1 /
      (
        (GenContFract.of x).dens n *
        (
          (GenContFract.of x).dens n +
          (GenContFract.of x).dens (n + 1)
        )
      )
      <
    abs (
      x - (GenContFract.of x).convs n
    ) := by
  obtain ⟨ifp, hs, hfr⟩ :=
    exists_stream_data_of_ne_convergent hne
  let B : ℝ := (GenContFract.of x).dens n
  let pB : ℝ := ((GenContFract.of x).contsAux n).b
  let b : ℝ :=
    ((GenContFract.IntFractPair.of ifp.fr⁻¹).b : ℝ)
  have hB : 0 < B := by
    exact gcf_den_pos_of_ne_convergent hne
  have hpB : 0 ≤ pB := by
    exact GenContFract.zero_le_of_contsAux_b
  have hfr_nonneg : 0 ≤ ifp.fr :=
    GenContFract.IntFractPair.nth_stream_fr_nonneg hs
  have hfr_pos : 0 < ifp.fr := by
    exact lt_of_le_of_ne hfr_nonneg (Ne.symm hfr)
  have hinv_pos : 0 < ifp.fr⁻¹ :=
    inv_pos.mpr hfr_pos
  have hfloor : ifp.fr⁻¹ < b + 1 := by
    change
      ifp.fr⁻¹ <
        ((⌊ifp.fr⁻¹⌋ : ℤ) : ℝ) + 1
    exact Int.lt_floor_add_one ifp.fr⁻¹
  have hdens :
      (GenContFract.of x).dens (n + 1) =
        b * B + pB := by
    simpa [b, B, pB] using
      gcf_dens_succ_eq_floor_recurrence hs hfr
  have hinner :
      ifp.fr⁻¹ * B + pB <
        (GenContFract.of x).dens (n + 1) + B := by
    calc
      ifp.fr⁻¹ * B + pB <
          (b + 1) * B + pB := by
            nlinarith [mul_lt_mul_of_pos_right hfloor hB]
      _ = (b * B + pB) + B := by ring
      _ = (GenContFract.of x).dens (n + 1) + B := by
            rw [hdens]
  have hinner_pos :
      0 < ifp.fr⁻¹ * B + pB := by
    positivity
  have hprod_pos :
      0 < B * (ifp.fr⁻¹ * B + pB) :=
    mul_pos hB hinner_pos
  have hprod_lt :
      B * (ifp.fr⁻¹ * B + pB) <
        B *
          (B + (GenContFract.of x).dens (n + 1)) := by
    apply mul_lt_mul_of_pos_left _ hB
    nlinarith [hinner]
  change
    1 / (B * (B + (GenContFract.of x).dens (n + 1))) <
      abs (x - (GenContFract.of x).convs n)
  have herr := GenContFract.sub_convs_eq hs
  simp [hfr] at herr
  rw [herr]
  change
    1 / (B * (B + (GenContFract.of x).dens (n + 1))) <
      abs (((-1 : ℝ) ^ n) /
        (B * (ifp.fr⁻¹ * B + pB)))
  rw [abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos hprod_pos]
  exact one_div_lt_one_div_of_lt hprod_pos hprod_lt












theorem gcf_of_contsAux_exists_int
    (x : ℝ) (n : ℕ) :
    ∃ A B : ℤ,
      (GenContFract.of x).contsAux n =
        { a := (A : ℝ), b := (B : ℝ) } := by
  induction n using Nat.twoStepInduction with
  | zero =>
      exact ⟨1, 0, by simp⟩
  | one =>
      refine ⟨⌊x⌋, 1, ?_⟩
      rw [GenContFract.first_contAux_eq_h_one]
      simp [GenContFract.of, GenContFract.IntFractPair.seq1,
        GenContFract.IntFractPair.of]
  | more n ih0 ih1 =>
      cases hs : (GenContFract.of x).s.get? n with
      | none =>
          obtain ⟨A, B, hAB⟩ := ih1
          refine ⟨A, B, ?_⟩
          rw [show n + 2 = Nat.succ (Nat.succ n) by omega]
          simp only [GenContFract.contsAux]
          rw [hs]
          exact hAB
      | some gp =>
          obtain ⟨A0, B0, h0⟩ := ih0
          obtain ⟨A1, B1, h1⟩ := ih1
          obtain ⟨ha, z, hb⟩ :=
            GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq
              hs
          refine
            ⟨z * A1 + A0, z * B1 + B0, ?_⟩
          rw [show n + 2 = Nat.succ (Nat.succ n) by omega]
          simp only [GenContFract.contsAux]
          rw [hs]
          change
            GenContFract.nextConts gp.a gp.b
              ((GenContFract.of x).contsAux n)
              ((GenContFract.of x).contsAux (n + 1)) =
            { a := ((z * A1 + A0 : ℤ) : ℝ),
              b := ((z * B1 + B0 : ℤ) : ℝ) }
          rw [ha, hb, h0, h1]
          simp [GenContFract.nextConts, GenContFract.nextNum,
            GenContFract.nextDen]












theorem gcf_of_num_den_exists_int
    (x : ℝ) (n : ℕ) :
    ∃ A B : ℤ,
      (GenContFract.of x).nums n = (A : ℝ) ∧
      (GenContFract.of x).dens n = (B : ℝ) := by
  obtain ⟨A, B, hAB⟩ :=
    gcf_of_contsAux_exists_int x (n + 1)
  refine ⟨A, B, ?_, ?_⟩
  · rw [GenContFract.num_eq_conts_a,
      GenContFract.nth_cont_eq_succ_nth_contAux]
    rw [hAB]
  · rw [GenContFract.den_eq_conts_b,
      GenContFract.nth_cont_eq_succ_nth_contAux]
    rw [hAB]












theorem gcf_of_num_den_reduced
    {x : ℝ} {n : ℕ}
    (hne :
      x ≠ (GenContFract.of x).convs n) :
    ∃ A B : ℤ,
      (GenContFract.of x).nums n = (A : ℝ)
      ∧
      (GenContFract.of x).dens n = (B : ℝ)
      ∧
      B.gcd A = 1
      ∧
      0 < B := by
  obtain ⟨A, B, hA, hB⟩ :=
    gcf_of_num_den_exists_int x n
  obtain ⟨A1, B1, hA1, hB1⟩ :=
    gcf_of_num_den_exists_int x (n + 1)
  have hnot :=
    gcf_not_terminatedAt_of_ne_convergent hne
  have hdet :=
    SimpContFract.determinant
      (s := SimpContFract.of x) hnot
  change
    (GenContFract.of x).nums n *
        (GenContFract.of x).dens (n + 1) -
      (GenContFract.of x).dens n *
        (GenContFract.of x).nums (n + 1) =
      (-1 : ℝ) ^ (n + 1) at hdet
  rw [hA, hB, hA1, hB1] at hdet
  have hdetZ :
      A * B1 - B * A1 =
        (-1 : ℤ) ^ (n + 1) := by
    exact_mod_cast hdet
  have hgcd : B.gcd A = 1 := by
    rw [Int.gcd_eq_one_iff]
    intro c hcB hcA
    have hd :
        c ∣ A * B1 - B * A1 :=
      dvd_sub
        (dvd_mul_of_dvd_left hcA B1)
        (dvd_mul_of_dvd_left hcB A1)
    rw [hdetZ] at hd
    rcases neg_one_pow_eq_or ℤ (n + 1) with hp | hp
    · rwa [hp] at hd
    · rw [hp] at hd
      exact (dvd_neg.mp hd)
  have hBpos : 0 < B := by
    have hreal :=
      gcf_den_pos_of_ne_convergent hne
    rw [hB] at hreal
    exact_mod_cast hreal
  exact ⟨A, B, hA, hB, hgcd, hBpos⟩












theorem gcf_den_eq_rat_den_of_convergent
    {x : ℝ} {n : ℕ}
    (hne :
      x ≠ (GenContFract.of x).convs n) :
    (GenContFract.of x).dens n =
      (((x.convergent n).den : ℕ) : ℝ) := by
  obtain ⟨A, B, hA, hB, hgcd, hBpos⟩ :=
    gcf_of_num_den_reduced hne
  have hcast :
      ((x.convergent n : ℚ) : ℝ) =
        (A : ℝ) / (B : ℝ) := by
    rw [← Real.convs_eq_convergent x n,
      GenContFract.conv_eq_num_div_den, hA, hB]
  have hrat :
      x.convergent n = Rat.divInt A B := by
    apply Rat.cast_injective (α := ℝ)
    rw [Rat.cast_divInt]
    exact hcast
  rw [hB, hrat, Rat.den_divInt]
  have hBne : B ≠ 0 := ne_of_gt hBpos
  simp [hBne, hgcd]
  have hBposR : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast hBpos
  exact (abs_of_pos hBposR).symm












theorem gcf_of_succ_num_den_reduced
    {x : ℝ} {n : ℕ}
    (hne :
      x ≠ (GenContFract.of x).convs n) :
    ∃ A B : ℤ,
      (GenContFract.of x).nums (n + 1) = (A : ℝ)
      ∧
      (GenContFract.of x).dens (n + 1) = (B : ℝ)
      ∧
      B.gcd A = 1
      ∧
      0 < B := by
  obtain ⟨A0, B0, hA0, hB0⟩ :=
    gcf_of_num_den_exists_int x n
  obtain ⟨A, B, hA, hB⟩ :=
    gcf_of_num_den_exists_int x (n + 1)
  have hnot :=
    gcf_not_terminatedAt_of_ne_convergent hne
  have hdet :=
    SimpContFract.determinant
      (s := SimpContFract.of x) hnot
  change
    (GenContFract.of x).nums n *
        (GenContFract.of x).dens (n + 1) -
      (GenContFract.of x).dens n *
        (GenContFract.of x).nums (n + 1) =
      (-1 : ℝ) ^ (n + 1) at hdet
  rw [hA0, hB0, hA, hB] at hdet
  have hdetZ :
      A0 * B - B0 * A =
        (-1 : ℤ) ^ (n + 1) := by
    exact_mod_cast hdet
  have hgcd : B.gcd A = 1 := by
    rw [Int.gcd_eq_one_iff]
    intro c hcB hcA
    have hd :
        c ∣ A0 * B - B0 * A :=
      dvd_sub
        (dvd_mul_of_dvd_right hcB A0)
        (dvd_mul_of_dvd_right hcA B0)
    rw [hdetZ] at hd
    rcases neg_one_pow_eq_or ℤ (n + 1) with hp | hp
    · rwa [hp] at hd
    · rw [hp] at hd
      exact dvd_neg.mp hd
  have hB0pos : 0 < B0 := by
    have hreal :=
      gcf_den_pos_of_ne_convergent hne
    rw [hB0] at hreal
    exact_mod_cast hreal
  have hmono :=
    GenContFract.of_den_mono (v := x) (n := n)
  rw [hB0, hB] at hmono
  have hBpos : 0 < B := by
    exact_mod_cast (lt_of_lt_of_le hB0pos
      (by exact_mod_cast hmono))
  exact ⟨A, B, hA, hB, hgcd, hBpos⟩




theorem gcf_succ_den_eq_rat_den_of_convergent
    {x : ℝ} {n : ℕ}
    (hne :
      x ≠ (GenContFract.of x).convs n) :
    (GenContFract.of x).dens (n + 1) =
      (((x.convergent (n + 1)).den : ℕ) : ℝ) := by
  obtain ⟨A, B, hA, hB, hgcd, hBpos⟩ :=
    gcf_of_succ_num_den_reduced hne
  have hcast :
      ((x.convergent (n + 1) : ℚ) : ℝ) =
        (A : ℝ) / (B : ℝ) := by
    rw [← Real.convs_eq_convergent x (n + 1),
      GenContFract.conv_eq_num_div_den, hA, hB]
  have hrat :
      x.convergent (n + 1) = Rat.divInt A B := by
    apply Rat.cast_injective (α := ℝ)
    rw [Rat.cast_divInt]
    exact hcast
  rw [hB, hrat, Rat.den_divInt]
  have hBne : B ≠ 0 := ne_of_gt hBpos
  simp [hBne, hgcd]
  have hBposR : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast hBpos
  exact (abs_of_pos hBposR).symm












theorem real_convergent_error_lower
    {x : ℝ} {n : ℕ}
    (hne :
      x ≠ ((x.convergent n : ℚ) : ℝ)) :
    1 /
      (
        ((x.convergent n).den : ℝ) *
        (
          ((x.convergent n).den : ℝ) +
          ((x.convergent (n + 1)).den : ℝ)
        )
      )
      <
    abs (
      x - ((x.convergent n : ℚ) : ℝ)
    ) := by
  have hneG :
      x ≠ (GenContFract.of x).convs n := by
    simpa only [Real.convs_eq_convergent] using hne
  have hlow :=
    gcf_convergent_error_lower hneG
  rw [gcf_den_eq_rat_den_of_convergent hneG,
    gcf_succ_den_eq_rat_den_of_convergent hneG,
    Real.convs_eq_convergent] at hlow
  exact hlow




theorem oneBlockGap_convergent_ne_alpha
    {a s n : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (_hne : ¬ (a = 1 ∧ s = 1))
    (hn :
      steinerSlopeRat a s =
        steinerAlpha.convergent n) :
    steinerAlpha ≠
      ((steinerAlpha.convergent n : ℚ) : ℝ) := by
  intro heq
  have hpos :=
    (oneBlockGap_steiner_approx ha hs hgap hdvd).1
  have hcast :=
    steinerSlopeRat_cast (a := a) (s := s) hs
  have hnCast :
      ((steinerSlopeRat a s : ℚ) : ℝ) =
        ((steinerAlpha.convergent n : ℚ) : ℝ) :=
    congrArg (fun q : ℚ => (q : ℝ)) hn
  have hslope :
      (((a + s : ℕ) : ℝ) / (s : ℝ)) =
        steinerAlpha := by
    calc
      (((a + s : ℕ) : ℝ) / (s : ℝ)) =
          ((steinerSlopeRat a s : ℚ) : ℝ) :=
        hcast.symm
      _ = ((steinerAlpha.convergent n : ℚ) : ℝ) :=
        hnCast
      _ = steinerAlpha := heq.symm
  rw [hslope] at hpos
  linarith




theorem oneBlockGap_convergent_error_lower
    {a s n : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1))
    (hn :
      steinerSlopeRat a s =
        steinerAlpha.convergent n) :
    1 /
      (
        ((steinerAlpha.convergent n).den : ℝ) *
        (
          ((steinerAlpha.convergent n).den : ℝ) +
          ((steinerAlpha.convergent (n + 1)).den : ℝ)
        )
      )
      <
    abs (
      steinerAlpha -
        ((steinerAlpha.convergent n : ℚ) : ℝ)
    ) := by
  exact real_convergent_error_lower
    (oneBlockGap_convergent_ne_alpha
      ha hs hgap hdvd hne hn)












theorem oneBlockGap_next_denominator_large
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1)) :
    ∃ n : ℕ,
      steinerSlopeRat a s =
        steinerAlpha.convergent n
      ∧
      (steinerAlpha.convergent n).den =
        steinerReducedS a s
      ∧
      (
        (2 * steinerScale a s ^ 2 - 1) *
          (steinerAlpha.convergent n).den
        <
          (steinerAlpha.convergent (n + 1)).den
      ) := by
  obtain ⟨n, hn, hden, hupp⟩ :=
    oneBlockGap_nontrivial_convergent_with_scale
      ha hs hgap hdvd hne
  have hlow :=
    oneBlockGap_convergent_error_lower
      ha hs hgap hdvd hne hn
  have hfrac := lt_trans hlow hupp
  let q : ℕ := (steinerAlpha.convergent n).den
  let qnext : ℕ :=
    (steinerAlpha.convergent (n + 1)).den
  let g : ℕ := steinerScale a s
  have hq : 0 < q := by
    exact Rat.den_pos _
  have hqnext : 0 < qnext := by
    exact Rat.den_pos _
  have hg : 0 < g := by
    exact steinerScale_pos ha hs
  change
    1 / ((q : ℝ) * ((q : ℝ) + (qnext : ℝ))) <
      1 /
        (2 * (g : ℝ) ^ 2 * (q : ℝ) ^ 2) at hfrac
  have hDleft :
      (0 : ℝ) <
        (q : ℝ) * ((q : ℝ) + (qnext : ℝ)) := by
    positivity
  have hDright :
      (0 : ℝ) <
        2 * (g : ℝ) ^ 2 * (q : ℝ) ^ 2 := by
    positivity
  have hdenR :
      2 * (g : ℝ) ^ 2 * (q : ℝ) ^ 2 <
        (q : ℝ) * ((q : ℝ) + (qnext : ℝ)) := by
    have h :=
      (div_lt_div_iff₀ hDleft hDright).mp hfrac
    simpa only [one_mul] using h
  have hqR : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast hq
  have hmul :
      (q : ℝ) * (2 * (g : ℝ) ^ 2 * (q : ℝ)) <
        (q : ℝ) * ((q : ℝ) + (qnext : ℝ)) := by
    nlinarith [hdenR]
  have hlinearR :
      2 * (g : ℝ) ^ 2 * (q : ℝ) <
        (q : ℝ) + (qnext : ℝ) := by
    nlinarith [hmul, hqR]
  have hlinear :
      2 * g ^ 2 * q < q + qnext := by
    exact_mod_cast hlinearR
  have hfactor : 1 ≤ 2 * g ^ 2 := by
    nlinarith [hg]
  have hsplit :
      (2 * g ^ 2 - 1) * q + q =
        2 * g ^ 2 * q := by
    calc
      (2 * g ^ 2 - 1) * q + q =
          ((2 * g ^ 2 - 1) + 1) * q := by
            rw [add_mul, one_mul]
      _ = 2 * g ^ 2 * q := by
            rw [Nat.sub_add_cancel hfactor]
  refine ⟨n, hn, hden, ?_⟩
  change (2 * g ^ 2 - 1) * q < qnext
  omega




theorem oneBlockGap_next_denominator_large_reduced
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1)) :
    ∃ n : ℕ,
      steinerSlopeRat a s =
        steinerAlpha.convergent n
      ∧
      (steinerAlpha.convergent n).den =
        steinerReducedS a s
      ∧
      (2 * steinerScale a s ^ 2 - 1) *
          steinerReducedS a s
        <
      (steinerAlpha.convergent (n + 1)).den := by
  obtain ⟨n, hn, hden, hjump⟩ :=
    oneBlockGap_next_denominator_large
      ha hs hgap hdvd hne
  refine ⟨n, hn, hden, ?_⟩
  rwa [hden] at hjump












theorem raw_fixed_nontrivial_next_convergent_den_large
    {d : BlockCoord}
    (hd : d.Valid)
    (hfix : nextCoord d = d)
    (hne : d ≠ oneCoord) :
    ∃ n : ℕ,
      steinerSlopeRat
          (coordClosingValuation d)
          d.r
        =
      steinerAlpha.convergent n
      ∧
      (
        2 *
          steinerScale
            (coordClosingValuation d)
            d.r ^ 2
        - 1
      ) *
        (steinerAlpha.convergent n).den
      <
        (steinerAlpha.convergent (n + 1)).den := by
  obtain ⟨n, hn, _hden, hjump⟩ :=
    oneBlockGap_next_denominator_large
      (coordClosingValuation_pos hd)
      hd.1
      (Nat.sub_pos_of_lt
        (raw_fixed_gap_pos hd hfix))
      (raw_fixed_gap_dvd_mersenne hd hfix)
      (raw_fixed_nontrivial_params_nontrivial
        hd hfix hne)
  exact ⟨n, hn, hjump⟩




theorem oneBlockGap_denominator_jump_spec
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1)) :
    ∃ n : ℕ,
      steinerSlopeRat a s =
        steinerAlpha.convergent n
      ∧
      (steinerAlpha.convergent n).den =
        steinerReducedS a s
      ∧
      (2 * steinerScale a s ^ 2 - 1) *
          steinerReducedS a s
        <
      (steinerAlpha.convergent (n + 1)).den := by
  exact oneBlockGap_next_denominator_large_reduced
    ha hs hgap hdvd hne




/-
The denominator jump is independent of any global irrationality proof:
the concrete Steiner candidate has strictly positive error, hence its
continued fraction is locally nonterminal at the selected index.




The optional partial-quotient corollary is intentionally postponed.
Mathlib indexes the coefficient carrying q_n to q_(n+1) through
partDens.get? n, while the available monotonicity lemma gives only
A*q_n <= q_(n+1).  A certified upper recurrence involving q_(n-1)
and its exact index is still needed before stating A >= 2*g^2-1.
-/
 
 
/-
Exact indexing convention: `partDens.get? n` is the coefficient used in
the transition from `dens n` to `dens (n + 1)`.
-/




theorem gcf_partDen_controls_next_den
    {x : ℝ} {n : ℕ} {b : ℝ}
    (hb :
      (GenContFract.of x).partDens.get? n =
        some b) :
    b * (GenContFract.of x).dens n ≤
      (GenContFract.of x).dens (n + 1) := by
  exact GenContFract.le_of_succ_get?_den hb




theorem gcf_exists_partDen_of_ne_convergent
    {x : ℝ} {n : ℕ}
    (hne :
      x ≠ (GenContFract.of x).convs n) :
    ∃ b : ℝ,
      (GenContFract.of x).partDens.get? n =
        some b := by
  obtain ⟨ifp, hs, hfr⟩ :=
    exists_stream_data_of_ne_convergent hne
  have hget :=
    GenContFract.get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero
      hs hfr
  refine ⟨((GenContFract.IntFractPair.of ifp.fr⁻¹).b : ℝ), ?_⟩
  exact GenContFract.partDen_eq_s_b hget




theorem gcf_exists_nat_partDen_of_ne_convergent
    {x : ℝ} {n : ℕ}
    (hne :
      x ≠ (GenContFract.of x).convs n) :
    ∃ A : ℕ,
      1 ≤ A ∧
      (GenContFract.of x).partDens.get? n =
        some (A : ℝ) := by
  obtain ⟨b, hb⟩ :=
    gcf_exists_partDen_of_ne_convergent hne
  obtain ⟨z, hz⟩ :=
    GenContFract.exists_int_eq_of_partDen hb
  have hbOne : (1 : ℝ) ≤ b :=
    GenContFract.of_one_le_get?_partDen hb
  have hzOne : (1 : ℤ) ≤ z := by
    rw [hz] at hbOne
    exact_mod_cast hbOne
  have hzNonneg : 0 ≤ z := by omega
  refine ⟨z.toNat, ?_, ?_⟩
  · have hzNat : (z.toNat : ℤ) = z :=
      Int.toNat_of_nonneg hzNonneg
    omega
  · have hzNat : (z.toNat : ℤ) = z :=
      Int.toNat_of_nonneg hzNonneg
    have hcast : ((z.toNat : ℕ) : ℝ) = b := by
      rw [hz]
      exact_mod_cast hzNat
    simpa only [hcast] using hb




noncomputable def gcfPrevDen (x : ℝ) (n : ℕ) : ℝ :=
  ((GenContFract.of x).contsAux n).b




theorem gcf_den_eq_succ_contsAux_b
    (x : ℝ) (n : ℕ) :
    (GenContFract.of x).dens n =
      ((GenContFract.of x).contsAux (n + 1)).b := by
  rw [GenContFract.den_eq_conts_b,
    GenContFract.nth_cont_eq_succ_nth_contAux]




theorem gcf_prevDen_nonneg
    (x : ℝ) (n : ℕ) :
    0 ≤ gcfPrevDen x n := by
  exact GenContFract.zero_le_of_contsAux_b




theorem gcf_next_den_exact
    {x : ℝ} {n A : ℕ}
    (hA :
      (GenContFract.of x).partDens.get? n =
        some (A : ℝ)) :
    (GenContFract.of x).dens (n + 1)
      =
    (A : ℝ) * (GenContFract.of x).dens n +
      gcfPrevDen x n := by
  obtain ⟨gp, hgp, hgb⟩ :=
    GenContFract.exists_s_b_of_partDen hA
  have hpa :
      (GenContFract.of x).partNums.get? n =
        some gp.a :=
    GenContFract.partNum_eq_s_a hgp
  have hga : gp.a = 1 :=
    GenContFract.of_partNum_eq_one hpa
  change
    ((GenContFract.of x).contsAux (n + 2)).b =
      (A : ℝ) *
        ((GenContFract.of x).contsAux (n + 1)).b +
      ((GenContFract.of x).contsAux n).b
  rw [show n + 2 = Nat.succ (Nat.succ n) by omega]
  simp only [GenContFract.contsAux]
  rw [hgp]
  simp [GenContFract.nextConts, GenContFract.nextDen,
    hga, hgb]




theorem gcf_prevDen_le_den
    {x : ℝ} {n : ℕ} :
    gcfPrevDen x n ≤
      (GenContFract.of x).dens n := by
  cases n with
  | zero =>
      simp [gcfPrevDen]
  | succ m =>
      change
        ((GenContFract.of x).contsAux (m + 1)).b ≤
          (GenContFract.of x).dens (m + 1)
      rw [← gcf_den_eq_succ_contsAux_b x m]
      exact GenContFract.of_den_mono




theorem gcf_next_den_le_partDen_add_one
    {x : ℝ} {n A : ℕ}
    (hA :
      (GenContFract.of x).partDens.get? n =
        some (A : ℝ)) :
    (GenContFract.of x).dens (n + 1)
      ≤
    (A + 1 : ℝ) *
      (GenContFract.of x).dens n := by
  rw [gcf_next_den_exact hA]
  calc
    (A : ℝ) * (GenContFract.of x).dens n +
          gcfPrevDen x n
        ≤
      (A : ℝ) * (GenContFract.of x).dens n +
          (GenContFract.of x).dens n := by
            have hp := gcf_prevDen_le_den (x := x) (n := n)
            linarith
    _ = (A + 1 : ℝ) *
          (GenContFract.of x).dens n := by ring








theorem real_next_convergent_den_le_partDen_add_one
    {x : ℝ} {n A : ℕ}
    (hne :
      x ≠ ((x.convergent n : ℚ) : ℝ))
    (hA :
      (GenContFract.of x).partDens.get? n =
        some (A : ℝ)) :
    (x.convergent (n + 1)).den
      ≤
    (A + 1) * (x.convergent n).den := by
  have hneG :
      x ≠ (GenContFract.of x).convs n := by
    simpa only [Real.convs_eq_convergent] using hne
  have hreal :=
    gcf_next_den_le_partDen_add_one hA
  rw [gcf_succ_den_eq_rat_den_of_convergent hneG,
    gcf_den_eq_rat_den_of_convergent hneG] at hreal
  exact_mod_cast hreal




theorem partialQuotient_large_of_den_jump
    {L A q qnext : ℕ}
    (_hq : 0 < q)
    (hjump : L * q < qnext)
    (hupper : qnext ≤ (A + 1) * q) :
    L ≤ A := by
  by_contra hLA
  have hAL : A + 1 ≤ L := by omega
  have hmul : (A + 1) * q ≤ L * q :=
    Nat.mul_le_mul_right q hAL
  omega




theorem oneBlockGap_partial_quotient_recurrence_spec
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1)) :
    ∃ n A : ℕ,
      steinerSlopeRat a s =
        steinerAlpha.convergent n
      ∧
      (steinerAlpha.convergent n).den =
        steinerReducedS a s
      ∧
      (GenContFract.of steinerAlpha).partDens.get? n =
        some (A : ℝ)
      ∧
      (2 * steinerScale a s ^ 2 - 1) *
          (steinerAlpha.convergent n).den
        <
      (steinerAlpha.convergent (n + 1)).den
      ∧
      (steinerAlpha.convergent (n + 1)).den
        ≤
      (A + 1) *
        (steinerAlpha.convergent n).den
      ∧
      2 * steinerScale a s ^ 2 - 1 ≤ A := by
  obtain ⟨n, hn, hden, hjump⟩ :=
    oneBlockGap_next_denominator_large
      ha hs hgap hdvd hne
  have hneAlpha :=
    oneBlockGap_convergent_ne_alpha
      ha hs hgap hdvd hne hn
  have hneG :
      steinerAlpha ≠
        (GenContFract.of steinerAlpha).convs n := by
    simpa only [Real.convs_eq_convergent] using hneAlpha
  obtain ⟨A, _hApos, hpart⟩ :=
    gcf_exists_nat_partDen_of_ne_convergent hneG
  have hupper :=
    real_next_convergent_den_le_partDen_add_one
      hneAlpha hpart
  have hq :
      0 < (steinerAlpha.convergent n).den :=
    Rat.den_pos _
  have hlarge :=
    partialQuotient_large_of_den_jump
      hq hjump hupper
  exact ⟨n, A, hn, hden, hpart,
    hjump, hupper, hlarge⟩




theorem oneBlockGap_next_partial_quotient_large
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1)) :
    ∃ n A : ℕ,
      steinerSlopeRat a s =
        steinerAlpha.convergent n
      ∧
      (steinerAlpha.convergent n).den =
        steinerReducedS a s
      ∧
      (GenContFract.of steinerAlpha).partDens.get? n =
        some (A : ℝ)
      ∧
      2 * steinerScale a s ^ 2 - 1 ≤ A := by
  obtain ⟨n, A, hn, hden, hpart,
      _hjump, _hupper, hlarge⟩ :=
    oneBlockGap_partial_quotient_recurrence_spec
      ha hs hgap hdvd hne
  exact ⟨n, A, hn, hden, hpart, hlarge⟩




theorem raw_fixed_nontrivial_next_partial_quotient_large
    {d : BlockCoord}
    (hd : d.Valid)
    (hfix : nextCoord d = d)
    (hne : d ≠ oneCoord) :
    ∃ n A : ℕ,
      steinerSlopeRat
          (coordClosingValuation d)
          d.r
        =
      steinerAlpha.convergent n
      ∧
      (GenContFract.of steinerAlpha).partDens.get? n =
        some (A : ℝ)
      ∧
      2 *
        steinerScale
          (coordClosingValuation d)
          d.r ^ 2
        - 1
        ≤ A := by
  obtain ⟨n, A, hn, _hden, hpart, hlarge⟩ :=
    oneBlockGap_next_partial_quotient_large
      (coordClosingValuation_pos hd)
      hd.1
      (Nat.sub_pos_of_lt
        (raw_fixed_gap_pos hd hfix))
      (raw_fixed_gap_dvd_mersenne hd hfix)
      (raw_fixed_nontrivial_params_nontrivial
        hd hfix hne)
  exact ⟨n, A, hn, hpart, hlarge⟩




theorem oneBlockGap_partial_quotient_spec
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1)) :
    ∃ n A : ℕ,
      steinerSlopeRat a s =
        steinerAlpha.convergent n
      ∧
      (steinerAlpha.convergent n).den =
        steinerReducedS a s
      ∧
      (GenContFract.of steinerAlpha).partDens.get? n =
        some (A : ℝ)
      ∧
      (2 * steinerScale a s ^ 2 - 1) *
          steinerReducedS a s
        <
      (steinerAlpha.convergent (n + 1)).den
      ∧
      2 * steinerScale a s ^ 2 - 1 ≤ A := by
  obtain ⟨n, A, hn, hden, hpart,
      hjump, _hupper, hlarge⟩ :=
    oneBlockGap_partial_quotient_recurrence_spec
      ha hs hgap hdvd hne
  refine ⟨n, A, hn, hden, hpart, ?_, hlarge⟩
  rw [← hden]
  exact hjump




/-
Thus the exact coefficient in the transition B_n -> B_(n+1) satisfies
2*g^2 - 1 <= A_n for every nontrivial one-block gap solution.
This does not classify the partial quotients and does not prove
OneBlockGapRigidity.
-/








theorem right_pow_pred_le_pow_sub_pow
    {X Y g : ℕ}
    (hg : 1 ≤ g)
    (hYX : Y < X) :
    Y ^ (g - 1) ≤ X ^ g - Y ^ g := by
  have hbase : Y + 1 ≤ X := by omega
  have hpow : Y ^ (g - 1) ≤ X ^ (g - 1) :=
    Nat.pow_le_pow_left (by omega) (g - 1)
  have hmul :
      (Y + 1) * Y ^ (g - 1) ≤
        X * X ^ (g - 1) :=
    Nat.mul_le_mul hbase hpow
  have hX : X * X ^ (g - 1) = X ^ g := by
    calc
      X * X ^ (g - 1) = X ^ (g - 1) * X := by ring
      _ = X ^ ((g - 1) + 1) := by rw [pow_succ]
      _ = X ^ g := by rw [Nat.sub_add_cancel hg]
  have hY :
      (Y + 1) * Y ^ (g - 1) =
        Y ^ g + Y ^ (g - 1) := by
    calc
      (Y + 1) * Y ^ (g - 1) =
          Y * Y ^ (g - 1) + Y ^ (g - 1) := by ring
      _ = Y ^ (g - 1) * Y + Y ^ (g - 1) := by ring
      _ = Y ^ ((g - 1) + 1) + Y ^ (g - 1) := by rw [pow_succ]
      _ = Y ^ g + Y ^ (g - 1) := by rw [Nat.sub_add_cancel hg]
  rw [hX, hY] at hmul
  exact Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hmul)




theorem three_pow_le_four_pow_sub_one
    {v : ℕ}
    (hv : 1 ≤ v) :
    3 ^ v ≤ 4 ^ v - 1 := by
  have hlt : 3 ^ v < 4 ^ v :=
    Nat.pow_lt_pow_left (by norm_num) (by omega)
  omega








theorem steiner_two_pow_a_scaled
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s) :
    2 ^ a =
      (2 ^ steinerReducedA a s) ^
        steinerScale a s := by
  have haeq :=
    steinerScale_mul_reducedA (a := a) (s := s) ha hs
  calc
    2 ^ a =
        2 ^ (steinerScale a s * steinerReducedA a s) := by
          rw [haeq]
    _ = 2 ^ (steinerReducedA a s * steinerScale a s) := by
          rw [Nat.mul_comm]
    _ = (2 ^ steinerReducedA a s) ^ steinerScale a s := by
          rw [pow_mul]




theorem steiner_three_pow_s_scaled
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s) :
    3 ^ s =
      (3 ^ steinerReducedS a s) ^
        steinerScale a s := by
  have hseq :=
    steinerScale_mul_reducedS (a := a) (s := s) ha hs
  calc
    3 ^ s =
        3 ^ (steinerScale a s * steinerReducedS a s) := by
          rw [hseq]
    _ = 3 ^ (steinerReducedS a s * steinerScale a s) := by
          rw [Nat.mul_comm]
    _ = (3 ^ steinerReducedS a s) ^ steinerScale a s := by
          rw [pow_mul]




theorem steiner_two_pow_a_add_s_scaled
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s) :
    2 ^ (a + s) =
      (2 ^
        (steinerReducedA a s +
         steinerReducedS a s)) ^
        steinerScale a s := by
  have haeq :=
    steinerScale_mul_reducedA (a := a) (s := s) ha hs
  have hseq :=
    steinerScale_mul_reducedS (a := a) (s := s) ha hs
  calc
    2 ^ (a + s) =
        2 ^
          (steinerScale a s * steinerReducedA a s +
           steinerScale a s * steinerReducedS a s) := by
            rw [haeq, hseq]
    _ = 2 ^
          (steinerScale a s *
            (steinerReducedA a s + steinerReducedS a s)) := by
            rw [Nat.mul_add]
    _ = 2 ^
          ((steinerReducedA a s + steinerReducedS a s) *
            steinerScale a s) := by
            rw [Nat.mul_comm]
    _ = (2 ^
          (steinerReducedA a s + steinerReducedS a s)) ^
            steinerScale a s := by
            rw [pow_mul]








theorem oneBlockGap_scale_eq_one
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1) :
    steinerScale a s = 1 := by
  let g := steinerScale a s
  let u := steinerReducedA a s
  let v := steinerReducedS a s
  let X := 2 ^ (u + v)
  let Y := 3 ^ v
  let Z := 2 ^ u
  have hgpos : 0 < g := by
    simpa [g] using steinerScale_pos ha hs
  have hg : 1 ≤ g := by omega
  have hupos : 0 < u := by
    simpa [u] using steinerReducedA_pos ha hs
  have hvpos : 0 < v := by
    simpa [v] using steinerReducedS_pos ha hs
  have haeq : g * u = a := by
    simpa [g, u] using steinerScale_mul_reducedA ha hs
  have hseq : g * v = s := by
    simpa [g, v] using steinerScale_mul_reducedS ha hs
  have hYg : Y ^ g = 3 ^ s := by
    simpa [Y, g, v] using
      (steiner_three_pow_s_scaled ha hs).symm
  have hXg : X ^ g = 2 ^ (a + s) := by
    simpa [X, g, u, v] using
      (steiner_two_pow_a_add_s_scaled ha hs).symm
  have hZg : Z ^ g = 2 ^ a := by
    simpa [Z, g, u] using
      (steiner_two_pow_a_scaled ha hs).symm
  by_contra hscale
  have hg2 : 2 ≤ g := by
    have : g ≠ 1 := by
      simpa [g] using hscale
    omega
  have hsqueeze :=
    oneBlockGap_power_squeeze ha hs hgap hdvd
  have hpowYX : Y ^ g < X ^ g := by
    rw [hYg, hXg]
    exact hsqueeze.2
  have hYX : Y < X := by
    by_contra hnot
    have hXY : X ≤ Y := by omega
    have hpowle : X ^ g ≤ Y ^ g :=
      Nat.pow_le_pow_left hXY g
    omega
  have hlower :
      Y ^ (g - 1) ≤ X ^ g - Y ^ g :=
    right_pow_pred_le_pow_sub_pow hg hYX
  have hgapUpper :=
    oneBlockGap_le_mersenne ha hs hgap hdvd
  have hgapUpperScaled :
      X ^ g - Y ^ g ≤ Z ^ g - 1 := by
    rw [hXg, hYg, hZg]
    exact hgapUpper
  have hZgpos : 0 < Z ^ g := by
    positivity
  have hprev_lt_Zg : Y ^ (g - 1) < Z ^ g := by
    have hchain : Y ^ (g - 1) ≤ Z ^ g - 1 :=
      le_trans hlower hgapUpperScaled
    omega
  have hsqueezeScaled :
      Z ^ g * (2 ^ (g * v) - 1) < Y ^ g := by
    rw [hZg, hYg, hseq]
    exact hsqueeze.1
  have hgvpos : 0 < g * v :=
    Nat.mul_pos hgpos hvpos
  have hTpos : 0 < 2 ^ (g * v) - 1 := by
    obtain ⟨m, hm⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hgvpos)
    rw [hm, pow_succ]
    have hp : 0 < 2 ^ m := by positivity
    omega
  have hYprevpos : 0 < Y ^ (g - 1) := by
    positivity
  have hmulLower :
      Y ^ (g - 1) * (2 ^ (g * v) - 1) <
        Z ^ g * (2 ^ (g * v) - 1) :=
    Nat.mul_lt_mul_of_pos_right hprev_lt_Zg hTpos
  have hprod :
      Y ^ (g - 1) * (2 ^ (g * v) - 1) <
        Y ^ (g - 1) * Y := by
    calc
      Y ^ (g - 1) * (2 ^ (g * v) - 1) <
          Z ^ g * (2 ^ (g * v) - 1) := hmulLower
      _ < Y ^ g := hsqueezeScaled
      _ = Y ^ (g - 1) * Y := by
        rw [← pow_succ, Nat.sub_add_cancel hg]
  have hTltY : 2 ^ (g * v) - 1 < Y := by
    exact (Nat.mul_lt_mul_left hYprevpos).mp hprod
  have htwov : 2 * v ≤ g * v :=
    Nat.mul_le_mul_right v hg2
  have hpowmono : 2 ^ (2 * v) ≤ 2 ^ (g * v) :=
    Nat.pow_le_pow_right (by norm_num) htwov
  have hfour : 2 ^ (2 * v) = 4 ^ v := by
    rw [pow_mul]
    norm_num
  have hsubmono :
      4 ^ v - 1 ≤ 2 ^ (g * v) - 1 := by
    rw [← hfour]
    exact Nat.sub_le_sub_right hpowmono 1
  have hthree : 3 ^ v ≤ 4 ^ v - 1 :=
    three_pow_le_four_pow_sub_one (by omega)
  have hcontr : 3 ^ v ≤ 2 ^ (g * v) - 1 :=
    le_trans hthree hsubmono
  have : Y = 3 ^ v := rfl
  omega








theorem oneBlockGap_coprime
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1) :
    Nat.Coprime a s := by
  rw [Nat.coprime_iff_gcd_eq_one]
  simpa [steinerScale] using
    oneBlockGap_scale_eq_one ha hs hgap hdvd




theorem oneBlockGap_reducedA_eq
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1) :
    steinerReducedA a s = a := by
  have hscale :=
    oneBlockGap_scale_eq_one ha hs hgap hdvd
  have hrec :=
    steinerScale_mul_reducedA ha hs
  rw [hscale, one_mul] at hrec
  exact hrec




theorem oneBlockGap_reducedS_eq
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1) :
    steinerReducedS a s = s := by
  have hscale :=
    oneBlockGap_scale_eq_one ha hs hgap hdvd
  have hrec :=
    steinerScale_mul_reducedS ha hs
  rw [hscale, one_mul] at hrec
  exact hrec




theorem oneBlockGap_slope_den_eq_s
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1) :
    (steinerSlopeRat a s).den = s := by
  rw [steinerSlopeRat_den_eq_reducedS ha hs,
    oneBlockGap_reducedS_eq ha hs hgap hdvd]




theorem oneBlockGap_nontrivial_convergent_exact_den
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1)) :
    ∃ n : ℕ,
      steinerSlopeRat a s =
        steinerAlpha.convergent n
      ∧
      (steinerAlpha.convergent n).den = s := by
  obtain ⟨n, hn⟩ :=
    oneBlockGap_nontrivial_slope_is_convergent
      ha hs hgap hdvd hne
  refine ⟨n, hn, ?_⟩
  calc
    (steinerAlpha.convergent n).den =
        (steinerSlopeRat a s).den :=
      congrArg Rat.den hn.symm
    _ = s :=
      oneBlockGap_slope_den_eq_s ha hs hgap hdvd




theorem oneBlockGap_scale_bound_eq_unscaled
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1)) :
    abs (
      steinerAlpha -
        ((steinerSlopeRat a s : ℚ) : ℝ)
    )
      <
    1 / (2 * (s : ℝ) ^ 2) := by
  have hs4 :=
    oneBlockGap_nontrivial_four_le_s
      ha hs hgap hdvd hne
  have habs :=
    oneBlockGap_legendre_abs ha hs4 hgap hdvd
  rw [← steinerSlopeRat_cast hs] at habs
  exact habs




theorem oneBlockGap_partial_quotient_scale_one
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1)) :
    ∃ n A : ℕ,
      steinerSlopeRat a s =
        steinerAlpha.convergent n
      ∧
      (GenContFract.of steinerAlpha).partDens.get? n =
        some (A : ℝ)
      ∧
      1 ≤ A := by
  obtain ⟨n, A, hn, _hden, hpart, hlarge⟩ :=
    oneBlockGap_next_partial_quotient_large
      ha hs hgap hdvd hne
  have hscale :=
    oneBlockGap_scale_eq_one ha hs hgap hdvd
  refine ⟨n, A, hn, hpart, ?_⟩
  simpa [hscale] using hlarge




theorem raw_fixed_closing_run_coprime
    {d : BlockCoord}
    (hd : d.Valid)
    (hfix : nextCoord d = d) :
    Nat.Coprime
      (coordClosingValuation d)
      d.r := by
  exact oneBlockGap_coprime
    (coordClosingValuation_pos hd)
    hd.1
    (Nat.sub_pos_of_lt
      (raw_fixed_gap_pos hd hfix))
    (raw_fixed_gap_dvd_mersenne hd hfix)




theorem raw_fixed_slope_den_eq_runLength
    {d : BlockCoord}
    (hd : d.Valid)
    (hfix : nextCoord d = d) :
    (
      steinerSlopeRat
        (coordClosingValuation d)
        d.r
    ).den = d.r := by
  exact oneBlockGap_slope_den_eq_s
    (coordClosingValuation_pos hd)
    hd.1
    (Nat.sub_pos_of_lt
      (raw_fixed_gap_pos hd hfix))
    (raw_fixed_gap_dvd_mersenne hd hfix)




theorem raw_fixed_nontrivial_convergent_exact_den
    {d : BlockCoord}
    (hd : d.Valid)
    (hfix : nextCoord d = d)
    (hne : d ≠ oneCoord) :
    ∃ n : ℕ,
      steinerSlopeRat
          (coordClosingValuation d)
          d.r
        =
      steinerAlpha.convergent n
      ∧
      (steinerAlpha.convergent n).den = d.r := by
  exact oneBlockGap_nontrivial_convergent_exact_den
    (coordClosingValuation_pos hd)
    hd.1
    (Nat.sub_pos_of_lt
      (raw_fixed_gap_pos hd hfix))
    (raw_fixed_gap_dvd_mersenne hd hfix)
    (raw_fixed_nontrivial_params_nontrivial
      hd hfix hne)




theorem oneBlockGap_primitive_convergent_spec
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1)) :
    Nat.Coprime a s
    ∧
    steinerScale a s = 1
    ∧
    steinerReducedA a s = a
    ∧
    steinerReducedS a s = s
    ∧
    (steinerSlopeRat a s).den = s
    ∧
    ∃ n : ℕ,
      steinerSlopeRat a s =
        steinerAlpha.convergent n
      ∧
      (steinerAlpha.convergent n).den = s := by
  exact ⟨
    oneBlockGap_coprime ha hs hgap hdvd,
    oneBlockGap_scale_eq_one ha hs hgap hdvd,
    oneBlockGap_reducedA_eq ha hs hgap hdvd,
    oneBlockGap_reducedS_eq ha hs hgap hdvd,
    oneBlockGap_slope_den_eq_s ha hs hgap hdvd,
    oneBlockGap_nontrivial_convergent_exact_den
      ha hs hgap hdvd hne⟩




/-
Every one-block gap solution is primitive: gcd(a,s)=1.  This does not
force (a,s)=(1,1), does not prove OneBlockGapRigidity, and does not prove
the Collatz conjecture.
-/








theorem reduced_fixed_nontrivial_raw_convergent_exact_den
    {c : BlockCoord}
    (hc : c.Valid)
    (hfix : normalizedNextCoord c = c)
    (hne : c ≠ oneCoord) :
    ∃ n : ℕ,
      steinerSlopeRat
          (coordClosingValuation (nextCoord c))
          (nextCoord c).r
        =
      steinerAlpha.convergent n
      ∧
      (steinerAlpha.convergent n).den =
        (nextCoord c).r := by
  have hd : (nextCoord c).Valid :=
    nextCoord_valid hc
  have hdfix :
      nextCoord (nextCoord c) = nextCoord c :=
    reduced_fixed_implies_raw_successor_fixed hc hfix
  have hneD : nextCoord c ≠ oneCoord := by
    intro hdOne
    apply hne
    calc
      c = normalizedNextCoord c := hfix.symm
      _ = normalizeCoord (nextCoord c) := rfl
      _ = normalizeCoord oneCoord := by rw [hdOne]
      _ = oneCoord := normalizeCoord_one
  exact raw_fixed_nontrivial_convergent_exact_den
    hd hdfix hneD








theorem three_pow_sub_two_pow_pos
    {s : ℕ}
    (hs : 1 ≤ s) :
    0 < 3 ^ s - 2 ^ s := by
  exact Nat.sub_pos_of_lt
    (two_pow_lt_three_pow (by omega))




theorem oneBlockGap_exists_positive_quotient
    {a s : ℕ}
    (ha : 1 ≤ a)
    (_hs : 1 ≤ s)
    (_hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1) :
    ∃ Q : ℕ,
      1 ≤ Q ∧
      (2 ^ (a + s) - 3 ^ s) * Q =
        2 ^ a - 1 := by
  obtain ⟨Q, hQ⟩ := hdvd
  have hpow : 1 < 2 ^ a := by
    exact Nat.one_lt_pow (by omega) (by norm_num)
  have hright : 0 < 2 ^ a - 1 := by omega
  have hQpos : 1 ≤ Q := by
    by_contra hzero
    have : Q = 0 := by omega
    subst Q
    simp at hQ
    omega
  exact ⟨Q, hQpos, hQ.symm⟩




theorem oneBlockGap_dual_factorization
    {a s Q : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hQ :
      (2 ^ (a + s) - 3 ^ s) * Q =
        2 ^ a - 1) :
    3 ^ s - 2 ^ s =
      (2 ^ (a + s) - 3 ^ s) *
        (2 ^ s * Q - 1) := by
  rw [pow_add] at hgap hQ ⊢
  have hCB : 3 ^ s ≤ 2 ^ a * 2 ^ s :=
    Nat.le_of_lt (Nat.sub_pos_iff_lt.mp hgap)
  have hAone : 1 ≤ 2 ^ a :=
    Nat.one_le_pow _ _ (by norm_num)
  have hpow : 1 < 2 ^ a :=
    Nat.one_lt_pow (by omega) (by norm_num)
  have hright : 0 < 2 ^ a - 1 :=
    Nat.sub_pos_iff_lt.mpr hpow
  have hQpos : 0 < Q := by
    by_contra hz
    have : Q = 0 := Nat.eq_zero_of_not_pos hz
    subst Q
    simp at hQ
    omega
  have hBQpos : 0 < 2 ^ s * Q :=
    Nat.mul_pos (Nat.pow_pos (by norm_num)) hQpos
  have hBQone : 1 ≤ 2 ^ s * Q := by omega
  have hBC : 2 ^ s ≤ 3 ^ s :=
    Nat.le_of_lt
      (Nat.pow_lt_pow_left (by norm_num) (by omega))
  have hQI :
      (((2 ^ a * 2 ^ s - 3 ^ s : ℕ) : ℤ) * (Q : ℤ)) =
        ((2 ^ a - 1 : ℕ) : ℤ) := by
    exact_mod_cast hQ
  rw [Nat.cast_sub hCB, Nat.cast_sub hAone] at hQI
  push_cast at hQI
  have hQIB :=
    congrArg (fun z : ℤ => z * (2 ^ s : ℤ)) hQI
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_sub hBC, Nat.cast_mul,
    Nat.cast_sub hCB, Nat.cast_sub hBQone]
  push_cast
  ring_nf at hQIB ⊢
  nlinarith [hQIB]




theorem oneBlockGap_two_adic_factorization
    {a s Q : ℕ}
    (ha : 1 ≤ a)
    (_hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hQ :
      (2 ^ (a + s) - 3 ^ s) * Q =
        2 ^ a - 1) :
    3 ^ s * Q - 1 =
      2 ^ a * (2 ^ s * Q - 1) := by
  rw [pow_add] at hgap hQ
  have hCB : 3 ^ s ≤ 2 ^ a * 2 ^ s :=
    Nat.le_of_lt (Nat.sub_pos_iff_lt.mp hgap)
  have hAone : 1 ≤ 2 ^ a :=
    Nat.one_le_pow _ _ (by norm_num)
  have hpow : 1 < 2 ^ a :=
    Nat.one_lt_pow (by omega) (by norm_num)
  have hright : 0 < 2 ^ a - 1 :=
    Nat.sub_pos_iff_lt.mpr hpow
  have hQpos : 0 < Q := by
    by_contra hz
    have : Q = 0 := Nat.eq_zero_of_not_pos hz
    subst Q
    simp at hQ
    omega
  have hCQpos : 0 < 3 ^ s * Q :=
    Nat.mul_pos (Nat.pow_pos (by norm_num)) hQpos
  have hBQpos : 0 < 2 ^ s * Q :=
    Nat.mul_pos (Nat.pow_pos (by norm_num)) hQpos
  have hCQone : 1 ≤ 3 ^ s * Q := by omega
  have hBQone : 1 ≤ 2 ^ s * Q := by omega
  have hQI :
      (((2 ^ a * 2 ^ s - 3 ^ s : ℕ) : ℤ) * (Q : ℤ)) =
        ((2 ^ a - 1 : ℕ) : ℤ) := by
    exact_mod_cast hQ
  rw [Nat.cast_sub hCB, Nat.cast_sub hAone] at hQI
  push_cast at hQI
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_sub hCQone]
  simp only [Nat.cast_mul]
  rw [Nat.cast_sub hBQone]
  push_cast
  ring_nf at hQI ⊢
  nlinarith [hQI]




theorem oneBlockGap_residual_pos
    {s Q : ℕ}
    (hs : 1 ≤ s)
    (hQ : 1 ≤ Q) :
    0 < 2 ^ s * Q - 1 := by
  have hpow : 2 ≤ 2 ^ s := by
    have h :=
      Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hs
    simpa using h
  have : 2 ≤ 2 ^ s * Q := by
    nlinarith
  omega




theorem oneBlockGap_residual_odd
    {s Q : ℕ}
    (hs : 1 ≤ s)
    (hQ : 1 ≤ Q) :
    Odd (2 ^ s * Q - 1) := by
  obtain ⟨t, ht⟩ : ∃ t, s = t + 1 :=
    ⟨s - 1, by omega⟩
  have hN : 0 < 2 ^ t * Q := by positivity
  refine ⟨2 ^ t * Q - 1, ?_⟩
  rw [ht]
  have hmul :
      2 ^ (t + 1) * Q = 2 * (2 ^ t * Q) := by
    ring
  rw [hmul]
  omega




theorem oneBlockGap_three_pow_mul_quotient_v2
    {a s Q : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hQpos : 1 ≤ Q)
    (hQ :
      (2 ^ (a + s) - 3 ^ s) * Q =
        2 ^ a - 1) :
    v2 (3 ^ s * Q - 1) = a := by
  rw [oneBlockGap_two_adic_factorization
    ha hs hgap hQ]
  exact v2_pow_two_mul_odd
    (oneBlockGap_residual_odd hs hQpos)








theorem oneBlockGap_three_pow_mul_quotient_modeq
    {a s Q : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hQpos : 1 ≤ Q)
    (hQ :
      (2 ^ (a + s) - 3 ^ s) * Q =
        2 ^ a - 1) :
    3 ^ s * Q ≡ 1 [MOD 2 ^ a] := by
  have hfac :=
    oneBlockGap_two_adic_factorization
      ha hs hgap hQ
  have hrespos :=
    oneBlockGap_residual_pos hs hQpos
  have hQstrict : 0 < Q := by omega
  have hCQpos : 0 < 3 ^ s * Q :=
    Nat.mul_pos (Nat.pow_pos (by norm_num)) hQstrict
  have hCQone : 1 ≤ 3 ^ s * Q := by omega
  have hfull :
      3 ^ s * Q =
        2 ^ a * (2 ^ s * Q - 1) + 1 := by
    omega
  change
    (3 ^ s * Q) % 2 ^ a = 1 % 2 ^ a
  rw [hfull]
  have hpow : 1 < 2 ^ a := by
    exact Nat.one_lt_pow (by omega) (by norm_num)
  simp




theorem oneBlockGap_three_pow_mul_quotient_not_modeq_next
    {a s Q : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hQpos : 1 ≤ Q)
    (hQ :
      (2 ^ (a + s) - 3 ^ s) * Q =
        2 ^ a - 1) :
    ¬ 3 ^ s * Q ≡ 1 [MOD 2 ^ (a + 1)] := by
  intro hmod
  have hQstrict : 0 < Q := by omega
  have hpos : 0 < 3 ^ s * Q :=
    Nat.mul_pos (Nat.pow_pos (by norm_num)) hQstrict
  have hle : 1 ≤ 3 ^ s * Q := by omega
  have hdvd :
      2 ^ (a + 1) ∣ 3 ^ s * Q - 1 :=
    (Nat.modEq_iff_dvd' hle).mp hmod.symm
  have hne : 3 ^ s * Q - 1 ≠ 0 := by
    have hrespos :=
      oneBlockGap_residual_pos hs hQpos
    rw [oneBlockGap_two_adic_factorization
      ha hs hgap hQ]
    positivity
  have hv :=
    (pow_dvd_iff_le_v2 hne).1 hdvd
  rw [oneBlockGap_three_pow_mul_quotient_v2
    ha hs hgap hQpos hQ] at hv
  omega




theorem quotient_coprime_dual_factor
    {s Q : ℕ}
    (_hs : 1 ≤ s)
    (hQ : 1 ≤ Q) :
    Nat.Coprime Q (2 ^ s * Q - 1) := by
  have hQstrict : 0 < Q := by omega
  have hprodPos : 0 < 2 ^ s * Q :=
    Nat.mul_pos (Nat.pow_pos (by norm_num)) hQstrict
  have hprod : 1 ≤ 2 ^ s * Q := by omega
  have hbase :
      Nat.Coprime (2 ^ s * Q) (2 ^ s * Q - 1) := by
    exact (Nat.coprime_self_sub_right hprod).2
      (Nat.coprime_one_right _)
  exact hbase.of_dvd_left (dvd_mul_left Q (2 ^ s))




theorem oneBlockGap_gap_eq_gcd
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1) :
    Nat.gcd
        (2 ^ a - 1)
        (3 ^ s - 2 ^ s)
      =
    2 ^ (a + s) - 3 ^ s := by
  obtain ⟨Q, hQpos, hQ⟩ :=
    oneBlockGap_exists_positive_quotient
      ha hs hgap hdvd
  have hdual :=
    oneBlockGap_dual_factorization
      ha hs hgap hQ
  rw [← hQ, hdual, Nat.gcd_mul_left,
    (quotient_coprime_dual_factor hs hQpos).gcd_eq_one,
    mul_one]








theorem oneBlockGap_gap_eq_gcd'
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1) :
    2 ^ (a + s) - 3 ^ s =
      Nat.gcd
        (2 ^ a - 1)
        (3 ^ s - 2 ^ s) := by
  simpa using
    (oneBlockGap_gap_eq_gcd ha hs hgap hdvd).symm




theorem oneBlockGap_primitive_gcd_spec
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1) :
    Nat.Coprime a s
    ∧
    Nat.gcd
      (2 ^ a - 1)
      (3 ^ s - 2 ^ s)
      =
      2 ^ (a + s) - 3 ^ s := by
  exact ⟨
    oneBlockGap_coprime ha hs hgap hdvd,
    oneBlockGap_gap_eq_gcd ha hs hgap hdvd⟩




theorem oneBlockGap_gap_dvd_three_pow_sub_two_pow
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1) :
    2 ^ (a + s) - 3 ^ s ∣
      3 ^ s - 2 ^ s := by
  obtain ⟨Q, hQpos, hQ⟩ :=
    oneBlockGap_exists_positive_quotient
      ha hs hgap hdvd
  have hdual :=
    oneBlockGap_dual_factorization
      ha hs hgap hQ
  exact ⟨2 ^ s * Q - 1, hdual⟩




theorem oneBlockGap_gap_dvd_both
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1) :
    (
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1
    )
    ∧
    (
      2 ^ (a + s) - 3 ^ s ∣
        3 ^ s - 2 ^ s
    ) := by
  exact ⟨hdvd,
    oneBlockGap_gap_dvd_three_pow_sub_two_pow
      ha hs hgap hdvd⟩




theorem raw_fixed_dual_factorization
    {d : BlockCoord}
    (hd : d.Valid)
    (hfix : nextCoord d = d) :
    3 ^ d.r - 2 ^ d.r
      =
    (
      2 ^
        (coordClosingValuation d + d.r)
      - 3 ^ d.r
    ) *
      decodeBlockCoord d := by
  have hdual :=
    oneBlockGap_dual_factorization
      (coordClosingValuation_pos hd)
      hd.1
      (Nat.sub_pos_of_lt
        (raw_fixed_gap_pos hd hfix))
      (raw_fixed_diophantine_equation hd hfix)
  simpa [decodeBlockCoord] using hdual




theorem raw_fixed_gap_eq_gcd
    {d : BlockCoord}
    (hd : d.Valid)
    (hfix : nextCoord d = d) :
    Nat.gcd
      (2 ^ coordClosingValuation d - 1)
      (3 ^ d.r - 2 ^ d.r)
      =
    2 ^
      (coordClosingValuation d + d.r)
      - 3 ^ d.r := by
  exact oneBlockGap_gap_eq_gcd
    (coordClosingValuation_pos hd)
    hd.1
    (Nat.sub_pos_of_lt
      (raw_fixed_gap_pos hd hfix))
    (raw_fixed_gap_dvd_mersenne hd hfix)




theorem raw_fixed_closing_run_coprime_and_gap_gcd
    {d : BlockCoord}
    (hd : d.Valid)
    (hfix : nextCoord d = d) :
    Nat.Coprime
      (coordClosingValuation d) d.r
    ∧
    Nat.gcd
      (2 ^ coordClosingValuation d - 1)
      (3 ^ d.r - 2 ^ d.r)
      =
      2 ^
        (coordClosingValuation d + d.r)
        - 3 ^ d.r := by
  exact ⟨
    raw_fixed_closing_run_coprime hd hfix,
    raw_fixed_gap_eq_gcd hd hfix⟩




theorem raw_fixed_two_adic_exact
    {d : BlockCoord}
    (hd : d.Valid)
    (hfix : nextCoord d = d) :
    v2 (3 ^ d.r * d.q - 1) =
      coordClosingValuation d := by
  exact oneBlockGap_three_pow_mul_quotient_v2
    (coordClosingValuation_pos hd)
    hd.1
    (Nat.sub_pos_of_lt
      (raw_fixed_gap_pos hd hfix))
    (valid_coord_q_pos hd)
    (raw_fixed_diophantine_equation hd hfix)




theorem raw_fixed_residual_eq_decode
    {d : BlockCoord}
    (_hd : d.Valid)
    (_hfix : nextCoord d = d) :
    2 ^ d.r * d.q - 1 =
      decodeBlockCoord d := by
  rfl




theorem reduced_fixed_raw_dual_gcd_spec
    {c : BlockCoord}
    (hc : c.Valid)
    (hfix : normalizedNextCoord c = c) :
    let d := nextCoord c
    3 ^ d.r - 2 ^ d.r =
        (
          2 ^ (coordClosingValuation d + d.r) -
            3 ^ d.r
        ) * decodeBlockCoord d
    ∧
    Nat.Coprime (coordClosingValuation d) d.r
    ∧
    Nat.gcd
        (2 ^ coordClosingValuation d - 1)
        (3 ^ d.r - 2 ^ d.r)
      =
      2 ^ (coordClosingValuation d + d.r) -
        3 ^ d.r := by
  let d := nextCoord c
  have hd : d.Valid := by
    exact nextCoord_valid hc
  have hdfix : nextCoord d = d := by
    exact reduced_fixed_implies_raw_successor_fixed hc hfix
  exact ⟨
    raw_fixed_dual_factorization hd hdfix,
    raw_fixed_closing_run_coprime hd hdfix,
    raw_fixed_gap_eq_gcd hd hdfix⟩




theorem oneBlockGap_prime_dvd_mersenne
    {a s p : ℕ}
    (_ha : 1 ≤ a)
    (_hs : 1 ≤ s)
    (_hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (_hp : Nat.Prime p)
    (hpd :
      p ∣ 2 ^ (a + s) - 3 ^ s) :
    p ∣ 2 ^ a - 1 := by
  exact hpd.trans hdvd




theorem oneBlockGap_prime_dvd_power_difference
    {a s p : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (_hp : Nat.Prime p)
    (hpd :
      p ∣ 2 ^ (a + s) - 3 ^ s) :
    p ∣ 3 ^ s - 2 ^ s := by
  exact hpd.trans
    (oneBlockGap_gap_dvd_three_pow_sub_two_pow
      ha hs hgap hdvd)




/-
For every one-block gap solution, the same positive gap is the exact gcd
of the Mersenne factor and the dual power difference.  The quotient has
exact 2-adic valuation a after multiplication by 3^s.  No rigidity or
Collatz conclusion is asserted here.
-/












theorem power_gap_eq_one_implies_trivial
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hD :
      2 ^ (a + s) - 3 ^ s = 1) :
    a = 1 ∧ s = 1 := by
  have hgap : 0 < 2 ^ (a + s) - 3 ^ s := by
    omega
  have hlt : 3 ^ s < 2 ^ (a + s) := by
    exact Nat.sub_pos_iff_lt.mp hgap
  have hEq : 2 ^ (a + s) = 3 ^ s + 1 := by
    have hcancel := Nat.sub_add_cancel (Nat.le_of_lt hlt)
    omega
  have hsum : 2 ≤ a + s := by omega
  by_contra hnot
  have hsum3 : 3 ≤ a + s := by
    omega
  obtain ⟨t, ht⟩ : ∃ t, a + s = 3 + t :=
    ⟨a + s - 3, by omega⟩
  have hleftMod : 2 ^ (a + s) % 8 = 0 := by
    rw [ht, pow_add]
    norm_num
  have hremLt : s % 2 < 2 :=
    Nat.mod_lt s (by norm_num)
  have hparity : s % 2 = 0 ∨ s % 2 = 1 := by
    omega
  rcases hparity with heven | hodd
  · have hd : 2 ∣ s :=
      Nat.dvd_of_mod_eq_zero heven
    obtain ⟨k, hk⟩ := hd
    have hbase : Nat.ModEq 8 9 1 := by
      norm_num [Nat.ModEq]
    have hp := hbase.pow k
    have hthreeMod : 3 ^ s % 8 = 1 := by
      subst s
      simpa [Nat.ModEq, pow_mul] using hp
    have hmodEq := congrArg (fun n : ℕ => n % 8) hEq
    rw [hleftMod, Nat.add_mod, hthreeMod] at hmodEq
    norm_num at hmodEq
  · let k := s / 2
    have hdecomp := Nat.mod_add_div s 2
    have hsEq : s = 2 * k + 1 := by
      dsimp [k]
      omega
    have hbase : Nat.ModEq 8 9 1 := by
      norm_num [Nat.ModEq]
    have hp := hbase.pow k
    have hevenMod : 3 ^ (2 * k) % 8 = 1 := by
      simpa [Nat.ModEq, pow_mul] using hp
    have hthreeMod : 3 ^ s % 8 = 3 := by
      rw [hsEq, pow_succ, Nat.mul_mod, hevenMod]
    have hmodEq := congrArg (fun n : ℕ => n % 8) hEq
    rw [hleftMod, Nat.add_mod, hthreeMod] at hmodEq
    norm_num at hmodEq




theorem oneBlockGap_gap_eq_one_iff_trivial
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1) :
    2 ^ (a + s) - 3 ^ s = 1
      ↔
    (a = 1 ∧ s = 1) := by
  constructor
  · exact power_gap_eq_one_implies_trivial ha hs
  · rintro ⟨rfl, rfl⟩
    norm_num




theorem oneBlockGap_nontrivial_gap_gt_one
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1)) :
    1 < 2 ^ (a + s) - 3 ^ s := by
  have hnotOne :
      2 ^ (a + s) - 3 ^ s ≠ 1 := by
    intro hOne
    exact hne
      ((oneBlockGap_gap_eq_one_iff_trivial
        ha hs hgap hdvd).1 hOne)
  omega




theorem oneBlockGap_nontrivial_exists_prime_gap_divisor
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1)) :
    ∃ p : ℕ,
      Nat.Prime p ∧
      p ∣ 2 ^ (a + s) - 3 ^ s := by
  have hneOne :
      2 ^ (a + s) - 3 ^ s ≠ 1 := by
    have hgt :=
      oneBlockGap_nontrivial_gap_gt_one
        ha hs hgap hdvd hne
    omega
  exact (Nat.ne_one_iff_exists_prime_dvd).1 hneOne




theorem oneBlockGap_prime_ne_two
    {a s p : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd :
      p ∣ 2 ^ (a + s) - 3 ^ s) :
    p ≠ 2 := by
  intro hpTwo
  subst p
  have hM :=
    oneBlockGap_prime_dvd_mersenne
      ha hs hgap hdvd Nat.prime_two hpd
  have hpow : 2 ∣ 2 ^ a := by
    obtain ⟨k, hk⟩ : ∃ k, a = k + 1 :=
      ⟨a - 1, by omega⟩
    rw [hk, pow_succ]
    exact dvd_mul_left 2 (2 ^ k)
  obtain ⟨u, hu⟩ := hM
  obtain ⟨v, hv⟩ := hpow
  have hpowpos : 0 < 2 ^ a := by positivity
  omega




theorem oneBlockGap_prime_ne_three
    {a s p : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd :
      p ∣ 2 ^ (a + s) - 3 ^ s) :
    p ≠ 3 := by
  intro hpThree
  subst p
  have hdiff :=
    oneBlockGap_prime_dvd_power_difference
      ha hs hgap hdvd Nat.prime_three hpd
  have hthree : 3 ∣ 3 ^ s := by
    obtain ⟨k, hk⟩ : ∃ k, s = k + 1 :=
      ⟨s - 1, by omega⟩
    rw [hk, pow_succ]
    exact dvd_mul_left 3 (3 ^ k)
  have hle : 2 ^ s ≤ 3 ^ s :=
    Nat.le_of_lt (two_pow_lt_three_pow (by omega))
  have htwoDvd : 3 ∣ 2 ^ s := by
    simpa [Nat.sub_sub_self hle] using
      Nat.dvd_sub hthree hdiff
  have htwo :=
    Nat.Prime.dvd_of_dvd_pow Nat.prime_three htwoDvd
  norm_num at htwo




/-!
## Gap unitario y órdenes multiplicativas




Para un primo divisor del gap no trivial, las congruencias exactas
producen órdenes multiplicativas que dividen, respectivamente, a `a`
y a `s`.
-/




theorem oneBlockGap_prime_two_pow_eq_one_zmod
    {a s p : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd :
      p ∣ 2 ^ (a + s) - 3 ^ s) :
    (2 : ZMod p) ^ a = 1 := by
  let : Fact (Nat.Prime p) := ⟨hp⟩
  have hM :
      p ∣ 2 ^ a - 1 :=
    oneBlockGap_prime_dvd_mersenne
      ha hs hgap hdvd hp hpd
  have hpow : 1 ≤ 2 ^ a :=
    Nat.one_le_pow _ _ (by norm_num)
  have hz :
      ((2 ^ a - 1 : ℕ) : ZMod p) = 0 := by
    exact (ZMod.natCast_eq_zero_iff _ _).2 hM
  rw [Nat.cast_sub hpow] at hz
  norm_num at hz ⊢
  exact sub_eq_zero.mp hz




theorem oneBlockGap_prime_three_pow_eq_two_pow_zmod
    {a s p : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd :
      p ∣ 2 ^ (a + s) - 3 ^ s) :
    (3 : ZMod p) ^ s = (2 : ZMod p) ^ s := by
  let : Fact (Nat.Prime p) := ⟨hp⟩
  have hD :
      p ∣ 3 ^ s - 2 ^ s :=
    oneBlockGap_prime_dvd_power_difference
      ha hs hgap hdvd hp hpd
  have hlt : 2 ^ s < 3 ^ s := by
    exact Nat.pow_lt_pow_left (by omega) (by omega)
  have hz :
      ((3 ^ s - 2 ^ s : ℕ) : ZMod p) = 0 := by
    exact (ZMod.natCast_eq_zero_iff _ _).2 hD
  rw [Nat.cast_sub (Nat.le_of_lt hlt)] at hz
  norm_num at hz ⊢
  exact sub_eq_zero.mp hz




theorem oneBlockGap_prime_two_ne_zero_zmod
    {a s p : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd :
      p ∣ 2 ^ (a + s) - 3 ^ s) :
    (2 : ZMod p) ≠ 0 := by
  let : Fact (Nat.Prime p) := ⟨hp⟩
  intro hz
  have hp2 : p ∣ 2 := by
    exact (ZMod.natCast_eq_zero_iff _ _).1 hz
  have hp_eq : p = 2 :=
    (Nat.dvd_prime Nat.prime_two).1 hp2 |>.resolve_left hp.ne_one
  exact oneBlockGap_prime_ne_two
    ha hs hgap hdvd hp hpd hp_eq




theorem oneBlockGap_prime_three_ne_zero_zmod
    {a s p : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd :
      p ∣ 2 ^ (a + s) - 3 ^ s) :
    (3 : ZMod p) ≠ 0 := by
  let : Fact (Nat.Prime p) := ⟨hp⟩
  intro hz
  have hp3 : p ∣ 3 := by
    exact (ZMod.natCast_eq_zero_iff _ _).1 hz
  have hp_eq : p = 3 :=
    (Nat.dvd_prime Nat.prime_three).1 hp3 |>.resolve_left hp.ne_one
  exact oneBlockGap_prime_ne_three
    ha hs hgap hdvd hp hpd hp_eq




theorem oneBlockGap_prime_ratio_pow_eq_one_zmod
    {a s p : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd :
      p ∣ 2 ^ (a + s) - 3 ^ s) :
    ((3 : ZMod p) * (2 : ZMod p)⁻¹) ^ s = 1 := by
  let : Fact (Nat.Prime p) := ⟨hp⟩
  rw [mul_pow, oneBlockGap_prime_three_pow_eq_two_pow_zmod
    ha hs hgap hdvd hp hpd, inv_pow]
  exact mul_inv_cancel₀ (pow_ne_zero _ <|
    oneBlockGap_prime_two_ne_zero_zmod
      ha hs hgap hdvd hp hpd)




noncomputable def steinerPrimeOrderTwo (p : ℕ) : ℕ :=
  orderOf (2 : ZMod p)




noncomputable def steinerPrimeOrderRatio (p : ℕ) : ℕ :=
  orderOf ((3 : ZMod p) * (2 : ZMod p)⁻¹)




theorem oneBlockGap_prime_order_two_dvd_a
    {a s p : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd :
      p ∣ 2 ^ (a + s) - 3 ^ s) :
    steinerPrimeOrderTwo p ∣ a := by
  let : Fact (Nat.Prime p) := ⟨hp⟩
  exact orderOf_dvd_of_pow_eq_one
    (oneBlockGap_prime_two_pow_eq_one_zmod
      ha hs hgap hdvd hp hpd)




theorem oneBlockGap_prime_order_ratio_dvd_s
    {a s p : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd :
      p ∣ 2 ^ (a + s) - 3 ^ s) :
    steinerPrimeOrderRatio p ∣ s := by
  let : Fact (Nat.Prime p) := ⟨hp⟩
  exact orderOf_dvd_of_pow_eq_one
    (oneBlockGap_prime_ratio_pow_eq_one_zmod
      ha hs hgap hdvd hp hpd)




theorem oneBlockGap_prime_orders_coprime
    {a s p : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd :
      p ∣ 2 ^ (a + s) - 3 ^ s) :
    Nat.Coprime
      (steinerPrimeOrderTwo p)
      (steinerPrimeOrderRatio p) := by
  have hc := oneBlockGap_coprime ha hs hgap hdvd
  exact (hc.of_dvd_left
    (oneBlockGap_prime_order_two_dvd_a
      ha hs hgap hdvd hp hpd)).of_dvd_right
    (oneBlockGap_prime_order_ratio_dvd_s
      ha hs hgap hdvd hp hpd)




theorem oneBlockGap_prime_order_two_pos
    {a s p : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd :
      p ∣ 2 ^ (a + s) - 3 ^ s) :
    0 < steinerPrimeOrderTwo p := by
  have hord := oneBlockGap_prime_order_two_dvd_a
    ha hs hgap hdvd hp hpd
  by_contra hn
  have hz : steinerPrimeOrderTwo p = 0 := by omega
  rw [hz] at hord
  simp at hord
  omega




theorem oneBlockGap_prime_order_ratio_pos
    {a s p : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd :
      p ∣ 2 ^ (a + s) - 3 ^ s) :
    0 < steinerPrimeOrderRatio p := by
  have hord := oneBlockGap_prime_order_ratio_dvd_s
    ha hs hgap hdvd hp hpd
  by_contra hn
  have hz : steinerPrimeOrderRatio p = 0 := by omega
  rw [hz] at hord
  simp at hord
  omega




theorem oneBlockGap_prime_two_mul_ratio_eq_three
    {a s p : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd :
      p ∣ 2 ^ (a + s) - 3 ^ s) :
    (2 : ZMod p) *
      ((3 : ZMod p) * (2 : ZMod p)⁻¹) =
    3 := by
  let : Fact (Nat.Prime p) := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 :=
    oneBlockGap_prime_two_ne_zero_zmod
      ha hs hgap hdvd hp hpd
  calc
    (2 : ZMod p) * ((3 : ZMod p) * (2 : ZMod p)⁻¹) =
        (3 : ZMod p) * ((2 : ZMod p) * (2 : ZMod p)⁻¹) := by
      ring
    _ = 3 := by rw [mul_inv_cancel₀ htwo, mul_one]




theorem oneBlockGap_prime_order_three_eq_product
    {a s p : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd :
      p ∣ 2 ^ (a + s) - 3 ^ s) :
    orderOf (3 : ZMod p) =
      steinerPrimeOrderTwo p *
        steinerPrimeOrderRatio p := by
  let : Fact (Nat.Prime p) := ⟨hp⟩
  have hco := oneBlockGap_prime_orders_coprime
    ha hs hgap hdvd hp hpd
  have hord :=
    (Commute.all
      (2 : ZMod p)
      ((3 : ZMod p) * (2 : ZMod p)⁻¹)
    ).orderOf_mul_eq_mul_orderOf_of_coprime hco
  rw [oneBlockGap_prime_two_mul_ratio_eq_three
    ha hs hgap hdvd hp hpd] at hord
  simpa [steinerPrimeOrderTwo, steinerPrimeOrderRatio] using hord




theorem oneBlockGap_prime_order_product_dvd_p_sub_one
    {a s p : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd :
      p ∣ 2 ^ (a + s) - 3 ^ s) :
    steinerPrimeOrderTwo p *
      steinerPrimeOrderRatio p ∣ p - 1 := by
  let : Fact (Nat.Prime p) := ⟨hp⟩
  have hthree : (3 : ZMod p) ≠ 0 :=
    oneBlockGap_prime_three_ne_zero_zmod
      ha hs hgap hdvd hp hpd
  have hord : orderOf (3 : ZMod p) ∣ p - 1 :=
    ZMod.orderOf_dvd_card_sub_one hthree
  rw [oneBlockGap_prime_order_three_eq_product
    ha hs hgap hdvd hp hpd] at hord
  exact hord




theorem oneBlockGap_prime_order_spec
    {a s p : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd :
      p ∣ 2 ^ (a + s) - 3 ^ s) :
    p ≠ 2
    ∧ p ≠ 3
    ∧ steinerPrimeOrderTwo p ∣ a
    ∧ steinerPrimeOrderRatio p ∣ s
    ∧ Nat.Coprime
        (steinerPrimeOrderTwo p)
        (steinerPrimeOrderRatio p)
    ∧ orderOf (3 : ZMod p) =
        steinerPrimeOrderTwo p *
          steinerPrimeOrderRatio p
    ∧ steinerPrimeOrderTwo p *
        steinerPrimeOrderRatio p ∣ p - 1 := by
  exact ⟨
    oneBlockGap_prime_ne_two
      ha hs hgap hdvd hp hpd,
    oneBlockGap_prime_ne_three
      ha hs hgap hdvd hp hpd,
    oneBlockGap_prime_order_two_dvd_a
      ha hs hgap hdvd hp hpd,
    oneBlockGap_prime_order_ratio_dvd_s
      ha hs hgap hdvd hp hpd,
    oneBlockGap_prime_orders_coprime
      ha hs hgap hdvd hp hpd,
    oneBlockGap_prime_order_three_eq_product
      ha hs hgap hdvd hp hpd,
    oneBlockGap_prime_order_product_dvd_p_sub_one
      ha hs hgap hdvd hp hpd⟩




theorem oneBlockGap_nontrivial_exists_prime_order_spec
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1)) :
    ∃ p : ℕ,
      Nat.Prime p
      ∧ p ∣ 2 ^ (a + s) - 3 ^ s
      ∧ p ≠ 2
      ∧ p ≠ 3
      ∧ steinerPrimeOrderTwo p ∣ a
      ∧ steinerPrimeOrderRatio p ∣ s
      ∧ Nat.Coprime
          (steinerPrimeOrderTwo p)
          (steinerPrimeOrderRatio p)
      ∧ steinerPrimeOrderTwo p *
          steinerPrimeOrderRatio p ∣ p - 1 := by
  obtain ⟨p, hp, hpd⟩ :=
    oneBlockGap_nontrivial_exists_prime_gap_divisor
      ha hs hgap hdvd hne
  rcases oneBlockGap_prime_order_spec
      ha hs hgap hdvd hp hpd with
    ⟨hp2, hp3, htwo, hratio, hco, _hthree, hprod⟩
  exact ⟨p, hp, hpd, hp2, hp3, htwo, hratio, hco, hprod⟩




theorem raw_fixed_nontrivial_exists_prime_order_spec
    {d : BlockCoord}
    (hd : d.Valid)
    (hfix : nextCoord d = d)
    (hne : d ≠ oneCoord) :
    ∃ p : ℕ,
      Nat.Prime p
      ∧ p ∣
        2 ^ (coordClosingValuation d + d.r) -
          3 ^ d.r
      ∧ steinerPrimeOrderTwo p ∣
          coordClosingValuation d
      ∧ steinerPrimeOrderRatio p ∣ d.r
      ∧ Nat.Coprime
          (steinerPrimeOrderTwo p)
          (steinerPrimeOrderRatio p)
      ∧ steinerPrimeOrderTwo p *
          steinerPrimeOrderRatio p ∣ p - 1 := by
  have ha : 1 ≤ coordClosingValuation d :=
    coordClosingValuation_pos hd
  have hgap :
      0 <
        2 ^ (coordClosingValuation d + d.r) -
          3 ^ d.r :=
    Nat.sub_pos_of_lt (raw_fixed_gap_pos hd hfix)
  obtain ⟨p, hp, hpd, _hp2, _hp3, htwo, hratio, hco, hprod⟩ :=
    oneBlockGap_nontrivial_exists_prime_order_spec
      ha hd.1 hgap
      (raw_fixed_gap_dvd_mersenne hd hfix)
      (raw_fixed_nontrivial_params_nontrivial hd hfix hne)
  exact ⟨p, hp, hpd, htwo, hratio, hco, hprod⟩




/-!
En esta etapa, cada solución no trivial aporta un primo divisor del
gap cuyos órdenes de `2` y `3/2` son coprimos, dividen a `a` y `s`,
y tienen producto divisor de `p - 1`. No se afirma que dichos órdenes
sean exactamente `a` y `s`, ni se concluye OneBlockGapRigidity.
-/








/-!
## Capa global de Euler para el OneBlockGap




El producto siguiente recorre los primos distintos del gap. No incorpora
la multiplicidad de cada primo en la factorización.
-/




noncomputable def steinerGapOrderProduct (D : ℕ) : ℕ :=
  ∏ p ∈ D.primeFactors,
    steinerPrimeOrderTwo p *
      steinerPrimeOrderRatio p




@[simp]
theorem steinerGapOrderProduct_zero :
    steinerGapOrderProduct 0 = 1 := by
  simp [steinerGapOrderProduct]




@[simp]
theorem steinerGapOrderProduct_one :
    steinerGapOrderProduct 1 = 1 := by
  simp [steinerGapOrderProduct]




theorem primeFactor_data
    {D p : ℕ}
    (hD : D ≠ 0)
    (hpD : p ∈ D.primeFactors) :
    Nat.Prime p ∧ p ∣ D := by
  exact (Nat.mem_primeFactors_of_ne_zero hD).1 hpD




theorem oneBlockGap_primeFactor_order_product_dvd
    {a s p : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hpMem :
      p ∈ (2 ^ (a + s) - 3 ^ s).primeFactors) :
    steinerPrimeOrderTwo p *
        steinerPrimeOrderRatio p
      ∣ p - 1 := by
  have hD : 2 ^ (a + s) - 3 ^ s ≠ 0 := by omega
  obtain ⟨hp, hpd⟩ := primeFactor_data hD hpMem
  exact oneBlockGap_prime_order_product_dvd_p_sub_one
    ha hs hgap hdvd hp hpd




theorem oneBlockGap_orderProduct_dvd_primeMinusOneProduct
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1) :
    steinerGapOrderProduct
        (2 ^ (a + s) - 3 ^ s)
      ∣
    ∏ p ∈ (2 ^ (a + s) - 3 ^ s).primeFactors,
      (p - 1) := by
  unfold steinerGapOrderProduct
  apply Finset.prod_dvd_prod_of_dvd
  intro p hpMem
  exact oneBlockGap_primeFactor_order_product_dvd
    ha hs hgap hdvd hpMem




theorem primeMinusOneProduct_dvd_totient
    {D : ℕ}
    (_hD : D ≠ 0) :
    (∏ p ∈ D.primeFactors, (p - 1)) ∣
      Nat.totient D := by
  rw [Nat.totient_eq_div_primeFactors_mul]
  exact dvd_mul_left _ _




theorem oneBlockGap_orderProduct_dvd_totient
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1) :
    steinerGapOrderProduct
        (2 ^ (a + s) - 3 ^ s)
      ∣
    Nat.totient
        (2 ^ (a + s) - 3 ^ s) := by
  exact dvd_trans
    (oneBlockGap_orderProduct_dvd_primeMinusOneProduct
      ha hs hgap hdvd)
    (primeMinusOneProduct_dvd_totient (by omega))




theorem oneBlockGap_totient_pos
    {a s : ℕ}
    (_ha : 1 ≤ a)
    (_hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (_hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1) :
    0 < Nat.totient
      (2 ^ (a + s) - 3 ^ s) := by
  exact Nat.totient_pos.mpr (by omega)




theorem oneBlockGap_orderProduct_le_totient
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1) :
    steinerGapOrderProduct
        (2 ^ (a + s) - 3 ^ s)
      ≤
    Nat.totient
        (2 ^ (a + s) - 3 ^ s) := by
  exact Nat.le_of_dvd
    (oneBlockGap_totient_pos ha hs hgap hdvd)
    (oneBlockGap_orderProduct_dvd_totient
      ha hs hgap hdvd)




theorem oneBlockGap_totient_le_gap
    {a s : ℕ} :
    Nat.totient
        (2 ^ (a + s) - 3 ^ s)
      ≤
    2 ^ (a + s) - 3 ^ s := by
  exact Nat.totient_le _




theorem oneBlockGap_nontrivial_totient_lt_gap
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1)) :
    Nat.totient
        (2 ^ (a + s) - 3 ^ s)
      <
    2 ^ (a + s) - 3 ^ s := by
  exact Nat.totient_lt
    (2 ^ (a + s) - 3 ^ s)
    (oneBlockGap_nontrivial_gap_gt_one
      ha hs hgap hdvd hne)




theorem oneBlockGap_euler_order_sandwich
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1)) :
    steinerGapOrderProduct
        (2 ^ (a + s) - 3 ^ s)
      ≤
    Nat.totient
        (2 ^ (a + s) - 3 ^ s)
    ∧
    Nat.totient
        (2 ^ (a + s) - 3 ^ s)
      <
    2 ^ (a + s) - 3 ^ s := by
  exact ⟨
    oneBlockGap_orderProduct_le_totient
      ha hs hgap hdvd,
    oneBlockGap_nontrivial_totient_lt_gap
      ha hs hgap hdvd hne⟩




theorem oneBlockGap_nontrivial_orderProduct_lt_gap
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1)) :
    steinerGapOrderProduct
        (2 ^ (a + s) - 3 ^ s)
      <
    2 ^ (a + s) - 3 ^ s := by
  exact lt_of_le_of_lt
    (oneBlockGap_orderProduct_le_totient
      ha hs hgap hdvd)
    (oneBlockGap_nontrivial_totient_lt_gap
      ha hs hgap hdvd hne)




theorem oneBlockGap_orderProduct_eq_orderThreeProduct
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1) :
    steinerGapOrderProduct
        (2 ^ (a + s) - 3 ^ s)
      =
    ∏ p ∈ (2 ^ (a + s) - 3 ^ s).primeFactors,
      orderOf (3 : ZMod p) := by
  unfold steinerGapOrderProduct
  apply Finset.prod_congr rfl
  intro p hpMem
  have hD : 2 ^ (a + s) - 3 ^ s ≠ 0 := by omega
  obtain ⟨hp, hpd⟩ := primeFactor_data hD hpMem
  exact (oneBlockGap_prime_order_three_eq_product
    ha hs hgap hdvd hp hpd).symm




theorem raw_fixed_nontrivial_euler_order_sandwich
    {d : BlockCoord}
    (hd : d.Valid)
    (hfix : nextCoord d = d)
    (hne : d ≠ oneCoord) :
    let D :=
      2 ^ (coordClosingValuation d + d.r) -
        3 ^ d.r
    steinerGapOrderProduct D ≤ Nat.totient D
    ∧ Nat.totient D < D := by
  dsimp only
  exact oneBlockGap_euler_order_sandwich
    (coordClosingValuation_pos hd)
    hd.1
    (Nat.sub_pos_of_lt (raw_fixed_gap_pos hd hfix))
    (raw_fixed_gap_dvd_mersenne hd hfix)
    (raw_fixed_nontrivial_params_nontrivial hd hfix hne)




theorem oneBlockGap_euler_order_spec
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap :
      0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd :
      2 ^ (a + s) - 3 ^ s ∣
        2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1)) :
    let D := 2 ^ (a + s) - 3 ^ s
    steinerGapOrderProduct D ∣ Nat.totient D
    ∧ steinerGapOrderProduct D ≤ Nat.totient D
    ∧ Nat.totient D < D
    ∧ steinerGapOrderProduct D < D := by
  dsimp only
  exact ⟨
    oneBlockGap_orderProduct_dvd_totient
      ha hs hgap hdvd,
    oneBlockGap_orderProduct_le_totient
      ha hs hgap hdvd,
    oneBlockGap_nontrivial_totient_lt_gap
      ha hs hgap hdvd hne,
    oneBlockGap_nontrivial_orderProduct_lt_gap
      ha hs hgap hdvd hne⟩




/-!
Para una solución no trivial, la capa global certifica únicamente




  M(D) ∣ φ(D)  y  M(D) ≤ φ(D) < D.




No se identifica ningún orden local con `a` o `s`, no se supone que
el gap sea libre de cuadrados y no se concluye OneBlockGapRigidity.
-/




theorem oneBlockGap_convergent_abs_error_eq
    {a s n : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hn : steinerSlopeRat a s = steinerAlpha.convergent n) :
    abs (steinerAlpha - ((steinerAlpha.convergent n : ℚ) : ℝ)) =
      (((a + s : ℕ) : ℝ) / (s : ℝ)) - steinerAlpha := by
  have happrox := oneBlockGap_steiner_approx ha hs hgap hdvd
  have hcast := steinerSlopeRat_cast (a := a) (s := s) hs
  have hnCast :
      ((steinerSlopeRat a s : ℚ) : ℝ) =
        ((steinerAlpha.convergent n : ℚ) : ℝ) :=
    congrArg (fun q : ℚ => (q : ℝ)) hn
  have hconv :
      ((steinerAlpha.convergent n : ℚ) : ℝ) =
        ((a + s : ℕ) : ℝ) / (s : ℝ) := by
    rw [← hnCast, hcast]
  have hneg :
      steinerAlpha - ((steinerAlpha.convergent n : ℚ) : ℝ) < 0 := by
    rw [hconv]
    linarith [happrox.1]
  rw [abs_of_neg hneg, hconv]
  ring




theorem reciprocal_bounds_force_right_denominator
    {q r B err : ℝ}
    (hq : 0 < q)
    (hr : 0 < r)
    (hB : 0 < B)
    (hlow : 1 / (q * r) < err)
    (hupp : err < 1 / (q * B)) :
    B < r := by
  have hfrac : 1 / (q * r) < 1 / (q * B) := lt_trans hlow hupp
  have hqr : 0 < q * r := mul_pos hq hr
  have hqB : 0 < q * B := mul_pos hq hB
  have hprod : q * B < q * r := by
    have h := (div_lt_div_iff₀ hqr hqB).mp hfrac
    simpa only [one_mul] using h
  nlinarith [hprod]




theorem oneBlockGap_next_den_log_lower
    {a s n : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1))
    (hn : steinerSlopeRat a s = steinerAlpha.convergent n)
    (hden : (steinerAlpha.convergent n).den = s) :
    Real.log 2 * ((2 : ℝ) ^ s - 1) <
      (s : ℝ) + ((steinerAlpha.convergent (n + 1)).den : ℝ) := by
  have hlow := oneBlockGap_convergent_error_lower ha hs hgap hdvd hne hn
  rw [oneBlockGap_convergent_abs_error_eq ha hs hgap hdvd hn] at hlow
  have hupp := (oneBlockGap_steiner_approx ha hs hgap hdvd).2
  have hq : 0 < (s : ℝ) := by
    exact_mod_cast (show 0 < s by omega)
  have hr :
      0 < (s : ℝ) + ((steinerAlpha.convergent (n + 1)).den : ℝ) := by
    positivity
  have hpow : 0 < (2 : ℝ) ^ s - 1 := by
    have htwo : (1 : ℝ) < 2 := by norm_num
    have hsne : s ≠ 0 := by omega
    nlinarith [one_lt_pow₀ htwo hsne]
  have hB : 0 < Real.log 2 * ((2 : ℝ) ^ s - 1) :=
    mul_pos log_two_pos hpow
  rw [hden] at hlow
  have hupp' :
      (((a + s : ℕ) : ℝ) / (s : ℝ)) - steinerAlpha <
        1 / ((s : ℝ) * (Real.log 2 * ((2 : ℝ) ^ s - 1))) := by
    simpa only [mul_assoc] using hupp
  exact reciprocal_bounds_force_right_denominator hq hr hB hlow hupp'




theorem oneBlockGap_nontrivial_exists_next_den_log_lower
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1)) :
    ∃ n : ℕ,
      steinerSlopeRat a s = steinerAlpha.convergent n ∧
      (steinerAlpha.convergent n).den = s ∧
      Real.log 2 * ((2 : ℝ) ^ s - 1) <
        (s : ℝ) + ((steinerAlpha.convergent (n + 1)).den : ℝ) := by
  obtain ⟨n, hn, hden⟩ :=
    oneBlockGap_nontrivial_convergent_exact_den ha hs hgap hdvd hne
  exact ⟨n, hn, hden,
    oneBlockGap_next_den_log_lower ha hs hgap hdvd hne hn hden⟩




theorem oneBlockGap_next_den_two_thirds_lower
    {a s n : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1))
    (hn : steinerSlopeRat a s = steinerAlpha.convergent n)
    (hden : (steinerAlpha.convergent n).den = s) :
    (2 : ℝ) / 3 * ((2 : ℝ) ^ s - 1) <
      (s : ℝ) + ((steinerAlpha.convergent (n + 1)).den : ℝ) := by
  have hlog :=
    oneBlockGap_next_den_log_lower ha hs hgap hdvd hne hn hden
  have hpow : 0 < (2 : ℝ) ^ s - 1 := by
    have htwo : (1 : ℝ) < 2 := by norm_num
    have hsne : s ≠ 0 := by omega
    nlinarith [one_lt_pow₀ htwo hsne]
  have hmul :
      (2 : ℝ) / 3 * ((2 : ℝ) ^ s - 1) <
        Real.log 2 * ((2 : ℝ) ^ s - 1) :=
    mul_lt_mul_of_pos_right two_thirds_lt_log_two hpow
  exact lt_trans hmul hlog




theorem oneBlockGap_next_den_exponential_lower
    {a s n : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1))
    (hn : steinerSlopeRat a s = steinerAlpha.convergent n)
    (hden : (steinerAlpha.convergent n).den = s) :
    2 ^ (s + 1) - 1 ≤
      3 * (s + (steinerAlpha.convergent (n + 1)).den) := by
  let qnext := (steinerAlpha.convergent (n + 1)).den
  have hreal :=
    oneBlockGap_next_den_two_thirds_lower ha hs hgap hdvd hne hn hden
  change
    (2 : ℝ) / 3 * ((2 : ℝ) ^ s - 1) <
      (s : ℝ) + (qnext : ℝ) at hreal
  have hpowNat : 1 ≤ 2 ^ s :=
    Nat.one_le_pow _ _ (by norm_num)
  have hsubcast :
      (((2 ^ s - 1 : ℕ) : ℝ)) = (2 : ℝ) ^ s - 1 := by
    rw [Nat.cast_sub hpowNat]
    norm_num
  have hscaledReal :
      (2 : ℝ) * (((2 ^ s - 1 : ℕ) : ℝ)) <
        (3 : ℝ) * ((s + qnext : ℕ) : ℝ) := by
    rw [hsubcast]
    norm_num at hreal ⊢
    nlinarith [hreal]
  have hscaledNat :
      2 * (2 ^ s - 1) < 3 * (s + qnext) := by
    exact_mod_cast hscaledReal
  have hid : 2 ^ (s + 1) - 1 = 2 * (2 ^ s - 1) + 1 := by
    rw [pow_succ]
    omega
  rw [hid]
  omega




theorem oneBlockGap_next_den_half_power_lower
    {a s n : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1))
    (hn : steinerSlopeRat a s = steinerAlpha.convergent n)
    (hden : (steinerAlpha.convergent n).den = s) :
    2 ^ (s - 1) ≤ s + (steinerAlpha.convergent (n + 1)).den := by
  let qnext := (steinerAlpha.convergent (n + 1)).den
  have hstrong :=
    oneBlockGap_next_den_exponential_lower ha hs hgap hdvd hne hn hden
  change 2 ^ (s + 1) - 1 ≤ 3 * (s + qnext) at hstrong
  have hpoweq : 2 ^ (s + 1) = 4 * 2 ^ (s - 1) := by
    calc
      2 ^ (s + 1) = 2 ^ ((s - 1) + 2) := by
        congr 1
        omega
      _ = 2 ^ (s - 1) * 2 ^ 2 := by rw [pow_add]
      _ = 4 * 2 ^ (s - 1) := by ring
  have hxpos : 0 < 2 ^ (s - 1) := by positivity
  rw [hpoweq] at hstrong
  omega




theorem oneBlockGap_next_den_sub_lower
    {a s n : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1))
    (hn : steinerSlopeRat a s = steinerAlpha.convergent n)
    (hden : (steinerAlpha.convergent n).den = s) :
    2 ^ (s - 1) - s ≤ (steinerAlpha.convergent (n + 1)).den := by
  have hhalf :=
    oneBlockGap_next_den_half_power_lower ha hs hgap hdvd hne hn hden
  omega




/-!
The strict real lower bound yields the certified natural inequality


  2^(s+1) - 1 ≤ 3 * (s + q_(n+1)).


Integrality alone does not turn this inequality into an equality: that would
require a matching upper bound.  The same distinction is retained below for
the partial quotient coefficient.
-/




theorem oneBlockGap_partial_quotient_log_lower
    {a s n A : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1))
    (hn : steinerSlopeRat a s = steinerAlpha.convergent n)
    (hden : (steinerAlpha.convergent n).den = s)
    (_hpart :
      (GenContFract.of steinerAlpha).partDens.get? n = some (A : ℝ))
    (hupper :
      (steinerAlpha.convergent (n + 1)).den ≤
        (A + 1) * (steinerAlpha.convergent n).den) :
    Real.log 2 * ((2 : ℝ) ^ s - 1) < (((A + 2) * s : ℕ) : ℝ) := by
  have hlog :=
    oneBlockGap_next_den_log_lower ha hs hgap hdvd hne hn hden
  have hupper' :
      (steinerAlpha.convergent (n + 1)).den ≤ (A + 1) * s := by
    simpa only [hden] using hupper
  have hsum :
      s + (steinerAlpha.convergent (n + 1)).den ≤ (A + 2) * s := by
    calc
      s + (steinerAlpha.convergent (n + 1)).den ≤ s + (A + 1) * s :=
        Nat.add_le_add_left hupper' s
      _ = (A + 2) * s := by ring
  have hsumCast :
      (s : ℝ) + ((steinerAlpha.convergent (n + 1)).den : ℝ) ≤
        (((A + 2) * s : ℕ) : ℝ) := by
    exact_mod_cast hsum
  exact lt_of_lt_of_le hlog hsumCast




theorem oneBlockGap_partial_quotient_exponential_lower
    {a s n A : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1))
    (hn : steinerSlopeRat a s = steinerAlpha.convergent n)
    (hden : (steinerAlpha.convergent n).den = s)
    (_hpart :
      (GenContFract.of steinerAlpha).partDens.get? n = some (A : ℝ))
    (hupper :
      (steinerAlpha.convergent (n + 1)).den ≤
        (A + 1) * (steinerAlpha.convergent n).den) :
    2 ^ (s + 1) - 1 ≤ 3 * ((A + 2) * s) := by
  have hstrong :=
    oneBlockGap_next_den_exponential_lower ha hs hgap hdvd hne hn hden
  have hupper' :
      (steinerAlpha.convergent (n + 1)).den ≤ (A + 1) * s := by
    simpa only [hden] using hupper
  have hsum :
      s + (steinerAlpha.convergent (n + 1)).den ≤ (A + 2) * s := by
    calc
      s + (steinerAlpha.convergent (n + 1)).den ≤ s + (A + 1) * s :=
        Nat.add_le_add_left hupper' s
      _ = (A + 2) * s := by ring
  exact hstrong.trans (Nat.mul_le_mul_left 3 hsum)




theorem oneBlockGap_partial_quotient_half_power_lower
    {a s n A : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1))
    (hn : steinerSlopeRat a s = steinerAlpha.convergent n)
    (hden : (steinerAlpha.convergent n).den = s)
    (_hpart :
      (GenContFract.of steinerAlpha).partDens.get? n = some (A : ℝ))
    (hupper :
      (steinerAlpha.convergent (n + 1)).den ≤
        (A + 1) * (steinerAlpha.convergent n).den) :
    2 ^ (s - 1) ≤ (A + 2) * s := by
  have hhalf :=
    oneBlockGap_next_den_half_power_lower ha hs hgap hdvd hne hn hden
  have hupper' :
      (steinerAlpha.convergent (n + 1)).den ≤ (A + 1) * s := by
    simpa only [hden] using hupper
  have hsum :
      s + (steinerAlpha.convergent (n + 1)).den ≤ (A + 2) * s := by
    calc
      s + (steinerAlpha.convergent (n + 1)).den ≤ s + (A + 1) * s :=
        Nat.add_le_add_left hupper' s
      _ = (A + 2) * s := by ring
  exact hhalf.trans hsum




theorem oneBlockGap_exponential_partial_quotient_lower_spec
    {a s : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hne : ¬ (a = 1 ∧ s = 1)) :
    ∃ n A : ℕ,
      steinerSlopeRat a s = steinerAlpha.convergent n ∧
      (steinerAlpha.convergent n).den = s ∧
      (GenContFract.of steinerAlpha).partDens.get? n = some (A : ℝ) ∧
      (steinerAlpha.convergent (n + 1)).den ≤ (A + 1) * s ∧
      Real.log 2 * ((2 : ℝ) ^ s - 1) <
        (s : ℝ) + ((steinerAlpha.convergent (n + 1)).den : ℝ) ∧
      2 ^ (s + 1) - 1 ≤
        3 * (s + (steinerAlpha.convergent (n + 1)).den) ∧
      Real.log 2 * ((2 : ℝ) ^ s - 1) < (((A + 2) * s : ℕ) : ℝ) ∧
      2 ^ (s + 1) - 1 ≤ 3 * ((A + 2) * s) ∧
      2 ^ (s - 1) ≤ (A + 2) * s := by
  obtain ⟨n, A, hn, hdenReduced, hpart,
      _hjump, hupper, _hlarge⟩ :=
    oneBlockGap_partial_quotient_recurrence_spec ha hs hgap hdvd hne
  have hden : (steinerAlpha.convergent n).den = s := by
    calc
      (steinerAlpha.convergent n).den = steinerReducedS a s := hdenReduced
      _ = s := oneBlockGap_reducedS_eq ha hs hgap hdvd
  have hupper' :
      (steinerAlpha.convergent (n + 1)).den ≤ (A + 1) * s := by
    simpa only [hden] using hupper
  exact ⟨n, A, hn, hden, hpart, hupper',
    oneBlockGap_next_den_log_lower ha hs hgap hdvd hne hn hden,
    oneBlockGap_next_den_exponential_lower ha hs hgap hdvd hne hn hden,
    oneBlockGap_partial_quotient_log_lower
      ha hs hgap hdvd hne hn hden hpart hupper,
    oneBlockGap_partial_quotient_exponential_lower
      ha hs hgap hdvd hne hn hden hpart hupper,
    oneBlockGap_partial_quotient_half_power_lower
      ha hs hgap hdvd hne hn hden hpart hupper⟩




theorem raw_fixed_nontrivial_exponential_partial_quotient_lower_spec
    {d : BlockCoord}
    (hd : d.Valid)
    (hfix : nextCoord d = d)
    (hne : d ≠ oneCoord) :
    ∃ n A : ℕ,
      steinerSlopeRat (coordClosingValuation d) d.r =
        steinerAlpha.convergent n ∧
      (steinerAlpha.convergent n).den = d.r ∧
      (GenContFract.of steinerAlpha).partDens.get? n = some (A : ℝ) ∧
      2 ^ (d.r + 1) - 1 ≤ 3 * ((A + 2) * d.r) ∧
      2 ^ (d.r - 1) ≤ (A + 2) * d.r := by
  obtain ⟨n, A, hn, hden, hpart, _hupper,
      _hlogDen, _hexpDen, _hlogA, hexpA, hhalfA⟩ :=
    oneBlockGap_exponential_partial_quotient_lower_spec
      (coordClosingValuation_pos hd)
      hd.1
      (Nat.sub_pos_of_lt (raw_fixed_gap_pos hd hfix))
      (raw_fixed_gap_dvd_mersenne hd hfix)
      (raw_fixed_nontrivial_params_nontrivial hd hfix hne)
  exact ⟨n, A, hn, hden, hpart, hexpA, hhalfA⟩




/-!
For a nontrivial candidate, if `A_n` is the partial quotient indexed by
`partDens.get? n` and controlling the transition from `q_n = s` to
`q_(n+1)`, then


  log(2) * (2^s - 1) < (A_n + 2) * s


and the certified integral consequence of `2/3 < log 2` is


  2^(s+1) - 1 ≤ 3 * (A_n + 2) * s.


Thus `A_n` has an exponential lower constraint of order `2^s / s` in the
informal growth sense.  No asymptotic equivalence, upper bound on partial
quotients, OneBlockGapRigidity, or Collatz convergence is asserted.
-/




theorem prime_square_dvd_iff_two_le_padicValNat
    {p n : ℕ}
    (hp : Nat.Prime p)
    (hn : n ≠ 0) :
    p ^ 2 ∣ n ↔ 2 ≤ padicValNat p n := by
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  exact padicValNat_dvd_iff_le hn




theorem oneBlockGap_gap_padicVal_eq_min
    {a s p : ℕ}
    (ha : 1 ≤ a)
    (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hp : Nat.Prime p) :
    padicValNat p (2 ^ (a + s) - 3 ^ s) =
      min (padicValNat p (2 ^ a - 1))
        (padicValNat p (3 ^ s - 2 ^ s)) := by
  have hA : 2 ^ a - 1 ≠ 0 := by
    have : 1 < 2 ^ a := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  have hB : 3 ^ s - 2 ^ s ≠ 0 := by
    have : 2 ^ s < 3 ^ s :=
      Nat.pow_lt_pow_left (by norm_num) (by omega)
    omega
  have hfac := Nat.factorization_gcd hA hB
  rw [oneBlockGap_gap_eq_gcd ha hs hgap hdvd] at hfac
  have hat := congrArg (fun f : ℕ →₀ ℕ => f p) hfac
  simpa [Nat.factorization_def _ hp] using hat




theorem oneBlockGap_prime_order_two_dvd_p_sub_one
    {a s p : ℕ}
    (ha : 1 ≤ a) (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd : p ∣ 2 ^ (a + s) - 3 ^ s) :
    steinerPrimeOrderTwo p ∣ p - 1 := by
  apply dvd_trans
    (b := steinerPrimeOrderTwo p * steinerPrimeOrderRatio p)
  · exact ⟨steinerPrimeOrderRatio p, rfl⟩
  · exact oneBlockGap_prime_order_product_dvd_p_sub_one
      ha hs hgap hdvd hp hpd




theorem oneBlockGap_prime_order_ratio_dvd_p_sub_one
    {a s p : ℕ}
    (ha : 1 ≤ a) (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd : p ∣ 2 ^ (a + s) - 3 ^ s) :
    steinerPrimeOrderRatio p ∣ p - 1 := by
  apply dvd_trans
    (b := steinerPrimeOrderTwo p * steinerPrimeOrderRatio p)
  · exact ⟨steinerPrimeOrderTwo p, by simp [mul_comm]⟩
  · exact oneBlockGap_prime_order_product_dvd_p_sub_one
      ha hs hgap hdvd hp hpd




theorem oneBlockGap_prime_not_dvd_order_two
    {a s p : ℕ}
    (ha : 1 ≤ a) (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd : p ∣ 2 ^ (a + s) - 3 ^ s) :
    ¬ p ∣ steinerPrimeOrderTwo p := by
  intro hpr
  have hppred : p ∣ p - 1 := dvd_trans hpr
    (oneBlockGap_prime_order_two_dvd_p_sub_one
      ha hs hgap hdvd hp hpd)
  have hpTwo : 2 ≤ p := hp.two_le
  have hpredpos : 0 < p - 1 := by omega
  have := Nat.le_of_dvd hpredpos hppred
  omega




theorem oneBlockGap_prime_not_dvd_order_ratio
    {a s p : ℕ}
    (ha : 1 ≤ a) (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd : p ∣ 2 ^ (a + s) - 3 ^ s) :
    ¬ p ∣ steinerPrimeOrderRatio p := by
  intro hpt
  have hppred : p ∣ p - 1 := dvd_trans hpt
    (oneBlockGap_prime_order_ratio_dvd_p_sub_one
      ha hs hgap hdvd hp hpd)
  have hpTwo : 2 ≤ p := hp.two_le
  have hpredpos : 0 < p - 1 := by omega
  have := Nat.le_of_dvd hpredpos hppred
  omega




theorem oneBlockGap_prime_order_two_base_dvd
    {a s p : ℕ}
    (ha : 1 ≤ a) (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd : p ∣ 2 ^ (a + s) - 3 ^ s) :
    p ∣ 2 ^ steinerPrimeOrderTwo p - 1 := by
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  let r := steinerPrimeOrderTwo p
  have hr : 0 < r :=
    oneBlockGap_prime_order_two_pos ha hs hgap hdvd hp hpd
  have hord : (2 : ZMod p) ^ r = 1 := by
    change (2 : ZMod p) ^ orderOf (2 : ZMod p) = 1
    exact pow_orderOf_eq_one (2 : ZMod p)
  have hone : 1 ≤ 2 ^ r := Nat.one_le_pow _ _ (by norm_num)
  have hz : ((2 ^ r - 1 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub hone, Nat.cast_pow, Nat.cast_ofNat, hord]
    norm_num
  exact (ZMod.natCast_eq_zero_iff _ p).mp hz




theorem oneBlockGap_prime_order_ratio_base_dvd
    {a s p : ℕ}
    (ha : 1 ≤ a) (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd : p ∣ 2 ^ (a + s) - 3 ^ s) :
    p ∣ 3 ^ steinerPrimeOrderRatio p -
      2 ^ steinerPrimeOrderRatio p := by
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  let t := steinerPrimeOrderRatio p
  have ht : 0 < t :=
    oneBlockGap_prime_order_ratio_pos ha hs hgap hdvd hp hpd
  have htwo : (2 : ZMod p) ≠ 0 :=
    oneBlockGap_prime_two_ne_zero_zmod ha hs hgap hdvd hp hpd
  have htwoPow : (2 : ZMod p) ^ t ≠ 0 := pow_ne_zero _ htwo
  have hord : ((3 : ZMod p) * (2 : ZMod p)⁻¹) ^ t = 1 := by
    change
      ((3 : ZMod p) * (2 : ZMod p)⁻¹) ^
        orderOf ((3 : ZMod p) * (2 : ZMod p)⁻¹) = 1
    exact pow_orderOf_eq_one ((3 : ZMod p) * (2 : ZMod p)⁻¹)
  have heq : (3 : ZMod p) ^ t = (2 : ZMod p) ^ t := by
    calc
      (3 : ZMod p) ^ t =
          ((3 : ZMod p) ^ t * ((2 : ZMod p) ^ t)⁻¹) *
            (2 : ZMod p) ^ t := by
        rw [mul_assoc, inv_mul_cancel₀ htwoPow, mul_one]
      _ = ((3 : ZMod p) * (2 : ZMod p)⁻¹) ^ t *
            (2 : ZMod p) ^ t := by rw [mul_pow, inv_pow]
      _ = (2 : ZMod p) ^ t := by rw [hord, one_mul]
  have hlt : 2 ^ t < 3 ^ t :=
    Nat.pow_lt_pow_left (by norm_num) (by omega)
  have hz : ((3 ^ t - 2 ^ t : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub (Nat.le_of_lt hlt), Nat.cast_pow, Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_ofNat, heq]
    norm_num
  exact (ZMod.natCast_eq_zero_iff _ p).mp hz




theorem padicValNat_mul_eq_right_of_not_dvd
    {p x y : ℕ}
    (hp : Nat.Prime p)
    (hx : x ≠ 0)
    (hy : y ≠ 0)
    (hpx : ¬ p ∣ x) :
    padicValNat p (x * y) = padicValNat p y := by
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  have hvx : padicValNat p x = 0 := by
    exact padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr hpx))
  rw [padicValNat.mul hx hy, hvx, zero_add]




theorem oneBlockGap_prime_mersenne_padicVal
    {a s p : ℕ}
    (ha : 1 ≤ a) (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd : p ∣ 2 ^ (a + s) - 3 ^ s) :
    padicValNat p (2 ^ a - 1) =
      padicValNat p (2 ^ steinerPrimeOrderTwo p - 1) +
        padicValNat p a := by
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  let r := steinerPrimeOrderTwo p
  let m := a / r
  have hrpos : 0 < r :=
    oneBlockGap_prime_order_two_pos ha hs hgap hdvd hp hpd
  have hrne : r ≠ 0 := by omega
  have hrda : r ∣ a :=
    oneBlockGap_prime_order_two_dvd_a ha hs hgap hdvd hp hpd
  have haeq : r * m = a := Nat.mul_div_cancel' hrda
  have hm : m ≠ 0 := by
    intro hm0
    rw [hm0, mul_zero] at haeq
    omega
  have hpr : ¬ p ∣ r :=
    oneBlockGap_prime_not_dvd_order_two ha hs hgap hdvd hp hpd
  have hvr : padicValNat p r = 0 := by
    exact padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr hpr))
  have hvm : padicValNat p m = padicValNat p a := by
    have hmul := padicValNat.mul (p := p) hrne hm
    rw [haeq, hvr, zero_add] at hmul
    exact hmul.symm
  have hpne2 := oneBlockGap_prime_ne_two ha hs hgap hdvd hp hpd
  have hpodd : Odd p := hp.odd_of_ne_two hpne2
  have hxlt : 1 < 2 ^ r := Nat.one_lt_pow (by omega) (by norm_num)
  have hpbase : p ∣ 2 ^ r - 1 :=
    oneBlockGap_prime_order_two_base_dvd ha hs hgap hdvd hp hpd
  have hppow : ¬ p ∣ 2 ^ r := by
    intro h
    have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow h
    have hpeq : p = 2 :=
      (Nat.dvd_prime Nat.prime_two).mp hp2 |>.resolve_left hp.ne_one
    exact hpne2 hpeq
  have hLTE := padicValNat.pow_sub_pow
    (x := 2 ^ r) (y := 1) (p := p)
    hpodd hxlt hpbase hppow hm
  rw [← pow_mul, one_pow, haeq, hvm] at hLTE
  simpa [r] using hLTE




theorem oneBlockGap_prime_power_difference_padicVal
    {a s p : ℕ}
    (ha : 1 ≤ a) (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd : p ∣ 2 ^ (a + s) - 3 ^ s) :
    padicValNat p (3 ^ s - 2 ^ s) =
      padicValNat p
          (3 ^ steinerPrimeOrderRatio p -
            2 ^ steinerPrimeOrderRatio p) +
        padicValNat p s := by
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  let t := steinerPrimeOrderRatio p
  let m := s / t
  have htpos : 0 < t :=
    oneBlockGap_prime_order_ratio_pos ha hs hgap hdvd hp hpd
  have htne : t ≠ 0 := by omega
  have htds : t ∣ s :=
    oneBlockGap_prime_order_ratio_dvd_s ha hs hgap hdvd hp hpd
  have hseq : t * m = s := Nat.mul_div_cancel' htds
  have hm : m ≠ 0 := by
    intro hm0
    rw [hm0, mul_zero] at hseq
    omega
  have hpt : ¬ p ∣ t :=
    oneBlockGap_prime_not_dvd_order_ratio ha hs hgap hdvd hp hpd
  have hvt : padicValNat p t = 0 := by
    exact padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr hpt))
  have hvm : padicValNat p m = padicValNat p s := by
    have hmul := padicValNat.mul (p := p) htne hm
    rw [hseq, hvt, zero_add] at hmul
    exact hmul.symm
  have hpne2 := oneBlockGap_prime_ne_two ha hs hgap hdvd hp hpd
  have hpne3 := oneBlockGap_prime_ne_three ha hs hgap hdvd hp hpd
  have hpodd : Odd p := hp.odd_of_ne_two hpne2
  have hbaseLt : 2 ^ t < 3 ^ t :=
    Nat.pow_lt_pow_left (by norm_num) (by omega)
  have hpbase : p ∣ 3 ^ t - 2 ^ t :=
    oneBlockGap_prime_order_ratio_base_dvd ha hs hgap hdvd hp hpd
  have hppow : ¬ p ∣ 3 ^ t := by
    intro h
    have hp3 : p ∣ 3 := hp.dvd_of_dvd_pow h
    have hpeq : p = 3 :=
      (Nat.dvd_prime Nat.prime_three).mp hp3 |>.resolve_left hp.ne_one
    exact hpne3 hpeq
  have hLTE := padicValNat.pow_sub_pow
    (x := 3 ^ t) (y := 2 ^ t) (p := p)
    hpodd hbaseLt hpbase hppow hm
  rw [← pow_mul, ← pow_mul, hseq, hvm] at hLTE
  simpa [t] using hLTE




theorem oneBlockGap_prime_gap_padicVal_order_formula
    {a s p : ℕ}
    (ha : 1 ≤ a) (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd : p ∣ 2 ^ (a + s) - 3 ^ s) :
    padicValNat p (2 ^ (a + s) - 3 ^ s) =
      min
        (padicValNat p (2 ^ steinerPrimeOrderTwo p - 1) +
          padicValNat p a)
        (padicValNat p
            (3 ^ steinerPrimeOrderRatio p -
              2 ^ steinerPrimeOrderRatio p) +
          padicValNat p s) := by
  rw [oneBlockGap_gap_padicVal_eq_min ha hs hgap hdvd hp,
    oneBlockGap_prime_mersenne_padicVal ha hs hgap hdvd hp hpd,
    oneBlockGap_prime_power_difference_padicVal
      ha hs hgap hdvd hp hpd]


theorem oneBlockGap_prime_square_dvd_gap_of_not_dvd_a
    {a s p : ℕ}
    (ha : 1 ≤ a) (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd : p ∣ 2 ^ (a + s) - 3 ^ s)
    (hp2 : p ^ 2 ∣ 2 ^ (a + s) - 3 ^ s)
    (hpa : ¬ p ∣ a) :
    p ^ 2 ∣ 2 ^ steinerPrimeOrderTwo p - 1 := by
  have hDne : 2 ^ (a + s) - 3 ^ s ≠ 0 := by omega
  have hvD : 2 ≤ padicValNat p (2 ^ (a + s) - 3 ^ s) :=
    (prime_square_dvd_iff_two_le_padicValNat hp hDne).mp hp2
  rw [oneBlockGap_prime_gap_padicVal_order_formula
    ha hs hgap hdvd hp hpd] at hvD
  have hvA : padicValNat p a = 0 :=
    padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr hpa))
  have hvBase :
      2 ≤ padicValNat p (2 ^ steinerPrimeOrderTwo p - 1) := by
    have := le_trans hvD (min_le_left _ _)
    simpa [hvA] using this
  have hrpos :=
    oneBlockGap_prime_order_two_pos ha hs hgap hdvd hp hpd
  have hbaseNe : 2 ^ steinerPrimeOrderTwo p - 1 ≠ 0 := by
    have : 1 < 2 ^ steinerPrimeOrderTwo p :=
      Nat.one_lt_pow (by omega) (by norm_num)
    omega
  exact (prime_square_dvd_iff_two_le_padicValNat hp hbaseNe).mpr hvBase




theorem oneBlockGap_prime_square_dvd_gap_of_not_dvd_s
    {a s p : ℕ}
    (ha : 1 ≤ a) (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd : p ∣ 2 ^ (a + s) - 3 ^ s)
    (hp2 : p ^ 2 ∣ 2 ^ (a + s) - 3 ^ s)
    (hps : ¬ p ∣ s) :
    p ^ 2 ∣ 3 ^ steinerPrimeOrderRatio p -
      2 ^ steinerPrimeOrderRatio p := by
  have hDne : 2 ^ (a + s) - 3 ^ s ≠ 0 := by omega
  have hvD : 2 ≤ padicValNat p (2 ^ (a + s) - 3 ^ s) :=
    (prime_square_dvd_iff_two_le_padicValNat hp hDne).mp hp2
  rw [oneBlockGap_prime_gap_padicVal_order_formula
    ha hs hgap hdvd hp hpd] at hvD
  have hvS : padicValNat p s = 0 :=
    padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr hps))
  have hvBase :
      2 ≤ padicValNat p
        (3 ^ steinerPrimeOrderRatio p -
          2 ^ steinerPrimeOrderRatio p) := by
    have := le_trans hvD (min_le_right _ _)
    simpa [hvS] using this
  have htpos :=
    oneBlockGap_prime_order_ratio_pos ha hs hgap hdvd hp hpd
  have hlt :
      2 ^ steinerPrimeOrderRatio p < 3 ^ steinerPrimeOrderRatio p :=
    Nat.pow_lt_pow_left (by norm_num) (by omega)
  have hbaseNe :
      3 ^ steinerPrimeOrderRatio p -
        2 ^ steinerPrimeOrderRatio p ≠ 0 := by omega
  exact (prime_square_dvd_iff_two_le_padicValNat hp hbaseNe).mpr hvBase




theorem oneBlockGap_prime_square_dvd_gap_implies_exceptional_lift
    {a s p : ℕ}
    (ha : 1 ≤ a) (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hp : Nat.Prime p)
    (hp2 : p ^ 2 ∣ 2 ^ (a + s) - 3 ^ s) :
    p ^ 2 ∣ 2 ^ steinerPrimeOrderTwo p - 1 ∨
      p ^ 2 ∣ 3 ^ steinerPrimeOrderRatio p -
        2 ^ steinerPrimeOrderRatio p := by
  have hpd : p ∣ 2 ^ (a + s) - 3 ^ s :=
    dvd_trans ⟨p, by simp [pow_two]⟩ hp2
  have hc := oneBlockGap_coprime ha hs hgap hdvd
  by_cases hpa : p ∣ a
  · right
    apply oneBlockGap_prime_square_dvd_gap_of_not_dvd_s
      ha hs hgap hdvd hp hpd hp2
    intro hps
    have hpg : p ∣ Nat.gcd a s :=
      (Nat.dvd_gcd_iff).mpr ⟨hpa, hps⟩
    rw [hc.gcd_eq_one] at hpg
    have hpTwo := hp.two_le
    have := Nat.le_of_dvd (by norm_num) hpg
    omega
  · left
    exact oneBlockGap_prime_square_dvd_gap_of_not_dvd_a
      ha hs hgap hdvd hp hpd hp2 hpa




theorem oneBlockGap_prime_square_dvd_gap_if_dvd_a
    {a s p : ℕ}
    (ha : 1 ≤ a) (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpa : p ∣ a)
    (hp2 : p ^ 2 ∣ 2 ^ (a + s) - 3 ^ s) :
    p ^ 2 ∣ 3 ^ steinerPrimeOrderRatio p -
      2 ^ steinerPrimeOrderRatio p := by
  have hpd : p ∣ 2 ^ (a + s) - 3 ^ s :=
    dvd_trans ⟨p, by simp [pow_two]⟩ hp2
  apply oneBlockGap_prime_square_dvd_gap_of_not_dvd_s
    ha hs hgap hdvd hp hpd hp2
  intro hps
  have hc := oneBlockGap_coprime ha hs hgap hdvd
  have hpg : p ∣ Nat.gcd a s :=
    (Nat.dvd_gcd_iff).mpr ⟨hpa, hps⟩
  rw [hc.gcd_eq_one] at hpg
  have hpTwo := hp.two_le
  have := Nat.le_of_dvd (by norm_num) hpg
  omega




theorem oneBlockGap_prime_square_dvd_gap_if_dvd_s
    {a s p : ℕ}
    (ha : 1 ≤ a) (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hp : Nat.Prime p)
    (hps : p ∣ s)
    (hp2 : p ^ 2 ∣ 2 ^ (a + s) - 3 ^ s) :
    p ^ 2 ∣ 2 ^ steinerPrimeOrderTwo p - 1 := by
  have hpd : p ∣ 2 ^ (a + s) - 3 ^ s :=
    dvd_trans ⟨p, by simp [pow_two]⟩ hp2
  apply oneBlockGap_prime_square_dvd_gap_of_not_dvd_a
    ha hs hgap hdvd hp hpd hp2
  intro hpa
  have hc := oneBlockGap_coprime ha hs hgap hdvd
  have hpg : p ∣ Nat.gcd a s :=
    (Nat.dvd_gcd_iff).mpr ⟨hpa, hps⟩
  rw [hc.gcd_eq_one] at hpg
  have hpTwo := hp.two_le
  have := Nat.le_of_dvd (by norm_num) hpg
  omega




theorem oneBlockGap_prime_square_dvd_gap_if_dvd_neither
    {a s p : ℕ}
    (ha : 1 ≤ a) (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpa : ¬ p ∣ a)
    (hps : ¬ p ∣ s)
    (hp2 : p ^ 2 ∣ 2 ^ (a + s) - 3 ^ s) :
    p ^ 2 ∣ 2 ^ steinerPrimeOrderTwo p - 1 ∧
      p ^ 2 ∣ 3 ^ steinerPrimeOrderRatio p -
        2 ^ steinerPrimeOrderRatio p := by
  have hpd : p ∣ 2 ^ (a + s) - 3 ^ s :=
    dvd_trans ⟨p, by simp [pow_two]⟩ hp2
  exact ⟨
    oneBlockGap_prime_square_dvd_gap_of_not_dvd_a
      ha hs hgap hdvd hp hpd hp2 hpa,
    oneBlockGap_prime_square_dvd_gap_of_not_dvd_s
      ha hs hgap hdvd hp hpd hp2 hps⟩




theorem oneBlockGap_two_lift_implies_p_minus_one_lift
    {a s p : ℕ}
    (ha : 1 ≤ a) (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd : p ∣ 2 ^ (a + s) - 3 ^ s)
    (hlift : p ^ 2 ∣ 2 ^ steinerPrimeOrderTwo p - 1) :
    p ^ 2 ∣ 2 ^ (p - 1) - 1 := by
  have hr := oneBlockGap_prime_order_two_dvd_p_sub_one
    ha hs hgap hdvd hp hpd
  exact dvd_trans hlift (Nat.pow_sub_one_dvd_pow_sub_one 2 hr)




theorem oneBlockGap_ratio_lift_implies_p_minus_one_lift
    {a s p : ℕ}
    (ha : 1 ≤ a) (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hp : Nat.Prime p)
    (hpd : p ∣ 2 ^ (a + s) - 3 ^ s)
    (hlift : p ^ 2 ∣ 3 ^ steinerPrimeOrderRatio p -
      2 ^ steinerPrimeOrderRatio p) :
    p ^ 2 ∣ 3 ^ (p - 1) - 2 ^ (p - 1) := by
  have ht := oneBlockGap_prime_order_ratio_dvd_p_sub_one
    ha hs hgap hdvd hp hpd
  exact dvd_trans hlift
    (Nat.pow_sub_pow_dvd_pow_sub_pow 3 2 ht)




theorem oneBlockGap_prime_square_dvd_gap_implies_wieferich_like
    {a s p : ℕ}
    (ha : 1 ≤ a) (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hp : Nat.Prime p)
    (hp2 : p ^ 2 ∣ 2 ^ (a + s) - 3 ^ s) :
    p ^ 2 ∣ 2 ^ (p - 1) - 1 ∨
      p ^ 2 ∣ 3 ^ (p - 1) - 2 ^ (p - 1) := by
  have hpd : p ∣ 2 ^ (a + s) - 3 ^ s :=
    dvd_trans ⟨p, by simp [pow_two]⟩ hp2
  rcases oneBlockGap_prime_square_dvd_gap_implies_exceptional_lift
      ha hs hgap hdvd hp hp2 with h | h
  · exact Or.inl (oneBlockGap_two_lift_implies_p_minus_one_lift
      ha hs hgap hdvd hp hpd h)
  · exact Or.inr (oneBlockGap_ratio_lift_implies_p_minus_one_lift
      ha hs hgap hdvd hp hpd h)




theorem oneBlockGap_squarefree_of_no_exceptional_lifts
    {a s : ℕ}
    (ha : 1 ≤ a) (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hno : ∀ p : ℕ,
      Nat.Prime p →
      p ∣ 2 ^ (a + s) - 3 ^ s →
      ¬ p ^ 2 ∣ 2 ^ steinerPrimeOrderTwo p - 1 ∧
      ¬ p ^ 2 ∣ 3 ^ steinerPrimeOrderRatio p -
        2 ^ steinerPrimeOrderRatio p) :
    Squarefree (2 ^ (a + s) - 3 ^ s) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hp2 : p ^ 2 ∣ 2 ^ (a + s) - 3 ^ s := by
    simpa [pow_two] using hpp
  have hpd : p ∣ 2 ^ (a + s) - 3 ^ s :=
    dvd_trans ⟨p, by simp [pow_two]⟩ hp2
  have hex := oneBlockGap_prime_square_dvd_gap_implies_exceptional_lift
    ha hs hgap hdvd hp hp2
  have hnone := hno p hp hpd
  exact hex.elim hnone.1 hnone.2




theorem raw_fixed_prime_square_gap_implies_exceptional_lift
    {d : BlockCoord} {p : ℕ}
    (hd : d.Valid)
    (hfix : nextCoord d = d)
    (hp : Nat.Prime p)
    (hp2 : p ^ 2 ∣
      2 ^ (coordClosingValuation d + d.r) - 3 ^ d.r) :
    p ^ 2 ∣ 2 ^ steinerPrimeOrderTwo p - 1 ∨
      p ^ 2 ∣ 3 ^ steinerPrimeOrderRatio p -
        2 ^ steinerPrimeOrderRatio p := by
  exact oneBlockGap_prime_square_dvd_gap_implies_exceptional_lift
    (coordClosingValuation_pos hd) hd.1
    (Nat.sub_pos_of_lt (raw_fixed_gap_pos hd hfix))
    (raw_fixed_gap_dvd_mersenne hd hfix) hp hp2




theorem raw_fixed_prime_square_gap_implies_wieferich_like
    {d : BlockCoord} {p : ℕ}
    (hd : d.Valid)
    (hfix : nextCoord d = d)
    (hp : Nat.Prime p)
    (hp2 : p ^ 2 ∣
      2 ^ (coordClosingValuation d + d.r) - 3 ^ d.r) :
    p ^ 2 ∣ 2 ^ (p - 1) - 1 ∨
      p ^ 2 ∣ 3 ^ (p - 1) - 2 ^ (p - 1) := by
  exact oneBlockGap_prime_square_dvd_gap_implies_wieferich_like
    (coordClosingValuation_pos hd) hd.1
    (Nat.sub_pos_of_lt (raw_fixed_gap_pos hd hfix))
    (raw_fixed_gap_dvd_mersenne hd hfix) hp hp2




/-!
This stage does not prove that the one-block gap is squarefree.  It proves
that if a prime `p` occurs with multiplicity at least two, then an exceptional
lift modulo `p²` occurs in at least one local order.  More precisely, with


  r = ord_p(2),   t = ord_p(3/2),


the exact formula is


  v_p(D) = min (v_p(2^r - 1) + v_p(a))
                 (v_p(3^t - 2^t) + v_p(s)).


Since `a` and `s` are coprime, divisibility of both exponents by `p` is
impossible.  If `p` divides neither exponent, a square factor `p² ∣ D`
forces both local lifts simultaneously.  No unconditional squarefreeness,
classification of Wieferich-type primes, OneBlockGapRigidity, or Collatz
convergence is asserted.
-/




theorem oneBlockGap_not_squarefree_implies_exists_exceptional_prime
    {a s : ℕ}
    (ha : 1 ≤ a) (hs : 1 ≤ s)
    (hgap : 0 < 2 ^ (a + s) - 3 ^ s)
    (hdvd : 2 ^ (a + s) - 3 ^ s ∣ 2 ^ a - 1)
    (hnsq : ¬ Squarefree (2 ^ (a + s) - 3 ^ s)) :
    ∃ p : ℕ,
      Nat.Prime p ∧
      p ^ 2 ∣ 2 ^ (a + s) - 3 ^ s ∧
      (p ^ 2 ∣ 2 ^ steinerPrimeOrderTwo p - 1 ∨
        p ^ 2 ∣ 3 ^ steinerPrimeOrderRatio p -
          2 ^ steinerPrimeOrderRatio p) := by
  rw [Nat.squarefree_iff_prime_squarefree] at hnsq
  push Not at hnsq
  obtain ⟨p, hp, hp2mul⟩ := hnsq
  have hp2 : p ^ 2 ∣ 2 ^ (a + s) - 3 ^ s := by
    simpa [pow_two] using hp2mul
  exact ⟨p, hp, hp2,
    oneBlockGap_prime_square_dvd_gap_implies_exceptional_lift
      ha hs hgap hdvd hp hp2⟩

/-!
## Abstract layered-grid representation of valid Collatz block states

This section keeps the deterministic Collatz dynamics, the geometric charts,
and layer-dependent move legality as separate notions.
-/


abbrev ValidCoord :=
  { c : BlockCoord // c.Valid }


def nextValidCoord (c : ValidCoord) : ValidCoord :=
  ⟨nextCoord c.1, nextCoord_valid c.2⟩


@[simp]
theorem nextValidCoord_val
    (c : ValidCoord) :
    (nextValidCoord c).1 = nextCoord c.1 := by
  rfl


theorem decode_nextValidCoord
    (c : ValidCoord) :
    decodeBlockCoord (nextValidCoord c).1 =
      blockNext (decodeBlockCoord c.1) := by
  exact decode_nextCoord c.2


def validCoordOrbit
    (c : ValidCoord)
    (n : ℕ) :
    ValidCoord :=
  ⟨coordOrbit c.1 n, coordOrbit_valid c.2 n⟩


@[simp]
theorem validCoordOrbit_val
    (c : ValidCoord)
    (n : ℕ) :
    (validCoordOrbit c n).1 = coordOrbit c.1 n := by
  rfl


theorem decode_validCoordOrbit
    (c : ValidCoord)
    (n : ℕ) :
    decodeBlockCoord (validCoordOrbit c n).1 =
      blockNext^[n] (decodeBlockCoord c.1) := by
  exact decode_coordOrbit c.2 n


abbrev GridPoint := ℤ × ℤ


def chebyshevDist
    (x y : GridPoint) : ℕ :=
  max
    (x.1 - y.1).natAbs
    (x.2 - y.2).natAbs


def GridLegal
    (K : ℕ)
    (x y : GridPoint) : Prop :=
  chebyshevDist x y ≤ K


theorem GridLegal.mono
    {K L : ℕ}
    {x y : GridPoint}
    (hKL : K ≤ L)
    (h : GridLegal K x y) :
    GridLegal L x y := by
  exact h.trans hKL


structure LayeredGridModel where
  chart : ℕ → ValidCoord ≃ GridPoint


def LayeredGridModel.transport
    (M : LayeredGridModel)
    (K L : ℕ) :
    GridPoint ≃ GridPoint :=
  (M.chart K).symm.trans (M.chart L)


@[simp]
theorem LayeredGridModel.transport_chart
    (M : LayeredGridModel)
    (K L : ℕ)
    (c : ValidCoord) :
    M.transport K L (M.chart K c) =
      M.chart L c := by
  simp [LayeredGridModel.transport]


@[simp]
theorem LayeredGridModel.transport_self
    (M : LayeredGridModel)
    (K : ℕ)
    (x : GridPoint) :
    M.transport K K x = x := by
  simp [LayeredGridModel.transport]


theorem LayeredGridModel.transport_comp
    (M : LayeredGridModel)
    (K L N : ℕ)
    (x : GridPoint) :
    M.transport L N (M.transport K L x) =
      M.transport K N x := by
  simp [LayeredGridModel.transport]


def LayeredGridModel.collatzStepAt
    (M : LayeredGridModel)
    (K : ℕ)
    (c : ValidCoord) :
    GridPoint :=
  M.chart K (nextValidCoord c)


def LayeredGridModel.collatzOrbitAt
    (M : LayeredGridModel)
    (K : ℕ)
    (c : ValidCoord)
    (n : ℕ) :
    GridPoint :=
  M.chart K (validCoordOrbit c n)


theorem LayeredGridModel.transport_collatzStep
    (M : LayeredGridModel)
    (K L : ℕ)
    (c : ValidCoord) :
    M.transport K L (M.collatzStepAt K c) =
      M.collatzStepAt L c := by
  exact M.transport_chart K L (nextValidCoord c)


theorem LayeredGridModel.transport_collatzOrbit
    (M : LayeredGridModel)
    (K L : ℕ)
    (c : ValidCoord)
    (n : ℕ) :
    M.transport K L (M.collatzOrbitAt K c n) =
      M.collatzOrbitAt L c n := by
  exact M.transport_chart K L (validCoordOrbit c n)


def LayeredGridModel.BlockedAt
    (M : LayeredGridModel)
    (B : Set ValidCoord)
    (K : ℕ)
    (x : GridPoint) : Prop :=
  (M.chart K).symm x ∈ B


@[simp]
theorem LayeredGridModel.blockedAt_chart
    (M : LayeredGridModel)
    (B : Set ValidCoord)
    (K : ℕ)
    (c : ValidCoord) :
    M.BlockedAt B K (M.chart K c) ↔
      c ∈ B := by
  simp [LayeredGridModel.BlockedAt]


theorem LayeredGridModel.blockedAt_transport
    (M : LayeredGridModel)
    (B : Set ValidCoord)
    (K L : ℕ)
    (x : GridPoint) :
    M.BlockedAt B L (M.transport K L x) ↔
      M.BlockedAt B K x := by
  simp [LayeredGridModel.BlockedAt, LayeredGridModel.transport]


def LayeredGridModel.StepLegalAt
    (M : LayeredGridModel)
    (K : ℕ)
    (c : ValidCoord) : Prop :=
  GridLegal K
    (M.chart K c)
    (M.collatzStepAt K c)


def constantLayerModel
    (e : ValidCoord ≃ GridPoint) :
    LayeredGridModel where
  chart := fun _ => e


def requiredPower
    (e : ValidCoord ≃ GridPoint)
    (c : ValidCoord) : ℕ :=
  chebyshevDist
    (e c)
    (e (nextValidCoord c))


theorem constantLayerModel_legal_iff
    (e : ValidCoord ≃ GridPoint)
    (K : ℕ)
    (c : ValidCoord) :
    (constantLayerModel e).StepLegalAt K c ↔
      requiredPower e c ≤ K := by
  rfl


theorem constantLayerModel_legal_mono
    (e : ValidCoord ≃ GridPoint)
    {K L : ℕ}
    (hKL : K ≤ L)
    (c : ValidCoord)
    (h :
      (constantLayerModel e).StepLegalAt K c) :
    (constantLayerModel e).StepLegalAt L c := by
  rw [constantLayerModel_legal_iff] at h ⊢
  exact h.trans hKL


theorem constantLayerModel_requiredPower_legal
    (e : ValidCoord ≃ GridPoint)
    (c : ValidCoord) :
    (constantLayerModel e).StepLegalAt
      (requiredPower e c) c := by
  rw [constantLayerModel_legal_iff]


theorem constantLayerModel_requiredPower_minimal
    (e : ValidCoord ≃ GridPoint)
    (c : ValidCoord)
    {K : ℕ}
    (h :
      (constantLayerModel e).StepLegalAt K c) :
    requiredPower e c ≤ K := by
  exact (constantLayerModel_legal_iff e K c).1 h


/-!
The chart transports above replicate the same abstract Collatz move on every
layer.  `StepLegalAt` is deliberately separate: for arbitrary layer-dependent
charts, replicated moves need not be legal and legality need not be monotone in
the layer index.  No concrete equivalence `ValidCoord ≃ GridPoint` is selected
in this section.
-/
