import Mathlib

/-!
# Prove2Me-compatible ANTIGRAV affine core

This module is a source-preserving extraction from `main.lean` so the selected
kernel can be compiled independently of `RhinBridge`.

Provenance:
* authority: `main.lean`
* authority SHA-256 before extraction: 1a8cbab8dd69370d5b01883c74d439ec5d888737e6e2bd97d8b42209c03c4735
* extraction: contiguous affine/parity section through
  `refineExactParityState_affineRealizes`

No mathematical statement or proof in the extracted section was changed.
-/

/-!
# AFFINE COLLATZ / BBP-LIKE ACCESS RESEARCH

FORMAL GOAL:
Represent finite Collatz transformations by composable affine
descriptors.

KNOWN DIRECTION:
descriptor + initial state -> distant state

OPEN DIRECTION:
initial state + position n
-> descriptor without orbit traversal
-> distant state

The phrase "BBP-like" is motivational only.
No random-access theorem, complexity claim, or Collatz
convergence result is asserted here.

FAIL FIRST:
An algebraically meaningful affine transformation is not
automatically a valid Collatz trajectory. Required valuations
and residue conditions must be certified separately.
-/


/--
  Affine descriptor `D = (R, S, C)`.

  Intended exact relation (see `AffineRealizes`):

      3^R * x + C = 2^S * y

  Semantics are multiplicative equalities, not truncated `Nat`
  division.  Algebraic integrity does not by itself certify a
  Collatz valuation or residue condition.
-/
structure AffineDescriptor where
  pow3       : ℕ
  pow2       : ℕ
  correction : ℕ
  deriving DecidableEq, Repr


/--
  Exact realization of an affine descriptor:

      3 ^ d.pow3 * x + d.correction = 2 ^ d.pow2 * y
-/
def AffineRealizes (d : AffineDescriptor) (x y : ℕ) : Prop :=
  3 ^ d.pow3 * x + d.correction = 2 ^ d.pow2 * y


instance instDecidableAffineRealizes
    (d : AffineDescriptor) (x y : ℕ) :
    Decidable (AffineRealizes d x y) := by
  unfold AffineRealizes
  infer_instance


/--
  Identity descriptor: `pow3 = 0`, `pow2 = 0`, `correction = 0`.
  Realizes `x = y`.
-/
def affineId : AffineDescriptor where
  pow3 := 0
  pow2 := 0
  correction := 0


theorem affineRealizes_id (x : ℕ) :
    AffineRealizes affineId x x := by
  unfold AffineRealizes affineId
  simp


/--
  Algebraic image of one accelerated odd Collatz step with
  prescribed 2-valuation `a`:

      3 * x + 1 = 2 ^ a * y

  FAIL FIRST:
  For a *real* accelerated Collatz step one also needs

      a = v2 (3 * x + 1)

  (and `x` odd, etc.).  `oddStepAffine` only packages the
  algebraic relation; it does not certify the valuation.
-/
def oddStepAffine (a : ℕ) : AffineDescriptor where
  pow3 := 1
  pow2 := a
  correction := 1


theorem affineRealizes_oddStepAffine
    (a x y : ℕ) :
    AffineRealizes (oddStepAffine a) x y ↔
      3 * x + 1 = 2 ^ a * y := by
  unfold AffineRealizes oddStepAffine
  simp


/--
  Composition of affine descriptors with orientation

      x --d1--> y --d2--> z

  Explicit formula:

      pow3       = d1.pow3 + d2.pow3
      pow2       = d1.pow2 + d2.pow2
      correction = 3 ^ d2.pow3 * d1.correction
                 + 2 ^ d1.pow2 * d2.correction
-/
def affineCompose
    (d1 d2 : AffineDescriptor) : AffineDescriptor where
  pow3 := d1.pow3 + d2.pow3
  pow2 := d1.pow2 + d2.pow2
  correction :=
    3 ^ d2.pow3 * d1.correction +
      2 ^ d1.pow2 * d2.correction


/--
  Central composition theorem:

  algebraic realization is preserved under `affineCompose`.
-/
theorem affineCompose_realizes
    {d1 d2 : AffineDescriptor} {x y z : ℕ}
    (h1 : AffineRealizes d1 x y)
    (h2 : AffineRealizes d2 y z) :
    AffineRealizes (affineCompose d1 d2) x z := by
  unfold AffineRealizes affineCompose at *
  calc
    3 ^ (d1.pow3 + d2.pow3) * x +
          (3 ^ d2.pow3 * d1.correction +
            2 ^ d1.pow2 * d2.correction)
        =
          3 ^ d2.pow3 * 3 ^ d1.pow3 * x +
            3 ^ d2.pow3 * d1.correction +
            2 ^ d1.pow2 * d2.correction := by
          rw [pow_add]
          ring
    _ = 3 ^ d2.pow3 * (3 ^ d1.pow3 * x + d1.correction) +
          2 ^ d1.pow2 * d2.correction := by
        ring
    _ = 3 ^ d2.pow3 * (2 ^ d1.pow2 * y) +
          2 ^ d1.pow2 * d2.correction := by
        rw [h1]
    _ = 2 ^ d1.pow2 * (3 ^ d2.pow3 * y) +
          2 ^ d1.pow2 * d2.correction := by
        ring
    _ = 2 ^ d1.pow2 * (3 ^ d2.pow3 * y + d2.correction) := by
        ring
    _ = 2 ^ d1.pow2 * (2 ^ d2.pow2 * z) := by
        rw [h2]
    _ = 2 ^ (d1.pow2 + d2.pow2) * z := by
        rw [pow_add]
        ring


theorem affineCompose_id_right (d : AffineDescriptor) :
    affineCompose d affineId = d := by
  cases d
  simp [affineCompose, affineId, pow_zero]


theorem affineCompose_id_left (d : AffineDescriptor) :
    affineCompose affineId d = d := by
  cases d
  simp [affineCompose, affineId, pow_zero]



/-! The unrelated block-coordinate experiments remain in `main.lean`. -/

/-!
# PARITY CODE → AFFINE DESCRIPTOR

This subsection sits inside the affine / BBP-like research section.
It formalizes a small bridge:

    algebraic parity word  (ParityCode)
      →  AffineDescriptor
      →  AffineRealizes

Three layers are kept deliberately distinct:

1. algebraic bit word (`ParityCode` / `parityCodeDescriptor`);
2. Collatz-realized word (`RealizesParityCode` / `ParityStep`);
3. future 2-adic interface `Q` (comment only; not formalized here).

Normalized one-step Collatz used in this section (NOT `Tstar`):

* PAR   (`false`):  `x → x / 2`          via  `Even x ∧ x = 2 * y`
* IMPAR (`true`):   `x → (3*x + 1) / 2`  via  `Odd x ∧ 3*x + 1 = 2 * y`

`Tstar` removes the full power of two after `3*x+1`.  Here every step
consumes exactly one factor of two, so a word of length `k` always
contributes `pow2 = k`.

FAIL FIRST:
* A bit word is not automatically a Collatz trajectory.
* An affine descriptor is not automatically a Collatz trajectory.
* Realization must be certified by `ParityStep` / `RealizesParityCode`.
* No random-access, no full `ℤ₂` theory, no BBP formula is claimed.
-/


/--
  Finite chronological word of parity decisions.

  Convention:
  * `false` = PAR step
  * `true`  = IMPAR step

  Order is chronological: `[b₀, b₁, ..., bₙ₋₁]` with `b₀` acting on
  the initial state.
-/
abbrev ParityCode := List Bool


/--
  One normalized Collatz parity step as an exact algebraic relation.

  * `b = true`  (IMPAR): `Odd x ∧ 3 * x + 1 = 2 * y`
  * `b = false` (PAR):   `Even x ∧ x = 2 * y`

  Certifies both the chosen branch and the exact multiplicative
  identity.  Nat division is not the primary semantics.
-/
def ParityStep (b : Bool) (x y : ℕ) : Prop :=
  if b then
    Odd x ∧ 3 * x + 1 = 2 * y
  else
    Even x ∧ x = 2 * y


/--
  Affine descriptor of a single parity bit.

  PAR (`false`):
      x = 2 * y
    ⇔  3^0 * x + 0 = 2^1 * y
    ⇔  D = (0, 1, 0)

  IMPAR (`true`):
      3 * x + 1 = 2 * y
    ⇔  3^1 * x + 1 = 2^1 * y
    ⇔  D = (1, 1, 1)
-/
def parityBitDescriptor (b : Bool) : AffineDescriptor :=
  if b then
    { pow3 := 1, pow2 := 1, correction := 1 }
  else
    { pow3 := 0, pow2 := 1, correction := 0 }


/--
  One certified `ParityStep` realizes its one-bit affine descriptor.
-/
theorem parityStep_affineRealizes
    {b : Bool} {x y : ℕ}
    (h : ParityStep b x y) :
    AffineRealizes (parityBitDescriptor b) x y := by
  cases b with
  | true =>
      unfold ParityStep parityBitDescriptor AffineRealizes at *
      simp at h
      -- h.2 : 3 * x + 1 = 2 * y
      simpa [pow_one] using h.2
  | false =>
      unfold ParityStep parityBitDescriptor AffineRealizes at *
      simp at h
      -- h.2 : x = 2 * y
      -- goal: 3^0 * x + 0 = 2^1 * y
      simpa [pow_zero, pow_one] using h.2


/--
  A parity word is realized by an actual normalized Collatz trajectory
  from `x` to `y`.

  * `[]` realizes the identity `x ↦ x`
  * `b :: bs` takes one `ParityStep b` then realizes the tail

  This is intentionally NOT defined as `AffineRealizes`: the bit word
  keeps Collatz meaning; the affine bridge is a theorem.
-/
inductive RealizesParityCode : ParityCode → ℕ → ℕ → Prop
  | nil (x : ℕ) :
      RealizesParityCode [] x x
  | cons {b : Bool} {bs : ParityCode} {x y z : ℕ}
      (hstep : ParityStep b x y)
      (htail : RealizesParityCode bs y z) :
      RealizesParityCode (b :: bs) x z


/--
  Compile a parity word into one affine descriptor.

  Orientation matches chronology:

      x --b₀--> x₁ --b₁--> ... --bₙ₋₁--> y

  so

      parityCodeDescriptor (b :: bs)
        = affineCompose
            (parityBitDescriptor b)
            (parityCodeDescriptor bs)
-/
def parityCodeDescriptor : ParityCode → AffineDescriptor
  | [] => affineId
  | b :: bs =>
      affineCompose
        (parityBitDescriptor b)
        (parityCodeDescriptor bs)


/--
  CENTRAL BRIDGE:

  every Collatz-realized parity word realizes its compiled
  `AffineDescriptor`.

      RealizesParityCode bits x y
        →  AffineRealizes (parityCodeDescriptor bits) x y
-/
theorem realizesParityCode_affineRealizes
    {bits : ParityCode} {x y : ℕ}
    (h : RealizesParityCode bits x y) :
    AffineRealizes (parityCodeDescriptor bits) x y := by
  induction h with
  | nil x =>
      simpa [parityCodeDescriptor] using affineRealizes_id x
  | cons hstep htail ih =>
      -- hstep : ParityStep b x y
      -- ih    : AffineRealizes (parityCodeDescriptor bs) y z
      simpa [parityCodeDescriptor] using
        affineCompose_realizes
          (parityStep_affineRealizes hstep) ih


/--
  Number of IMPAR (`true`) bits in a parity word.
  Defined explicitly to avoid depending on `List.count` details.
-/
def parityOnes : ParityCode → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + parityOnes bs


/--
  For a word of length `k`, the compiled descriptor has `pow2 = k`.
-/
theorem parityCodeDescriptor_pow2 (bits : ParityCode) :
    (parityCodeDescriptor bits).pow2 = bits.length := by
  induction bits with
  | nil =>
      simp [parityCodeDescriptor, affineId]
  | cons b bs ih =>
      cases b <;>
        simp [parityCodeDescriptor, parityBitDescriptor,
          affineCompose, ih, Nat.add_comm]


/--
  For a word with `m = parityOnes bits` odd steps, the compiled
  descriptor has `pow3 = m`.
-/
theorem parityCodeDescriptor_pow3 (bits : ParityCode) :
    (parityCodeDescriptor bits).pow3 = parityOnes bits := by
  induction bits with
  | nil =>
      simp [parityCodeDescriptor, affineId, parityOnes]
  | cons b bs ih =>
      cases b <;>
        simp [parityCodeDescriptor, parityBitDescriptor,
          affineCompose, parityOnes, ih]


/-!
  ## Order of bits matters

  Both words

      [true, false]   -- IMPAR then PAR
      [false, true]   -- PAR then IMPAR

  have

      length = 2
      parityOnes = 1

  hence the same aggregate phase data

      pow3 = 1
      pow2 = 2

  but different corrections:

  * IMPAR then PAR:  `3x + 1 = 4z`  ⇒  `D₁₀ = (1, 2, 1)`
  * PAR then IMPAR:  `3x + 2 = 4z`  ⇒  `D₀₁ = (1, 2, 2)`

  Division of responsibilities (not a critique of `RhinBridge`):

  * `PhaseGap` / `RhinBridge`: aggregated phase / drift information
    of the form `m log₂ 3 − k`;
  * `ParityCode`: ordered sequence of branch decisions;
  * `AffineDescriptor.correction`: algebraic image of that order.

  A quantity depending only on `m log₂ 3 − k` cannot reconstruct the
  parity word in general.
-/


example :
    parityCodeDescriptor [true, false] =
      { pow3 := 1, pow2 := 2, correction := 1 } := by
  native_decide


example :
    parityCodeDescriptor [false, true] =
      { pow3 := 1, pow2 := 2, correction := 2 } := by
  native_decide


example :
    (parityCodeDescriptor [true, false]).correction = 1 := by
  native_decide


example :
    (parityCodeDescriptor [false, true]).correction = 2 := by
  native_decide


example :
    (parityCodeDescriptor [true, false]).pow3 = 1 ∧
      (parityCodeDescriptor [true, false]).pow2 = 2 ∧
      (parityCodeDescriptor [false, true]).pow3 = 1 ∧
      (parityCodeDescriptor [false, true]).pow2 = 2 := by
  native_decide


example :
    parityOnes [true, false] = 1 ∧
      parityOnes [false, true] = 1 ∧
      [true, false].length = 2 ∧
      [false, true].length = 2 := by
  native_decide


/-!
  ## Concrete trajectory examples
-/


/--
  A) Two successive odd steps: `7 → 11 → 17`, bits = `[true, true]`.

      D = (2, 2, 5)
      3² · 7 + 5 = 2² · 17
      63 + 5 = 68
-/
example :
    parityCodeDescriptor [true, true] =
      { pow3 := 2, pow2 := 2, correction := 5 } := by
  native_decide


example :
    AffineRealizes (parityCodeDescriptor [true, true]) 7 17 := by
  native_decide


example : 3 ^ 2 * 7 + 5 = 2 ^ 2 * 17 := by
  native_decide


/--
  Witness that `[true, true]` is a real Collatz parity trajectory
  from 7 to 17.
-/
example :
    RealizesParityCode [true, true] 7 17 := by
  have h0 : ParityStep true 7 11 := by
    unfold ParityStep; exact ⟨by decide, by decide⟩
  have h1 : ParityStep true 11 17 := by
    unfold ParityStep; exact ⟨by decide, by decide⟩
  exact RealizesParityCode.cons h0
    (RealizesParityCode.cons h1 (RealizesParityCode.nil 17))


/--
  B) Different order: `6 → 3 → 5`, bits = `[false, true]`.

      D = (1, 2, 2)
      3 · 6 + 2 = 4 · 5
-/
example :
    parityCodeDescriptor [false, true] =
      { pow3 := 1, pow2 := 2, correction := 2 } := by
  native_decide


example :
    AffineRealizes (parityCodeDescriptor [false, true]) 6 5 := by
  native_decide


example : 3 * 6 + 2 = 4 * 5 := by
  native_decide


example :
    RealizesParityCode [false, true] 6 5 := by
  have h0 : ParityStep false 6 3 := by
    unfold ParityStep; exact ⟨by decide, by decide⟩
  have h1 : ParityStep true 3 5 := by
    unfold ParityStep; exact ⟨by decide, by decide⟩
  exact RealizesParityCode.cons h0
    (RealizesParityCode.cons h1 (RealizesParityCode.nil 5))


/--
  Comparison: `5 → 8 → 4`, bits = `[true, false]`.

      D = (1, 2, 1)

  Same aggregate `(pow3, pow2) = (1, 2)` as the previous word, but
  different correction: `(1, 2, 1) ≠ (1, 2, 2)`.
-/
example :
    parityCodeDescriptor [true, false] =
      { pow3 := 1, pow2 := 2, correction := 1 } := by
  native_decide


example :
    AffineRealizes (parityCodeDescriptor [true, false]) 5 4 := by
  native_decide


example : 3 * 5 + 1 = 4 * 4 := by
  native_decide


example :
    RealizesParityCode [true, false] 5 4 := by
  have h0 : ParityStep true 5 8 := by
    unfold ParityStep; exact ⟨by decide, by decide⟩
  have h1 : ParityStep false 8 4 := by
    unfold ParityStep; exact ⟨by decide, by decide⟩
  exact RealizesParityCode.cons h0
    (RealizesParityCode.cons h1 (RealizesParityCode.nil 4))


example :
    parityCodeDescriptor [true, false] ≠
      parityCodeDescriptor [false, true] := by
  native_decide


/--
  Little-endian binary value of a finite parity word:

      value([]) = 0
      value(b :: bs) = bit(b) + 2 * value(bs)

  i.e. `v₀ + 2 v₁ + 4 v₂ + ⋯`.

  Prepares the future interface `Q(x) mod 2^n`.  Full coding theory
  is not developed here.
-/
def parityCodeValue : ParityCode → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * parityCodeValue bs


example : parityCodeValue [true, true] = 3 := by
  native_decide


example : parityCodeValue [false, true] = 2 := by
  native_decide


example : parityCodeValue [true, false] = 1 := by
  native_decide


example : parityCodeValue [] = 0 := by
  native_decide


/-!
  ## Q / PARITY-CODE INTERFACE — NOT A RANDOM-ACCESS RESULT

  Future interpretation (NOT formalized in this task; no extra
  2-adic theory is imported solely for this interface):

      Q(x) = ∑_{i ≥ 0} vᵢ 2ⁱ

  where

      vᵢ = Tⁱ(x) mod 2

  and the length-`n` prefix is

      Qₙ(x) = Q(x) mod 2ⁿ.

  Conceptual pipeline:

      Qₙ(x)
        ↓ decode bits
      ParityCode of length n
        ↓ parityCodeDescriptor
      AffineDescriptor
        ↓ AffineRealizes
      Tⁿ(x)

  IMPORTANT:
  The traditional definition of `Qₙ(x)` obtains those bits by
  walking the orbit.  This interface therefore does NOT yet solve
  random access to the n-th parity bit, nor efficient evaluation of
  the n-step affine descriptor from `(x, n)` alone.

  No claim is made that `Q` can be computed efficiently.
  Existence of the parity code is not an algorithm for its n-th bit.
-/


/-!
  ## RESEARCH QUESTION — NOT A THEOREM

  Refined BBP-like objective (motivational only):

  Can the affine image of the first `n` parity bits,

      parityCodeDescriptor (Q_prefix(x, n)),

  be computed without materializing the `n` parity bits and without
  enumerating the `n` intermediate Collatz states?

  Conceptual diagram:

      (x, n)  ≟→  Dₙ  →  Tⁿ(x)

  The second arrow is already formalized by the affine theory
  (`AffineRealizes` / `realizesParityCode_affineRealizes`).

  The first arrow remains open.

  Equivalently: is there a direct map

      (x, n) ↦ parityCodeDescriptor (first n parity bits of x)

  that avoids orbit traversal?

  KNOWN here:
  * `ParityCode → AffineDescriptor` compilation is exact;
  * realized words satisfy the affine identity;
  * order of bits is recorded in `correction`.

  UNKNOWN (explicitly not claimed):
  * random access to bit n;
  * sublinear descriptor construction;
  * a BBP-style digit formula for Collatz;
  * prediction of bits via `RhinBridge` alone;
  * Collatz convergence.
-/


/-!
  ## Future: divide-and-conquer via affine composition

  Research note only, unless the theorem below compiles:

  If `D(u)` and `D(v)` are descriptors of two parity words, then

      D(u ++ v) = D(u) ⋆ D(v)

  where `⋆ = affineCompose`.

  This is the algebraic property that could support a future
  divide-and-conquer strategy on parity words.  It does not by
  itself yield random access.
-/


/--
  Descriptor of a concatenated parity word is the affine composition
  of the descriptors.  Orientation matches chronology of `u ++ v`.
-/
theorem parityCodeDescriptor_append
    (u v : ParityCode) :
    parityCodeDescriptor (u ++ v) =
      affineCompose
        (parityCodeDescriptor u)
        (parityCodeDescriptor v) := by
  induction u with
  | nil =>
      -- affineCompose affineId (parityCodeDescriptor v)
      --   = parityCodeDescriptor v
      simpa [parityCodeDescriptor, List.nil_append] using
        (affineCompose_id_left (parityCodeDescriptor v)).symm
  | cons b bs ih =>
      -- IH: parityCodeDescriptor (bs ++ v)
      --       = affineCompose (parityCodeDescriptor bs)
      --                       (parityCodeDescriptor v)
      -- Goal uses associativity of the explicit triple formula.
      -- Expand both sides through affineCompose.
      cases b <;>
        simp [parityCodeDescriptor, parityBitDescriptor,
          affineCompose, List.cons_append, ih, Nat.pow_add,
          Nat.mul_add, Nat.mul_assoc, Nat.add_assoc,
          Nat.mul_left_comm, Nat.mul_comm]


/-!
  ## Block affine transducer

  Pure algebraic lifting of a residue through a fixed affine
  descriptor.  If

      3^R · r + C = 2^S · a

  then for every high part `h`:

      3^R · (r + 2^S · h) + C = 2^S · (a + 3^R · h)

  Interpretation: if `x = r + 2^S · h` and the descriptor sends
  `r ↦ a`, the same descriptor sends

      x ↦ a + 3^R · h.

  This is the core of the block affine transducer.  It is NOT yet
  random access: the lower-block descriptor must already be known
  / certified.
-/


/--
  Algebraic high-part lift for an arbitrary affine descriptor.

  Only uses the realizing identity `ha`; no Collatz semantics.
-/
theorem affineRealizes_lift_high
    {d : AffineDescriptor} {r a h : ℕ}
    (ha : AffineRealizes d r a) :
    AffineRealizes d
      (r + 2 ^ d.pow2 * h)
      (a + 3 ^ d.pow3 * h) := by
  unfold AffineRealizes at *
  -- Goal: 3^R (r + 2^S h) + C = 2^S (a + 3^R h)
  calc
    3 ^ d.pow3 * (r + 2 ^ d.pow2 * h) + d.correction
        = 3 ^ d.pow3 * r + 3 ^ d.pow3 * (2 ^ d.pow2 * h) +
            d.correction := by
          ring
    _ = (3 ^ d.pow3 * r + d.correction) +
            3 ^ d.pow3 * (2 ^ d.pow2 * h) := by
          ring
    _ = 2 ^ d.pow2 * a + 3 ^ d.pow3 * (2 ^ d.pow2 * h) := by
          rw [ha]
    _ = 2 ^ d.pow2 * a + 2 ^ d.pow2 * (3 ^ d.pow3 * h) := by
          ring
    _ = 2 ^ d.pow2 * (a + 3 ^ d.pow3 * h) := by
          ring


/-!
  Specialization to a parity-code descriptor.  Using the already
  proved phase identities

      pow2 = bits.length
      pow3 = parityOnes bits

  one obtains the exact block transducer formula

      T^k (r + 2^k · h) = a_k(r) + 3^{m_k} · h

  when `bits` is the length-`k` parity prefix, `m = parityOnes bits`,
  and `a` is the image of the residue `r` under that prefix.

  IMPORTANT:
  this is NOT random access.  The lower-block descriptor must be
  known / certified before the lift applies.
-/


/--
  Block affine transducer specialized to `parityCodeDescriptor`.
-/
theorem parityCodeDescriptor_lift_high
    {bits : ParityCode} {r a h : ℕ}
    (ha :
      AffineRealizes
        (parityCodeDescriptor bits) r a) :
    AffineRealizes
      (parityCodeDescriptor bits)
      (r + 2 ^ bits.length * h)
      (a + 3 ^ parityOnes bits * h) := by
  -- Rewrite exponents via the existing phase lemmas, then lift.
  simpa [parityCodeDescriptor_pow2, parityCodeDescriptor_pow3] using
    (affineRealizes_lift_high (d := parityCodeDescriptor bits) ha)


/--
  Modular form of the block transducer: after lifting, the residue
  relevant for a subsequent length-`k` block is exactly

      (a + 3^m · h) mod 2^k

  where `k = bits.length` and `m = parityOnes bits`.
-/
theorem parityCodeDescriptor_lift_high_mod
    {bits : ParityCode} {r a h : ℕ}
    (ha :
      AffineRealizes
        (parityCodeDescriptor bits) r a) :
    AffineRealizes
      (parityCodeDescriptor bits)
      (r + 2 ^ bits.length * h)
      (a + 3 ^ parityOnes bits * h) ∧
      (a + 3 ^ parityOnes bits * h) % (2 ^ bits.length) =
        (a + 3 ^ parityOnes bits * h) % (2 ^ bits.length) := by
  exact ⟨parityCodeDescriptor_lift_high ha, rfl⟩


/-!
  ## Injectivity of `parityCodeDescriptor`

  Strategy (FAIL FIRST): recover the head bit from the parity of
  `correction`, cancel the first bit by left-cancellation of
  `parityBitDescriptor`, then induct on the tail.

  Observation for a word `b :: bs` with `d := parityCodeDescriptor bs`:

  * PAR (`b = false`):
        C(false :: bs) = 2 · C(bs)
    hence the correction is even.

  * IMPAR (`b = true`):
        C(true :: bs) = 3^{R(bs)} + 2 · C(bs)
    hence the correction is odd (`3^R` odd, `2·C` even).

  Therefore the head bit is recovered by

      b₀ = C mod 2.

  Conceptual decoder (not implemented as executable code here):

  * `C mod 2` recovers the first bit;
  * if even:  `C_tail = C / 2`;
  * if odd:   `R_tail = R - 1`,
              `C_tail = (C - 3^{R_tail}) / 2`.
-/


/--
  PAR head: correction of `false :: bs` is twice the tail correction,
  hence even.
-/
theorem correction_cons_false_even (bs : ParityCode) :
    Even (parityCodeDescriptor (false :: bs)).correction := by
  -- Expand: correction = 2 * (parityCodeDescriptor bs).correction
  -- `even_two_mul` is a simp lemma, so simp closes the goal.
  simp [parityCodeDescriptor, parityBitDescriptor, affineCompose,
    pow_one]


/--
  IMPAR head: correction of `true :: bs` is `3^R + 2·C`, hence odd.
-/
theorem correction_cons_true_odd (bs : ParityCode) :
    Odd (parityCodeDescriptor (true :: bs)).correction := by
  -- Expand: correction = 3^(parityCodeDescriptor bs).pow3
  --                      + 2 * (parityCodeDescriptor bs).correction
  have hform :
      (parityCodeDescriptor (true :: bs)).correction =
        3 ^ (parityCodeDescriptor bs).pow3 +
          2 * (parityCodeDescriptor bs).correction := by
    simp [parityCodeDescriptor, parityBitDescriptor, affineCompose,
      pow_one]
  rw [hform]
  -- 3^R is odd; 2·C is even; odd + even = odd.
  have h3 : Odd (3 ^ (parityCodeDescriptor bs).pow3) :=
    Odd.pow (by decide : Odd 3)
  have h2 : Even (2 * (parityCodeDescriptor bs).correction) :=
    even_two_mul _
  exact h3.add_even h2


/--
  Head bit is recovered from the parity of the correction:

      Even C(b :: bs)  ↔  b = false
-/
theorem parityCodeDescriptor_correction_even_iff_head_false
    (b : Bool) (bs : ParityCode) :
    Even (parityCodeDescriptor (b :: bs)).correction ↔ b = false := by
  cases b with
  | false =>
      constructor
      · intro _; rfl
      · intro _; exact correction_cons_false_even bs
  | true =>
      constructor
      · intro hEven
        -- correction is odd, contradiction with even
        have hOdd := correction_cons_true_odd bs
        exact (Nat.not_even_iff_odd.mpr hOdd hEven).elim
      · intro h
        cases h


/--
  Left-cancellation of a one-bit affine prefix:

      parityBitDescriptor b ⋆ d₁ = parityBitDescriptor b ⋆ d₂
        →  d₁ = d₂

  Cases:

  * `b = false`: pow3 of the tail is preserved; pow2 = 1 + tail.pow2;
    correction = 2 · tail.correction.  Cancel by Nat arithmetic.
  * `b = true`: pow3 = 1 + tail.pow3; pow2 = 1 + tail.pow2;
    correction = 3^{tail.pow3} + 2 · tail.correction.
    Cancel the common `3^R` summand and the factor 2.
-/
theorem parityBitDescriptor_left_cancel
    (b : Bool) {d₁ d₂ : AffineDescriptor}
    (h :
      affineCompose (parityBitDescriptor b) d₁ =
      affineCompose (parityBitDescriptor b) d₂) :
    d₁ = d₂ := by
  cases d₁ with
  | mk p3₁ p2₁ c₁ =>
    cases d₂ with
    | mk p3₂ p2₂ c₂ =>
      cases b with
      | false =>
        -- parityBitDescriptor false = (0,1,0)
        -- composed = (p3, 1+p2, 2*c)
        have hb : parityBitDescriptor false =
            { pow3 := 0, pow2 := 1, correction := 0 } := rfl
        rw [hb] at h
        have hp3 := congrArg AffineDescriptor.pow3 h
        have hp2 := congrArg AffineDescriptor.pow2 h
        have hc := congrArg AffineDescriptor.correction h
        simp only [affineCompose, pow_one] at hp3 hp2 hc
        have hp3' : p3₁ = p3₂ := by
          simpa using hp3
        have hp2' : p2₁ = p2₂ := by
          have : 1 + p2₁ = 1 + p2₂ := by
            simpa using hp2
          exact Nat.add_left_cancel this
        have hc' : c₁ = c₂ := by
          have : 2 * c₁ = 2 * c₂ := by
            simpa [hp3'] using hc
          exact Nat.mul_left_cancel (Nat.succ_pos 1) this
        simp [hp3', hp2', hc']
      | true =>
        -- parityBitDescriptor true = (1,1,1)
        -- composed = (1+p3, 1+p2, 3^p3 + 2*c)
        have hb : parityBitDescriptor true =
            { pow3 := 1, pow2 := 1, correction := 1 } := rfl
        rw [hb] at h
        have hp3 := congrArg AffineDescriptor.pow3 h
        have hp2 := congrArg AffineDescriptor.pow2 h
        have hc := congrArg AffineDescriptor.correction h
        simp only [affineCompose, pow_one] at hp3 hp2 hc
        have hp3' : p3₁ = p3₂ := by
          have : 1 + p3₁ = 1 + p3₂ := by
            simpa using hp3
          exact Nat.add_left_cancel this
        have hp2' : p2₁ = p2₂ := by
          have : 1 + p2₁ = 1 + p2₂ := by
            simpa using hp2
          exact Nat.add_left_cancel this
        have hc' : c₁ = c₂ := by
          have hc2 : 3 ^ p3₁ + 2 * c₁ = 3 ^ p3₁ + 2 * c₂ := by
            simpa [hp3'] using hc
          exact Nat.mul_left_cancel (Nat.succ_pos 1) (Nat.add_left_cancel hc2)
        simp [hp3', hp2', hc']


/--
  Empty parity word is the unique word with `pow2 = 0`.
-/
theorem parityCodeDescriptor_pow2_eq_zero_iff
    (bits : ParityCode) :
    (parityCodeDescriptor bits).pow2 = 0 ↔ bits = [] := by
  constructor
  · intro h
    cases bits with
    | nil => rfl
    | cons b bs =>
        have hlen :
            (parityCodeDescriptor (b :: bs)).pow2 =
              (b :: bs).length :=
          parityCodeDescriptor_pow2 (b :: bs)
        -- length (b::bs) = succ _ ≠ 0
        rw [hlen] at h
        cases h
  · intro h
    subst h
    simp [parityCodeDescriptor, affineId]


/--
  `parityCodeDescriptor` is injective:

      D(u) = D(v)  ⇒  u = v

  Cases:

  * `[]` vs `[]`;
  * `[]` vs `b :: bs` / `b :: bs` vs `[]` — distinguished by `pow2`
    (`D([]).pow2 = 0`, while a nonempty word has `pow2 = length > 0`);
  * `b :: bs` vs `c :: cs` — recover `b = c` from parity of
    `correction`, left-cancel the common bit, apply IH on the tails.

  INTERPRETATION:
  `parityCodeDescriptor_injective` shows that the full affine
  descriptor is a **collision-free** encoding of the finite parity
  word.  Hence

      ParityCode  ↪  AffineDescriptor.

  The triple `(pow3, pow2, correction)` retains enough information to
  distinguish every finite word.

  This is an informational statement only:
  any method whose intermediate result is the complete
  `AffineDescriptor` still represents the parity-prefix information
  losslessly.  It rules out the naive hope that `AffineDescriptor` is
  by itself a many-to-one compression of the itinerary.

  It does NOT prove a time-complexity lower bound, nor that the
  descriptor cannot be computed by some other sublinear algorithm.
  Lean has not proved any runtime complexity bound here.
-/
theorem parityCodeDescriptor_injective :
    Function.Injective parityCodeDescriptor := by
  intro u
  induction u with
  | nil =>
      intro v hv
      -- D([]) = D(v) ⇒ pow2(v) = 0 ⇒ v = []
      have hpow :
          (parityCodeDescriptor v).pow2 = 0 := by
        have := congrArg AffineDescriptor.pow2 hv
        simpa [parityCodeDescriptor, affineId] using this.symm
      exact ((parityCodeDescriptor_pow2_eq_zero_iff v).mp hpow).symm
  | cons b bs ih =>
      intro v hv
      cases v with
      | nil =>
          -- nonempty vs empty: pow2 contradiction
          have hpow :
              (parityCodeDescriptor (b :: bs)).pow2 = 0 := by
            have := congrArg AffineDescriptor.pow2 hv
            simpa [parityCodeDescriptor, affineId] using this
          have hne :
              (parityCodeDescriptor (b :: bs)).pow2 ≠ 0 := by
            intro h0
            have : b :: bs = [] :=
              (parityCodeDescriptor_pow2_eq_zero_iff (b :: bs)).mp h0
            cases this
          exact (hne hpow).elim
      | cons c cs =>
          -- First recover b = c from correction parity.
          have hcorr :
              (parityCodeDescriptor (b :: bs)).correction =
                (parityCodeDescriptor (c :: cs)).correction :=
            congrArg AffineDescriptor.correction hv
          have hc_iff :=
            parityCodeDescriptor_correction_even_iff_head_false c cs
          have hbc : b = c := by
            cases b with
            | false =>
                have hEven :
                    Even
                      (parityCodeDescriptor (false :: bs)).correction :=
                  correction_cons_false_even bs
                have hEvenC :
                    Even
                      (parityCodeDescriptor (c :: cs)).correction := by
                  rwa [← hcorr]
                have : c = false := hc_iff.mp hEvenC
                simp [this]
            | true =>
                have hOdd := correction_cons_true_odd bs
                have hNotEven :
                    ¬ Even
                      (parityCodeDescriptor (true :: bs)).correction :=
                  Nat.not_even_iff_odd.mpr hOdd
                have hNotEvenC :
                    ¬ Even
                      (parityCodeDescriptor (c :: cs)).correction := by
                  simpa [hcorr] using hNotEven
                cases c with
                | false =>
                    exact (hNotEvenC (correction_cons_false_even cs)).elim
                | true =>
                    rfl
          -- Substitute common head bit.
          subst hbc
          -- Equal total descriptors ⇒ equal composed tails after cancel.
          have hcomp :
              affineCompose
                  (parityBitDescriptor b)
                  (parityCodeDescriptor bs) =
                affineCompose
                  (parityBitDescriptor b)
                  (parityCodeDescriptor cs) := by
            simpa [parityCodeDescriptor] using hv
          have htail :
              parityCodeDescriptor bs = parityCodeDescriptor cs :=
            parityBitDescriptor_left_cancel b hcomp
          have hbs : bs = cs := ih htail
          simp [hbs]


/-!
  ## Transducer example

  Take `bits = [true, true]`, so

      D = (2, 2, 5)

  Choose residue `r = 3`, high part `h = 6`:

      x = r + 2^2 · h = 3 + 4 · 6 = 27

  Base realization:

      3² · 3 + 5 = 4 · 8

  so the transducer yields

      3² · 27 + 5 = 4 · (8 + 9 · 6) = 4 · 62

  i.e. `T²(27) = 62` under the parity prefix `[true, true]`.
-/


example :
    parityCodeDescriptor [true, true] =
      { pow3 := 2, pow2 := 2, correction := 5 } := by
  native_decide


example :
    AffineRealizes (parityCodeDescriptor [true, true]) 3 8 := by
  native_decide


example :
    AffineRealizes (parityCodeDescriptor [true, true]) 27 62 := by
  -- Direct check; equivalently via the lift lemma from (3 ↦ 8), h = 6.
  native_decide


example :
    AffineRealizes (parityCodeDescriptor [true, true]) 27 62 := by
  have ha :
      AffineRealizes (parityCodeDescriptor [true, true]) 3 8 := by
    native_decide
  -- r=3, h=6: 3 + 2^2·6 = 27, 8 + 3^2·6 = 62
  have hlift :=
    parityCodeDescriptor_lift_high (bits := [true, true])
      (r := 3) (a := 8) (h := 6) ha
  -- Reduce length / parityOnes and evaluate the arithmetic.
  simpa [parityOnes, List.length_cons, List.length_nil] using hlift


-- Collision-free on the classical order-swap pair (already present above;
-- restated here as part of the injectivity package).
example :
    parityCodeDescriptor [true, false] ≠
      parityCodeDescriptor [false, true] := by
  native_decide


/-!
# EXACT REFINEMENT BEFORE MINIMIZATION

The correct recurrence is

    E_k → E_{k+1}

on **exact** states `(m, a)`.

Only afterwards does one project

    (m, a) ↦ (a mod 2^k ,  3^m mod 2^k).

Do NOT claim a direct recurrence between minimized machines:

    S_k^{min}  ⇏  S_{k+1}^{min}

without additional information.

Layers kept deliberately separate (FAIL FIRST):

1. exact state `(m, a)`;
2. modular projection;
3. future minimization.

In particular, this file does **not** assert that the projected pair
`(m, a mod 2^k)` is closed under refinement.  The counter-example
`exact_projection_not_closed_mod2` below records that knowing only
`a mod 2^k` can be insufficient to climb one precision level.

Exact one-level generator formalized here:

    (m, a, β)  ↦  ( m + b ,  (3^b · (a + 3^m · β) + b) / 2 )

where

    b = (a + β) mod 2,     β ∈ {0, 1}.

Reuses (does not duplicate):
`AffineDescriptor`, `AffineRealizes`, `ParityCode`, `ParityStep`,
`parityOnes`, `parityCodeDescriptor`, `affineRealizes_lift_high`,
`parityCodeDescriptor_lift_high`, `parityCodeDescriptor_injective`,
`parityStep_affineRealizes`, `parityCodeDescriptor_append`.
-/


/--
  Exact parity-tracking state before any modular projection.

  * `oddCount` = `m` = number of odd (IMPAR) steps so far;
  * `value`    = `a` = exact image under the prefix (not reduced mod 2^k).
-/
structure ExactParityState where
  oddCount : ℕ
  value    : ℕ
  deriving DecidableEq, Repr


/-- Bit of lift: `true ↦ 1`, `false ↦ 0`. -/
def parityLiftBit (β : Bool) : ℕ :=
  if β then 1 else 0


theorem parityLiftBit_le_one (β : Bool) : parityLiftBit β ≤ 1 := by
  cases β <;> simp [parityLiftBit]


theorem parityLiftBit_mod_two (β : Bool) :
    parityLiftBit β % 2 = parityLiftBit β := by
  cases β <;> simp [parityLiftBit]


/-- Exact one-level lift of the value: `a + 3^m · β`. -/
def exactLiftValue (s : ExactParityState) (β : Bool) : ℕ :=
  s.value + 3 ^ s.oddCount * parityLiftBit β


/-- Next normalized parity bit of the lifted value: `y mod 2`. -/
def exactNextBit (s : ExactParityState) (β : Bool) : ℕ :=
  exactLiftValue s β % 2


/--
  Because `3^m` is odd,

      (a + 3^m · β) ≡ a + β  (mod 2).

  This is the exact bit identity

      b_k ≡ a + β (mod 2).
-/
theorem exactNextBit_eq
    (s : ExactParityState) (β : Bool) :
    exactNextBit s β =
      (s.value + parityLiftBit β) % 2 := by
  unfold exactNextBit exactLiftValue
  have h3 : (3 ^ s.oddCount) % 2 = 1 :=
    Nat.odd_iff.mp (Odd.pow (by decide : Odd 3))
  -- (a + 3^m·β) % 2 = (a % 2 + (3^m % 2)·(β % 2) % 2) % 2
  --                  = (a % 2 + β % 2) % 2
  --                  = (a + β) % 2
  rw [Nat.add_mod, Nat.mul_mod, h3, Nat.one_mul, Nat.mod_mod,
    ← Nat.add_mod]


/-- The next bit is a genuine bit: `b ∈ {0, 1}`. -/
theorem exactNextBit_le_one
    (s : ExactParityState) (β : Bool) :
    exactNextBit s β ≤ 1 := by
  unfold exactNextBit
  exact Nat.lt_succ_iff.mp
    (Nat.mod_lt (exactLiftValue s β) (by decide : 0 < 2))


/--
  Exact one-level refinement generator

      (m, a, β)  ↦  ( m + b ,  (3^b · y + b) / 2 )

  with `y = a + 3^m · β` and `b = y mod 2`.
-/
def refineExactParityState
    (s : ExactParityState) (β : Bool) : ExactParityState :=
  let y := exactLiftValue s β
  let b := y % 2
  {
    oddCount := s.oddCount + b
    value := (3 ^ b * y + b) / 2
  }


/-- Unfolded form of the unified exact recurrence. -/
theorem refineExactParityState_formula
    (s : ExactParityState) (β : Bool) :
    (refineExactParityState s β).oddCount =
      s.oddCount + exactNextBit s β ∧
    (refineExactParityState s β).value =
      (3 ^ exactNextBit s β * exactLiftValue s β +
        exactNextBit s β) / 2 := by
  simp [refineExactParityState, exactNextBit]


/--
  Even branch of exact refinement:

      exactNextBit s β = 0  ⇒  m' = m,  a' = y / 2.
-/
theorem refineExactParityState_bit_zero
    (s : ExactParityState) (β : Bool)
    (hb : exactNextBit s β = 0) :
    refineExactParityState s β =
      { oddCount := s.oddCount
        value := exactLiftValue s β / 2 } := by
  unfold refineExactParityState exactNextBit at *
  have hy : exactLiftValue s β % 2 = 0 := hb
  -- m' = m + 0; a' = (3^0·y + 0)/2 = y/2
  simp [hy, pow_zero]


/--
  Odd branch of exact refinement:

      exactNextBit s β = 1  ⇒  m' = m + 1,  a' = (3 · y + 1) / 2.
-/
theorem refineExactParityState_bit_one
    (s : ExactParityState) (β : Bool)
    (hb : exactNextBit s β = 1) :
    refineExactParityState s β =
      { oddCount := s.oddCount + 1
        value := (3 * exactLiftValue s β + 1) / 2 } := by
  unfold refineExactParityState exactNextBit at *
  have hy : exactLiftValue s β % 2 = 1 := hb
  -- m' = m + 1; a' = (3^1·y + 1)/2 = (3·y + 1)/2
  simp [hy, pow_one]


/--
  The exact value after refinement is always the integer half of
  `3^b · y + b` (division is exact on both branches).
-/
theorem refineExactParityState_value_mul_two
    (s : ExactParityState) (β : Bool) :
    2 * (refineExactParityState s β).value =
      3 ^ exactNextBit s β * exactLiftValue s β +
        exactNextBit s β := by
  unfold refineExactParityState exactNextBit
  set y := exactLiftValue s β
  set b := y % 2
  -- `b ∈ {0,1}` and on each branch `3^b·y + b` is even.
  have hb_le : b ≤ 1 :=
    Nat.lt_succ_iff.mp (Nat.mod_lt y (by decide : 0 < 2))
  have hdiv :
      2 * ((3 ^ b * y + b) / 2) = 3 ^ b * y + b := by
    -- Cases on the bit.
    have hb_cases : b = 0 ∨ b = 1 := by
      omega
    rcases hb_cases with hb0 | hb1
    · -- even y: y = 2*(y/2)
      have hy0 : y % 2 = 0 := hb0
      have hy_even : Even y := Nat.even_iff.mpr hy0
      have hy_eq : 2 * (y / 2) = y := by
        have := Nat.div_add_mod y 2
        simpa [hy0] using this
      simp [hb0, pow_zero, hy_eq]
    · -- odd y: 3y+1 even
      have hy1 : y % 2 = 1 := hb1
      have hy_odd : Odd y := Nat.odd_iff.mpr hy1
      -- 3 odd, y odd ⇒ 3y odd ⇒ 3y+1 even
      have h3y_odd : Odd (3 * y) := (by decide : Odd 3).mul hy_odd
      have hnum_even : Even (3 * y + 1) := h3y_odd.add_one
      have hnum_eq : 2 * ((3 * y + 1) / 2) = 3 * y + 1 := by
        have := Nat.div_add_mod (3 * y + 1) 2
        have hmod : (3 * y + 1) % 2 = 0 := Nat.even_iff.mp hnum_even
        simpa [hmod] using this
      simpa [hb1, pow_one] using hnum_eq
  simpa using hdiv


/--
  Unified boxed recurrence:

      (m', a')
        = ( m + b ,  (3^b · (a + 3^m · β) + b) / 2 )

  with `b = exactNextBit s β`.
-/
theorem refineExactParityState_unified
    (s : ExactParityState) (β : Bool) :
    let y := exactLiftValue s β
    let b := exactNextBit s β
    let s' := refineExactParityState s β
    s'.oddCount = s.oddCount + b ∧
      2 * s'.value = 3 ^ b * y + b := by
  intro y b s'
  refine ⟨?_, ?_⟩
  · simpa [y, b, s'] using
      (refineExactParityState_formula s β).1
  · simpa [y, b, s'] using
      refineExactParityState_value_mul_two s β


/-!
  ## Bridge with the already formalized transducer

  For `bits : ParityCode` with `m = parityOnes bits`, if

      AffineRealizes (parityCodeDescriptor bits) r a

  then for any refinement bit `β`, the lifted residue

      r_β = r + 2^{|bits|} · β

  is sent by the same prefix to

      y = a + 3^m · β.

  This is exactly `parityCodeDescriptor_lift_high` (not re-proved).
-/


/--
  One-bit high-part lift of a certified parity-code realization.
  Direct specialization of `parityCodeDescriptor_lift_high`.
-/
theorem parityCodeDescriptor_lift_bit
    {bits : ParityCode} {r a : ℕ} (β : Bool)
    (ha :
      AffineRealizes (parityCodeDescriptor bits) r a) :
    AffineRealizes (parityCodeDescriptor bits)
      (r + 2 ^ bits.length * parityLiftBit β)
      (a + 3 ^ parityOnes bits * parityLiftBit β) :=
  parityCodeDescriptor_lift_high ha


/-- Exact state read off a certified parity-code image. -/
def exactStateOfParity
    (bits : ParityCode) (a : ℕ) : ExactParityState where
  oddCount := parityOnes bits
  value := a


theorem exactLiftValue_exactStateOfParity
    (bits : ParityCode) (a : ℕ) (β : Bool) :
    exactLiftValue (exactStateOfParity bits a) β =
      a + 3 ^ parityOnes bits * parityLiftBit β := by
  simp [exactLiftValue, exactStateOfParity]


/--
  After lifting by a single bit `β`, the next normalized parity bit is

      y mod 2 = (a + β) mod 2.
-/
theorem exactNextBit_exactStateOfParity
    (bits : ParityCode) (a : ℕ) (β : Bool) :
    exactNextBit (exactStateOfParity bits a) β =
      (a + parityLiftBit β) % 2 := by
  simpa [exactStateOfParity] using
    exactNextBit_eq (exactStateOfParity bits a) β


/--
  Lifted residue / image pair under a certified parity prefix.
-/
theorem parityCodeDescriptor_lift_bit_exact
    {bits : ParityCode} {r a : ℕ} (β : Bool)
    (ha :
      AffineRealizes (parityCodeDescriptor bits) r a) :
    let s := exactStateOfParity bits a
    let rβ := r + 2 ^ bits.length * parityLiftBit β
    let y := exactLiftValue s β
    AffineRealizes (parityCodeDescriptor bits) rβ y := by
  intro s rβ y
  -- y = a + 3^m · β by definition of exactStateOfParity
  simpa [s, rβ, y, exactLiftValue_exactStateOfParity] using
    (parityCodeDescriptor_lift_bit (bits := bits) (r := r) (a := a) β ha)


/-- Boolean form of the next exact bit. -/
def exactNextBool (s : ExactParityState) (β : Bool) : Bool :=
  decide (exactNextBit s β = 1)


theorem exactNextBool_true_iff
    (s : ExactParityState) (β : Bool) :
    exactNextBool s β = true ↔ exactNextBit s β = 1 := by
  simp [exactNextBool]


theorem exactNextBool_false_iff
    (s : ExactParityState) (β : Bool) :
    exactNextBool s β = false ↔ exactNextBit s β = 0 := by
  simp [exactNextBool]
  have hle := exactNextBit_le_one s β
  omega


/--
  The exact refinement step is a genuine `ParityStep` from the lifted
  value `y` to the refined value `a'`.
-/
theorem refineExactParityState_parityStep
    (s : ExactParityState) (β : Bool) :
    ParityStep
      (exactNextBool s β)
      (exactLiftValue s β)
      (refineExactParityState s β).value := by
  unfold ParityStep exactNextBool
  have hmul := refineExactParityState_value_mul_two s β
  have hle := exactNextBit_le_one s β
  -- Case split on the next bit ∈ {0,1}.
  have hbit : exactNextBit s β = 0 ∨ exactNextBit s β = 1 := by
    omega
  rcases hbit with hb0 | hb1
  · -- PAR branch
    have hdecide : decide (exactNextBit s β = 1) = false := by
      simp [hb0]
    simp [hdecide]
    -- Even y and y = 2 * a'
    have hy0 : exactLiftValue s β % 2 = 0 := by
      simpa [exactNextBit] using hb0
    have hy_even : Even (exactLiftValue s β) := Nat.even_iff.mpr hy0
    refine ⟨hy_even, ?_⟩
    -- From hmul with b=0: 2*a' = y
    have hmul0 :
        2 * (refineExactParityState s β).value =
          exactLiftValue s β := by
      simpa [hb0, pow_zero] using hmul
    exact hmul0.symm
  · -- IMPAR branch
    have hdecide : decide (exactNextBit s β = 1) = true := by
      simp [hb1]
    simp [hdecide]
    have hy1 : exactLiftValue s β % 2 = 1 := by
      simpa [exactNextBit] using hb1
    have hy_odd : Odd (exactLiftValue s β) := Nat.odd_iff.mpr hy1
    refine ⟨hy_odd, ?_⟩
    -- From hmul with b=1: 2*a' = 3*y + 1
    have hmul1 :
        2 * (refineExactParityState s β).value =
          3 * exactLiftValue s β + 1 := by
      simpa [hb1, pow_one] using hmul
    exact hmul1.symm


/--
  Bridge: extending a certified parity prefix by the exact next bit
  realizes the refined exact state on the lifted residue.

  Uses `parityCodeDescriptor_lift_high`, `parityStep_affineRealizes`,
  `parityCodeDescriptor_append` and `affineCompose_realizes`.
-/
theorem refineExactParityState_affineRealizes
    {bits : ParityCode} {r a : ℕ} (β : Bool)
    (ha :
      AffineRealizes (parityCodeDescriptor bits) r a) :
    let s := exactStateOfParity bits a
    let s' := refineExactParityState s β
    let rβ := r + 2 ^ bits.length * parityLiftBit β
    let b := exactNextBool s β
    AffineRealizes
      (parityCodeDescriptor (bits ++ [b]))
      rβ s'.value := by
  intro s s' rβ b
  -- Prefix sends rβ ↦ y
  have hPrefix :
      AffineRealizes (parityCodeDescriptor bits) rβ
        (exactLiftValue s β) := by
    simpa [s, rβ] using
      parityCodeDescriptor_lift_bit_exact (bits := bits) (r := r)
        (a := a) β ha
  -- One more ParityStep y ↦ s'.value
  have hStep :
      ParityStep b (exactLiftValue s β) s'.value := by
    simpa [s, s', b] using refineExactParityState_parityStep s β
  have hBit :
      AffineRealizes (parityBitDescriptor b)
        (exactLiftValue s β) s'.value :=
    parityStep_affineRealizes hStep
  -- Descriptor of the singleton extension
  have hDesc :
      parityCodeDescriptor (bits ++ [b]) =
        affineCompose
          (parityCodeDescriptor bits)
          (parityBitDescriptor b) := by
    -- parityCodeDescriptor [b] = parityBitDescriptor b
    have hsing :
        parityCodeDescriptor [b] = parityBitDescriptor b := by
      simp [parityCodeDescriptor, affineCompose_id_right]
    simpa [hsing] using parityCodeDescriptor_append bits [b]
  -- Compose realizations
  have hComp :=
    affineCompose_realizes hPrefix hBit
  simpa [hDesc, s', rβ] using hComp


