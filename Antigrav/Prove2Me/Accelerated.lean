import Mathlib

/-!
# Accelerated ANTIGRAV map

Minimal extraction of the definitions needed to state a future Prove2Me bridge.
The mathematical authority remains `main.lean`; this module is imported there.
The Prove2Me Syracuse definition is intentionally not guessed here.
-/

def v2 (n : ℕ) : ℕ :=
  padicValNat 2 n


def collatzExponent (m : ℕ) : ℕ :=
  v2 (3 * m + 1)


def Tstar (m : ℕ) : ℕ :=
  (3 * m + 1) / 2 ^ collatzExponent m

