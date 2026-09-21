import Antigrav.Prove2Me.Accelerated
import Antigrav.Prove2Me.AffineCore

/-!
# ANTIGRAV / Prove2Me bridge boundary

This module contains bridge statements only.  It deliberately does not define
Prove2Me's Syracuse map: its exact Lean declaration and normalization convention
must be read from the Prove2Me DAG before the first unconditional bridge can be
stated.

`Prove2MeSyracuseSpec` is therefore an explicit, temporary interface obligation,
not a claim that Prove2Me uses this definition.  In particular, no theorem in
this file is suitable for publication until the external `syracuse` declaration
has been imported and the hypothesis below has been discharged from its source.
-/

/--
Temporary interface obligation for a candidate Prove2Me Syracuse map.

The restriction to odd inputs makes the expected accelerated-map boundary
explicit.  Whether Prove2Me's map is accelerated, total, and oriented in this
direction is currently **UNIMPLEMENTED** pending read-only DAG access.
-/
def Prove2MeSyracuseSpec (syracuse : ℕ → ℕ) : Prop :=
  ∀ m, Odd m → syracuse m = Tstar m

/--
First conditional bridge statement.  This only projects a supplied, formally
verified interface obligation; it creates no mathematical or Prove2Me authority.
-/
theorem tstar_eq_prove2me_syracuse_of_spec
    (syracuse : ℕ → ℕ)
    (hSpec : Prove2MeSyracuseSpec syracuse)
    {m : ℕ} (hm : Odd m) :
    Tstar m = syracuse m := by
  exact (hSpec m hm).symm
