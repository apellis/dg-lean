import Mathlib.Algebra.Module.PUnit
import DG.Module.Basic

/-!
# The zero dg module

The trivial abelian group `PUnit` is a dg abelian group with the trivial grading and zero
differential, and a dg module over every dg ring. It is the zero object of the category of dg
modules.
-/

namespace DG

instance : DGAddCommGroup PUnit where
  grading _ := ⊤
  decomposition :=
    { decompose' := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _ }
  d := 0
  d_mem' _ := trivial
  d_d' _ := rfl

instance {A : Type*} [Ring A] [DGAddCommGroup A] : DGModule A PUnit where
  smul_mem _ _ _ _ _ _ := trivial
  d_smul' _ _ := Subsingleton.elim _ _

end DG
