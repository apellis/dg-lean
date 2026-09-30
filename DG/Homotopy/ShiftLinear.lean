import DG.Homotopy.ForgetTriangulated

/-!
# Linearity of the shift and forgetful functors on the homotopy category

Let `A` be a dg `R`-algebra. The homotopy category `DG.HomotopyCategory A` is `R`-linear
(`DG.HomotopyCategory.instLinear`), and so is the quotient functor from dg modules. This file
shows:

* `DG.HomotopyCategory.shiftFunctor_linear`: the shift functors of `DG.HomotopyCategory A` are
  `R`-linear; hence both sides of the commutation isomorphism
  `(quotient A).commShiftIso n : shiftFunctor _ n ⋙ quotient A ≅ quotient A ⋙ shiftFunctor _ n`
  are `R`-linear functors;
* `DG.HomotopyCategory.forget_linear`: the forgetful functor
  `DG.HomotopyCategory.forget R A` to Mathlib's homotopy category of cochain complexes of
  `R`-modules is `R`-linear.

Both are deduced from the corresponding statements on `DGModuleCat A` with two general
lemmas, `CategoryTheory.Functor.linear_of_iso` and
`CategoryTheory.Functor.linear_of_full_essSurj_comp`, the `R`-linear analogues of Mathlib's
`Functor.additive_of_iso` and `Functor.additive_of_full_essSurj_comp`.
-/

open CategoryTheory

universe v u w

-- Mathlib now provides `Functor.linear_of_iso` and
-- `Functor.linear_of_full_essSurj_comp` under their original names.

namespace DG

namespace HomotopyCategory

variable (R : Type w) (A : Type u) [CommRing R] [Ring A] [DGAddCommGroup A] [Algebra R A]
  [DGRing A] [DGAlgebra R A]

/-- The shift functors of the homotopy category of a dg `R`-algebra are `R`-linear. -/
instance (priority := 100) shiftFunctor_linear (n : ℤ) :
    (shiftFunctor (HomotopyCategory.{v} A) n).Linear R := by
  have : (quotient A ⋙ shiftFunctor (HomotopyCategory.{v} A) n).Linear R :=
    Functor.linear_of_iso R ((quotient A).commShiftIso n)
  exact Functor.linear_of_full_essSurj_comp (quotient A) _

/-- The forgetful functor from the homotopy category of dg `A`-modules to the homotopy category
of cochain complexes of `R`-modules is `R`-linear. -/
instance forget_linear : (forget.{v} R A).Linear R := by
  have : (quotient A ⋙ forget.{v} R A).Linear R := Functor.linear_of_iso R (forgetFactors R A).symm
  exact Functor.linear_of_full_essSurj_comp (quotient A) _

end HomotopyCategory

end DG
