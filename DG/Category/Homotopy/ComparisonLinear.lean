import DG.Category.Homotopy.Comparison
import DG.Category.Homotopy.Linear
import DG.Homotopy.ShiftLinear

/-!
# Linearity of the one-object comparison

Let `A` be a dg `R`-algebra. The one-object category `SingleObj A` is a dg category over `R`
(`DG.SingleObj.dgLinear`), so dg modules over it and their homotopy category are `R`-linear
(`DG.CatModule.instLinear`, `DG.CatModule.HomotopyCategory.instLinear`). The scalar
endomorphism `r • 𝟙` of the unique object is `algebraMap R A r`, so the comparison functors with
dg `A`-modules are `R`-linear:

* `DG.CatModule.toDGModuleCat_linear`: evaluation at the unique object
  `CatModule (SingleObj A) ⥤ DGModuleCat A`;
* `DG.CatModule.HomotopyCategory.toDGHomotopyCategory_linear`: the induced functor
  `HomotopyCategory (SingleObj A) ⥤ DG.HomotopyCategory A` (an equivalence,
  `DG.CatModule.HomotopyCategory.singleObjEquivalence`).
-/

open CategoryTheory

universe w u

namespace DG

namespace CatModule

variable (R : Type*) (A : Type u) [CommRing R] [Ring A] [Algebra R A] [DGAddCommGroup A]
  [DGRing A] [DGAlgebra R A]

/-- Evaluation at the unique object, `CatModule (SingleObj A) ⥤ DGModuleCat A`, is
`R`-linear. -/
instance toDGModuleCat_linear : (toDGModuleCat.{w} A).Linear R where
  map_smul {M N} φ r := DGModuleCat.hom_ext_apply fun m => by
    change N.act (r • 𝟙 (SingleObj.star A)) (φ.app _ m) =
      N.act (X := SingleObj.star A) (Y := SingleObj.star A) (algebraMap R A r) (φ.app _ m)
    rw [DG.SingleObj.smul_id_eq_algebraMap]

namespace HomotopyCategory

/-- The comparison functor `HomotopyCategory (SingleObj A) ⥤ DG.HomotopyCategory A` is
`R`-linear. -/
instance toDGHomotopyCategory_linear : (toDGHomotopyCategory.{w} A).Linear R := by
  have : (quotient (SingleObj A) ⋙ toDGHomotopyCategory.{w} A).Linear R :=
    Functor.linear_of_iso R (toDGHomotopyCategoryFactors A).symm
  exact Functor.linear_of_full_essSurj_comp (quotient (SingleObj A)) _

end HomotopyCategory

end CatModule

end DG
