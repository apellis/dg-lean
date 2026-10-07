import DG.Derived.ExternalTensor
import DG.Homotopy.ExternalTensorTriangulated
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# The derived external tensor product is triangulated in each variable

For dg rings `A`, `B` and `A ⊗ B = A ᵍ⊗[ℤ] B`, the derived external tensor product
`- ⊠ᴸ - : D(A) ⥤ D(B) ⥤ D(A ⊗ B)` (`DG.DerivedCategory.externalTensor`) is computed on the
K-projective objects of the homotopy categories, through the equivalences
`DG.DerivedCategory.kProjectiveEquivalence A : KProjective A ≌ D(A)`.

* The K-projective objects form a triangulated subcategory of `K(A)` (the left orthogonal of the
  acyclic objects), and `kProjectiveEquivalence A` is a triangulated equivalence
  (`DG.DerivedCategory.kProjectiveEquivalence_isTriangulated`).
* Hence, since `X ⊠ -` and `- ⊠ Y` are triangulated on homotopy categories
  (`DG/Homotopy/ExternalTensorTriangulated.lean`), `X ⊠ᴸ -` and `- ⊠ᴸ Y` are triangulated
  functors for all `X ∈ D(A)`, `Y ∈ D(B)`: instances for `(externalTensor A B).obj X` and
  `(externalTensor A B).flip.obj Y`.
-/

open CategoryTheory Pretriangulated
open scoped TensorProduct

universe w u

noncomputable section

namespace DG

namespace DerivedCategory

section KProjective

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A] [HasDerivedCategory.{w, u} A]

instance kProjectiveEquivalence_functor_commShift :
    (kProjectiveEquivalence.{w} A).functor.CommShift ℤ :=
  inferInstanceAs ((kProjectiveFunctor.{w} A).CommShift ℤ)

instance kProjectiveEquivalence_functor_isTriangulated :
    (kProjectiveEquivalence.{w} A).functor.IsTriangulated :=
  inferInstanceAs (kProjectiveFunctor.{w} A).IsTriangulated

/-- The inverse of `kProjectiveEquivalence A` (a K-projective resolution functor) commutes with
the shifts. -/
noncomputable instance kProjectiveEquivalence_inverse_commShift :
    (kProjectiveEquivalence.{w} A).inverse.CommShift ℤ :=
  (kProjectiveEquivalence.{w} A).commShiftInverse ℤ

instance kProjectiveEquivalence_commShift : (kProjectiveEquivalence.{w} A).CommShift ℤ :=
  (kProjectiveEquivalence.{w} A).commShift_of_functor ℤ

/-- **`KProjective A ≌ D(A)` is a triangulated equivalence.** -/
instance kProjectiveEquivalence_isTriangulated : (kProjectiveEquivalence.{w} A).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ inferInstance

end KProjective

variable {A B : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B]

local notation "𝒜" => DGAlgebra.gradingSubmodule ℤ A
local notation "ℬ" => DGAlgebra.gradingSubmodule ℤ B
local notation "AB" => 𝒜 ᵍ⊗[ℤ] ℬ

variable [HasDerivedCategory.{w, u} A] [HasDerivedCategory.{w, u} B]
  [HasDerivedCategory.{w, u} (DGAlgebra.gradingSubmodule ℤ A ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ B)]

/-- **`X ⊠ᴸ -` commutes with the shifts**, for every `X ∈ D(A)`. -/
noncomputable instance externalTensor_obj_commShift (X : DerivedCategory.{w, u} A) :
    ((externalTensor A B).obj X).CommShift ℤ :=
  inferInstanceAs (((((kProjectiveEquivalence.{w} B).inverse ⋙
    (HomotopyCategory.subcategoryKProjective.{u} B).ι) ⋙
      (ExternalTensor.homotopyFunctor.{u} A B).obj
        ((HomotopyCategory.subcategoryKProjective.{u} A).ι.obj
          ((kProjectiveEquivalence.{w} A).inverse.obj X))) ⋙ Qh).CommShift ℤ)

/-- **`X ⊠ᴸ -` is a triangulated functor** `D(B) ⥤ D(A ⊗ B)`, for every `X ∈ D(A)`. -/
instance externalTensor_obj_isTriangulated (X : DerivedCategory.{w, u} A) :
    ((externalTensor A B).obj X).IsTriangulated :=
  inferInstanceAs (((((kProjectiveEquivalence.{w} B).inverse ⋙
    (HomotopyCategory.subcategoryKProjective.{u} B).ι) ⋙
      (ExternalTensor.homotopyFunctor.{u} A B).obj
        ((HomotopyCategory.subcategoryKProjective.{u} A).ι.obj
          ((kProjectiveEquivalence.{w} A).inverse.obj X))) ⋙ Qh).IsTriangulated)

variable (A) in
/-- `- ⊠ᴸ Y` as a composite: a K-projective resolution in the first variable, `- ⊠ P_Y` on
homotopy categories, and the localization functor. -/
def externalTensorFlipObjIso (Y : DerivedCategory.{w, u} B) :
    (externalTensor A B).flip.obj Y ≅
      (((kProjectiveEquivalence.{w} A).inverse ⋙
        (HomotopyCategory.subcategoryKProjective.{u} A).ι) ⋙
        (ExternalTensor.homotopyFunctor.{u} A B).flip.obj
          ((HomotopyCategory.subcategoryKProjective.{u} B).ι.obj
            ((kProjectiveEquivalence.{w} B).inverse.obj Y))) ⋙ Qh :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ =>
    (Category.comp_id _).trans (Category.id_comp _).symm

/-- **`- ⊠ᴸ Y` commutes with the shifts**, for every `Y ∈ D(B)`. -/
noncomputable instance externalTensor_flip_obj_commShift (Y : DerivedCategory.{w, u} B) :
    ((externalTensor A B).flip.obj Y).CommShift ℤ :=
  Functor.CommShift.ofIso (externalTensorFlipObjIso A Y).symm ℤ

instance (Y : DerivedCategory.{w, u} B) :
    NatTrans.CommShift (externalTensorFlipObjIso A Y).symm.hom ℤ :=
  Functor.CommShift.ofIso_compatibility _ ℤ

/-- **`- ⊠ᴸ Y` is a triangulated functor** `D(A) ⥤ D(A ⊗ B)`, for every `Y ∈ D(B)`. -/
instance externalTensor_flip_obj_isTriangulated (Y : DerivedCategory.{w, u} B) :
    ((externalTensor A B).flip.obj Y).IsTriangulated :=
  Functor.isTriangulated_of_iso (externalTensorFlipObjIso A Y).symm

end DerivedCategory

end DG
