import DG.Derived.ExternalTensorOver
import DG.Homotopy.ExternalTensorKProjective
import DG.Homotopy.Forget

/-!
# The derived external tensor product over `R` on K-projective modules

Let `R` be a commutative ring and `A`, `B` dg `R`-algebras. For K-projective dg modules `P` over
`A` and `P'` over `B`, the derived external tensor product over `R` is the external tensor
product `P ⊗_R P'` (`DG.ExternalTensorOver`):

`Q P ⊠ᴸ_R Q P' ≅ Q (P ⊗_R P')` (`DG.DerivedCategory.externalTensorOverObjIso`),

and `P ⊗_R P'` is K-projective (`DG.ExternalTensorOver.isKProjective`). The isomorphism is the
composite of `Q P ⊠ᴸ Q P' ≅ Q (P ⊠ P')` (`DG.DerivedCategory.externalTensorObjIso`), derived
induction of the K-projective module `P ⊠ P'` (`DG.ExternalTensor.isKProjective`,
`DG.DGRingHom.derivedInductionObjIso`), and `(A ⊗_R B) ⊗_{A ⊗_ℤ B} (P ⊗_ℤ P') ≅ P ⊗_R P'`
(`DG.ExternalTensorOver.extendEquiv`). The `R`-module structures on `P` and `P'` are those
through `algebraMap` (`DG.DGModuleCat.Algebra`).
-/

open CategoryTheory DG.DGModuleCat.Algebra
open scoped TensorProduct

universe w w₁ w₂ u

noncomputable section

namespace DG

namespace DerivedCategory

variable (R : Type*) [CommRing R]
  {A B : Type u} [Ring A] [Algebra R A] [DGAddCommGroup A] [DGRing A] [DGAlgebra R A]
  [Ring B] [Algebra R B] [DGAddCommGroup B] [DGRing B] [DGAlgebra R B]
  [HasDerivedCategory.{w, u} A] [HasDerivedCategory.{w, u} B]
  [HasDerivedCategory.{w, u} (DGAlgebra.gradingSubmodule ℤ A ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ B)]
  [HasDerivedCategory.{w, u} (DGAlgebra.gradingSubmodule R A ᵍ⊗[R] DGAlgebra.gradingSubmodule R B)]
  [CatModule.HasDerivedCategory.{w₁, u}
    (SingleObj (DGAlgebra.gradingSubmodule ℤ A ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ B))]
  [CatModule.HasDerivedCategory.{w₂, u}
    (SingleObj (DGAlgebra.gradingSubmodule R A ᵍ⊗[R] DGAlgebra.gradingSubmodule R B))]

/-- **`Q P ⊠ᴸ_R Q P' ≅ Q (P ⊗_R P')`** for K-projective `P` and `P'`. -/
def externalTensorOverObjIso {P : DGModuleCat.{u} A} (hP : IsKProjective.{u} A P)
    {P' : DGModuleCat.{u} B} (hP' : IsKProjective.{u} B P') :
    ((externalTensorOver R A B).obj (Q.obj P)).obj (Q.obj P') ≅
      Q.obj (DGModuleCat.of (DGAlgebra.gradingSubmodule R A ᵍ⊗[R] DGAlgebra.gradingSubmodule R B)
        (ExternalTensorOver R A B P P')) :=
  (GradedTensorProduct.intComparison R A B).derivedInduction.mapIso
      (externalTensorObjIso hP hP') ≪≫
    (GradedTensorProduct.intComparison R A B).derivedInductionObjIso
      (P := DGModuleCat.of _ (P ⊗[ℤ] P')) (ExternalTensor.isKProjective hP hP') ≪≫
    Q.mapIso (ExternalTensorOver.extendEquiv R A B P P').toDGModuleCatIso

end DerivedCategory

end DG
