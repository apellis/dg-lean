import DG.Positive.ScalarExtensionBimodule
import DG.Positive.ScalarExtensionDerived
import DG.Category.Derived.DGBimodule

/-!
# Base change of the derived tensor product with a dg bimodule

Let `K` be a commutative ring and `X` a dg `(A, B)`-bimodule which is K-projective as a left dg
`A`-module. Then `K ⊗_ℤ X` is a dg `(K ⊗ A, K ⊗ B)`-bimodule which is K-projective as a left
dg `K ⊗ A`-module (`DG.ExtendScalars.isKProjective_baseChange`), so the derived tensor product
`(K ⊗ X) ⊗^L_{K ⊗ B} -` is defined (`DG.DGBimodule.derivedTensor`), and:

* `DG.ExtendScalars.derivedTensorBaseChangeSelfIso`: `(K ⊗ X) ⊗^L_{K ⊗ B} (K ⊗ B) ≅ K ⊗_ℤ X`;
* `DG.ExtendScalars.K0_mk_derivedTensor_self`: if `X` is moreover compact in `D(A)`, then in
  `K₀(K ⊗ A)`, `[(K ⊗ X) ⊗^L_{K ⊗ B} (K ⊗ B)] = K₀(unitHom) [X ⊗^L_B B]`: the class of the
  base-changed functor applied to `K ⊗ B = unitHom^*(B)` is the image of the class of the
  original functor applied to `B`.
-/

open CategoryTheory
open scoped TensorProduct

universe w₁ w₂ w₃ w₄ u

noncomputable section

namespace DG

namespace ExtendScalars

variable (K : Type u) [CommRing K] {A B : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]
  [Ring B] [DGAddCommGroup B] [DGRing B]
  {X : Type u} [AddCommGroup X] [DGAddCommGroup X] [Module A X] [Module Bᵐᵒᵖ X]
  [DGBimodule A B X] (hX : IsKProjective.{u} A X)

omit [DGRing B] in
include hX in
/-- `K ⊗_ℤ X` is K-projective as a left dg `K ⊗ A`-module when `X` is K-projective over `A`. -/
theorem isKProjective_tensor :
    IsKProjective.{u} (ExtendScalars K A) (DegreeZeroRing K ⊗[ℤ] X) :=
  isKProjective_baseChange K (P := DGModuleCat.of A X) hX

section Iso

variable [CatModule.HasDerivedCategory.{w₁, u} (SingleObj (ExtendScalars K B))]
  [CatModule.HasDerivedCategory.{w₂, u} (SingleObj (ExtendScalars K A))]
  [DG.HasDerivedCategory.{w₃, u} (ExtendScalars K B)]
  [DG.HasDerivedCategory.{w₄, u} (ExtendScalars K A)]

/-- `(K ⊗ X) ⊗^L_{K ⊗ B} (K ⊗ B) ≅ K ⊗_ℤ X` in `D(K ⊗ A)`. -/
def derivedTensorBaseChangeSelfIso :
    (DGBimodule.derivedTensor.{w₁, w₂, w₃, w₄} (ExtendScalars K A) (ExtendScalars K B)
        (DegreeZeroRing K ⊗[ℤ] X) (isKProjective_tensor (B := B) K hX)).obj
        (DerivedCategory.Q.obj (DGModuleCat.of (ExtendScalars K B) (ExtendScalars K B))) ≅
      DerivedCategory.Q.obj ((baseChange K A).obj (DGModuleCat.of A X)) :=
  DGBimodule.derivedTensorSelfIso (ExtendScalars K A) (ExtendScalars K B)
    (DegreeZeroRing K ⊗[ℤ] X) (isKProjective_tensor (B := B) K hX)

end Iso

section K0

variable [CatModule.HasDerivedCategory.{w₁, u} (SingleObj (ExtendScalars K B))]
  [CatModule.HasDerivedCategory.{w₂, u} (SingleObj (ExtendScalars K A))]
  [DG.HasDerivedCategory.{w₃, u} (ExtendScalars K B)]
  [DG.HasDerivedCategory.{u, u} (ExtendScalars K A)]
  [CatModule.HasDerivedCategory.{w₄, u} (SingleObj B)]
  [CatModule.HasDerivedCategory.{w₄, u} (SingleObj A)]
  [DG.HasDerivedCategory.{w₄, u} B] [DG.HasDerivedCategory.{u, u} A]
  (hc : IsCompact.{u} (DerivedCategory.Q.obj (DGModuleCat.of A X)))

/-- **`K₀` of the base-changed derived tensor product**: for `X` K-projective as a left dg
`A`-module and compact in `D(A)`,
`[(K ⊗ X) ⊗^L_{K ⊗ B} (K ⊗ B)] = K₀(unitHom) [X ⊗^L_B B]` in `K₀(K ⊗ A)`. -/
theorem K0_mk_derivedTensor_self :
    DG.K0.mk (⟨(DGBimodule.derivedTensor.{w₁, w₂, w₃, u} (ExtendScalars K A) (ExtendScalars K B)
        (DegreeZeroRing K ⊗[ℤ] X) (isKProjective_tensor (B := B) K hX)).obj
        (DerivedCategory.Q.obj (DGModuleCat.of (ExtendScalars K B) (ExtendScalars K B))),
      (isCompact_Q_baseChange_obj K (P := DGModuleCat.of A X) hX hc).of_iso
        (derivedTensorBaseChangeSelfIso K hX)⟩ : PerfectDerivedCategory (ExtendScalars K A)) =
      DGRing.K0.map (unitHom K A) (DG.K0.mk (⟨
        (DGBimodule.derivedTensor.{w₄, w₄, w₄, u} A B X hX).obj
          (DerivedCategory.Q.obj (DGModuleCat.of B B)),
        hc.of_iso (DGBimodule.derivedTensorSelfIso A B X hX)⟩ : PerfectDerivedCategory A)) := by
  exact (DG.K0.mk_eq_of_iso_obj (derivedTensorBaseChangeSelfIso K hX)).trans
    ((K0_map_mk K (P := DGModuleCat.of A X) hX hc).symm.trans
      (congrArg _ (DG.K0.mk_eq_of_iso_obj (DGBimodule.derivedTensorSelfIso A B X hX)).symm))

end K0

end ExtendScalars

end DG

end
