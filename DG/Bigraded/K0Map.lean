import DG.Bigraded.DegreeZero
import DG.Bigraded.K0Morita
import DG.Category.Derived.InductionComp
import DG.K0.DGCategory

/-!
# `K₀` of a morphism of bigraded dg rings is `ℤ[q, q⁻¹]`-linear

Let `φ : A → B` be a morphism of dg rings preserving the weight gradings, and
`F = DG.WeightCategory.mapFunctor φ : C_A ⥤ C_B` the induced dg functor between the weight dg
categories. This file shows that `K₀(F) : K₀(C_A) → K₀(C_B)` (derived induction,
`DG.DGCategory.K0.map`) is `ℤ[q, q⁻¹]`-linear, `qⁿ` acting by the internal shift `⟨n⟩`
(`DG.WeightCategory.K0LinearMap`). No positivity or finiteness hypothesis is needed.

The internal shift `⟨s⟩` of `D(C_A)` is restriction along the dg automorphism `σₛ : k ↦ k + s`
of `C_A`. Restriction along an isomorphism of dg categories is derived induction along its
inverse (`DG.CatModule.DerivedCategory.inductionIsoRestrict`: both are left adjoint to restriction
along the inverse), so `⟨s⟩ ≅ L(σ₋ₛ)_!` (`DG.WeightCategory.internalShiftIsoInduction`), and
since `F` commutes with the `σₛ` on the nose, `K₀(F)` commutes with the internal shifts by
functoriality of `K₀` (`DG.DGCategory.K0.map_comp`).

## Main definitions and results

* `DG.CatModule.DerivedCategory.restrictEquivalenceOfIso`: for dg functors `G : C ⥤ D`,
  `G' : D ⥤ C` inverse to each other up to natural isomorphisms with degree-`0` cocycle
  components, restriction `G'^* : D(C) ⥤ D(D)` is an equivalence with inverse `G^*`;
  `DG.CatModule.DerivedCategory.inductionIsoRestrict : LG_! ≅ G'^*`.
* `DG.WeightCategory.internalShiftIsoInduction`, `DG.WeightCategory.K0_map_internalShift`:
  `[M⟨s⟩] = K₀(σ₋ₛ) [M]`.
* `DG.WeightCategory.K0LinearMap φ hφ : K₀(C_A) →ₗ[ℤ[q, q⁻¹]] K₀(C_B)`, with underlying map
  `K₀(F)`.
-/

open CategoryTheory Limits

universe w₂ w v₁ v₂ u₁ u₂ u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace DG

namespace CatModule.DerivedCategory

section Inverse

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] [DGCategory D]
  (G : C ⥤ D) [G.Additive] [G.IsDGFunctor] (G' : D ⥤ C) [G'.Additive] [G'.IsDGFunctor]
  (e : G ⋙ G' ≅ 𝟭 C) (he : ∀ X, e.hom.app X ∈ grading 0) (hde : ∀ X, d (e.hom.app X) = 0)
  (he' : ∀ X, e.inv.app X ∈ grading 0) (hde' : ∀ X, d (e.inv.app X) = 0)
  (f : G' ⋙ G ≅ 𝟭 D) (hf : ∀ X, f.hom.app X ∈ grading 0) (hdf : ∀ X, d (f.hom.app X) = 0)
  (hf' : ∀ X, f.inv.app X ∈ grading 0) (hdf' : ∀ X, d (f.inv.app X) = 0)
  [HasDerivedCategory.{max u₁ v₁ v₂ w, max u₁ v₁ v₂ w} C]
  [HasDerivedCategory.{w₂, max u₁ v₁ v₂ w} D]

/-- For dg functors `G : C ⥤ D` and `G' : D ⥤ C` which are inverse to each other up to natural
isomorphisms with degree-`0` cocycle components, restriction `G'^* : D(C) ⥤ D(D)` is an
equivalence, with inverse `G^*`. -/
def restrictEquivalenceOfIso :
    DerivedCategory.{max u₁ v₁ v₂ w, max u₁ v₁ v₂ w} C ≌
      DerivedCategory.{w₂, max u₁ v₁ v₂ w} D :=
  CategoryTheory.Equivalence.mk (restrict G') (restrict G)
    ((restrictIdIso C).symm ≪≫ (restrictNatIso e he hde he' hde').symm ≪≫
      restrictCompIso G G')
    ((restrictCompIso G' G).symm ≪≫ restrictNatIso f hf hdf hf' hdf' ≪≫ restrictIdIso D)

/-- Derived induction along `G` is restriction along a quasi-inverse `G'`: both are left adjoint
to restriction along `G`. -/
def inductionIsoRestrict :
    induction.{max u₁ v₁ v₂ w, w₂, w} G ≅ restrict G' :=
  (inductionAdjunction G).leftAdjointUniq
    (restrictEquivalenceOfIso.{w₂, w} G G' e he hde he' hde' f hf hdf hf' hdf').toAdjunction

end Inverse

end CatModule.DerivedCategory

namespace WeightCategory

open CatModule CatModule.DerivedCategory

variable {A : Type u} [Ring A] [DGAddCommGroup A] [InternalGrading A] [BigradedDGRing A]
  [DGRing A]

variable (A) in
/-- `σₜ ⋙ σₛ ≅ 𝟭` for `s + t = 0`, by `1 ∈ A⟨0⟩`. -/
def shiftFunctorCompIsoId (s t : ℤ) (h : s + t = 0) :
    shiftFunctor A s ⋙ shiftFunctor A t ≅ 𝟭 (WeightCategory A) :=
  NatIso.ofComponents (fun _ => isoOfEq (by simp [add_assoc, h]))
    (fun f => Subtype.ext (by simp))

variable [CatModule.HasDerivedCategory.{max u w, max u w} (WeightCategory A)]

variable (A) in
/-- The internal shift `⟨s⟩` (restriction along `σₛ : k ↦ k + s`) is derived induction along
`σ₋ₛ`. -/
def internalShiftIsoInduction (s : ℤ) :
    CatModule.DerivedCategory.induction.{max u w, max u w, max u w} (shiftFunctor A (-s)) ≅ internalShift.{max u w, max u w} A s :=
  inductionIsoRestrict (shiftFunctor A (-s)) (shiftFunctor A s)
    (shiftFunctorCompIsoId A (-s) s (neg_add_cancel s))
    (fun _ => mem_grading_zero_of_val_eq_one _ rfl) (fun _ => d_eq_zero_of_val_eq_one _ rfl)
    (fun _ => mem_grading_zero_of_val_eq_one _ rfl) (fun _ => d_eq_zero_of_val_eq_one _ rfl)
    (shiftFunctorCompIsoId A s (-s) (add_neg_cancel s))
    (fun _ => mem_grading_zero_of_val_eq_one _ rfl) (fun _ => d_eq_zero_of_val_eq_one _ rfl)
    (fun _ => mem_grading_zero_of_val_eq_one _ rfl) (fun _ => d_eq_zero_of_val_eq_one _ rfl)

/-- The action of `qˢ` on `K₀(C_A)` is `K₀` of the dg functor `σ₋ₛ : k ↦ k - s`. -/
theorem K0_map_internalShift (s : ℤ)
    (x : DGCategory.K0.{max u w, max u w} (WeightCategory A)) :
    DG.K0.map ((compactInternalShiftAction.{max u w, max u w} A).functor s) x =
      DGCategory.K0.map.{max u w, max u w} (shiftFunctor A (-s)) x := by
  induction x using DG.K0.induction_on with
  | zero => rw [map_zero, map_zero]
  | mk X =>
    rw [DGCategory.K0.map_mk, DG.K0.map_mk]
    exact DG.K0.mk_eq_of_iso_obj ((internalShiftIsoInduction A s).app X.obj).symm
  | neg x hx => rw [map_neg, map_neg, hx]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

variable {B : Type u} [Ring B] [DGAddCommGroup B] [InternalGrading B] [BigradedDGRing B]
  [DGRing B] (φ : A →ᵈᵍ+* B) (hφ : ∀ {k : ℤ} {a : A}, a ∈ wgrading k → φ a ∈ wgrading k)
  [CatModule.HasDerivedCategory.{max u w, max u w} (WeightCategory B)]

/-- `K₀` of the dg functor induced by a weight-preserving morphism of dg rings commutes with the
internal shifts. -/
theorem K0_map_mapFunctor_internalShift (s : ℤ)
    (x : DGCategory.K0.{max u w, max u w} (WeightCategory A)) :
    DGCategory.K0.map.{max u w, max u w} (mapFunctor φ hφ)
        (DG.K0.map ((compactInternalShiftAction.{max u w, max u w} A).functor s) x) =
      DG.K0.map ((compactInternalShiftAction.{max u w, max u w} B).functor s)
        (DGCategory.K0.map.{max u w, max u w} (mapFunctor φ hφ) x) := by
  rw [K0_map_internalShift, K0_map_internalShift, ← AddMonoidHom.comp_apply,
    ← AddMonoidHom.comp_apply, ← DGCategory.K0.map_comp, ← DGCategory.K0.map_comp]
  rfl

/-- **`K₀` of a weight-preserving morphism of dg rings is `ℤ[q, q⁻¹]`-linear**: the map
`K₀(C_A) → K₀(C_B)` induced by derived induction along `C_A ⥤ C_B`, `qⁿ` acting by `⟨n⟩`. -/
def K0LinearMap :
    DGCategory.K0.{max u w, max u w} (WeightCategory A) →ₗ[LaurentPolynomial ℤ]
      DGCategory.K0.{max u w, max u w} (WeightCategory B) :=
  TriangulatedIntAction.linearMapOfCommute (compactInternalShiftAction A)
    (compactInternalShiftAction B) (DGCategory.K0.map.{max u w, max u w} (mapFunctor φ hφ))
    (K0_map_mapFunctor_internalShift φ hφ)

@[simp]
theorem K0LinearMap_apply (x : DGCategory.K0.{max u w, max u w} (WeightCategory A)) :
    K0LinearMap φ hφ x = DGCategory.K0.map.{max u w, max u w} (mapFunctor φ hφ) x :=
  rfl

end WeightCategory

end DG
