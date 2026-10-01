import DG.Category.Derived.Morita
import DG.Category.ShiftedObjects
import DG.K0.DGCategory

/-!
# Derived Morita invariance for formal shifts of objects

A dg functor `F : C ⥤ D` is *shift-dense* (`DG.IsShiftDense F`) if every object `Y` of `D` is a
retract of an object `F X` by closed homogeneous morphisms of opposite degrees: there are cocycles
`a : Y ⟶ F X` of degree `n` and `b : F X ⟶ Y` of degree `-n` with `a ≫ b = 𝟙 Y`. (For `n = 0`
this is a special case of `DG.IsSummandDense`.) Restriction along a shift-dense dg functor
reflects acyclicity (`DG.CatModule.isAcyclic_of_isAcyclic_precomp_of_isShiftDense`), so a
quasi-fully faithful shift-dense dg functor induces an equivalence of derived categories
(`DG.CatModule.DerivedCategory.inductionEquivalenceOfIsShiftDense`) and an isomorphism on `K₀`
(`DG.DGCategory.K0.mapEquivOfReflects`).

This applies to the dg categories of formal shifts `DG.ShiftedObjects`: the dg functors
`DG.ShiftedObjects.reindexFunctor` and `DG.ShiftedObjects.toClosure` are quasi-fully faithful
(they are the identity on Hom complexes), and `toClosure : C ⥤ ShiftedObjects id` is shift-dense
(`DG.ShiftedObjects.isShiftDense_toClosure`): `(X, m)` and `(X, 0)` are related by the identity
of `X`, a cocycle of degree `m` (resp. `-m`).
-/

open CategoryTheory Limits Pretriangulated

universe w₂ w v₁ v₂ u₁ u₂ u'

set_option backward.isDefEq.respectTransparency false

namespace DG

section General

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] [DGCategory D] (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]

/-- A dg functor `F : C ⥤ D` is *shift-dense* if every object `Y` of `D` is a retract of an object
`F X` by closed homogeneous morphisms of opposite degrees: `a : Y ⟶ F X` and `b : F X ⟶ Y`,
cocycles of degrees `n` and `-n`, with `a ≫ b = 𝟙 Y`. -/
def IsShiftDense : Prop :=
  ∀ Y : D, ∃ (X : C) (n : ℤ) (a : Y ⟶ F.obj X) (b : F.obj X ⟶ Y),
    a ∈ cocycles (Y ⟶ F.obj X) n ∧ b ∈ cocycles (F.obj X ⟶ Y) (-n) ∧ a ≫ b = 𝟙 Y

variable {F}

namespace CatModule

omit [DGCategory C] [DGCategory D] in
/-- Restriction along a shift-dense dg functor reflects acyclicity: if `N(F X)` is acyclic for
every `X`, then `N` is acyclic. -/
theorem isAcyclic_of_isAcyclic_precomp_of_isShiftDense (hF : IsShiftDense F)
    {N : CatModule.{w} D} (h : IsAcyclic ((precomp F).obj N)) : IsAcyclic N := by
  intro Y
  obtain ⟨X, n, a, b, ha, hb, hab⟩ := hF Y
  refine DG.isAcyclic_iff.mpr fun k y hy hdy => ?_
  have hday : d (a • y) = 0 := by
    rw [d_smul ha.1, ha.2, hdy]
    simp
  obtain ⟨z, hz, hdz⟩ : ∃ z : N.obj (F.obj X), z ∈ grading (n + k - 1) ∧ d z = a • y :=
    DG.isAcyclic_iff.mp (h X) (n + k) (a • y) (smul_mem_grading ha.1 hy) hday
  refine ⟨koszulSign n • (b • z), ?_, ?_⟩
  · rw [Units.smul_def]
    refine zsmul_mem ?_ _
    have := smul_mem_grading hb.1 hz
    rwa [show -n + (n + k - 1) = k - 1 by ring] at this
  · rw [d_units_smul, d_smul hb.1, hb.2, zero_smul, zero_add, hdz, ← comp_smul, hab, id_smul,
      smul_smul, ← koszulSign_add, add_neg_cancel, koszulSign_zero, one_smul]

end CatModule

namespace CatModule.DerivedCategory

variable [HasDerivedCategory.{max u₁ v₁ v₂ w, max u₁ v₁ v₂ w} C]
  [HasDerivedCategory.{w₂, max u₁ v₁ v₂ w} D]

/-- For a quasi-fully faithful, shift-dense dg functor `F`, derived induction
`LF_! : D(C) ≌ D(D)` is an equivalence, with quasi-inverse the restriction `F^*`. -/
noncomputable def inductionEquivalenceOfIsShiftDense (hF : IsQuasiFullyFaithful F)
    (hD : IsShiftDense F) :
    DerivedCategory.{max u₁ v₁ v₂ w, max u₁ v₁ v₂ w} C ≌ DerivedCategory.{w₂, max u₁ v₁ v₂ w} D :=
  inductionEquivalence hF fun _ => isAcyclic_of_isAcyclic_precomp_of_isShiftDense hD

end CatModule.DerivedCategory

namespace DGCategory.K0

variable [CatModule.HasDerivedCategory.{max u₁ v₁ v₂ w, max u₁ v₁ v₂ w} C]
  [CatModule.HasDerivedCategory.{w₂, max u₁ v₁ v₂ w} D]

/-- A quasi-fully faithful dg functor `F` such that restriction along `F` reflects acyclicity
induces an isomorphism `K₀(C) ≃+ K₀(D)`, since derived induction is then a triangulated
equivalence (`DG.CatModule.DerivedCategory.inductionEquivalence`). -/
noncomputable def mapEquivOfReflects (hF : IsQuasiFullyFaithful F)
    (hR : ∀ N : CatModule.{max u₁ v₁ v₂ w} D, CatModule.IsAcyclic ((CatModule.precomp F).obj N) →
      CatModule.IsAcyclic N) :
    K0.{max u₁ v₁ v₂ w, max u₁ v₁ v₂ w} C ≃+ K0.{w₂, max u₁ v₁ v₂ w} D :=
  haveI : (CatModule.DerivedCategory.inductionEquivalence.{w, w₂} hF hR).functor.IsTriangulated :=
    inferInstanceAs (CatModule.DerivedCategory.induction.{max u₁ v₁ v₂ w, w₂, w} F).IsTriangulated
  DG.K0.compactMapEquiv (CatModule.DerivedCategory.inductionEquivalence.{w, w₂} hF hR)

@[simp]
theorem mapEquivOfReflects_apply (hF : IsQuasiFullyFaithful F)
    (hR : ∀ N : CatModule.{max u₁ v₁ v₂ w} D, CatModule.IsAcyclic ((CatModule.precomp F).obj N) →
      CatModule.IsAcyclic N)
    (x : K0.{max u₁ v₁ v₂ w, max u₁ v₁ v₂ w} C) :
    mapEquivOfReflects.{w₂, w} hF hR x = map.{w₂, w} F x :=
  rfl

/-- A quasi-fully faithful, shift-dense dg functor induces an isomorphism `K₀(C) ≃+ K₀(D)`. -/
noncomputable def mapEquivOfIsShiftDense (hF : IsQuasiFullyFaithful F) (hD : IsShiftDense F) :
    K0.{max u₁ v₁ v₂ w, max u₁ v₁ v₂ w} C ≃+ K0.{w₂, max u₁ v₁ v₂ w} D :=
  mapEquivOfReflects hF fun _ => CatModule.isAcyclic_of_isAcyclic_precomp_of_isShiftDense hD

@[simp]
theorem mapEquivOfIsShiftDense_apply (hF : IsQuasiFullyFaithful F) (hD : IsShiftDense F)
    (x : K0.{max u₁ v₁ v₂ w, max u₁ v₁ v₂ w} C) :
    mapEquivOfIsShiftDense.{w₂, w} hF hD x = map.{w₂, w} F x :=
  rfl

end DGCategory.K0

end General

/-! ### Formal shifts of objects -/

namespace ShiftedObjects

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] {ι : Type u'}

omit [DGCategory C] in
/-- Reindexing is quasi-fully faithful: it is the identity on Hom complexes. -/
theorem isQuasiFullyFaithful_reindexFunctor (φ : ι → C × ℤ) {κ : Type*} (ψ : κ → ι) :
    IsQuasiFullyFaithful (reindexFunctor φ ψ) :=
  IsQuasiFullyFaithful.of_bijective _ (fun _ _ => Function.bijective_id) fun h => h

omit [DGCategory C] in
/-- The inclusion `X ↦ (X, 0)` into the closure under formal shifts is quasi-fully faithful: it
is the identity on Hom complexes. -/
theorem isQuasiFullyFaithful_toClosure : IsQuasiFullyFaithful (toClosure C) :=
  IsQuasiFullyFaithful.of_bijective _ (fun _ _ => Function.bijective_id) fun {X Y n f} h => by
    rw [mem_grading_iff] at h
    simpa using h

/-- Every formal shift `(X, m)` is related to `(X, 0)` by the identity of `X`, a cocycle of degree
`m` with inverse of degree `-m`. -/
theorem isShiftDense_toClosure : IsShiftDense (toClosure C) := by
  rintro ⟨X, m⟩
  refine ⟨X, m, shiftHom (j := (toClosure C).obj X) rfl, shiftHom (i := (toClosure C).obj X) rfl,
    ?_, ?_, ?_⟩
  · simpa using shiftHom_mem_cocycles (φ := id) (i := ⟨(X, m)⟩) (j := (toClosure C).obj X) rfl
  · simpa using shiftHom_mem_cocycles (φ := id) (i := (toClosure C).obj X) (j := ⟨(X, m)⟩) rfl
  · rw [shiftHom_comp_shiftHom]
    rfl

end ShiftedObjects

end DG
