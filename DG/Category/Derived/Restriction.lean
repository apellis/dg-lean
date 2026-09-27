import DG.Category.Derived.Basic

/-!
# Restriction along a dg functor on derived categories

Let `F : C ⥤ D` be a dg functor between dg categories. Restriction along `F`
(`DG.CatModule.precomp F`, `(M ∘ F) X = M (F X)`) preserves quasi-isomorphisms
(`DG.CatModule.IsQuasiIso.precomp`): the cohomology of `M ∘ F` at `X` is the cohomology of `M`
at `F X`. Hence the triangulated functor
`DG.CatModule.HomotopyCategory.precomp F : HomotopyCategory D ⥤ HomotopyCategory C` induces a
functor on the derived categories.

## Main definitions and results

* `DG.CatModule.IsAcyclic.precomp`, `DG.CatModule.IsQuasiIso.precomp`: restriction preserves
  acyclic modules and quasi-isomorphisms;
  `DG.CatModule.HomotopyCategory.precomp_map_mem_quasiIso`: so does its version on homotopy
  categories.
* `DG.CatModule.DerivedCategory.restrict F : DerivedCategory D ⥤ DerivedCategory C`, induced by
  restriction along `F` (`DG.CatModule.DerivedCategory.QhCompRestrictIso`,
  `DG.CatModule.DerivedCategory.QCompRestrictIso`); it commutes with the shifts and is a
  triangulated functor (`DG.CatModule.DerivedCategory.restrict_isTriangulated`).
-/

open CategoryTheory Category Limits Pretriangulated

universe w' w'' w v₁ v₂ u₁ u₂

namespace DG

namespace CatModule

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [∀ X Y : D, DGAddCommGroup (X ⟶ Y)]
  (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]

/-- Restriction along a dg functor preserves acyclic dg modules. -/
theorem IsAcyclic.precomp {M : CatModule.{w} D} (hM : IsAcyclic M) :
    IsAcyclic ((CatModule.precomp F).obj M) :=
  fun X => hM (F.obj X)

/-- Restriction along a dg functor preserves quasi-isomorphisms. -/
theorem IsQuasiIso.precomp {M N : CatModule.{w} D} {φ : M ⟶ N} (hφ : IsQuasiIso φ) :
    IsQuasiIso ((CatModule.precomp F).map φ) :=
  fun X n => hφ (F.obj X) n

variable [DGCategory C] [DGCategory D]

namespace HomotopyCategory

/-- Restriction along a dg functor on homotopy categories preserves quasi-isomorphisms. -/
theorem precomp_map_mem_quasiIso {M N : HomotopyCategory.{w} D} {f : M ⟶ N}
    (hf : quasiIso D f) : quasiIso C ((precomp F).map f) := by
  obtain ⟨M, rfl⟩ := quotient_obj_surjective M
  obtain ⟨N, rfl⟩ := quotient_obj_surjective N
  obtain ⟨f, rfl⟩ := (quotient _).map_surjective f
  rw [quotient_map_mem_quasiIso_iff] at hf
  rw [precomp_map_quotient_map, quotient_map_mem_quasiIso_iff]
  exact hf.precomp F

/-- Restriction along a dg functor, as a morphism of localizers for the quasi-isomorphisms. -/
@[simps]
noncomputable def precompLocalizerMorphism :
    LocalizerMorphism (quasiIso.{w} D) (quasiIso.{w} C) where
  functor := precomp F
  map _ _ _ hf := precomp_map_mem_quasiIso F hf

end HomotopyCategory

namespace DerivedCategory

variable [HasDerivedCategory.{w', w} C] [HasDerivedCategory.{w'', w} D]

/-- Restriction along a dg functor `F : C ⥤ D`, on derived categories: the functor
`D(D) ⥤ D(C)` induced by `DG.CatModule.HomotopyCategory.precomp F`. -/
noncomputable def restrict : DerivedCategory D ⥤ DerivedCategory C :=
  Localization.lift (HomotopyCategory.precomp F ⋙ Qh)
    (fun _ _ _ hf => Localization.inverts Qh (HomotopyCategory.quasiIso C) _
      (HomotopyCategory.precomp_map_mem_quasiIso F hf))
    Qh

noncomputable instance restrictLifting :
    Localization.Lifting Qh (HomotopyCategory.quasiIso D) (HomotopyCategory.precomp F ⋙ Qh)
      (restrict F) :=
  inferInstanceAs (Localization.Lifting _ _ _ (Localization.lift _ _ Qh))

/-- Restriction on derived categories is induced by restriction on homotopy categories. -/
noncomputable def QhCompRestrictIso : Qh ⋙ restrict F ≅ HomotopyCategory.precomp F ⋙ Qh :=
  Localization.Lifting.iso Qh (HomotopyCategory.quasiIso D) _ _

/-- Restriction on derived categories is induced by restriction of dg modules. -/
noncomputable def QCompRestrictIso : Q ⋙ restrict F ≅ CatModule.precomp F ⋙ Q :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (QhCompRestrictIso F) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (HomotopyCategory.precompFactors F) _ ≪≫ Functor.associator _ _ _

/-- Restriction on derived categories commutes with the shifts. -/
noncomputable instance restrict_commShift : (restrict F).CommShift ℤ :=
  Functor.commShiftOfLocalization Qh (HomotopyCategory.quasiIso D) ℤ
    (HomotopyCategory.precomp F ⋙ Qh) (restrict F)

instance : NatTrans.CommShift (QhCompRestrictIso F).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization _ _ _ _ _

/-- Restriction along a dg functor is a triangulated functor on derived categories. -/
instance restrict_isTriangulated : (restrict F).IsTriangulated :=
  Functor.isTriangulated_of_precomp_iso (QhCompRestrictIso F)

end DerivedCategory

end CatModule

end DG
