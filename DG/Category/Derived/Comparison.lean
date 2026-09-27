import Mathlib.CategoryTheory.Localization.LocalizerMorphism
import DG.Category.Derived.Basic
import DG.Derived.Basic

/-!
# The derived category of a one-object dg category

Let `A` be a dg ring. The comparison functor
`DG.CatModule.HomotopyCategory.toDGHomotopyCategory A :
CatModule.HomotopyCategory (SingleObj A) ⥤ DG.HomotopyCategory A` (evaluation at the unique
object) is a triangulated equivalence (`DG/Category/Homotopy/Comparison.lean`), and the
quasi-isomorphisms correspond under it. Hence it induces an equivalence of triangulated
categories between the derived category `D(SingleObj A)` of the one-object dg category and the
derived category `D(A)` of dg `A`-modules (`DG.DerivedCategory A`).

## Main definitions and results

* `DG.CatModule.HomotopyCategory.quasiIso_singleObj_eq_inverseImage`: `quasiIso (SingleObj A)` is
  the inverse image of `DG.HomotopyCategory.quasiIso A` under the comparison functor;
  `DG.CatModule.HomotopyCategory.singleObjLocalizerMorphism A`, the comparison functor as a
  morphism of localizers, is a localized equivalence.
* `DG.CatModule.DerivedCategory.toDGDerivedCategory A :
  DerivedCategory (SingleObj A) ⥤ DG.DerivedCategory A`, the functor induced by the comparison
  functor (`DG.CatModule.DerivedCategory.QhCompToDGDerivedCategoryIso`). It is an equivalence,
  commutes with the shifts and is a triangulated functor
  (`DG.CatModule.DerivedCategory.toDGDerivedCategory_isTriangulated`).
* `DG.CatModule.DerivedCategory.singleObjEquivalence A :
  DerivedCategory (SingleObj A) ≌ DG.DerivedCategory A`.

Both derived categories are given by chosen localizations, with possibly different universes
of morphisms.
-/

open CategoryTheory Category Limits Pretriangulated

universe w'' w' w u

namespace DG

namespace CatModule

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

namespace HomotopyCategory

/-- The quasi-isomorphisms of the homotopy category of dg modules over `SingleObj A` are the
inverse image of the quasi-isomorphisms of dg `A`-modules under the comparison functor. -/
theorem quasiIso_singleObj_eq_inverseImage :
    quasiIso.{w} (SingleObj A) =
      (DG.HomotopyCategory.quasiIso.{w} A).inverseImage (toDGHomotopyCategory A) := by
  ext M N f
  obtain ⟨M, rfl⟩ := quotient_obj_surjective M
  obtain ⟨N, rfl⟩ := quotient_obj_surjective N
  obtain ⟨f, rfl⟩ := (quotient _).map_surjective f
  rw [MorphismProperty.inverseImage_iff, quotient_map_mem_quasiIso_iff,
    toDGHomotopyCategory_map_quotient_map, DG.HomotopyCategory.quotient_map_mem_quasiIso_iff]
  exact ⟨fun h n => h (SingleObj.star A) n, fun h _ n => h n⟩

/-- The comparison functor as a morphism of localizers from the quasi-isomorphisms of dg modules
over `SingleObj A` to the quasi-isomorphisms of dg `A`-modules. -/
@[simps]
noncomputable def singleObjLocalizerMorphism :
    LocalizerMorphism (quasiIso.{w} (SingleObj A)) (DG.HomotopyCategory.quasiIso.{w} A) where
  functor := toDGHomotopyCategory A
  map := (quasiIso_singleObj_eq_inverseImage A).le

/-- The comparison functor induces an equivalence on the localizations at the
quasi-isomorphisms. -/
instance singleObjLocalizerMorphism_isLocalizedEquivalence :
    (singleObjLocalizerMorphism.{w} A).IsLocalizedEquivalence :=
  have : (singleObjLocalizerMorphism.{w} A).functor.IsEquivalence :=
    inferInstanceAs (toDGHomotopyCategory A).IsEquivalence
  LocalizerMorphism.IsLocalizedEquivalence.of_equivalence _ (by
    rw [singleObjLocalizerMorphism_functor, quasiIso_singleObj_eq_inverseImage,
      MorphismProperty.map_inverseImage_eq_of_isEquivalence])

end HomotopyCategory

namespace DerivedCategory

variable [HasDerivedCategory.{w', w} (SingleObj A)] [DG.HasDerivedCategory.{w'', w} A]

/-- The functor `D(SingleObj A) ⥤ D(A)` induced by the comparison functor
`DG.CatModule.HomotopyCategory.toDGHomotopyCategory A`. -/
noncomputable def toDGDerivedCategory : DerivedCategory (SingleObj A) ⥤ DG.DerivedCategory A :=
  Localization.lift (HomotopyCategory.toDGHomotopyCategory A ⋙ DG.DerivedCategory.Qh)
    (fun _ _ _ hf => Localization.inverts DG.DerivedCategory.Qh
      (DG.HomotopyCategory.quasiIso A) _ ((HomotopyCategory.singleObjLocalizerMorphism A).map _ hf))
    Qh

noncomputable instance toDGDerivedCategoryLifting :
    Localization.Lifting Qh (HomotopyCategory.quasiIso (SingleObj A))
      (HomotopyCategory.toDGHomotopyCategory A ⋙ DG.DerivedCategory.Qh)
      (toDGDerivedCategory A) :=
  inferInstanceAs (Localization.Lifting _ _ _ (Localization.lift _ _ Qh))

/-- The functor `toDGDerivedCategory A` is induced by the comparison functor on homotopy
categories. -/
noncomputable def QhCompToDGDerivedCategoryIso :
    Qh ⋙ toDGDerivedCategory A ≅
      HomotopyCategory.toDGHomotopyCategory A ⋙ DG.DerivedCategory.Qh :=
  Localization.Lifting.iso Qh (HomotopyCategory.quasiIso (SingleObj A)) _ _

noncomputable instance : CatCommSq (HomotopyCategory.singleObjLocalizerMorphism A).functor Qh
    DG.DerivedCategory.Qh (toDGDerivedCategory A) :=
  ⟨(QhCompToDGDerivedCategoryIso A).symm⟩

/-- The functor `D(SingleObj A) ⥤ D(A)` is an equivalence of categories. -/
instance toDGDerivedCategory_isEquivalence : (toDGDerivedCategory A).IsEquivalence :=
  (HomotopyCategory.singleObjLocalizerMorphism A).isEquivalence Qh DG.DerivedCategory.Qh _

/-- The functor `D(SingleObj A) ⥤ D(A)` commutes with the shifts. -/
noncomputable instance toDGDerivedCategory_commShift : (toDGDerivedCategory A).CommShift ℤ :=
  Functor.commShiftOfLocalization Qh (HomotopyCategory.quasiIso (SingleObj A)) ℤ
    (HomotopyCategory.toDGHomotopyCategory A ⋙ DG.DerivedCategory.Qh) (toDGDerivedCategory A)

instance : NatTrans.CommShift (QhCompToDGDerivedCategoryIso A).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization _ _ _ _ _

/-- The functor `D(SingleObj A) ⥤ D(A)` is a triangulated functor. -/
instance toDGDerivedCategory_isTriangulated : (toDGDerivedCategory A).IsTriangulated :=
  Functor.isTriangulated_of_precomp_iso (QhCompToDGDerivedCategoryIso A)

/-- The derived category of the one-object dg category `SingleObj A` is equivalent to the
derived category of dg `A`-modules. The functor is `toDGDerivedCategory A`, which commutes with
the shifts and is triangulated, so this is an equivalence of triangulated categories. -/
noncomputable def singleObjEquivalence : DerivedCategory (SingleObj A) ≌ DG.DerivedCategory A :=
  (toDGDerivedCategory A).asEquivalence

@[simp]
theorem singleObjEquivalence_functor :
    (singleObjEquivalence A).functor = toDGDerivedCategory A := rfl

end DerivedCategory

end CatModule

end DG
