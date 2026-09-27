import Mathlib.CategoryTheory.Localization.LocalizerMorphism
import DG.Derived.Basic
import DG.Homotopy.Comparison

/-!
# Comparison with Mathlib's derived category

Let `R` be a commutative ring, regarded as a dg ring concentrated in degree `0` (the scoped
instances of `DG.DegreeZero`). The forgetful functor
`DG.HomotopyCategory.forget R R : DG.HomotopyCategory R ⥤ HomotopyCategory (ModuleCat R) (up ℤ)`
is a triangulated equivalence (`DG/Homotopy/Comparison.lean`) and the quasi-isomorphisms
correspond under it (`DG.HomotopyCategory.mem_quasiIso_iff_forget`). Hence it induces an
equivalence of triangulated categories between the derived category `D(R)` of dg modules over `R`
and Mathlib's derived category of `R`-modules.

## Main definitions and results

* `DG.HomotopyCategory.quasiIso_eq_inverseImage`: `quasiIso R` is the inverse image of Mathlib's
  quasi-isomorphisms under the forgetful functor;
  `DG.HomotopyCategory.comparisonLocalizerMorphism R`, the forgetful functor as a morphism of
  localizers, is a localized equivalence
  (`DG.HomotopyCategory.comparisonLocalizerMorphism_isLocalizedEquivalence`).
* `DG.DerivedCategory.comparison R : DG.DerivedCategory R ⥤ DerivedCategory (ModuleCat R)`, the
  functor induced by the forgetful functor (`DG.DerivedCategory.QhCompComparisonIso`,
  `DG.DerivedCategory.QCompComparisonIso`). It is an equivalence
  (`DG.DerivedCategory.comparison_isEquivalence`), commutes with the shifts
  (`DG.DerivedCategory.comparison_commShift`, compatibly with `QhCompComparisonIso`) and is a
  triangulated functor (`DG.DerivedCategory.comparison_isTriangulated`).
* `DG.DerivedCategory.comparisonEquivalence R :
  DG.DerivedCategory R ≌ DerivedCategory (ModuleCat R)`.

Both derived categories are given by chosen localizations (`[DG.HasDerivedCategory R]`,
`[HasDerivedCategory (ModuleCat R)]`), with possibly different universes of morphisms.
-/

open CategoryTheory Category Limits Pretriangulated

universe w w' u

namespace DG

open DegreeZero

variable (R : Type u) [CommRing R]

namespace HomotopyCategory

/-- The quasi-isomorphisms of the homotopy category of dg modules over `R` are the inverse
image of Mathlib's quasi-isomorphisms under the forgetful functor. -/
theorem quasiIso_eq_inverseImage :
    quasiIso.{u} R = (_root_.HomotopyCategory.quasiIso (ModuleCat.{u} R)
      (ComplexShape.up ℤ)).inverseImage (forget R R) := by
  ext X Y f
  exact mem_quasiIso_iff_forget R f

/-- The forgetful functor `DG.HomotopyCategory.forget R R` as a morphism of localizers from the
quasi-isomorphisms of dg modules over `R` to the quasi-isomorphisms of cochain complexes. -/
@[simps]
noncomputable def comparisonLocalizerMorphism :
    LocalizerMorphism (quasiIso.{u} R)
      (_root_.HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) where
  functor := forget R R
  map _ _ f hf := (mem_quasiIso_iff_forget R f).mp hf

/-- The forgetful functor induces an equivalence on the localizations at the
quasi-isomorphisms. -/
instance comparisonLocalizerMorphism_isLocalizedEquivalence :
    (comparisonLocalizerMorphism R).IsLocalizedEquivalence :=
  have : (comparisonLocalizerMorphism R).functor.IsEquivalence :=
    inferInstanceAs (forget R R).IsEquivalence
  LocalizerMorphism.IsLocalizedEquivalence.of_equivalence _ (by
    rw [comparisonLocalizerMorphism_functor, quasiIso_eq_inverseImage,
      MorphismProperty.map_inverseImage_eq_of_isEquivalence])

end HomotopyCategory

namespace DerivedCategory

variable [HasDerivedCategory.{w, u} R] [_root_.HasDerivedCategory.{w'} (ModuleCat.{u} R)]

/-- The comparison functor `D(R) ⥤ D(Mod R)` from the derived category of dg modules over `R`
to Mathlib's derived category of `R`-modules, induced by the forgetful functor
`DG.HomotopyCategory.forget R R`. -/
noncomputable def comparison : DerivedCategory R ⥤ _root_.DerivedCategory (ModuleCat.{u} R) :=
  Localization.lift (HomotopyCategory.forget R R ⋙ _root_.DerivedCategory.Qh)
    (fun _ _ f hf => Localization.inverts _root_.DerivedCategory.Qh
      (_root_.HomotopyCategory.quasiIso _ _) _
      ((HomotopyCategory.mem_quasiIso_iff_forget R f).mp hf))
    Qh

noncomputable instance comparisonLifting :
    Localization.Lifting Qh (HomotopyCategory.quasiIso R)
      (HomotopyCategory.forget R R ⋙ _root_.DerivedCategory.Qh) (comparison R) :=
  inferInstanceAs (Localization.Lifting _ _ _ (Localization.lift _ _ Qh))

/-- The comparison functor is induced by the forgetful functor on homotopy categories. -/
noncomputable def QhCompComparisonIso :
    Qh ⋙ comparison R ≅ HomotopyCategory.forget R R ⋙ _root_.DerivedCategory.Qh :=
  Localization.Lifting.iso Qh (HomotopyCategory.quasiIso R) _ _

/-- On dg modules, the comparison functor is induced by the forgetful functor
`DG.DGModuleCat.forget R R` to cochain complexes. -/
noncomputable def QCompComparisonIso :
    Q ⋙ comparison R ≅ DGModuleCat.forget R R ⋙ _root_.DerivedCategory.Q :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (QhCompComparisonIso R) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (HomotopyCategory.forgetFactors R R) _ ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (_root_.DerivedCategory.quotientCompQhIso (ModuleCat.{u} R))

noncomputable instance : CatCommSq (HomotopyCategory.comparisonLocalizerMorphism R).functor Qh
    _root_.DerivedCategory.Qh (comparison R) :=
  ⟨(QhCompComparisonIso R).symm⟩

/-- The comparison functor is an equivalence of categories. -/
instance comparison_isEquivalence : (comparison R).IsEquivalence :=
  (HomotopyCategory.comparisonLocalizerMorphism R).isEquivalence Qh _root_.DerivedCategory.Qh _

/-- The comparison functor commutes with the shifts (the structure induced by
`DG.HomotopyCategory.forgetCommShift`). -/
noncomputable instance comparison_commShift : (comparison R).CommShift ℤ :=
  Functor.commShiftOfLocalization Qh (HomotopyCategory.quasiIso R) ℤ
    (HomotopyCategory.forget R R ⋙ _root_.DerivedCategory.Qh) (comparison R)

instance : NatTrans.CommShift (QhCompComparisonIso R).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization _ _ _ _ _

/-- The comparison functor is a triangulated functor. -/
instance comparison_isTriangulated : (comparison R).IsTriangulated :=
  Functor.isTriangulated_of_precomp_iso (QhCompComparisonIso R)

/-- The derived category of dg modules over a commutative ring `R` (concentrated in degree
`0`) is equivalent to Mathlib's derived category of `R`-modules. The functor is
`DG.DerivedCategory.comparison R`, which commutes with the shifts and is triangulated, so this
is an equivalence of triangulated categories. -/
noncomputable def comparisonEquivalence :
    DerivedCategory R ≌ _root_.DerivedCategory (ModuleCat.{u} R) :=
  (comparison R).asEquivalence

@[simp]
theorem comparisonEquivalence_functor :
    (comparisonEquivalence R).functor = comparison R := rfl

end DerivedCategory

end DG
