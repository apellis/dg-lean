import Mathlib.CategoryTheory.Localization.LocalizerMorphism
import DG.Derived.Basic
import DG.Homotopy.ComparisonRing

/-!
# The derived category of a ring in degree `0`

Let `S` be a ring, not necessarily commutative, regarded as a dg ring concentrated in degree `0`
(the scoped instances of `DG.DegreeZero`). The triangulated equivalence
`DG.DegreeZero.homotopyFunctor S : DG.HomotopyCategory S ⥤ HomotopyCategory (ModuleCat S) (up ℤ)`
detects quasi-isomorphisms (`DG/Homotopy/ComparisonRing.lean`), hence induces a triangulated
equivalence between the derived category `D(S)` of dg modules over `S` and Mathlib's derived
category of `S`-modules. For a commutative ring, `DG/Derived/Comparison.lean` gives the
analogous equivalence through the forgetful functor `DG.DGModuleCat.forget S S`.

## Main definitions and results

* `DG.DegreeZero.derivedComparison S : DG.DerivedCategory S ⥤ DerivedCategory (ModuleCat S)`,
  with `DG.DegreeZero.QCompDerivedComparisonIso`, an equivalence
  (`DG.DegreeZero.derivedComparison_isEquivalence`) which commutes with the shifts and is
  triangulated;
* `DG.DegreeZero.derivedComparisonEquivalence S : DG.DerivedCategory S ≌
  DerivedCategory (ModuleCat S)`.
-/

open CategoryTheory Category Limits Pretriangulated

universe w w' u

namespace DG

namespace DegreeZero

variable (S : Type u) [Ring S]

/-- The quasi-isomorphisms of the homotopy category of dg modules over `S` are the inverse image
of Mathlib's quasi-isomorphisms. -/
theorem quasiIso_eq_inverseImage :
    HomotopyCategory.quasiIso.{u} S = (_root_.HomotopyCategory.quasiIso (ModuleCat.{u} S)
      (ComplexShape.up ℤ)).inverseImage (homotopyFunctor S) := by
  ext X Y f
  exact mem_quasiIso_iff f

/-- `DG.DegreeZero.homotopyFunctor S` as a morphism of localizers. -/
@[simps]
noncomputable def homotopyLocalizerMorphism :
    LocalizerMorphism (HomotopyCategory.quasiIso.{u} S)
      (_root_.HomotopyCategory.quasiIso (ModuleCat.{u} S) (ComplexShape.up ℤ)) where
  functor := homotopyFunctor S
  map _ _ f hf := (mem_quasiIso_iff f).mp hf

instance homotopyLocalizerMorphism_isLocalizedEquivalence :
    (homotopyLocalizerMorphism S).IsLocalizedEquivalence :=
  have : (homotopyLocalizerMorphism S).functor.IsEquivalence :=
    inferInstanceAs (homotopyFunctor S).IsEquivalence
  LocalizerMorphism.IsLocalizedEquivalence.of_equivalence _ (by
    rw [homotopyLocalizerMorphism_functor, quasiIso_eq_inverseImage,
      MorphismProperty.map_inverseImage_eq_of_isEquivalence])

variable [HasDerivedCategory.{w, u} S] [_root_.HasDerivedCategory.{w'} (ModuleCat.{u} S)]

open _root_.DG.DerivedCategory in
/-- The comparison functor `D(S) ⥤ D(Mod S)` from the derived category of dg modules over a ring
`S` in degree `0` to Mathlib's derived category of `S`-modules. -/
noncomputable def derivedComparison :
    DerivedCategory S ⥤ _root_.DerivedCategory (ModuleCat.{u} S) :=
  Localization.lift (homotopyFunctor S ⋙ _root_.DerivedCategory.Qh)
    (fun _ _ f hf => Localization.inverts _root_.DerivedCategory.Qh
      (_root_.HomotopyCategory.quasiIso _ _) _ ((mem_quasiIso_iff f).mp hf))
    Qh

set_option backward.isDefEq.respectTransparency false in
open _root_.DG.DerivedCategory in
noncomputable instance derivedComparisonLifting :
    Localization.Lifting Qh (HomotopyCategory.quasiIso S)
      (homotopyFunctor S ⋙ _root_.DerivedCategory.Qh) (derivedComparison S) :=
  inferInstanceAs (Localization.Lifting _ _ _ (Localization.lift _ _ Qh))

open _root_.DG.DerivedCategory in
/-- The comparison functor is induced by `DG.DegreeZero.homotopyFunctor S`. -/
noncomputable def QhCompDerivedComparisonIso :
    Qh ⋙ derivedComparison S ≅ homotopyFunctor S ⋙ _root_.DerivedCategory.Qh :=
  Localization.Lifting.iso Qh (HomotopyCategory.quasiIso S) _ _

open _root_.DG.DerivedCategory in
/-- On dg modules, the comparison functor is induced by `DG.DegreeZero.complexFunctor S`. -/
noncomputable def QCompDerivedComparisonIso :
    Q ⋙ derivedComparison S ≅ complexFunctor S ⋙ _root_.DerivedCategory.Q :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (QhCompDerivedComparisonIso S) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (homotopyFunctorFactors S) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (_root_.DerivedCategory.quotientCompQhIso (ModuleCat.{u} S))

open _root_.DG.DerivedCategory in
noncomputable instance : CatCommSq (homotopyLocalizerMorphism S).functor Qh
    _root_.DerivedCategory.Qh (derivedComparison S) :=
  ⟨(QhCompDerivedComparisonIso S).symm⟩

/-- The comparison functor is an equivalence of categories. -/
instance derivedComparison_isEquivalence : (derivedComparison S).IsEquivalence :=
  (homotopyLocalizerMorphism S).isEquivalence DerivedCategory.Qh _root_.DerivedCategory.Qh _

open _root_.DG.DerivedCategory in
/-- The comparison functor commutes with the shifts. -/
noncomputable instance derivedComparison_commShift : (derivedComparison S).CommShift ℤ :=
  Functor.commShiftOfLocalization Qh (HomotopyCategory.quasiIso S) ℤ
    (homotopyFunctor S ⋙ _root_.DerivedCategory.Qh) (derivedComparison S)

instance : NatTrans.CommShift (QhCompDerivedComparisonIso S).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization _ _ _ _ _

/-- The comparison functor is a triangulated functor. -/
instance derivedComparison_isTriangulated : (derivedComparison S).IsTriangulated :=
  Functor.isTriangulated_of_precomp_iso (QhCompDerivedComparisonIso S)

/-- **The derived category of a ring**: for a ring `S` concentrated in degree `0`, the derived
category of dg modules over `S` is equivalent, as a triangulated category, to Mathlib's derived
category of `S`-modules. -/
noncomputable def derivedComparisonEquivalence :
    DerivedCategory S ≌ _root_.DerivedCategory (ModuleCat.{u} S) :=
  (derivedComparison S).asEquivalence

@[simp]
theorem derivedComparisonEquivalence_functor :
    (derivedComparisonEquivalence S).functor = derivedComparison S := rfl

noncomputable instance : (derivedComparisonEquivalence S).functor.CommShift ℤ :=
  inferInstanceAs ((derivedComparison S).CommShift ℤ)

instance : (derivedComparisonEquivalence S).functor.IsTriangulated :=
  inferInstanceAs (derivedComparison S).IsTriangulated

end DegreeZero

end DG
