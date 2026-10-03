import DG.HalfGraded.DiagonalEssentialImage
import Mathlib.CategoryTheory.Equivalence

/-!
# Equivalences with the concrete diagonal image subcategories

The module target is the full subcategory supported at weights divisible by four.
The derived target consists of objects admitting a representative whose off-support
weight cohomology vanishes. Membership is proved equivalent to that condition for
any representative; it does not require the representative's values to vanish.
Both equivalences lift the existing diagonal functors, with inclusion comparisons.
No compactness, shift coherence, cone or triangulated compatibility is asserted.
-/

open CategoryTheory
universe w' w v u
namespace DG.Diagonal
noncomputable section
variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The existing value-support predicate as a property of actual module objects. -/
abbrev supportedProperty : ObjectProperty
    (CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) := Supported A

/-- The concrete full subcategory of supported diagonal weight modules. -/
abbrev SupportedModules := (supportedProperty.{v} A).FullSubcategory

/-- The actual diagonal module functor with its supported codomain. -/
def toSupported : DGModuleCat.{v} A ⥤ SupportedModules A :=
  (supportedProperty A).lift (toCatModule A) (fun M =>
    (mem_essImage_toCatModule_iff_supported A _).mp
      ((toCatModule A).obj_mem_essImage M))

instance : (toSupported.{v} A).Full := by
  dsimp only [toSupported]
  infer_instance

instance : (toSupported.{v} A).Faithful := by
  dsimp only [toSupported]
  infer_instance

instance : (toSupported.{v} A).EssSurj where
  mem_essImage N := by
    obtain ⟨M, ⟨e⟩⟩ := (mem_essImage_toCatModule_iff_supported A N.obj).mpr N.property
    exact ⟨M, ⟨ObjectProperty.isoMk _ e⟩⟩

instance : (toSupported.{v} A).IsEquivalence := {}

/-- Ordinary dg modules are equivalent to the actual supported full subcategory. -/
def supportedEquivalence : DGModuleCat.{v} A ≌ SupportedModules A :=
  (toSupported A).asEquivalence

/-- Including the supported equivalence recovers the original diagonal functor. -/
def supportedEquivalenceCompInclusion :
    (supportedEquivalence.{v} A).functor ⋙ (supportedProperty A).ι ≅ toCatModule A :=
  Iso.refl _

variable [HasDerivedCategory.{w, v} A]
  [CatModule.HasDerivedCategory.{w', v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]

/-- The concrete derived support property, expressed using an actual module representative. -/
def DerivedSupported : ObjectProperty (CatModule.DerivedCategory.{w', v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) := fun X =>
  ∃ N : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded),
    CohomologicallySupported A N ∧ Nonempty (CatModule.DerivedCategory.Q.obj N ≅ X)

/-- The concrete derived support property is exactly the existing essential image. -/
theorem mem_essImage_toDerived_iff_derivedSupported
    (X : CatModule.DerivedCategory.{w', v}
      (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    (toDerived.{w', w, v} A).essImage X ↔ DerivedSupported A X := by
  constructor
  · intro h
    let Q := CatModule.DerivedCategory.Q (C :=
      WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)
    have : Q.EssSurj := Localization.essSurj Q (CatModule.quasiIso _)
    let N := Q.objPreimage X
    let e := Q.objObjPreimageIso X
    exact ⟨N, (mem_essImage_toDerived_iff_of_iso A N X e).mp h, ⟨e⟩⟩
  · rintro ⟨N, hN, ⟨e⟩⟩
    exact (mem_essImage_toDerived_iff_of_iso A N X e).mpr hN

/-- Derived support is detected on every chosen representative, not just one. -/
theorem derivedSupported_iff_of_iso
    (N : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded))
    {X : CatModule.DerivedCategory.{w', v}
      (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)}
    (e : CatModule.DerivedCategory.Q.obj N ≅ X) :
    DerivedSupported A X ↔ CohomologicallySupported A N :=
  (mem_essImage_toDerived_iff_derivedSupported A X).symm.trans
    (mem_essImage_toDerived_iff_of_iso A N X e)

/-- The concrete full subcategory of off-support-acyclic derived objects. -/
abbrev SupportedDerived := (DerivedSupported.{w', v} A).FullSubcategory

/-- The existing derived diagonal functor with its concrete codomain restricted. -/
def toSupportedDerived : DerivedCategory.{w, v} A ⥤ SupportedDerived.{w', v} A :=
  (DerivedSupported A).lift (toDerived A) (fun X =>
    (mem_essImage_toDerived_iff_derivedSupported A _).mp ((toDerived A).obj_mem_essImage X))

instance : (toSupportedDerived.{w', w, v} A).Full := by
  dsimp only [toSupportedDerived]
  infer_instance

instance : (toSupportedDerived.{w', w, v} A).Faithful := by
  dsimp only [toSupportedDerived]
  infer_instance

instance : (toSupportedDerived.{w', w, v} A).EssSurj where
  mem_essImage X := by
    obtain ⟨M, ⟨e⟩⟩ := (mem_essImage_toDerived_iff_derivedSupported A X.obj).mpr X.property
    exact ⟨M, ⟨ObjectProperty.isoMk _ e⟩⟩

instance : (toSupportedDerived.{w', w, v} A).IsEquivalence := {}

/-- The actual derived diagonal functor is an equivalence onto its concrete image category. -/
def supportedDerivedEquivalence : DerivedCategory.{w, v} A ≌ SupportedDerived.{w', v} A :=
  (toSupportedDerived A).asEquivalence

/-- Inclusion of the concrete derived equivalence is the existing derived diagonal functor. -/
def supportedDerivedEquivalenceCompInclusion :
    (supportedDerivedEquivalence.{w', w, v} A).functor ⋙ (DerivedSupported A).ι ≅
      toDerived A := Iso.refl _

end
end DG.Diagonal
