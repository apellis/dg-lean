import DG.HalfGraded.DiagonalShiftCoherence
import DG.Category.Derived.Restriction
import DG.Category.Derived.Comparison

/-!
# Triangulated recovery of diagonal dg modules

The existing derived recovery at every integer weight is induced by actual restriction
and one-object evaluation on homotopy categories. The comparison below identifies this
construction with the original quasi-isomorphism localization, without defining a new
derived recovery functor. Its coherent shift structure and distinguished-triangle
preservation descend through the homotopy localization, with independent Hom universes.

This does not prove that the forward diagonal functor is triangulated, that its derived
adjunction is shift-compatible, or that either functor preserves compact objects.
-/

open CategoryTheory
universe w' w v u
namespace DG.Diagonal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- Actual restriction and one-object evaluation on homotopy categories. -/
def recoveryHomotopy (s : ℤ) :
    CatModule.HomotopyCategory.{v}
      (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) ⥤ HomotopyCategory.{v} A :=
  CatModule.HomotopyCategory.precomp (scalarInclusion A s) ⋙
    CatModule.HomotopyCategory.toDGHomotopyCategory A

/-- This functor is induced by the existing module recovery. -/
def recoveryHomotopyFactors (s : ℤ) :
    CatModule.HomotopyCategory.quotient _ ⋙ recoveryHomotopy.{v} A s ≅
      recover A s ⋙ HomotopyCategory.quotient A :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (CatModule.HomotopyCategory.precompFactors
      (scalarInclusion A s)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (CatModule.HomotopyCategory.toDGHomotopyCategoryFactors A) ≪≫
    (Functor.associator _ _ _).symm

instance recoveryHomotopyCommShift (s : ℤ) : (recoveryHomotopy.{v} A s).CommShift ℤ :=
  inferInstanceAs ((CatModule.HomotopyCategory.precomp (scalarInclusion A s) ⋙
    CatModule.HomotopyCategory.toDGHomotopyCategory A).CommShift ℤ)

instance recoveryHomotopy_isTriangulated (s : ℤ) :
    (recoveryHomotopy.{v} A s).IsTriangulated :=
  inferInstanceAs ((CatModule.HomotopyCategory.precomp (scalarInclusion A s) ⋙
    CatModule.HomotopyCategory.toDGHomotopyCategory A).IsTriangulated)

variable [HasDerivedCategory.{w, v} A]
  [CatModule.HasDerivedCategory.{w', v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]

/-- The existing derived recovery also factors through the actual homotopy restriction. -/
def QhCompRecoveryDerivedIso (s : ℤ) :
    CatModule.DerivedCategory.Qh ⋙ recoveryDerived.{w', w, v} A s ≅
      recoveryHomotopy A s ⋙ DerivedCategory.Qh :=
  CategoryTheory.Quotient.natIsoLift _
    ((Functor.associator _ _ _).symm ≪≫ QCompRecoveryDerivedIso A s ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (recoveryHomotopyFactors A s).symm _ ≪≫
      Functor.associator _ _ _)

instance recoveryDerivedHomotopyLifting (s : ℤ) :
    Localization.Lifting CatModule.DerivedCategory.Qh
      (CatModule.HomotopyCategory.quasiIso
        (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded))
      (recoveryHomotopy A s ⋙ DerivedCategory.Qh) (recoveryDerived.{w', w, v} A s) :=
  ⟨QhCompRecoveryDerivedIso A s⟩

/-- Coherent shifts on the existing derived recovery at every weight. -/
instance recoveryDerivedCommShift (s : ℤ) : (recoveryDerived.{w', w, v} A s).CommShift ℤ :=
  Functor.commShiftOfLocalization CatModule.DerivedCategory.Qh
    (CatModule.HomotopyCategory.quasiIso
      (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) ℤ
    (recoveryHomotopy A s ⋙ DerivedCategory.Qh) (recoveryDerived A s)

instance QhCompRecoveryDerivedIso_commShift (s : ℤ) :
    NatTrans.CommShift (QhCompRecoveryDerivedIso.{w', w, v} A s).hom ℤ := by
  change NatTrans.CommShift (Localization.Lifting.iso CatModule.DerivedCategory.Qh
    (CatModule.HomotopyCategory.quasiIso
      (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded))
    (recoveryHomotopy A s ⋙ DerivedCategory.Qh) (recoveryDerived A s)).hom ℤ
  exact NatTrans.commShift_iso_hom_of_localization _ _ _ _ _

/-- Actual derived recovery preserves distinguished triangles at every weight. -/
instance recoveryDerived_isTriangulated (s : ℤ) :
    (recoveryDerived.{w', w, v} A s).IsTriangulated :=
  Functor.isTriangulated_of_precomp_iso (QhCompRecoveryDerivedIso A s)
end
end DG.Diagonal
