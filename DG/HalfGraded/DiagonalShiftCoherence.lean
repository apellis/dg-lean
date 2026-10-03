import DG.HalfGraded.DiagonalShift
import Mathlib.CategoryTheory.Shift.Adjunction
/-!
# Coherence of the actual diagonal signed-shift comparison

The restriction functor `recover A s` has its existing signed-shift structure at every
weight. Mathlib's adjunction construction gives the compatible structure on its actual
left adjoint `toCatModule A`. The counit formula identifies that structure's comparison
with `toCatModuleShiftNatIso`, rather than replacing the original shifts or actions.
Consequently the existing comparison satisfies zero and addition coherence.

Localization gives the same result for `toDerived A`, with independent derived Hom
universes. Its comparison is identified with the existing `toDerivedShiftNatIso` by
localization extensionality and the actual source/target localization comparisons.

No preservation of cones, triangulatedness, compactness, or equivalence with the whole
target category is asserted.
-/

open CategoryTheory
universe w' w v u

namespace DG.Diagonal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- Signed-shift coherence for actual restriction at every weight. -/
instance recoverCommShift (s : ℤ) : (recover.{v} A s).CommShift ℤ :=
  inferInstanceAs ((CatModule.precomp (scalarInclusion A s) ⋙
    CatModule.toDGModuleCat A).CommShift ℤ)

/-- The restriction structure uses exactly the existing recovery comparison. -/
theorem recover_commShiftIso (s k : ℤ) :
    (recover.{v} A s).commShiftIso k = recoveryShiftNatIso A s k := by
  rfl

/-- The actual diagonal left adjoint inherits coherent signed shifts from recovery. -/
instance toCatModuleCommShift : (toCatModule.{v} A).CommShift ℤ :=
  (diagonalAdjunction A).leftAdjointCommShift ℤ

/-- The existing unit and counit are compatible with these signed-shift structures. -/
instance diagonalAdjunctionCommShift : (diagonalAdjunction.{v} A).CommShift ℤ :=
  (diagonalAdjunction A).commShift_of_rightAdjoint ℤ

/-- The adjunction comparison is the previously constructed, action-compatible diagonal
comparison. The proof uses the actual unit, recovery restriction, and counit formula. -/
theorem toCatModule_commShiftIso (k : ℤ) :
    (toCatModule.{v} A).commShiftIso k = toCatModuleShiftNatIso A k := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  have h := Adjunction.CommShift.compatibilityCounit_left (diagonalAdjunction A)
    ((toCatModule A).commShiftIso k) ((recover A 0).commShiftIso k)
    (fun N => ((diagonalAdjunction A).commShiftIso_hom_app_counit_app_shift ℤ k N).symm) M
  rw [recover_commShiftIso] at h
  simpa [toCatModuleShiftNatIso, shiftedRecoveryNatIso, shiftedDiagonalCounitIso,
    diagonalAdjunction, diagonalCounit, Functor.map_comp] using h

/-- Zero coherence for the existing module comparison. -/
theorem toCatModuleShiftNatIso_zero :
    toCatModuleShiftNatIso.{v} A 0 = Functor.CommShift.isoZero (toCatModule A) ℤ := by
  rw [← toCatModule_commShiftIso, Functor.commShiftIso_zero]

/-- Addition coherence for the existing module comparison, for arbitrary integer shifts. -/
theorem toCatModuleShiftNatIso_add (a b : ℤ) :
    toCatModuleShiftNatIso.{v} A (a + b) = Functor.CommShift.isoAdd
      (toCatModuleShiftNatIso A a) (toCatModuleShiftNatIso A b) := by
  simp only [← toCatModule_commShiftIso, Functor.commShiftIso_add]

section Derived

variable [HasDerivedCategory.{w, v} A]
  [CatModule.HasDerivedCategory.{w', v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]

/-- Coherent shifts descend through the actual quasi-isomorphism localization. -/
instance toDerivedCommShift : (toDerived.{w', w, v} A).CommShift ℤ :=
  Functor.commShiftOfLocalization DerivedCategory.Q (DGModuleCat.quasiIso A) ℤ
    (toCatModule A ⋙ CatModule.DerivedCategory.Q) (toDerived A)

/-- The localization-induced comparison is exactly the existing derived comparison,
with independently chosen source and target derived Hom universes. -/
theorem toDerived_commShiftIso (k : ℤ) :
    (toDerived.{w', w, v} A).commShiftIso k = toDerivedShiftNatIso A k := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q (DGModuleCat.quasiIso A)
  intro M
  rw [Functor.commShiftOfLocalization_iso_hom_app]
  rw [toDerivedShiftNatIso_hom_app_Q]
  simp [QCompShiftToDerivedIso, QCompToDerivedShiftIso,
    Functor.commShiftIso_comp_hom_app, toCatModule_commShiftIso, QCompToDerivedIso]

/-- Zero coherence for the existing derived comparison. -/
theorem toDerivedShiftNatIso_zero :
    toDerivedShiftNatIso.{w', w, v} A 0 =
      Functor.CommShift.isoZero (toDerived A) ℤ := by
  rw [← toDerived_commShiftIso, Functor.commShiftIso_zero]

/-- Addition coherence for the existing derived comparison. -/
theorem toDerivedShiftNatIso_add (a b : ℤ) :
    toDerivedShiftNatIso.{w', w, v} A (a + b) = Functor.CommShift.isoAdd
      (toDerivedShiftNatIso A a) (toDerivedShiftNatIso A b) := by
  simp only [← toDerived_commShiftIso, Functor.commShiftIso_add]
end Derived

end
end DG.Diagonal
