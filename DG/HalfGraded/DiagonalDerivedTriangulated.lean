import DG.HalfGraded.DiagonalRecoveryTriangulated
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Triangulatedness of the actual derived diagonal functor

The existing localization comparison for recovery agrees with the comparison through
homotopy restriction and evaluation. It therefore commutes with the published shifts.
Together with the forward localization comparison, this shows that the actual derived
recovery isomorphism, hence the unit of `diagonalDerivedAdjunction`, commutes with shifts.
Mathlib's adjunction theorem then proves that `toDerived` is triangulated.

All functors, the adjunction, and both `CommShift` structures are the existing ones.
The source and target derived Hom universes remain independent. No explicit cone
comparison or preservation of all compact objects is asserted.
-/

open CategoryTheory
universe w' w v u

namespace DG.Diagonal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- Actual homotopy restriction and evaluation factorization respects signed shifts. -/
instance recoveryHomotopyFactors_commShift (s : ℤ) :
    NatTrans.CommShift (recoveryHomotopyFactors.{v} A s).hom ℤ := by
  dsimp [recoveryHomotopyFactors, recoveryHomotopy, recover, recoverCommShift,
    recoveryHomotopyCommShift]
  infer_instance

/-- The module recovery isomorphism respects the shifts of the actual adjunction. -/
instance recoveryNatIso_commShift :
    NatTrans.CommShift (recoveryNatIso.{v} A).hom ℤ := by
  have : NatTrans.CommShift (recoveryNatIso A).symm.hom ℤ :=
    inferInstanceAs (NatTrans.CommShift (diagonalAdjunction A).unit ℤ)
  exact NatTrans.CommShift.of_iso_inv (recoveryNatIso A).symm ℤ

variable [HasDerivedCategory.{w, v} A]
  [CatModule.HasDerivedCategory.{w', v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]

/-- The forward comparison respects the existing localization-induced shifts. -/
instance QCompToDerivedIso_commShift :
    NatTrans.CommShift (QCompToDerivedIso.{w', w, v} A).hom ℤ := by
  exact NatTrans.commShift_iso_hom_of_localization DerivedCategory.Q
    (DGModuleCat.quasiIso A) ℤ (toCatModule A ⋙ CatModule.DerivedCategory.Q) (toDerived A)

/-- The original module-localization comparison is the composite of the actual
homotopy factorization and its localized comparison, at every weight. -/
theorem QCompRecoveryDerivedIso_eq (s : ℤ) :
    QCompRecoveryDerivedIso.{w', w, v} A s =
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (QhCompRecoveryDerivedIso A s) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (recoveryHomotopyFactors A s) _ ≪≫
      Functor.associator _ _ _ := by
  ext N
  dsimp [QhCompRecoveryDerivedIso, Quotient.natIsoLift, Quotient.natTransLift]
  simp [← Functor.map_comp]
  change (QCompRecoveryDerivedIso A s).hom.app N =
    𝟙 _ ≫ (QCompRecoveryDerivedIso A s).hom.app N ≫ 𝟙 _ ≫
      DerivedCategory.Qh.map ((recoveryHomotopyFactors A s).inv.app N ≫
        (recoveryHomotopyFactors A s).hom.app N)
  simp
  exact (Category.comp_id _).symm

/-- The original recovery comparison respects the published homotopy-localized shifts. -/
instance QCompRecoveryDerivedIso_commShift (s : ℤ) :
    NatTrans.CommShift (QCompRecoveryDerivedIso.{w', w, v} A s).hom ℤ := by
  rw [QCompRecoveryDerivedIso_eq]
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom]
  infer_instance

/-- The localization comparison for forward functor followed by recovery respects shifts. -/
instance QCompToDerivedRecoveryIso_commShift :
    NatTrans.CommShift (QCompToDerivedRecoveryIso.{w', w, v} A).hom ℤ := by
  dsimp [QCompToDerivedRecoveryIso]
  infer_instance

/-- Before descent the actual recovery isomorphism is the composite of the fixed
localization comparisons and the original module recovery isomorphism. -/
theorem whiskerLeft_derivedRecoveryNatIso_hom :
    Functor.whiskerLeft DerivedCategory.Q (derivedRecoveryNatIso.{w', w, v} A).hom =
    (QCompToDerivedRecoveryIso A).hom ≫
      Functor.whiskerRight (recoveryNatIso A).hom DerivedCategory.Q ≫
      (Functor.leftUnitor DerivedCategory.Q).hom ≫
      (Functor.rightUnitor DerivedCategory.Q).inv := by
  ext M
  simp [derivedRecoveryNatIso_hom_app_Q, QCompToDerivedRecoveryIso,
    toDerivedObjIso, recoveryDerivedObjIso, recoveryNatIso]

/-- Shift compatibility descends to the existing derived recovery isomorphism. -/
instance derivedRecoveryNatIso_commShift :
    NatTrans.CommShift (derivedRecoveryNatIso.{w', w, v} A).hom ℤ := by
  have : NatTrans.CommShift
      (Functor.whiskerLeft DerivedCategory.Q (derivedRecoveryNatIso A).hom) ℤ := by
    rw [whiskerLeft_derivedRecoveryNatIso_hom]
    infer_instance
  constructor
  intro k
  apply Localization.natTrans_ext DerivedCategory.Q (DGModuleCat.quasiIso A)
  intro M
  have h := NatTrans.shift_app_comm
    (Functor.whiskerLeft DerivedCategory.Q (derivedRecoveryNatIso A).hom) k M
  simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app,
    Category.assoc] at h
  rw [← NatTrans.naturality_assoc] at h
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app, Category.assoc]
  exact (cancel_epi ((toDerived A ⋙ recoveryDerived A 0).map
    ((DerivedCategory.Q.commShiftIso k).hom.app M))).mp h

/-- The existing derived adjunction is compatible with the existing forward and
recovery shift structures; in particular both its unit and counit commute with shifts. -/
instance diagonalDerivedAdjunctionCommShift :
    (diagonalDerivedAdjunction.{w', w, v} A).CommShift ℤ := by
  apply Adjunction.CommShift.mk'
  rw [diagonalDerivedAdjunction_unit]
  infer_instance

/-- The actual forward diagonal functor is triangulated, as the shift-compatible
left adjoint of the existing triangulated recovery functor. -/
instance toDerived_isTriangulated : (toDerived.{w', w, v} A).IsTriangulated :=
  (diagonalDerivedAdjunction A).isTriangulated_leftAdjoint

end
end DG.Diagonal
