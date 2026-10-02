import DG.HalfGraded.DiagonalAdjunction
import DG.HalfGraded.DiagonalDerivedRecovery
import Mathlib.CategoryTheory.Localization.Adjunction

/-!
# The derived diagonal adjunction

The actual diagonal embedding–recovery adjunction descends through the existing
quasi-isomorphism localizations. Its unit is the inverse of `derivedRecoveryNatIso`,
not merely an unrelated left-inverse comparison. Consequently `toDerived` is fully
faithful on arbitrary derived morphisms. No compactness or essential-image
characterization is asserted.
-/

open CategoryTheory

universe w' w v u

namespace DG.Diagonal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]
  [HasDerivedCategory.{w, v} A]
  [CatModule.HasDerivedCategory.{w', v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]

local instance toDerivedCatCommSq :
    CatCommSq (toCatModule A) DerivedCategory.Q CatModule.DerivedCategory.Q
      (toDerived.{w', w, v} A) :=
  ⟨(QCompToDerivedIso A).symm⟩

local instance recoveryDerivedCatCommSq :
    CatCommSq (recover A 0) CatModule.DerivedCategory.Q DerivedCategory.Q
      (recoveryDerived.{w', w, v} A 0) :=
  ⟨(QCompRecoveryDerivedIso A 0).symm⟩

/-- Localization of the actual module adjunction, on unrestricted derived CatModules. -/
def diagonalDerivedAdjunction : toDerived.{w', w, v} A ⊣ recoveryDerived A 0 :=
  (diagonalAdjunction A).localization DerivedCategory.Q (DGModuleCat.quasiIso A)
    CatModule.DerivedCategory.Q
    (CatModule.quasiIso (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded))
    (toDerived A) (recoveryDerived A 0)

/-- The actual descended unit is computed using the fixed localization comparisons. -/
theorem diagonalDerivedAdjunction_unit_app_Q (M : DGModuleCat.{v} A) :
    (diagonalDerivedAdjunction A).unit.app (DerivedCategory.Q.obj M) =
      DerivedCategory.Q.map (recoveryIso A M).inv ≫
        (recoveryDerivedObjIso A 0 ((toCatModule A).obj M)).inv ≫
        (recoveryDerived A 0).map (toDerivedObjIso A M).inv := by
  exact (diagonalAdjunction A).localization_unit_app _ _ _ _ _ _ M

/-- The descended counit is localization of the action-compatible module counit. -/
theorem diagonalDerivedAdjunction_counit_app_Q
    (N : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    (diagonalDerivedAdjunction A).counit.app (CatModule.DerivedCategory.Q.obj N) =
      (toDerived A).map (recoveryDerivedObjIso A 0 N).hom ≫
        (toDerivedObjIso A ((recover A 0).obj N)).hom ≫
        CatModule.DerivedCategory.Q.map (counitMap A N) := by
  exact (diagonalAdjunction A).localization_counit_app _ _ _ _ _ _ N

/-- The unit of this adjunction, rather than just some left-inverse map, is invertible. -/
theorem diagonalDerivedAdjunction_unit :
    (diagonalDerivedAdjunction.{w', w, v} A).unit = (derivedRecoveryNatIso A).inv := by
  apply (cancel_mono (derivedRecoveryNatIso A).hom).mp
  rw [Iso.inv_hom_id]
  apply Localization.natTrans_ext DerivedCategory.Q (DGModuleCat.quasiIso A)
  intro M
  simp only [NatTrans.comp_app, diagonalDerivedAdjunction_unit_app_Q,
    derivedRecoveryNatIso_hom_app_Q, NatTrans.id_app]
  simp [← Functor.map_comp, Category.assoc]

instance diagonalDerivedAdjunction_unit_isIso :
    IsIso (diagonalDerivedAdjunction.{w', w, v} A).unit := by
  rw [diagonalDerivedAdjunction_unit]
  infer_instance

/-- Full faithfulness follows from the invertible unit of the actual derived adjunction. -/
def toDerivedFullyFaithful : (toDerived.{w', w, v} A).FullyFaithful :=
  (diagonalDerivedAdjunction A).fullyFaithfulLOfIsIsoUnit

instance toDerived_full : (toDerived.{w', w, v} A).Full :=
  (toDerivedFullyFaithful A).full

/-- A preimage for every derived morphism between diagonal images, not only localized maps. -/
def toDerivedPreimage {M N : DerivedCategory.{w, v} A}
    (f : (toDerived.{w', w, v} A).obj M ⟶ (toDerived A).obj N) : M ⟶ N :=
  (toDerivedFullyFaithful A).preimage f

@[simp]
theorem toDerived_map_preimage {M N : DerivedCategory.{w, v} A}
    (f : (toDerived.{w', w, v} A).obj M ⟶ (toDerived A).obj N) :
    (toDerived A).map (toDerivedPreimage A f) = f :=
  (toDerivedFullyFaithful A).map_preimage f

@[simp]
theorem toDerived_preimage_map {M N : DerivedCategory.{w, v} A} (f : M ⟶ N) :
    toDerivedPreimage A ((toDerived.{w', w, v} A).map f) = f :=
  (toDerivedFullyFaithful A).preimage_map f

end

end DG.Diagonal
