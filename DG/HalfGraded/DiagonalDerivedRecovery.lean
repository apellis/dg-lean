import DG.HalfGraded.DiagonalRecovery
import DG.HalfGraded.DiagonalDerived

/-!
# Derived recovery of diagonal dg modules

Restriction of the actual CatModule action at any weight preserves quasi-isomorphisms:
its cohomology map is the existing weightwise cohomology map. It therefore descends to
the ordinary derived category. At weight zero, localization of `recoveryNatIso` gives a
natural left inverse to `toDerived`, hence faithfulness. No fullness, essential-image
characterization, or general compactness preservation is asserted.
-/

open CategoryTheory

universe w' w v u

namespace DG.Diagonal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- Recovery retains exactly the cohomology map at the chosen weight. -/
theorem cohomologyMap_recover (s : ℤ)
    {M N : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)}
    (f : M ⟶ N) (n : ℤ) :
    cohomology.map ((recover A s).map f).hom n = CatModule.cohomologyMap f ⟨s⟩ n := by
  rfl

/-- Action-compatible recovery preserves quasi-isomorphisms at every weight. -/
theorem isQuasiIso_recover (s : ℤ)
    {M N : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)}
    (f : M ⟶ N) (hf : CatModule.IsQuasiIso f) :
    ((recover A s).map f).hom.IsQuasiIso := by
  intro n
  rw [cohomologyMap_recover]
  exact hf ⟨s⟩ n

variable [HasDerivedCategory.{w, v} A]

/-- Recovery followed by ordinary localization inverts the actual CatModule quasi-isomorphisms. -/
theorem recoverCompQ_inverts (s : ℤ) :
    (CatModule.quasiIso (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)).IsInvertedBy
      (recover.{v} A s ⋙ DerivedCategory.Q) := by
  intro M N f hf
  exact (DerivedCategory.isIso_Q_map_iff _).mpr (isQuasiIso_recover A s f hf)

variable [CatModule.HasDerivedCategory.{w', v}
  (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]

/-- Recovery on the existing derived categories, with no support or field hypothesis. -/
def recoveryDerived (s : ℤ) :
    CatModule.DerivedCategory.{w', v}
      (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) ⥤ DerivedCategory.{w, v} A :=
  Localization.lift (recover A s ⋙ DerivedCategory.Q) (recoverCompQ_inverts A s)
    CatModule.DerivedCategory.Q

noncomputable instance recoveryDerivedLifting (s : ℤ) :
    Localization.Lifting CatModule.DerivedCategory.Q
      (CatModule.quasiIso (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded))
      (recover A s ⋙ DerivedCategory.Q) (recoveryDerived A s) :=
  inferInstanceAs (Localization.Lifting _ _ _ (Localization.lift _ _ CatModule.DerivedCategory.Q))

/-- The natural localization comparison for recovery of arbitrary CatModules. -/
def QCompRecoveryDerivedIso (s : ℤ) :
    CatModule.DerivedCategory.Q ⋙ recoveryDerived A s ≅ recover A s ⋙ DerivedCategory.Q :=
  Localization.Lifting.iso CatModule.DerivedCategory.Q
    (CatModule.quasiIso (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) _ _

/-- The comparison on an actual CatModule. -/
def recoveryDerivedObjIso (s : ℤ)
    (M : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    (recoveryDerived A s).obj (CatModule.DerivedCategory.Q.obj M) ≅
      DerivedCategory.Q.obj ((recover A s).obj M) :=
  (QCompRecoveryDerivedIso A s).app M

/-- Recovery of every actual localized CatModule morphism is computed by naturality. -/
@[reassoc]
theorem recoveryDerived_map_Q (s : ℤ)
    {M N : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)}
    (f : M ⟶ N) :
    (recoveryDerived A s).map (CatModule.DerivedCategory.Q.map f) ≫
        (recoveryDerivedObjIso A s N).hom =
      (recoveryDerivedObjIso A s M).hom ≫ DerivedCategory.Q.map ((recover A s).map f) :=
  (QCompRecoveryDerivedIso A s).hom.naturality f

/-- The composite derived functor lifts the actual composite on dg modules. -/
def QCompToDerivedRecoveryIso :
    DerivedCategory.Q ⋙ (toDerived A ⋙ recoveryDerived A 0) ≅
      (toCatModule A ⋙ recover A 0) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (QCompToDerivedIso A) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (QCompRecoveryDerivedIso A 0) ≪≫
    (Functor.associator _ _ _).symm

/-- The left-inverse comparison is obtained by uniqueness of localization, not assumed. -/
def derivedRecoveryNatIso :
    toDerived A ⋙ recoveryDerived A 0 ≅ 𝟭 (DerivedCategory.{w, v} A) := by
  letI : Localization.Lifting DerivedCategory.Q (DGModuleCat.quasiIso A)
      ((toCatModule A ⋙ recover A 0) ⋙ DerivedCategory.Q)
      (toDerived A ⋙ recoveryDerived A 0) := ⟨QCompToDerivedRecoveryIso A⟩
  exact Localization.liftNatIso DerivedCategory.Q (DGModuleCat.quasiIso A)
    ((toCatModule A ⋙ recover A 0) ⋙ DerivedCategory.Q) DerivedCategory.Q
    (toDerived A ⋙ recoveryDerived A 0) (𝟭 _)
    (Functor.isoWhiskerRight (recoveryNatIso A) DerivedCategory.Q ≪≫
      Functor.leftUnitor DerivedCategory.Q)

/-- On an actual module the derived left inverse is the localization of genuine recovery,
conjugated by the two localization comparisons. -/
theorem derivedRecoveryNatIso_hom_app_Q (M : DGModuleCat.{v} A) :
    (derivedRecoveryNatIso A).hom.app (DerivedCategory.Q.obj M) =
      (recoveryDerived A 0).map (toDerivedObjIso A M).hom ≫
        (recoveryDerivedObjIso A 0 ((toCatModule A).obj M)).hom ≫
        DerivedCategory.Q.map (recoveryIso A M).hom := by
  simp [derivedRecoveryNatIso, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app, QCompToDerivedRecoveryIso,
    toDerivedObjIso, recoveryDerivedObjIso, recoveryNatIso]

/-- A genuine derived left inverse implies faithfulness, not fullness. -/
instance toDerived_faithful : (toDerived.{w', w, v} A).Faithful :=
  (derivedRecoveryNatIso A).faithful_of_comp

/-- Equality is reflected for arbitrary derived morphisms, not just module-level maps. -/
theorem toDerived_map_injective {M N : DerivedCategory.{w, v} A}
    {f g : M ⟶ N} (h : (toDerived A).map f = (toDerived A).map g) : f = g :=
  (toDerived A).map_injective h

end

end DG.Diagonal
