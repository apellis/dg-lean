import DG.HalfGraded.DiagonalEssentialImage
import DG.Category.Homotopy.Comparison
import DG.Category.Homotopy.Precomp

/-!
# Signed shifts of the actual diagonal functor

For every ordinary dg ring and integer shift, the actual diagonal module functor
commutes with the library's original signed shifts. Restriction already commutes
with these shifts on their actual actions; shifting leaves diagonal support
unchanged, so the actual action-compatible adjunction counit is invertible.
This supplies a natural isomorphism at every weight, including vanishing
unsupported weights, without transporting an action or a shift structure.

The comparison descends through the existing localizations, with independent
derived Hom universes, and its value on localized modules is computed explicitly.
No `CommShift` instance for the diagonal functor, zero/add coherence, cone
comparison, triangulatedness, or compactness preservation is asserted here.
-/

open CategoryTheory
universe w' w v u
namespace DG.Diagonal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The original and regraded action signs coincide at every supported weight. -/
theorem supported_action_shift_sign (k n t : ℤ) :
    koszulSign (k * (n + 2 * t)) = koszulSign (k * n) := by
  rw [mul_add, koszulSign_add]
  have h : k * (2 * t) = 2 * (k * t) := by ring
  rw [h, supported_shift_sign, mul_one]

/-- Restriction of the actual signed shift, at any weight, is the ordinary signed shift.
The existing restriction comparisons prove action compatibility on the original actions. -/
def recoveryShiftNatIso (s k : ℤ) :
    shiftFunctor (CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) k ⋙
        recover A s ≅
      recover A s ⋙ shiftFunctor (DGModuleCat.{v} A) k := by
  letI : (recover.{v} A s).CommShift ℤ :=
    inferInstanceAs ((CatModule.precomp (scalarInclusion A s) ⋙
      CatModule.toDGModuleCat A).CommShift ℤ)
  exact (recover A s).commShiftIso k

/-- Shifting a diagonal module leaves every unsupported weight zero. -/
theorem supported_shift_diagonal (M : DGModuleCat.{v} A) (k : ℤ) :
    Supported A (CatModule.shift k ((toCatModule A).obj M)) := by
  intro s hs
  let := value_subsingleton A M s hs
  change Subsingleton (Shift k (Value A M s))
  exact (Shift.unmk k (M := Value A M s)).injective.subsingleton

/-- Recovery of the existing shifted diagonal module is the original shifted module. -/
def shiftedRecoveryNatIso (k : ℤ) :
    (toCatModule.{v} A ⋙ shiftFunctor _ k) ⋙ recover A 0 ≅
      shiftFunctor (DGModuleCat.{v} A) k :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (recoveryShiftNatIso A 0 k) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (recoveryNatIso A) _ ≪≫ Functor.leftUnitor _

/-- The actual counit is an isomorphism on shifted diagonal modules, including
unsupported weights (where both sides vanish). -/
def shiftedDiagonalCounitIso (k : ℤ) :
    ((toCatModule.{v} A ⋙ shiftFunctor _ k) ⋙ recover A 0) ⋙ toCatModule A ≅
      toCatModule A ⋙ shiftFunctor _ k :=
  NatIso.ofComponents (fun M => by
    letI := (isIso_counitMap_iff_supported A
      (CatModule.shift k ((toCatModule A).obj M))).mpr (supported_shift_diagonal A M k)
    exact asIso (counitMap A (CatModule.shift k ((toCatModule A).obj M)))) (by
      intro M N f
      exact (diagonalCounit A).naturality
        ((shiftFunctor _ k).map ((toCatModule A).map f)))

/-- The genuine diagonal functor commutes with every integer signed shift.
This is a natural isomorphism of actual module functors, not a transported shift.
No zero/add coherence or triangulatedness is asserted here. -/
def toCatModuleShiftNatIso (k : ℤ) :
    shiftFunctor (DGModuleCat.{v} A) k ⋙ toCatModule A ≅
      toCatModule A ⋙ shiftFunctor _ k :=
  Functor.isoWhiskerRight (shiftedRecoveryNatIso A k).symm (toCatModule A) ≪≫
    shiftedDiagonalCounitIso A k

/-- The comparison uses the actual counit, hence the existing periodic-unit action
on every supported weight rather than any transported module structure. -/
theorem toCatModuleShiftNatIso_hom_app (k : ℤ) (M : DGModuleCat.{v} A) :
    (toCatModuleShiftNatIso A k).hom.app M =
      (toCatModule A).map ((shiftedRecoveryNatIso A k).inv.app M) ≫
        counitMap A (CatModule.shift k ((toCatModule A).obj M)) := rfl

/-- Objectwise form, comparing the original signed shifts at every weight. -/
def toCatModuleShiftIso (k : ℤ) (M : DGModuleCat.{v} A) :
    (toCatModule A).obj ((shiftFunctor (DGModuleCat.{v} A) k).obj M) ≅
      CatModule.shift k ((toCatModule A).obj M) :=
  (toCatModuleShiftNatIso A k).app M

/-- The signed differential equation on the underlying unshifted target value.
It holds at all weights, including the unsupported ones. -/
theorem toCatModuleShiftIso_unmk_d (k : ℤ) (M : DGModuleCat.{v} A)
    (s : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)
    (x : ((toCatModule A).obj ((shiftFunctor (DGModuleCat.{v} A) k).obj M)).obj s) :
    CatModule.shift.unmk k ((toCatModuleShiftIso A k M).hom.app s (d x)) =
      koszulSign k • d (CatModule.shift.unmk k ((toCatModuleShiftIso A k M).hom.app s x)) := by
  rw [CatModule.Hom.map_d, CatModule.shift.unmk_d]

/-- The actual action comparison, with the existing CatModule shift's Koszul sign. -/
theorem toCatModuleShiftIso_unmk_smul (k : ℤ) (M : DGModuleCat.{v} A)
    {s t : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded}
    {n : ℤ} {f : s ⟶ t} (hf : f ∈ DG.grading n)
    (x : ((toCatModule A).obj ((shiftFunctor (DGModuleCat.{v} A) k).obj M)).obj s) :
    CatModule.shift.unmk k ((toCatModuleShiftIso A k M).hom.app t (f • x)) =
      koszulSign (k * n) •
        (f • CatModule.shift.unmk k ((toCatModuleShiftIso A k M).hom.app s x)) := by
  rw [CatModule.Hom.map_smul, CatModule.shift.unmk_smul hf]

variable [HasDerivedCategory.{w, v} A]
  [CatModule.HasDerivedCategory.{w', v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]

/-- The source-side shift comparison before lifting the natural isomorphism. -/
def QCompShiftToDerivedIso (k : ℤ) :
    DerivedCategory.Q ⋙ (shiftFunctor (DerivedCategory.{w, v} A) k ⋙ toDerived A) ≅
      (shiftFunctor (DGModuleCat.{v} A) k ⋙ toCatModule A) ⋙ CatModule.DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (DerivedCategory.Q.commShiftIso k).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (QCompToDerivedIso A) ≪≫
    (Functor.associator _ _ _).symm

/-- The target-side shift comparison uses the existing derived-category shift. -/
def QCompToDerivedShiftIso (k : ℤ) :
    DerivedCategory.Q ⋙ (toDerived.{w', w, v} A ⋙ shiftFunctor _ k) ≅
      (toCatModule A ⋙ shiftFunctor _ k) ⋙ CatModule.DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (QCompToDerivedIso A) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (CatModule.DerivedCategory.Q.commShiftIso k).symm ≪≫
    (Functor.associator _ _ _).symm

/-- The actual diagonal derived functor commutes with arbitrary integer shifts,
with independently chosen source and target derived Hom universes.
This descends the genuine module comparison; it does not assert shift coherence. -/
def toDerivedShiftNatIso (k : ℤ) :
    shiftFunctor (DerivedCategory.{w, v} A) k ⋙ toDerived A ≅
      toDerived.{w', w, v} A ⋙ shiftFunctor _ k := by
  letI : Localization.Lifting DerivedCategory.Q (DGModuleCat.quasiIso A)
      ((shiftFunctor (DGModuleCat.{v} A) k ⋙ toCatModule A) ⋙ CatModule.DerivedCategory.Q)
      (shiftFunctor (DerivedCategory.{w, v} A) k ⋙ toDerived A) :=
    ⟨QCompShiftToDerivedIso A k⟩
  letI : Localization.Lifting DerivedCategory.Q (DGModuleCat.quasiIso A)
      ((toCatModule A ⋙ shiftFunctor _ k) ⋙ CatModule.DerivedCategory.Q)
      (toDerived.{w', w, v} A ⋙ shiftFunctor _ k) :=
    ⟨QCompToDerivedShiftIso A k⟩
  exact Localization.liftNatIso DerivedCategory.Q (DGModuleCat.quasiIso A) _ _ _ _
    (Functor.isoWhiskerRight (toCatModuleShiftNatIso A k) CatModule.DerivedCategory.Q)

/-- On actual modules the derived comparison is exactly the localization of the
module comparison, conjugated by the existing localization/shift comparisons. -/
theorem toDerivedShiftNatIso_hom_app_Q (k : ℤ) (M : DGModuleCat.{v} A) :
    (toDerivedShiftNatIso A k).hom.app (DerivedCategory.Q.obj M) =
      (QCompShiftToDerivedIso A k).hom.app M ≫
        CatModule.DerivedCategory.Q.map ((toCatModuleShiftNatIso A k).hom.app M) ≫
        (QCompToDerivedShiftIso A k).inv.app M := by
  simp only [toDerivedShiftNatIso, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app]

end
end DG.Diagonal
