import DG.HalfGraded.DiagonalConeRecovery
import DG.HalfGraded.DiagonalShiftCoherence

/-!
# The all-weight diagonal cone comparison

The actual target cone is supported at multiples of four. Its original, action-compatible
counit is therefore invertible. Combining this counit with the explicit recovered cone
isomorphism gives an isomorphism on the original CatModules, not a transported action.

The comparison respects every weight-category arrow, the original inclusion and first
projection, the previously constructed coherent signed shift, and the actual standard
triangles' negative connecting maps. Its supported-weight formula uses original
evaluation, the explicit cone lift, and the original periodic-unit action. No new
homotopy/derived descent or equivalence with the whole target is asserted.
-/

open CategoryTheory
universe v u
namespace DG.Diagonal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- Morphisms out of a diagonal module, into any CatModule, are determined at zero.
This uses the genuine all-weight adjunction, not faithfulness of unrestricted recovery. -/
theorem diagonalSource_hom_ext {M : DGModuleCat.{v} A}
    {P : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)}
    {f g : (toCatModule A).obj M ⟶ P}
    (h : ∀ x, f.app ⟨0⟩ x = g.app ⟨0⟩ x) : f = g := by
  apply ((diagonalAdjunction A).homEquiv M P).injective
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply]
  congr 1
  apply DGModuleCat.hom_ext
  apply DGModuleHom.ext
  exact h

variable {M N : DGModuleCat.{v} A} (f : M ⟶ N)

/-- The original cone of diagonal modules has no off-support weight values. -/
theorem diagonalCone_supported : Supported A (CatModule.cone ((toCatModule A).map f)) := by
  intro w hw
  let := value_subsingleton A M w hw
  let := value_subsingleton A N w hw
  change Subsingleton ((CatModule.shift 1 ((toCatModule A).obj M)).obj ⟨w⟩ ×
    ((toCatModule A).obj N).obj ⟨w⟩)
  exact inferInstanceAs (Subsingleton (Value A M w × Value A N w))

/-- The original action-compatible counit is an isomorphism on the actual target cone. -/
def diagonalConeCounitIso :
    (toCatModule A).obj ((recover A 0).obj (CatModule.cone ((toCatModule A).map f))) ≅
      CatModule.cone ((toCatModule A).map f) := by
  letI := (isIso_counitMap_iff_supported A _).mpr (diagonalCone_supported A f)
  exact asIso (counitMap A _)

/-- All-weight comparison between the diagonal of the original ordinary cone and the
original CatModule cone. The counit supplies compatibility across distinct weights. -/
def diagonalConeIso :
    (toCatModule A).obj (DGModuleCat.of A (Cone f.hom)) ≅
      CatModule.cone ((toCatModule A).map f) :=
  (toCatModule A).mapIso (diagonalConeRecoveryIso A f).symm ≪≫ diagonalConeCounitIso A f

/-- Formula using only the original regraded map and the original counit. -/
theorem diagonalConeIso_hom_app
    (w : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)
    (x : ((toCatModule A).obj (DGModuleCat.of A (Cone f.hom))).obj w) :
    (diagonalConeIso A f).hom.app w x = counitApp A
      (CatModule.cone ((toCatModule A).map f)) w.as
      (((toCatModule A).map (diagonalConeRecoveryIso A f).inv).app w x) := rfl

/-- Naturality for every weight-category arrow, including distinct weights and
inhomogeneous arrows, with the existing actions on both original cones. -/
theorem diagonalConeIso_hom_act
    {s t : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded} (a : s ⟶ t)
    (x : ((toCatModule A).obj (DGModuleCat.of A (Cone f.hom))).obj s) :
    (diagonalConeIso A f).hom.app t
        (((toCatModule A).obj (DGModuleCat.of A (Cone f.hom))).act a x) =
      (CatModule.cone ((toCatModule A).map f)).act a ((diagonalConeIso A f).hom.app s x) :=
  (diagonalConeIso A f).hom.map_smul a x

/-- The all-weight map agrees at zero with the previous explicit cone lift. -/
theorem diagonalConeIso_hom_zero (x : Value A (DGModuleCat.of A (Cone f.hom)) 0) :
    (diagonalConeIso A f).hom.app ⟨0⟩ x =
      diagonalConeLift A f (valueEvaluation A (DGModuleCat.of A (Cone f.hom)) 0 x) := by
  rw [diagonalConeIso_hom_app, counitApp_zero]
  exact evaluation_regradedMap (diagonalConeRecoveryIso A f).inv x.1

/-- At every supported weight the map evaluates the original cone, lifts its two
summands at zero, and acts by the original periodic unit on the actual target cone. -/
theorem diagonalConeIso_hom_supported (t : ℤ)
    (x : Value A (DGModuleCat.of A (Cone f.hom)) (4 * t)) :
    (diagonalConeIso A f).hom.app ⟨4 * t⟩ x =
      (CatModule.cone ((toCatModule A).map f)).act (periodicUnit A t)
        (diagonalConeLift A f (valueEvaluation A (DGModuleCat.of A (Cone f.hom)) (4 * t) x)) := by
  rw [diagonalConeIso_hom_app, counitApp_supported]
  exact congrArg ((CatModule.cone ((toCatModule A).map f)).act (periodicUnit A t))
    (evaluation_regradedMap (diagonalConeRecoveryIso A f).inv x.1)

/-- The original negative differential of the first summand is respected at all weights. -/
theorem diagonalConeIso_d_fst
    (w : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)
    (x : ((toCatModule A).obj (DGModuleCat.of A (Cone f.hom))).obj w) :
    CatModule.shift.unmk 1 ((diagonalConeIso A f).hom.app w (d x)).1 =
      -d (CatModule.shift.unmk 1 ((diagonalConeIso A f).hom.app w x).1) := by
  rw [CatModule.Hom.map_d]
  change CatModule.shift.unmk 1
    (d (M := (CatModule.shift 1 ((toCatModule A).obj M)).obj w)
      ((diagonalConeIso A f).hom.app w x).1) = _
  simpa only [koszulSign, Int.negOnePow_one, Units.neg_smul, one_smul] using
    (CatModule.shift.unmk_d (M := (toCatModule A).obj M) (X := w) (n := 1)
      ((diagonalConeIso A f).hom.app w x).1)

/-- The original positive off-diagonal term is respected at all weights. -/
theorem diagonalConeIso_d_snd
    (w : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)
    (x : ((toCatModule A).obj (DGModuleCat.of A (Cone f.hom))).obj w) :
    ((diagonalConeIso A f).hom.app w (d x)).2 =
      ((toCatModule A).map f).app w
        (CatModule.shift.unmk 1 ((diagonalConeIso A f).hom.app w x).1) +
        d ((diagonalConeIso A f).hom.app w x).2 := by
  rw [CatModule.Hom.map_d]
  rfl

/-- Compatibility with the original second-summand inclusion, at every weight. -/
theorem diagonalConeIso_inr :
    (toCatModule A).map (DGModuleCat.Hom.mk
      (N := DGModuleCat.of A (Cone f.hom)) (Cone.inr f.hom)) ≫ (diagonalConeIso A f).hom =
      CatModule.cone.inr ((toCatModule A).map f) := by
  apply diagonalSource_hom_ext A
  intro x
  change (diagonalConeIso A f).hom.app ⟨0⟩
    (((toCatModule A).map (DGModuleCat.Hom.mk
      (N := DGModuleCat.of A (Cone f.hom)) (Cone.inr f.hom))).app ⟨0⟩ x) = _
  rw [diagonalConeIso_hom_zero]
  have h : valueEvaluation A (DGModuleCat.of A (Cone f.hom)) 0
      (((toCatModule A).map (DGModuleCat.Hom.mk (N := DGModuleCat.of A (Cone f.hom))
        (Cone.inr f.hom))).app ⟨0⟩ x) = Cone.inr f.hom (valueEvaluation A N 0 x) :=
    evaluation_regradedMap (DGModuleCat.Hom.mk (N := DGModuleCat.of A (Cone f.hom))
      (Cone.inr f.hom)) x.1
  rw [h]
  apply Prod.ext
  · exact congrArg (CatModule.shift.mk 1) (map_zero (weightZeroLift A M))
  · exact weightZeroLift_valueEvaluation A N x

/-- At zero the existing coherent shift comparison is the signed homogeneous lift. -/
theorem toCatModuleShiftIso_hom_zero (k : ℤ) (P : DGModuleCat.{v} A)
    (x : Value A ((shiftFunctor (DGModuleCat A) k).obj P) 0) :
    (toCatModuleShiftIso A k P).hom.app ⟨0⟩ x =
      CatModule.shift.mk k (weightZeroLift A P
        (Shift.unmk k (valueEvaluation A ((shiftFunctor (DGModuleCat A) k).obj P) 0 x))) := by
  change counitApp A (CatModule.shift k ((toCatModule A).obj P)) 0 _ = _
  rw [counitApp_zero]
  refine (evaluation_regradedMap ((shiftedRecoveryNatIso A k).inv.app P) x.1).trans ?_
  change Shift.mk k ((recoveryIso A P).inv _) = _
  apply congrArg (Shift.mk k)
  apply (recoveryMap_bijective A P).injective
  have h := congrArg (fun g : P ⟶ P => g.hom
    (Shift.unmk k (valueEvaluation A ((shiftFunctor (DGModuleCat A) k).obj P) 0 x)))
    (recoveryIso A P).inv_hom_id
  exact h.trans (valueEvaluation_weightZeroLift A P _).symm

/-- The first projection commutes with the previously constructed coherent signed
shift comparison, not with a newly chosen shift isomorphism. -/
theorem diagonalConeIso_fst :
    (diagonalConeIso A f).hom ≫ CatModule.cone.fstHom ((toCatModule A).map f) =
      (toCatModule A).map (DGModuleCat.Hom.mk
        (M := DGModuleCat.of A (Cone f.hom)) (N := DGModuleCat.of A (Shift 1 M))
        (Cone.fstHom f.hom)) ≫ (toCatModuleShiftIso A 1 M).hom := by
  apply diagonalSource_hom_ext A
  intro x
  change ((diagonalConeIso A f).hom.app ⟨0⟩ x).1 =
    (toCatModuleShiftIso A 1 M).hom.app ⟨0⟩ _
  rw [diagonalConeIso_hom_zero, toCatModuleShiftIso_hom_zero]
  have h := evaluation_regradedMap (DGModuleCat.Hom.mk
    (M := DGModuleCat.of A (Cone f.hom)) (N := DGModuleCat.of A (Shift 1 M))
    (Cone.fstHom f.hom)) x.1
  exact congrArg (fun y : Shift 1 M => CatModule.shift.mk 1
    (weightZeroLift A M (Shift.unmk 1 y))) h.symm

/-- The original componentwise diagonal functor preserves addition of morphisms. -/
instance toCatModule_additive : (toCatModule.{v} A).Additive where
  map_add := by
    intro P Q g h
    apply CatModule.Hom.ext
    intro w x
    apply Subtype.ext
    change regradedMap (g + h) x.1 = regradedMap g x.1 + regradedMap h x.1
    induction x.1 using HalfRegrade.induction_on with
    | zero => simp
    | mk p m hm =>
      simp only [regradedMap_mk]
      exact HalfRegrade.mk_add p (map_mem_grading g hm) (map_mem_grading h hm)
    | add x y hx hy => simp only [map_add, hx, hy]; abel

/-- Compatibility with the actual standard triangles' negative first projections. -/
theorem diagonalConeIso_triangle_mor₃ :
    (diagonalConeIso A f).hom ≫ (CatModule.cone.triangle ((toCatModule A).map f)).mor₃ =
      (toCatModule A).map (Cone.triangle f).mor₃ ≫ (toCatModuleShiftIso A 1 M).hom := by
  let p : DGModuleCat.of A (Cone f.hom) ⟶ DGModuleCat.of A (Shift 1 M) :=
    DGModuleCat.Hom.mk (Cone.fstHom f.hom)
  change (diagonalConeIso A f).hom ≫ (-CatModule.cone.fstHom ((toCatModule A).map f)) =
    (toCatModule A).map (-p) ≫ _
  rw [Preadditive.comp_neg, Functor.map_neg, Preadditive.neg_comp, diagonalConeIso_fst]

end
end DG.Diagonal
