import DG.HalfGraded.DiagonalRecovery
import DG.Category.Homotopy.Comparison
import DG.Category.Homotopy.Precomp

/-!
# Explicit weight-zero cone recovery for the diagonal functor

This is a module-level prerequisite for the all-weight diagonal cone comparison.
It compares the actual cone after weight-zero restriction with the original ordinary
cone, using evaluation and its explicit inverse. The signed shifts and both cone
constructions are the original ones. It does not assert an all-weight comparison
or a homotopy/derived descent of that comparison.
-/

open CategoryTheory
universe v u
namespace DG.Diagonal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- Actual scalar restriction preserves the original cone, at any weight.
Both comparison maps are the identity on the underlying pairs; action compatibility
uses the existing signed restriction and one-object comparison. -/
def recoveryConeIso (s : ℤ)
    {M N : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)}
    (f : M ⟶ N) :
    (recover A s).obj (CatModule.cone f) ≅
      DGModuleCat.of A (Cone ((recover A s).map f).hom) :=
  (CatModule.toDGModuleCat A).mapIso
      (CatModule.cone.precompIso (scalarInclusion A s) f) ≪≫
    CatModule.cone.toDGModuleCatIso ((CatModule.precomp (scalarInclusion A s)).map f)

variable {M N : DGModuleCat.{v} A} (f : M ⟶ N)

/-- Evaluation on the two summands of the actual target cone. -/
def diagonalConeEvaluation :
    (recover A 0).obj (CatModule.cone ((toCatModule A).map f)) ⟶
      DGModuleCat.of A (Cone f.hom) :=
  (recoveryConeIso A 0 ((toCatModule A).map f)).hom ≫
    DGModuleCat.Hom.mk (Cone.map (recoveryMap A M).hom (recoveryMap A N).hom (by
      apply DGModuleHom.ext
      intro x
      exact evaluation_regradedMap f x.1))

/-- The comparison is explicitly componentwise evaluation, including the shifted summand. -/
theorem diagonalConeEvaluation_apply
    (p : (CatModule.cone ((toCatModule A).map f)).obj ⟨0⟩) :
    diagonalConeEvaluation A f p =
      (Shift.mk 1 (valueEvaluation A M 0 (CatModule.shift.unmk 1 p.1)),
        valueEvaluation A N 0 p.2) := rfl

/-- The explicit inverse inserts the original homogeneous decomposition at weight zero. -/
def diagonalConeLift (p : Cone f.hom) :
    (CatModule.cone ((toCatModule A).map f)).obj ⟨0⟩ :=
  (CatModule.shift.mk 1 (weightZeroLift A M (Shift.unmk 1 p.1)),
    weightZeroLift A N p.2)

@[simp] theorem diagonalConeEvaluation_lift (p : Cone f.hom) :
    diagonalConeEvaluation A f (diagonalConeLift A f p) = p := by
  rw [diagonalConeEvaluation_apply]
  apply Prod.ext
  · exact congrArg (Shift.mk 1) (valueEvaluation_weightZeroLift A M _)
  · exact valueEvaluation_weightZeroLift A N _

@[simp] theorem diagonalConeLift_evaluation
    (p : (CatModule.cone ((toCatModule A).map f)).obj ⟨0⟩) :
    diagonalConeLift A f (diagonalConeEvaluation A f p) = p := by
  rw [diagonalConeEvaluation_apply]
  apply Prod.ext
  · exact congrArg (CatModule.shift.mk 1) (weightZeroLift_valueEvaluation A M _)
  · exact weightZeroLift_valueEvaluation A N _

/-- An action-compatible isomorphism between the recovered actual target cone and
`DG.Cone f.hom`, with explicit inverse, not an assumed cone isomorphism. -/
def diagonalConeRecoveryIso :
    (recover A 0).obj (CatModule.cone ((toCatModule A).map f)) ≅
      DGModuleCat.of A (Cone f.hom) :=
  DGModuleEquiv.toDGModuleCatIso
    (M := (recover A 0).obj (CatModule.cone ((toCatModule A).map f)))
    (N := Cone f.hom)
    { toFun := diagonalConeEvaluation A f
      invFun := diagonalConeLift A f
      left_inv := diagonalConeLift_evaluation A f
      right_inv := diagonalConeEvaluation_lift A f
      map_add' := map_add _
      map_smul' := (diagonalConeEvaluation A f).hom.map_smul
      map_mem' := (diagonalConeEvaluation A f).hom.map_mem
      map_d' := (diagonalConeEvaluation A f).hom.map_d }

/-- The forward isomorphism is the explicit evaluation map above. -/
@[simp] theorem diagonalConeRecoveryIso_hom_apply
    (p : (CatModule.cone ((toCatModule A).map f)).obj ⟨0⟩) :
    (diagonalConeRecoveryIso A f).hom p = diagonalConeEvaluation A f p := rfl

/-- The inverse is the explicit homogeneous-decomposition lift. -/
@[simp] theorem diagonalConeRecoveryIso_inv_apply (p : Cone f.hom) :
    (diagonalConeRecoveryIso A f).inv p = diagonalConeLift A f p := rfl

/-- Compatibility with the actual second-summand dg inclusion. -/
theorem diagonalConeEvaluation_inr (y : Value A N 0) :
    diagonalConeEvaluation A f ((CatModule.cone.inr ((toCatModule A).map f)).app ⟨0⟩ y) =
      Cone.inr f.hom (valueEvaluation A N 0 y) := by
  rw [diagonalConeEvaluation_apply]
  apply Prod.ext
  · exact congrArg (Shift.mk 1) (map_zero (valueEvaluation A M 0))
  · rfl

/-- Compatibility with the actual first-summand projection, with its shifted type. -/
theorem diagonalConeEvaluation_fst
    (p : (CatModule.cone ((toCatModule A).map f)).obj ⟨0⟩) :
    Cone.fstHom f.hom (diagonalConeEvaluation A f p) =
      Shift.mk 1 (valueEvaluation A M 0 (CatModule.shift.unmk 1
        ((CatModule.cone.fstHom ((toCatModule A).map f)).app ⟨0⟩ p))) := rfl

/-- Compatibility with the second projection, which is not a chain map. -/
theorem diagonalConeEvaluation_snd
    (p : (CatModule.cone ((toCatModule A).map f)).obj ⟨0⟩) :
    Cone.sndLinear f.hom (diagonalConeEvaluation A f p) =
      valueEvaluation A N 0 (CatModule.cone.sndAddHom ((toCatModule A).map f) ⟨0⟩ p) := rfl

/-- The standard triangle uses negative first projection, not positive projection.
This is its elementwise compatibility after unwrapping the signed shift. -/
theorem diagonalConeEvaluation_connecting
    (p : (CatModule.cone ((toCatModule A).map f)).obj ⟨0⟩) :
    -Shift.unmk 1 (Cone.fstHom f.hom (diagonalConeEvaluation A f p)) =
      valueEvaluation A M 0 (-CatModule.shift.unmk 1
        ((CatModule.cone.fstHom ((toCatModule A).map f)).app ⟨0⟩ p)) := by
  exact (map_neg (valueEvaluation A M 0) _).symm

/-- Compatibility with the original standard triangles' actual third morphisms,
after applying weight-zero evaluation and unwrapping the signed shifts. -/
theorem diagonalConeEvaluation_triangle_mor₃
    (p : (CatModule.cone ((toCatModule A).map f)).obj ⟨0⟩) :
    Shift.unmk 1 ((Cone.triangle f).mor₃ (diagonalConeEvaluation A f p)) =
      valueEvaluation A M 0 (CatModule.shift.unmk 1
        ((CatModule.cone.triangle ((toCatModule A).map f)).mor₃.app ⟨0⟩ p)) :=
  diagonalConeEvaluation_connecting A f p

/-- The negative sign in the shifted summand is the original cone differential. -/
theorem diagonalConeEvaluation_d_fst
    (p : (CatModule.cone ((toCatModule A).map f)).obj ⟨0⟩) :
    Shift.unmk 1 (Cone.fstHom f.hom (diagonalConeEvaluation A f (d p))) =
      -d (valueEvaluation A M 0 (CatModule.shift.unmk 1 p.1)) := by
  rw [(diagonalConeEvaluation A f).hom.map_d, Cone.fstHom_d, Shift.unmk_d]
  simp only [koszulSign, Int.negOnePow_one, Units.neg_smul, one_smul]
  rfl

/-- The off-diagonal differential is the original map `f`, with positive sign. -/
theorem diagonalConeEvaluation_d_snd
    (p : (CatModule.cone ((toCatModule A).map f)).obj ⟨0⟩) :
    Cone.sndLinear f.hom (diagonalConeEvaluation A f (d p)) =
      f.hom (valueEvaluation A M 0 (CatModule.shift.unmk 1 p.1)) +
        d (valueEvaluation A N 0 p.2) := by
  rw [(diagonalConeEvaluation A f).hom.map_d, Cone.sndLinear_d]
  rfl

/-- The actual diagonal of the original cone and the actual target cone agree after
weight-zero scalar restriction. No comparison at other weights is asserted here. -/
def weightZeroDiagonalConeIso :
    (recover A 0).obj ((toCatModule A).obj (DGModuleCat.of A (Cone f.hom))) ≅
      (recover A 0).obj (CatModule.cone ((toCatModule A).map f)) :=
  recoveryIso A (DGModuleCat.of A (Cone f.hom)) ≪≫ (diagonalConeRecoveryIso A f).symm

end
end DG.Diagonal
