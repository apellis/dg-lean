import DG.HalfGraded.DiagonalEvaluation
import DG.Category.Comparison

/-!
# Action-compatible recovery of ordinary dg modules

The original ring embeds in the weight-zero endomorphisms at every weight by placing
its homogeneous summands in bidegrees `(n, 0)`. This is an actual dg functor from
`SingleObj A`, so restriction gives `recover A w : CatModule C_A ⥤ DGModuleCat A`
for arbitrary modules over the diagonal weight category.

At weight zero, evaluation gives a natural isomorphism `toCatModule A ⋙ recover A 0 ≅ 𝟭`.
Its linearity is proved from the existing CatModule action, not imposed by transport
along an additive equivalence. No full faithfulness after localization, general compactness
preservation, or CatModule shift/cone comparison is asserted.
-/

open CategoryTheory DirectSum
universe v u
namespace DG.Diagonal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- Insert every original homogeneous summand into weight zero. -/
def weightZeroLift (M : DGModuleCat.{v} A) : M →+ Value A M 0 :=
  (DirectSum.toAddMonoid (toWeightZero A M)).comp
    (decomposeAddEquiv (DG.grading (M := M))).toAddMonoidHom

@[simp] theorem weightZeroLift_homogeneous (M : DGModuleCat.{v} A) {n : ℤ} {m : M}
    (hm : m ∈ DG.grading n) :
    weightZeroLift A M m = toWeightZero A M n ⟨m, hm⟩ := by
  change DirectSum.toAddMonoid (toWeightZero A M) (decompose (DG.grading (M := M)) m) = _
  rw [decompose_of_mem _ hm, DirectSum.toAddMonoid_of]

@[simp] theorem valueEvaluation_toWeightZero (M : DGModuleCat.{v} A) (n : ℤ)
    (m : DG.grading (M := M) n) :
    valueEvaluation A M 0 (toWeightZero A M n m) = m := evaluation_mk _ _ _

@[simp] theorem valueEvaluation_weightZeroLift (M : DGModuleCat.{v} A) (m : M) :
    valueEvaluation A M 0 (weightZeroLift A M m) = m := by
  induction m using DG.induction_on with
  | h_zero => simp
  | h_homogeneous m => rw [weightZeroLift_homogeneous A M m.2, valueEvaluation_toWeightZero]
  | h_add x y hx hy => simp only [map_add, hx, hy]

@[simp] theorem weightZeroLift_valueEvaluation (M : DGModuleCat.{v} A) (x : Value A M 0) :
    weightZeroLift A M (valueEvaluation A M 0 x) = x := by
  apply Subtype.ext
  change (weightZeroLift A M (evaluation x.1)).1 = x.1
  refine HalfRegrade.weightGrading_induction
    (P := fun x : RegradedModule M => (weightZeroLift A M (evaluation x)).1 = x)
    (by simp) (fun n m hm => ?_) (fun x y hx hy => by
      rw [map_add, map_add]
      exact congrArg₂ (· + ·) hx hy) x.2
  rw [evaluation_mk, weightZeroLift_homogeneous A M
    (show m ∈ DG.grading n from (halfGrading_zero_weight M n) ▸ hm)]
  rfl

/-- The original ring maps to weight-zero endomorphisms at every weight. -/
def scalarHom (w : ℤ) : A →+ ((⟨w⟩ : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) ⟶ ⟨w⟩) where
  toFun a := ⟨(weightZeroLift A (DGModuleCat.of A A) a).1, by
    simpa only [sub_self] using (weightZeroLift A (DGModuleCat.of A A) a).2⟩
  map_zero' := Subtype.ext (congrArg (fun x : Value A (DGModuleCat.of A A) 0 => x.1) (map_zero (weightZeroLift A (DGModuleCat.of A A))))
  map_add' a b := Subtype.ext (congrArg (fun x : Value A (DGModuleCat.of A A) 0 => x.1) (map_add (weightZeroLift A (DGModuleCat.of A A)) a b))

@[simp] theorem scalarHom_homogeneous (w n : ℤ) (a : A) (ha : a ∈ DG.grading n) :
    (scalarHom A w a).1 = (HalfGradedDGRing.ofDGRing A).place (n, 0) a
      (by change a ∈ halfGrading (grading A) 2 (n, 0)
          rw [halfGrading_zero_weight A]; exact ha) := by
  change (weightZeroLift A (DGModuleCat.of A A) a).1 = _
  rw [weightZeroLift_homogeneous A (DGModuleCat.of A A) ha]
  rfl

theorem scalarHom_one (w : ℤ) : scalarHom A w 1 = 𝟙 _ := by
  apply Subtype.ext
  rw [scalarHom_homogeneous A w 0 1 one_mem_grading]
  exact HalfGradedDGRing.one_eq_place.symm

theorem scalarHom_mul (w : ℤ) (a b : A) :
    scalarHom A w (a * b) = scalarHom A w b ≫ scalarHom A w a := by
  induction a using DG.induction_on with
  | h_zero => simp
  | h_add a a' ha ha' => simp only [add_mul, map_add, ha, ha', Preadditive.comp_add]
  | @h_homogeneous i a =>
    induction b using DG.induction_on with
    | h_zero => simp
    | h_add b b' hb hb' => simp only [mul_add, map_add, hb, hb', Preadditive.add_comp]
    | @h_homogeneous j b =>
      apply Subtype.ext
      rw [WeightCategory.comp_val, scalarHom_homogeneous A w (i + j) _ (mul_mem_grading a.2 b.2),
        scalarHom_homogeneous A w i _ a.2, scalarHom_homogeneous A w j _ b.2,
        HalfGradedDGRing.place_mul_place]
      rfl

theorem scalarHom_mem (w : ℤ) {n : ℤ} {a : A} (ha : a ∈ DG.grading n) :
    scalarHom A w a ∈ DG.grading n := by
  change (scalarHom A w a).1 ∈ DG.grading n
  rw [scalarHom_homogeneous A w n a ha]
  exact (HalfGradedDGRing.ofDGRing A).place_mem_grading (n, 0) _

theorem scalarHom_d (w : ℤ) (a : A) : scalarHom A w (d a) = d (scalarHom A w a) := by
  induction a using DG.induction_on with
  | h_zero => simp
  | h_add a b ha hb => simp only [map_add, ha, hb]
  | @h_homogeneous n a =>
    apply Subtype.ext
    rw [WeightCategory.d_val, scalarHom_homogeneous A w (n + 1) _ (DG.d_mem a.2),
      scalarHom_homogeneous A w n _ a.2, HalfGradedDGRing.d_place]
    rfl

/-- Embed the one-object dg category of `A` at any weight, using actual ring placements. -/
def scalarInclusion (w : ℤ) : SingleObj A ⥤ WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded where
  obj _ := ⟨w⟩
  map a := scalarHom A w a
  map_id _ := scalarHom_one A w
  map_comp a b := scalarHom_mul A w b a

instance (w : ℤ) : (scalarInclusion A w).Additive where
  map_add := fun {_ _ f g} => map_add (scalarHom A w) f g

instance (w : ℤ) : (scalarInclusion A w).IsDGFunctor where
  map_mem' := scalarHom_mem A w
  map_d' := scalarHom_d A w

/-- Evaluation with the `A`-action induced by weight-zero endomorphisms, not forgotten. -/
def recover (w : ℤ) :
    CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) ⥤ DGModuleCat.{v} A :=
  CatModule.precomp (scalarInclusion A w) ⋙ CatModule.toDGModuleCat A

/-- Evaluation intertwines the actual weight-zero endomorphism action with the original
`A`-action, at every weight and for arbitrary (not necessarily homogeneous) elements. -/
theorem valueEvaluation_scalarHom (M : DGModuleCat.{v} A) (w : ℤ) (a : A)
    (x : Value A M w) :
    valueEvaluation A M w (((toCatModule A).obj M).act (scalarHom A w a) x) =
      a • valueEvaluation A M w x := by
  induction a using DG.induction_on with
  | h_zero => simp only [map_zero, AddMonoidHom.zero_apply, zero_smul]
  | h_add a b ha hb => simp only [map_add, AddMonoidHom.add_apply, ha, hb, add_smul]
  | @h_homogeneous n a =>
    change evaluation ((scalarHom A w a).1 • x.1) = a.1 • evaluation x.1
    rw [scalarHom_homogeneous A w n _ a.2]
    induction x.1 using HalfRegrade.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | mk q m hm => rw [place_smul_mk, evaluation_mk, evaluation_mk]

/-- The action on recovery is the existing CatModule action, restricted along `A`. -/
theorem recover_smul (N : CatModule.{v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) (w : ℤ) (a : A)
    (x : (recover A w).obj N) :
    (a • x : (recover A w).obj N) = N.act (scalarHom A w a) x := rfl

/-- Weight-zero evaluation is a genuine morphism of dg `A`-modules. -/
def recoveryMap (M : DGModuleCat.{v} A) :
    (recover A 0).obj ((toCatModule A).obj M) ⟶ M :=
  DGModuleCat.Hom.mk
    { toLinearMap := { valueEvaluation A M 0 with
        map_smul' := valueEvaluation_scalarHom A M 0 }
      map_mem' := fun {n x} hx => by
        change evaluation x.1 ∈ DG.grading n
        have h := valueEvaluation_mem A M (t := 0) hx
        change evaluation x.1 ∈ DG.grading (n + 2 * 0) at h
        simpa only [mul_zero, add_zero] using h
      map_d' := valueEvaluation_d A M 0 }

theorem recoveryMap_bijective (M : DGModuleCat.{v} A) :
    Function.Bijective (recoveryMap A M) := by
  constructor
  · exact Function.LeftInverse.injective (weightZeroLift_valueEvaluation A M)
  · exact Function.RightInverse.surjective (valueEvaluation_weightZeroLift A M)

/-- The original dg module is recovered with its action, grading and differential. -/
def recoveryIso (M : DGModuleCat.{v} A) :
    (recover A 0).obj ((toCatModule A).obj M) ≅ M := by
  letI := DGModuleCat.isIso_of_bijective (recoveryMap A M) (recoveryMap_bijective A M)
  exact asIso (recoveryMap A M)

/-- Action-compatible weight-zero recovery is natural in every ordinary dg module map. -/
def recoveryNatIso : toCatModule.{v} A ⋙ recover A 0 ≅ 𝟭 (DGModuleCat.{v} A) :=
  NatIso.ofComponents (recoveryIso A) (by
    intro M N f
    apply DGModuleCat.hom_ext
    apply DGModuleHom.ext
    intro x
    exact evaluation_regradedMap f x.1)

@[simp] theorem recoveryIso_hom_toWeightZero (M : DGModuleCat.{v} A) (n : ℤ)
    (m : DG.grading (M := M) n) :
    (recoveryIso A M).hom (toWeightZero A M n m) = m :=
  valueEvaluation_toWeightZero A M n m

end
end DG.Diagonal
