import DG.HalfGraded.DiagonalFullness

/-!
# The actual diagonal embedding–recovery adjunction

For an arbitrary dg ring, the diagonal module functor is left adjoint to weight-zero
recovery on unrestricted modules over the diagonal weight category. At weight `4t`,
the counit evaluates in the original module and acts by the periodic unit of degree
`-2t`; at unsupported weights its source is zero. Factorization of every arrow between
supported weights and vanishing of the remaining relevant arrows prove action coherence.

The unit is the inverse of the existing action-compatible recovery isomorphism. Both
triangle identities are proved on the actual module categories. No derived fullness or
general compactness preservation is asserted here; those require localization and
coproduct arguments beyond this module-level adjunction.
-/

open CategoryTheory
universe v u
namespace DG.Diagonal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The periodic unit is homogeneous in its actual cohomological degree. -/
theorem periodicUnit_mem (t : ℤ) : periodicUnit A t ∈ DG.grading (-2 * t) :=
  (HalfGradedDGRing.ofDGRing A).place_mem_grading (-2 * t, 4 * t) _

/-- The periodic unit is a cocycle. -/
@[simp] theorem periodicUnit_d (t : ℤ) : d (periodicUnit A t) = 0 := by
  apply Subtype.ext
  change d ((HalfGradedDGRing.ofDGRing A).place (-2 * t, 4 * t) 1 _) = 0
  rw [HalfGradedDGRing.d_place]
  simp only [HalfGradedDGRing.ofDGRing_hd, d_one, HalfGradedDGRing.place_zero]

/-- The supported counit component uses the existing action of an arbitrary CatModule. -/
def supportedCounit (N : CatModule.{v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) (t : ℤ) :
    Value A ((recover A 0).obj N) (4 * t) →+ N.obj ⟨4 * t⟩ :=
  (N.act (periodicUnit A t)).comp (valueEvaluation A ((recover A 0).obj N) (4 * t))

theorem supportedCounit_mem (N : CatModule.{v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) (t : ℤ)
    {n : ℤ} {x : Value A ((recover A 0).obj N) (4 * t)} (hx : x ∈ DG.grading n) :
    supportedCounit A N t x ∈ DG.grading n := by
  have h := N.act_mem' (periodicUnit_mem A t)
    (valueEvaluation_mem A ((recover A 0).obj N) hx)
  rw [show -2 * t + (n + 2 * t) = n by ring] at h
  exact h

theorem supportedCounit_d (N : CatModule.{v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) (t : ℤ)
    (x : Value A ((recover A 0).obj N) (4 * t)) :
    supportedCounit A N t (d x) = d (supportedCounit A N t x) := by
  change N.act (periodicUnit A t) (valueEvaluation A ((recover A 0).obj N) (4 * t) (d x)) = _
  rw [valueEvaluation_d]
  change _ = d (N.act (periodicUnit A t) _)
  rw [N.d_act' (periodicUnit_mem A t), periodicUnit_d, map_zero,
    AddMonoidHom.zero_apply, zero_add]
  rw [show koszulSign (-2 * t) = 1 from koszulSign_even ⟨-t, by ring⟩, one_smul]
  rfl

@[simp] theorem supportedCounit_supportedElement (N : CatModule.{v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) (n t : ℤ)
    (m : DG.grading (M := (recover A 0).obj N) (n + 2 * t)) :
    supportedCounit A N t (supportedElement A ((recover A 0).obj N) n t m) =
      N.act (periodicUnit A t) m.1 := by
  exact congrArg (N.act (periodicUnit A t))
    (valueEvaluation_supportedElement A ((recover A 0).obj N) n t m)

/-- The periodic unit commutes with every original scalar, in the actual weight category. -/
theorem scalarHom_comp_periodicUnit (t : ℤ) (a : A) :
    scalarHom A 0 a ≫ periodicUnit A t = periodicUnit A t ≫ scalarHom A (4 * t) a := by
  induction a using DG.induction_on with
  | h_zero => simp
  | h_add a b ha hb => simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, ha, hb]
  | @h_homogeneous n a =>
    apply Subtype.ext
    simp only [WeightCategory.comp_val, scalarHom_homogeneous A 0 n _ a.2,
      scalarHom_homogeneous A (4 * t) n _ a.2, periodicUnit,
      HalfGradedDGRing.place_mul_place, one_mul, mul_one]
    exact HalfGradedDGRing.place_congr (by ext <;> dsimp <;> ring) rfl _ _

/-- The supported component intertwines the restricted original-ring action. -/
theorem supportedCounit_scalarHom (N : CatModule.{v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) (t : ℤ) (a : A)
    (x : Value A ((recover A 0).obj N) (4 * t)) :
    supportedCounit A N t
      (((toCatModule A).obj ((recover A 0).obj N)).act (scalarHom A (4 * t) a) x) =
      N.act (scalarHom A (4 * t) a) (supportedCounit A N t x) := by
  refine (congrArg (N.act (periodicUnit A t))
    (valueEvaluation_scalarHom A ((recover A 0).obj N) (4 * t) a x)).trans ?_
  change N.act (periodicUnit A t) (N.act (scalarHom A 0 a) _) = _
  rw [← N.act_comp', scalarHom_comp_periodicUnit, N.act_comp']
  rfl

/-- These components are natural for arbitrary CatModule morphisms. -/
theorem supportedCounit_naturality
    {N P : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)}
    (f : N ⟶ P) (t : ℤ) (x : Value A ((recover A 0).obj N) (4 * t)) :
    f.app ⟨4 * t⟩ (supportedCounit A N t x) =
      supportedCounit A P t
        (((toCatModule A).map ((recover A 0).map f)).app ⟨4 * t⟩ x) := by
  exact (f.map_smul (periodicUnit A t) _).trans
    (congrArg (P.act (periodicUnit A t))
      (evaluation_regradedMap ((recover A 0).map f) x.1).symm)

@[simp] theorem periodicUnit_zero : periodicUnit A 0 = 𝟙 _ := by
  apply Subtype.ext
  simp only [periodicUnit, mul_zero]
  exact HalfGradedDGRing.one_eq_place.symm

/-- Evaluation respects the actual regraded module action. -/
theorem evaluation_smul (M : DGModuleCat.{v} A)
    (a : (HalfGradedDGRing.ofDGRing A).Regraded) (x : RegradedModule M) :
    evaluation (a • x) = evaluation (M := A) a • evaluation x := by
  induction a using HalfGradedDGRing.induction_on with
  | zero => simp
  | add a b ha hb => simp only [add_smul, map_add, ha, hb]
  | mk p a ha =>
    induction x using HalfRegrade.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | mk q m hm =>
      rw [place_smul_mk, evaluation_mk]
      change a • m = evaluation (HalfRegrade.mk (grading A) 2 p a ha) •
        evaluation (HalfRegrade.mk (grading M) 2 q m hm)
      rw [evaluation_mk, evaluation_mk]

/-- All arrows between supported weights factor through the actual periodic units. -/
theorem periodicUnit_comp (s t : ℤ)
    (f : (⟨4 * s⟩ : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) ⟶ ⟨4 * t⟩) :
    periodicUnit A s ≫ f = scalarHom A 0 (evaluation (M := A) f.1) ≫ periodicUnit A t := by
  apply Subtype.ext
  change f.1 * (periodicUnit A s).1 =
    (periodicUnit A t).1 * (scalarHom A 0 (evaluation (M := A) f.1)).1
  refine HalfGradedDGRing.wgrading_induction
    (P := fun x : (HalfGradedDGRing.ofDGRing A).Regraded => x * (periodicUnit A s).1 =
      (periodicUnit A t).1 * (scalarHom A 0 (evaluation (M := A) x)).1)
    (by simp) (fun n a ha => ?_)
    (fun x y hx hy => by simp only [add_mul, map_add, WeightCategory.add_val, mul_add, hx, hy]) f.2
  have ha' : a ∈ DG.grading (n + 2 * (t - s)) := by
    change a ∈ halfGrading (grading A) 2 (n, 4 * t - 4 * s) at ha
    rw [show 4 * t - 4 * s = 4 * (t - s) by ring, halfGrading_supported] at ha
    exact ha
  change _ = (periodicUnit A t).1 *
    (scalarHom A 0 (evaluation (HalfRegrade.mk (grading A) 2 (n, 4 * t - 4 * s) a ha))).1
  rw [evaluation_mk, scalarHom_homogeneous A 0 _ a ha']
  simp only [periodicUnit, HalfGradedDGRing.place_mul_place, mul_one, one_mul]
  exact HalfGradedDGRing.place_congr (by ext <;> dsimp <;> ring) rfl _ _

/-- Compatibility with every arrow between supported weights, not just scalars. -/
theorem supportedCounit_act (N : CatModule.{v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) (s t : ℤ)
    (f : (⟨4 * s⟩ : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) ⟶ ⟨4 * t⟩)
    (x : Value A ((recover A 0).obj N) (4 * s)) :
    supportedCounit A N t (((toCatModule A).obj ((recover A 0).obj N)).act f x) =
      N.act f (supportedCounit A N s x) := by
  refine (congrArg (N.act (periodicUnit A t))
    (evaluation_smul A ((recover A 0).obj N) f.1 x.1)).trans ?_
  change N.act (periodicUnit A t) (N.act (scalarHom A 0 _) _) = _
  rw [← N.act_comp', ← periodicUnit_comp, N.act_comp']
  rfl

/-- The counit at all weights: unsupported diagonal source values are zero. -/
def counitApp (N : CatModule.{v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) (w : ℤ) :
    Value A ((recover A 0).obj N) w →+ N.obj ⟨w⟩ :=
  if h : 4 * (w / 4) = w then
    cast (congrArg (fun j => Value A ((recover A 0).obj N) j →+ N.obj ⟨j⟩) h)
      (supportedCounit A N (w / 4)) else 0

@[simp] theorem counitApp_supported (N : CatModule.{v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) (t : ℤ) :
    counitApp A N (4 * t) = supportedCounit A N t := by
  unfold counitApp
  split
  · apply eq_of_heq
    apply (cast_heq _ _).trans
    congr 1
    omega
  · omega

theorem counitApp_unsupported (N : CatModule.{v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) (w : ℤ)
    (hw : ¬ ∃ t : ℤ, w = 4 * t) : counitApp A N w = 0 := by
  rw [counitApp, dite_eq_right (fun h => hw ⟨w / 4, h.symm⟩)]

/-- There are no arrows whose weight difference lies outside the supported congruence class. -/
theorem weightHom_eq_zero {s t : ℤ}
    (f : (⟨s⟩ : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) ⟶ ⟨t⟩)
    (h : ¬ ∃ r : ℤ, t - s = 4 * r) : f = 0 := by
  have he := (value_subsingleton A (DGModuleCat.of A A) (t - s) h).elim
    (⟨f.1, f.2⟩ : Value A (DGModuleCat.of A A) (t - s)) 0
  exact Subtype.ext (congrArg
    (fun x : Value A (DGModuleCat.of A A) (t - s) => x.1) he)

/-- The actual counit is a dg CatModule morphism, for unrestricted target modules. -/
def counitMap (N : CatModule.{v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    (toCatModule A).obj ((recover A 0).obj N) ⟶ N where
  app w := counitApp A N w.as
  map_mem' := by
    rintro ⟨w⟩ n x hx
    by_cases hw : ∃ t : ℤ, w = 4 * t
    · obtain ⟨t, rfl⟩ := hw
      exact (counitApp_supported A N t) ▸ supportedCounit_mem A N t hx
    · rw [counitApp_unsupported A N w hw]
      exact zero_mem _
  map_d' := by
    rintro ⟨w⟩ x
    by_cases hw : ∃ t : ℤ, w = 4 * t
    · obtain ⟨t, rfl⟩ := hw
      rw [counitApp_supported]
      exact supportedCounit_d A N t x
    · rw [counitApp_unsupported A N w hw]
      exact d_zero.symm
  map_smul' := by
    rintro ⟨s⟩ ⟨t⟩ f x
    by_cases hs : ∃ r : ℤ, s = 4 * r
    · obtain ⟨r, rfl⟩ := hs
      by_cases ht : ∃ q : ℤ, t = 4 * q
      · obtain ⟨q, rfl⟩ := ht
        rw [counitApp_supported, counitApp_supported]
        exact supportedCounit_act A N r q f x
      · have hf : f = 0 := weightHom_eq_zero A f (by
          rintro ⟨q, hq⟩
          exact ht ⟨q + r, by omega⟩)
        subst f
        simp
    · let := value_subsingleton A ((recover A 0).obj N) s hs
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp

/-- The actual counit is natural in unrestricted CatModules. -/
def diagonalCounit : recover.{v} A 0 ⋙ toCatModule A ⟶ 𝟭 _ where
  app := counitMap A
  naturality := by
    intro N P f
    apply CatModule.Hom.ext
    rintro ⟨w⟩ x
    by_cases hw : ∃ t : ℤ, w = 4 * t
    · obtain ⟨t, rfl⟩ := hw
      change counitApp A P (4 * t) _ = f.app _ (counitApp A N (4 * t) x)
      rw [counitApp_supported, counitApp_supported]
      exact (supportedCounit_naturality A f t x).symm
    · change counitApp A P w _ = f.app ⟨w⟩ (counitApp A N w x)
      rw [counitApp_unsupported A N w hw, counitApp_unsupported A P w hw]
      exact (f.app ⟨w⟩).map_zero.symm

/-- On weight-zero recovery the counit is exactly the existing recovery isomorphism. -/
theorem recover_counitMap (N : CatModule.{v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    (recover A 0).map (counitMap A N) = (recoveryIso A ((recover A 0).obj N)).hom := by
  apply DGModuleCat.hom_ext
  apply DGModuleHom.ext
  intro x
  change counitApp A N (4 * 0) x = valueEvaluation A ((recover A 0).obj N) 0 x
  rw [counitApp_supported]
  change N.act (periodicUnit A 0) _ = _
  rw [periodicUnit_zero]
  exact N.act_id' _ _

/-- The diagonal embedding is left adjoint to actual weight-zero recovery.
The unit is the inverse of `recoveryNatIso`; the counit uses the existing action
of each unrestricted CatModule, and all weight-category arrows are respected. -/
def diagonalAdjunction : toCatModule.{v} A ⊣ recover A 0 where
  unit := (recoveryNatIso A).inv
  counit := diagonalCounit A
  left_triangle_components M := by
    apply diagonal_hom_ext A
    have h : (recover A 0).map
        ((toCatModule A).map (recoveryIso A M).inv ≫ counitMap A ((toCatModule A).obj M)) =
        𝟙 _ := by
      rw [Functor.map_comp, recover_counitMap]
      have hn := (recoveryNatIso A).hom.naturality (recoveryIso A M).inv
      change (recover A 0).map ((toCatModule A).map (recoveryIso A M).inv) ≫
        (recoveryIso A ((recover A 0).obj ((toCatModule A).obj M))).hom =
          (recoveryIso A M).hom ≫ (recoveryIso A M).inv at hn
      exact hn.trans (recoveryIso A M).hom_inv_id
    intro x
    exact congrArg (fun k => k.hom x) h
  right_triangle_components N := by
    change (recoveryIso A ((recover A 0).obj N)).inv ≫
      (recover A 0).map (counitMap A N) = 𝟙 _
    rw [recover_counitMap]
    exact (recoveryIso A ((recover A 0).obj N)).inv_hom_id

end
end DG.Diagonal
