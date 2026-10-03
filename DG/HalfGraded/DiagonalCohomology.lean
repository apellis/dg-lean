import DG.HalfGraded.DiagonalFunctor
import DG.Category.Homotopy.Acyclic
import DG.Derived.QuasiIso

/-!
# All-weight cohomology of the diagonal ordinary-module functor

For an arbitrary dg ring and module, evaluation identifies the component at weight `4t`
and cohomological degree `n` with the original degree `n + 2t`. Every other weight is zero.
The differential comparison is untwisted because the shift `2t` is even, including for
negative `t`. Evaluation induces a natural additive equivalence on cohomology. Consequently
the existing functor preserves and reflects the existing quasi-isomorphism predicates.
No derived equivalence, full faithfulness, or compactness assertion is made here.
-/

open CategoryTheory DirectSum
namespace DG.Diagonal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {M : Type*} [AddCommGroup M] [DGAddCommGroup M]

/-- The supported weights are precisely the multiples of four, not all even weights. -/
theorem halfDegree_mem_range_iff (n w : ℤ) :
    halfDegree 2 (n, w) ∈ Set.range diagonalDegree ↔ ∃ t : ℤ, w = 4 * t := by
  constructor
  · rintro ⟨j, hj⟩
    have h₁ := congrArg Prod.fst hj
    have h₂ := congrArg Prod.snd hj
    change 2 * j = w + n * 2 at h₁
    change (j : ZMod 2) = (n : ZMod 2) at h₂
    have hmod := (ZMod.intCast_eq_intCast_iff' j n 2).mp h₂
    exact ⟨(j - n) / 2, by omega⟩
  · rintro ⟨t, rfl⟩
    refine ⟨n + 2 * t, ?_⟩
    apply Prod.ext
    · change 2 * (n + 2 * t) = 4 * t + n * 2
      ring
    · change ((n + 2 * t : ℤ) : ZMod 2) = (n : ZMod 2)
      apply (ZMod.intCast_eq_intCast_iff' _ _ 2).mpr
      omega

/-- The original degree at weight `4t` and degree `n` is `n + 2t`. -/
theorem halfGrading_supported (n t : ℤ) :
    halfGrading (grading M) 2 (n, 4 * t) = DG.grading (M := M) (n + 2 * t) := by
  have h : halfDegree 2 (n, 4 * t) = diagonalDegree (n + 2 * t) := by
    apply Prod.ext
    · change 4 * t + n * 2 = 2 * (n + 2 * t)
      ring
    · change (n : ZMod 2) = ((n + 2 * t : ℤ) : ZMod 2)
      apply (ZMod.intCast_eq_intCast_iff' _ _ 2).mpr
      omega
  change grading M (halfDegree 2 (n, 4 * t)) = _
  rw [h, grading_diagonal]

/-- Every unsupported homogeneous component vanishes. -/
theorem halfGrading_unsupported (n w : ℤ) (hw : ¬ ∃ t : ℤ, w = 4 * t) :
    halfGrading (grading M) 2 (n, w) = ⊥ :=
  grading_eq_bot (by rwa [halfDegree_mem_range_iff])

/-- The shift at every supported weight is even, hence has no differential sign twist. -/
theorem supported_shift_sign (t : ℤ) : koszulSign (2 * t) = 1 :=
  koszulSign_even (even_two_mul t)

/-- Forget the bidegrees and sum the original elements. -/
def evaluation : RegradedModule M →+ M :=
  DirectSum.toAddMonoid fun p => (halfGrading (grading M) 2 p).subtype

@[simp] theorem evaluation_mk (p : ℤ × ℤ) (m : M)
    (hm : m ∈ grading M (halfDegree 2 p)) :
    evaluation (HalfRegrade.mk (grading M) 2 p m hm) = m :=
  DirectSum.toAddMonoid_of _ _ _

theorem evaluation_d (x : RegradedModule M) : evaluation (d x) = d (evaluation x) := by
  induction x using HalfRegrade.induction_on with
  | zero => simp
  | mk p m hm => rw [d_mk, evaluation_mk, evaluation_mk]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Expose the existing direct-sum representation for component evaluation. -/
abbrev asSum (x : RegradedModule M) : ⨁ p : ℤ × ℤ, ↥(halfGrading (grading M) 2 p) := x

/-- A bihomogeneous element is its single original component. -/
theorem homogeneous_eq_mk {n w : ℤ} {x : RegradedModule M}
    (hn : x ∈ DG.grading n) (hw : x ∈ wgrading w) :
    x = HalfRegrade.mk (grading M) 2 (n, w) ((asSum x (n, w) : M)) (asSum x (n, w)).2 := by
  apply DFinsupp.ext
  intro p
  by_cases hp : p = (n, w)
  · subst p; simp [HalfRegrade.mk]
  · rw [HalfRegrade.mk, DirectSum.of_eq_of_ne _ _ _ hp]
    by_cases hpn : p.1 = n
    · exact hw p (fun hpw => hp (Prod.ext hpn hpw))
    · exact hn p hpn

variable (M)
/-- Evaluation identifies a supported bihomogeneous component with its original degree. -/
def componentEquiv (n t : ℤ) :
    DG.bigrading (RegradedModule M) (n, 4 * t) ≃+ DG.grading (M := M) (n + 2 * t) where
  toFun x := ⟨evaluation x, by
    rw [homogeneous_eq_mk x.2.1 x.2.2, evaluation_mk]
    exact (halfGrading_supported (M := M) n t) ▸ (asSum x.1 (n, 4 * t)).2⟩
  invFun m := ⟨HalfRegrade.mk (grading M) 2 (n, 4 * t) m
      (by change m.1 ∈ halfGrading (grading M) 2 (n, 4 * t)
          rw [halfGrading_supported]; exact m.2),
    HalfRegrade.mk_mem_cohGrading _ _, HalfRegrade.mk_mem_weightGrading _ _⟩
  left_inv x := by
    apply Subtype.ext
    apply (HalfRegrade.mk_congr rfl _ _ _).trans (homogeneous_eq_mk x.2.1 x.2.2).symm
    change evaluation x.1 = (asSum x.1 (n, 4 * t) : M)
    conv_lhs => rw [homogeneous_eq_mk x.2.1 x.2.2, evaluation_mk]
  right_inv m := Subtype.ext (evaluation_mk _ _ _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
variable (A) (M : DGModuleCat A)

/-- The actual value of the diagonal functor at a weight. -/
abbrev Value (w : ℤ) := ((toCatModule A).obj M).obj ⟨w⟩

/-- Evaluation on the value at any weight. -/
def valueEvaluation (w : ℤ) : Value A M w →+ M :=
  evaluation.comp (wgrading (M := RegradedModule M) w).subtype

theorem valueEvaluation_d (w : ℤ) (x : Value A M w) :
    valueEvaluation A M w (d x) = d (valueEvaluation A M w x) := evaluation_d x.1

/-- Evaluation agrees with the differential of the library's signed shift. -/
theorem valueEvaluation_shift_d (t : ℤ) (x : Value A M (4 * t)) :
    Shift.mk (2 * t) (valueEvaluation A M (4 * t) (d x)) =
      d (Shift.mk (2 * t) (valueEvaluation A M (4 * t) x)) := by
  rw [Shift.d_mk, supported_shift_sign, one_smul, valueEvaluation_d]

theorem valueEvaluation_mem {n t : ℤ} {x : Value A M (4 * t)}
    (hx : x ∈ DG.grading n) : valueEvaluation A M (4 * t) x ∈ DG.grading (n + 2 * t) :=
  (componentEquiv M n t ⟨x.1, hx, x.2⟩).2

theorem valueEvaluation_injective_degree {n t : ℤ} {x y : Value A M (4 * t)}
    (hx : x ∈ DG.grading n) (hy : y ∈ DG.grading n)
    (h : valueEvaluation A M (4 * t) x = valueEvaluation A M (4 * t) y) : x = y := by
  apply Subtype.ext
  have he : (⟨x.1, hx, x.2⟩ : DG.bigrading (RegradedModule M) (n, 4 * t)) =
      ⟨y.1, hy, y.2⟩ := (componentEquiv M n t).injective (Subtype.ext h)
  exact congrArg (fun z : DG.bigrading (RegradedModule M) (n, 4 * t) => z.1) he

/-- Insert an original homogeneous element into the supported weight value. -/
def supportedElement (n t : ℤ) (m : DG.grading (M := M) (n + 2 * t)) : Value A M (4 * t) :=
  ⟨((componentEquiv M n t).symm m).1, ((componentEquiv M n t).symm m).2.2⟩

theorem supportedElement_mem (n t : ℤ) (m : DG.grading (M := M) (n + 2 * t)) :
    supportedElement A M n t m ∈ DG.grading n := ((componentEquiv M n t).symm m).2.1

@[simp] theorem valueEvaluation_supportedElement (n t : ℤ)
    (m : DG.grading (M := M) (n + 2 * t)) :
    valueEvaluation A M (4 * t) (supportedElement A M n t m) = m :=
  congrArg Subtype.val ((componentEquiv M n t).apply_symm_apply m)

/-- Unsupported weights vanish as entire dg abelian groups. -/
theorem value_subsingleton (w : ℤ) (hw : ¬ ∃ t : ℤ, w = 4 * t) :
    Subsingleton (Value A M w) := by
  suffices h : ∀ x : Value A M w, x = 0 from ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  apply Subtype.ext
  change x.1 = (0 : RegradedModule M)
  refine HalfRegrade.weightGrading_induction (P := fun x : RegradedModule M => x = 0) rfl
    (fun n m hm => ?_) (fun x y hx hy => by rw [hx, hy, add_zero]) x.2
  have hm0 : m = 0 := by
    change m ∈ halfGrading (grading M) 2 (n, w) at hm
    rw [halfGrading_unsupported n w hw] at hm
    exact hm
  subst m
  exact HalfRegrade.mk_zero _

/-- Evaluation sends supported cocycles to cocycles in the shifted original degree. -/
def supportedCocycles (n t : ℤ) : cocycles (Value A M (4 * t)) n →+ cocycles M (n + 2 * t) where
  toFun z := ⟨valueEvaluation A M (4 * t) z,
    valueEvaluation_mem A M z.2.1, by
      change d (valueEvaluation A M (4 * t) z) = 0
      rw [← valueEvaluation_d, z.2.2, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- Boundaries correspond, not just cycles: this includes negative degrees and weights. -/
theorem valueEvaluation_mem_coboundaries_iff (n t : ℤ) (z : cocycles (Value A M (4 * t)) n) :
    valueEvaluation A M (4 * t) z ∈ coboundaries M (n + 2 * t) ↔
      (z : Value A M (4 * t)) ∈ coboundaries (Value A M (4 * t)) n := by
  constructor
  · rintro ⟨m, hm, hd⟩
    change m ∈ DG.grading (n + 2 * t - 1) at hm
    let y := supportedElement A M (n - 1) t ⟨m, by
      simpa only [show n - 1 + 2 * t = n + 2 * t - 1 by omega] using hm⟩
    refine ⟨y, supportedElement_mem A M _ _ _, ?_⟩
    apply valueEvaluation_injective_degree A M (n := n)
      (by simpa using DG.d_mem (supportedElement_mem A M (n - 1) t _)) z.2.1
    rw [valueEvaluation_d, valueEvaluation_supportedElement, hd]
  · rintro ⟨y, hy, hd⟩
    refine ⟨valueEvaluation A M (4 * t) y, ?_, ?_⟩
    · change valueEvaluation A M (4 * t) y ∈ DG.grading (n + 2 * t - 1)
      simpa only [show n - 1 + 2 * t = n + 2 * t - 1 by omega] using valueEvaluation_mem A M hy
    · rw [← valueEvaluation_d, hd]

/-- The all-supported-weight cohomology comparison, induced by actual evaluation. -/
def supportedCohomologyMap (n t : ℤ) :
    cohomology (Value A M (4 * t)) n →+ cohomology M (n + 2 * t) :=
  cohomology.lift ((cohomology.mk M _).comp (supportedCocycles A M n t)) fun z hz =>
    (cohomology.mk_eq_zero_iff _).mpr ((valueEvaluation_mem_coboundaries_iff A M n t z).mpr hz)

@[simp] theorem supportedCohomologyMap_mk (n t : ℤ) (z : cocycles (Value A M (4 * t)) n) :
    supportedCohomologyMap A M n t (cohomology.mk _ n z) =
      cohomology.mk M _ (supportedCocycles A M n t z) := cohomology.lift_mk _ _ _

theorem supportedCohomologyMap_bijective (n t : ℤ) :
    Function.Bijective (supportedCohomologyMap A M n t) := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨z, rfl⟩ := cohomology.mk_surjective _ _ x
    rw [supportedCohomologyMap_mk, cohomology.mk_eq_zero_iff] at hx
    exact (cohomology.mk_eq_zero_iff _).mpr
      ((valueEvaluation_mem_coboundaries_iff A M n t z).mp hx)
  · intro x
    obtain ⟨z, rfl⟩ := cohomology.mk_surjective _ _ x
    let y := supportedElement A M n t ⟨z, z.2.1⟩
    have hy : d y = 0 := by
      apply valueEvaluation_injective_degree A M (n := n + 1)
        (DG.d_mem (supportedElement_mem A M n t _)) (zero_mem _)
      rw [valueEvaluation_d, valueEvaluation_supportedElement, z.2.2, map_zero]
    refine ⟨cohomology.mk _ n ⟨y, supportedElement_mem A M n t _, hy⟩, ?_⟩
    rw [supportedCohomologyMap_mk]
    congr 1
    apply Subtype.ext
    exact valueEvaluation_supportedElement A M n t _

/-- At every supported weight, `Hⁿ(F(M)(4t)) = Hⁿ⁺²ᵗ(M)`. -/
def supportedCohomologyEquiv (n t : ℤ) :
    cohomology (Value A M (4 * t)) n ≃+ cohomology M (n + 2 * t) :=
  AddEquiv.ofBijective (supportedCohomologyMap A M n t) (supportedCohomologyMap_bijective A M n t)

/-- At every unsupported weight, all cohomology vanishes. -/
theorem unsupportedCohomology_subsingleton (w n : ℤ) (hw : ¬ ∃ t : ℤ, w = 4 * t) :
    Subsingleton (cohomology (Value A M w) n) := by
  let := value_subsingleton A M w hw
  exact ⟨fun x y => by
    obtain ⟨x, rfl⟩ := cohomology.mk_surjective _ _ x
    obtain ⟨y, rfl⟩ := cohomology.mk_surjective _ _ y
    exact congrArg (cohomology.mk _ _) (Subsingleton.elim x y)⟩

variable {A M} {N : DGModuleCat A}

omit [DGRing A] in
/-- Evaluation is natural for the actual componentwise functor map. -/
theorem evaluation_regradedMap (f : M ⟶ N) (x : RegradedModule M) :
    evaluation (regradedMap f x) = f.hom (evaluation x) := by
  induction x using HalfRegrade.induction_on with
  | zero => simp
  | mk p m hm => rw [regradedMap_mk, evaluation_mk, evaluation_mk]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Naturality of the supported cohomology comparison in every degree and weight. -/
theorem supportedCohomologyMap_natural (f : M ⟶ N) (n t : ℤ)
    (x : cohomology (Value A M (4 * t)) n) :
    supportedCohomologyMap A N n t (CatModule.cohomologyMap ((toCatModule A).map f) ⟨4 * t⟩ n x) =
      cohomology.map f.hom (n + 2 * t) (supportedCohomologyMap A M n t x) := by
  obtain ⟨z, rfl⟩ := cohomology.mk_surjective _ _ x
  rw [CatModule.cohomologyMap_mk, supportedCohomologyMap_mk,
    supportedCohomologyMap_mk, cohomology.map_mk]
  congr 1
  apply Subtype.ext
  exact evaluation_regradedMap f z.1.1

/-- Quasi-isomorphism in a supported weight is exactly the original cohomology bijection. -/
theorem supported_bijective_iff (f : M ⟶ N) (n t : ℤ) :
    Function.Bijective (CatModule.cohomologyMap ((toCatModule A).map f) ⟨4 * t⟩ n) ↔
      Function.Bijective (cohomology.map f.hom (n + 2 * t)) := by
  have h : (supportedCohomologyMap A N n t) ∘
      (CatModule.cohomologyMap ((toCatModule A).map f) ⟨4 * t⟩ n) =
      (cohomology.map f.hom (n + 2 * t)) ∘ (supportedCohomologyMap A M n t) :=
    funext (supportedCohomologyMap_natural f n t)
  rw [← (supportedCohomologyMap_bijective A N n t).of_comp_iff', h,
    Function.Bijective.of_comp_iff _ (supportedCohomologyMap_bijective A M n t)]

/-- The diagonal ordinary-module functor preserves and reflects genuine quasi-isomorphisms.
Preservation uses every supported weight and the vanishing of every unsupported weight. -/
theorem isQuasiIso_toCatModule_iff (f : M ⟶ N) :
    CatModule.IsQuasiIso ((toCatModule A).map f) ↔ f.hom.IsQuasiIso := by
  constructor
  · intro hf n
    have h := (supported_bijective_iff f n 0).mp (hf ⟨4 * 0⟩ n)
    have hn : n + 2 * (0 : ℤ) = n := by omega
    rw [hn] at h
    exact h
  · intro hf w n
    obtain ⟨w⟩ := w
    by_cases hw : ∃ t : ℤ, w = 4 * t
    · obtain ⟨t, rfl⟩ := hw
      exact (supported_bijective_iff f n t).mpr (hf _)
    · let := unsupportedCohomology_subsingleton A M w n hw
      let := unsupportedCohomology_subsingleton A N w n hw
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

/-- The same comparison stated directly with the existing categorical predicate. -/
theorem quasiIso_toCatModule_iff (f : M ⟶ N) :
    CatModule.IsQuasiIso ((toCatModule A).map f) ↔ DGModuleCat.quasiIso A f :=
  isQuasiIso_toCatModule_iff f

end
end DG.Diagonal
