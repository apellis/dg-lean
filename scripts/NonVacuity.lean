import DG

/-!
# Non-vacuity checks for the headline theorems

Each `example` below applies a headline theorem to a concrete datum and discharges every
hypothesis by proof. If a later change makes a hypothesis set unsatisfiable for these data, or
breaks the statement's shape, this file stops compiling and CI fails. Where cheap, a second
`example` records that the conclusion is not degenerate.

Data: the rings `ℤ` and `ℚ` and the matrix ring `M₂(ℚ)`, each concentrated in degree `0` (the
scoped instances of `DG.DegreeZero`); the identity map of `ℚ`; the idempotent `E₁₁` of `M₂(ℚ)`;
the Clifford algebra `Cl₁` over `ℚ` as a half-graded dg ring with parameter `1`. Derived
categories are the small models `DG.HasDerivedCategory.small`.
-/

open CategoryTheory DG

open scoped DG.DegreeZero

noncomputable section

namespace NonVacuity

instance : DG.HasDerivedCategory.{0, 0} ℤ := DG.HasDerivedCategory.small ℤ
instance : DG.HasDerivedCategory.{0, 0} ℚ := DG.HasDerivedCategory.small ℚ

/-! ### `K₀` of a principal ideal domain (roadmap 5.6) -/

example : DGRing.K0 ℤ ≃+ ℤ := DGRing.K0.equivIntOfIsPrincipalIdealRing ℤ

/-- Non-degeneracy: the class of `ℤ` is sent to `1`. -/
example : DGRing.K0.equivIntOfIsPrincipalIdealRing ℤ (DGRing.K0.self ℤ) = 1 :=
  DGRing.K0.equivIntOfIsPrincipalIdealRing_self ℤ

/-! ### `K₀` of a field (roadmap 5.6) -/

example : DGRing.K0.equivIntOfField ℚ (DGRing.K0.self ℚ) = 1 :=
  DGRing.K0.equivIntOfField_self ℚ

/-! ### Compact objects of `D(k)` for a field (roadmap 5.6) -/

example (X : DG.DerivedCategory ℚ) :
    DG.IsCompact.{0} X ↔ DG.DerivedCategory.HasFiniteCohomology ℚ X :=
  DG.DerivedCategory.isCompact_iff_hasFiniteCohomology

/-! ### Compact objects of `D(R)` are the perfect complexes (roadmap 5.6) -/

example (X : DG.DerivedCategory ℤ) :=
  letI := _root_.HasDerivedCategory.standard (ModuleCat.{0} ℤ)
  DG.DerivedCategory.isCompact_iff_isPerfect ℤ X

/-! ### Keller's theorem for dg rings, along the identity of `ℚ` -/

example : DG.DerivedCategory ℚ ≌ DG.DerivedCategory ℚ :=
  DGRingHom.derivedEquivalence.{0} DGRingHom.id (DGRingHom.isQuasiIso_id ℚ)

/-! ### `K₀` of a positive dg algebra with `A⁰ = k` (roadmap 6.3), for `A = ℚ` -/

/-- `ℚ` in degree `0` is positive. -/
theorem isPositive_rat : IsPositive ℚ := IsPositive.degreeZero ℚ

instance : DG.HasDerivedCategory.{0, 0} isPositive_rat.degreeZeroDGSubring :=
  DG.HasDerivedCategory.small _

example : isPositive_rat.K0EquivIntOfField ℚ (fun a _ => ⟨a, rfl⟩) (DGRing.K0.self ℚ) = 1 :=
  isPositive_rat.K0EquivIntOfField_self ℚ (fun a _ => ⟨a, rfl⟩)

/-! ### `K₀(A) ≃ ℤ` for a connected dg ring over `ℤ` (roadmap 6.6), for `A = ℤ` -/

theorem cohomology_int_eq_zero {n : ℤ} (hn : n ≠ 0) (x : cohomology ℤ n) : x = 0 := by
  induction x using cohomology.induction_on with
  | h z =>
    rw [show z = 0 from Subtype.ext
      (((DegreeZero.mem_grading_iff (R := ℤ)).mp (cocycles.mem_grading z)).resolve_left hn),
      map_zero]

theorem isConnectedInt_int : IsConnectedInt ℤ where
  grading_neg n hn := by
    ext a
    rw [AddSubgroup.mem_bot, DegreeZero.mem_grading_iff]
    omega
  exists_intCast a _ := ⟨a, Int.cast_id⟩
  intCast_injective a b h := by simpa using h

example :
    DGRing.K0.equivIntOfIsConnectedInt isConnectedInt_int (cohomology_int_eq_zero one_ne_zero)
      (fun _ _ x _ => cohomology_int_eq_zero two_ne_zero x) (DGRing.K0.self ℤ) = 1 :=
  DGRing.K0.equivIntOfIsConnectedInt_self _ _ _

/-! ### Morita theory for an idempotent (roadmap 7.3), for `E₁₁ ∈ M₂(ℚ)` -/

/-- The matrix unit `E₁₁` of `M₂(ℚ)`, a degree-`0` idempotent cocycle. -/
def e11 : DGIdempotent (Matrix (Fin 2) (Fin 2) ℚ) where
  val := Matrix.single 0 0 1
  mem_zero := DegreeZero.mem_grading_iff.mpr (Or.inl rfl)
  mul_self := by rw [Matrix.single_mul_single_same, mul_one]
  d_eq_zero := rfl

theorem mem_cocycles_zero (a : Matrix (Fin 2) (Fin 2) ℚ) : a ∈ cocycles _ 0 :=
  mem_cocycles.mpr ⟨DegreeZero.mem_grading_iff.mpr (Or.inl rfl), rfl⟩

/-- `1 = E₁₁ E₁₁ E₁₁ + E₂₁ E₁₁ E₁₂`, so `E₁₁` is full up to homotopy. -/
theorem isFullH0_e11 : e11.IsFullH0 := by
  refine ⟨2, ![1, Matrix.single 1 0 1], ![1, Matrix.single 0 1 1], fun _ => mem_cocycles_zero _,
    fun _ => mem_cocycles_zero _, ?_⟩
  have h : ∑ k, ![1, Matrix.single 1 0 1] k * e11.val * ![1, Matrix.single 0 1 1] k -
      (1 : Matrix (Fin 2) (Fin 2) ℚ) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [e11, Fin.sum_univ_two]
  rw [h]
  exact zero_mem _

instance : DG.HasDerivedCategory.{0, 0} e11.Corner := DG.HasDerivedCategory.small _
instance : DG.HasDerivedCategory.{0, 0} (Matrix (Fin 2) (Fin 2) ℚ) :=
  DG.HasDerivedCategory.small _

example : DG.DerivedCategory e11.Corner ≌ DG.DerivedCategory (Matrix (Fin 2) (Fin 2) ℚ) :=
  e11.moritaEquivalence.{0} isFullH0_e11

/-! ### Superrings in internal degree `0` are positive: `Cl₁` over `ℚ` -/

example : (HalfGradedDGRing.clifford ℚ 1).IsPositive :=
  HalfGradedDGRing.isPositive_clifford one_pos

/-- Non-degeneracy: `Cl₁` has a nonzero odd element of internal degree `0`. -/
example : ∃ a ∈ (HalfGradedDGRing.clifford ℚ 1).hgrading (0, 1), a ≠ 0 :=
  HalfGradedDGRing.clifford_odd_ne_zero 1

end NonVacuity
