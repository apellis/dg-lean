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

/-! ### Dimension shift from Webster Lemma 6.8 -/

open CategoryTheory.Limits CategoryTheory.Pretriangulated

open scoped ZeroObject

private def zeroDGSequence : ShortComplex (DGModuleCat.{0} ℤ) :=
  ShortComplex.mk (𝟙 (0 : DGModuleCat.{0} ℤ)) (𝟙 (0 : DGModuleCat.{0} ℤ)) (by
    exact (isZero_zero _).eq_of_src _ _)

private theorem zeroDGSequence_shortExact : zeroDGSequence.ShortExact := by
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_isZero_X₂ zeroDGSequence (isZero_zero (DGModuleCat.{0} ℤ))) ?_ ?_
  · change Mono (𝟙 (0 : DGModuleCat.{0} ℤ))
    infer_instance
  · change Epi (𝟙 (0 : DGModuleCat.{0} ℤ))
    infer_instance

example : ∃ δ : DG.DerivedCategory.Q.obj zeroDGSequence.X₃ ⟶
    (DG.DerivedCategory.Q.obj zeroDGSequence.X₁)⟦(1 : ℤ)⟧,
    Triangle.mk (DG.DerivedCategory.Q.map zeroDGSequence.f)
      (DG.DerivedCategory.Q.map zeroDGSequence.g) δ ∈ distTriang (DG.DerivedCategory ℤ) :=
  DG.DerivedCategory.exists_distinguished_of_shortExact zeroDGSequence zeroDGSequence_shortExact

example : IsZero ((DG.DerivedCategory.homologyFunctor ℤ 1).obj
    (DG.DerivedCategory.Q.obj zeroDGSequence.X₃)) := by
  apply DG.DerivedCategory.isZero_homology_obj_of_shortExact ℤ
    (𝟭 (DG.DerivedCategory ℤ)) zeroDGSequence zeroDGSequence_shortExact
  · intro n _
    exact Functor.map_isZero _ (DG.DerivedCategory.Q.map_isZero (isZero_zero (DGModuleCat.{0} ℤ)))
  · intro n _
    exact Functor.map_isZero _ (DG.DerivedCategory.Q.map_isZero (isZero_zero (DGModuleCat.{0} ℤ)))
  · change Mono ((DG.DerivedCategory.homologyFunctor ℤ 0).map
      (DG.DerivedCategory.Q.map (𝟙 (0 : DGModuleCat.{0} ℤ))))
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    infer_instance
  · decide

/-! ### A split extension in the proof of Webster Lemma 6.8 -/

private def splitDGSequence : ShortComplex (DGModuleCat.{0} ℤ) :=
  ShortComplex.mk (DGModuleCat.ofHom (DGModuleHom.inl ℤ ℤ))
    (DGModuleCat.ofHom (DGModuleHom.snd ℤ ℤ)) (by ext; rfl)

private theorem splitDGSequence_shortExact : splitDGSequence.ShortExact :=
  (DGModuleCat.shortExact_iff _).2 ⟨
    fun _ _ h => congrArg Prod.fst h,
    fun ⟨x, _⟩ => ⟨fun hy => ⟨x, Prod.ext rfl hy.symm⟩,
      fun ⟨_, h⟩ => (congrArg Prod.snd h).symm⟩,
    fun y => ⟨(0, y), rfl⟩⟩

private theorem H1_Z : IsZero ((DG.DerivedCategory.homologyFunctor ℤ 1).obj
    (DG.DerivedCategory.Q.obj (DGModuleCat.of ℤ ℤ))) := by
  let : Subsingleton (cocycles ℤ 1) := ⟨fun x y => by
    apply Subtype.ext
    have hx := DegreeZero.mem_grading_iff.mp (mem_cocycles.mp x.2).1
    have hy := DegreeZero.mem_grading_iff.mp (mem_cocycles.mp y.2).1
    exact (hx.resolve_left (by decide)).trans (hy.resolve_left (by decide)).symm⟩
  let := (cohomology.mk_surjective ℤ 1).subsingleton
  exact ModuleCat.isZero_iff_subsingleton.mpr
    ((DG.DerivedCategory.cohomologyAddEquiv ℤ (DGModuleCat.of ℤ ℤ) 1).surjective.subsingleton)

example : IsZero ((DG.DerivedCategory.homologyFunctor ℤ 1).obj
    (DG.DerivedCategory.Q.obj (DGModuleCat.of ℤ (ℤ × ℤ)))) :=
  DG.DerivedCategory.isZero_homology_middle_of_shortExact ℤ
    (𝟭 (DG.DerivedCategory ℤ)) splitDGSequence splitDGSequence_shortExact 1 H1_Z H1_Z

/-! ### Exactness of ordinary bimodule tensor for Webster Lemma 6.8 -/

section OrdinaryBimoduleTensor

local instance : Fact (∀ x : ℤ, x ∈ grading 0) :=
  ⟨fun _ => DegreeZero.mem_grading_iff.mpr (Or.inl rfl)⟩

example : (DG.HomotopyCategory.tensorFunctor ℤ ℤ (B := ℤ)).IsTriangulated := by
  infer_instance

end OrdinaryBimoduleTensor

/-! ### Degree-zero tensor cohomology in Webster Lemma 6.8 -/

section OrdinaryTensorHomology

local instance : Fact (∀ x : ℤ, x ∈ grading 0) :=
  ⟨fun _ => DegreeZero.mem_grading_iff.mpr (Or.inl rfl)⟩

example : Function.Exact
    (DG.TensorProductOver.map (LinearMap.id : ℤ →ₗ[ℤᵐᵒᵖ] ℤ) (0 : ℤ →ₗ[ℤ] ℤ))
    (DG.TensorProductOver.map (LinearMap.id : ℤ →ₗ[ℤᵐᵒᵖ] ℤ) (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) := by
  apply DG.TensorProductOver.exact_map_id_of_surjective
  · intro x
    simp [eq_comm]
  · exact Function.surjective_id

example : Function.Bijective (cohomology.map
    (DGModuleHom.lTensor ℤ ℤ (DGModuleHom.id : ℤ →ᵈᵍ[ℤ] ℤ)) 0) := by
  apply DG.tensor_aug_bijective_H0
  · rw [cohomology.map_id]
    exact Function.bijective_id
  · intro x hx
    exact (DegreeZero.mem_grading_iff.mp hx).resolve_left one_ne_zero

example : (DGModuleCat.of ℤ ℤ) ≃+
    (DG.DerivedCategory.homologyFunctor ℤ 0).obj
      (DG.DerivedCategory.Q.obj (DGModuleCat.of ℤ ℤ)) :=
  DG.DerivedCategory.degreeZeroHomologyQEquiv _
    (fun _ => DegreeZero.mem_grading_iff.mpr (Or.inl rfl)) (fun _ => rfl)

end OrdinaryTensorHomology

end NonVacuity


namespace NonVacuity.CoendCoproduct

private abbrev C := SingleObj ℤ
private abbrev X : C := SingleObj.star ℤ
private abbrev R := CatModule.representable (DGOpposite.op X)
private abbrev N := CatModule.cone (𝟙 R)
private abbrev F (_ : Bool) := CatModule.representable X

private theorem acyclicCoefficient : CatModule.IsAcyclic N :=
  (CatModule.isQuasiIso_iff_isAcyclic_cone (𝟙 R)).mp (CatModule.isQuasiIso_id R)

example : IsAcyclic (CatTensorProduct N (CatModule.directSum F)) :=
  CatTensorProduct.isAcyclic_directSum N F
    (fun _ => CatTensorProduct.isAcyclic_rid acyclicCoefficient X)

private def two : X ⟶ X := by
  change ℤ
  exact 2

example : (DGOpposite.doubleUnopFunctor C).map
    (DGOpposite.homOp (DGOpposite.homOp two)) = two := rfl

end NonVacuity.CoendCoproduct


namespace NonVacuity.CoendSymmetry

open DGOpposite

private abbrev C := SingleObj ℤ
private abbrev X : C := SingleObj.star ℤ
private abbrev N := CatModule.shift (-1) (CatModule.representable (op X))
private abbrev M := CatModule.shift (-1) (CatModule.representable X)

private theorem mapsDegreeZero {Y Z : C} (f : Y ⟶ Z) :
    f ∈ grading (0 : ℤ) := mem_degreeZeroGrading_zero ℤ (f : ℤ)

private def x : N.obj (op X) := Shift.mk (-1) (𝟙 (op X))
private def y : M.obj X := Shift.mk (-1) (𝟙 X)

private theorem hx : x ∈ grading (1 : ℤ) := by
  change Shift.mk (-1) (𝟙 (op X)) ∈ grading (M := Shift (-1) ((op X) ⟶ (op X))) (1 : ℤ)
  simpa only [zero_sub, neg_neg] using Shift.mk_mem_grading (n := -1)
    (id_mem_grading (op X))

private theorem hy : y ∈ grading (1 : ℤ) := by
  change Shift.mk (-1) (𝟙 (X)) ∈ grading (M := Shift (-1) ((X) ⟶ (X))) (1 : ℤ)
  simpa only [zero_sub, neg_neg] using Shift.mk_mem_grading (n := -1)
    (id_mem_grading X)

example : CatTensorProduct.transposeHom N M mapsDegreeZero
    (CatTensorProduct.tmul X x y) = -CatTensorProduct.tmul (op X) y x := by
  rw [CatTensorProduct.transposeHom_tmul_of_mem N M mapsDegreeZero X hx hy]
  simp only [one_mul, koszulSign, Int.negOnePow_one, Units.neg_smul, one_smul]

end NonVacuity.CoendSymmetry
