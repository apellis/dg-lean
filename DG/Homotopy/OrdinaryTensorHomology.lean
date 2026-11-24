import DG.Module.TensorProductOverExact
import DG.Homotopy.KProjective
import DG.Homotopy.BimoduleTensor
import DG.Homotopy.Comparison

/-!
# Degree-zero cohomology of ordinary bimodule tensor

An ordinary bimodule preserves the degree-zero comparison of a nonpositive DG model
with a degree-zero module. This is the cohomology comparison needed in Webster,
[arXiv:1309.3796v2](https://arxiv.org/abs/1309.3796v2), Lemma 6.8, proof of (6.21).
-/

open DirectSum
open scoped DG.DegreeZero

namespace DG

noncomputable section

variable {B M N : Type*} [Ring B] [AddCommGroup M] [DGAddCommGroup M] [Module Bᵐᵒᵖ M]
  [Fact (∀ m : M, m ∈ grading 0)]
  [AddCommGroup N] [DGAddCommGroup N] [Module B N] [DGModule B N]

/-- The homogeneous submodule of a dg module over an ordinary ring. -/
def ordinaryGrade (n : ℤ) : Submodule B N where
  __ := grading (M := N) n
  smul_mem' b x hx := by
    have hb : b ∈ grading 0 := DG.DegreeZero.mem_grading_iff.mpr (Or.inl rfl)
    simpa using smul_mem_grading hb hx

instance ordinaryGrade_decomposition : Decomposition (ordinaryGrade (B := B) (N := N)) where
  decompose' := decompose (grading (M := N))
  left_inv := Decomposition.left_inv (ℳ := grading (M := N))
  right_inv := Decomposition.right_inv (ℳ := grading (M := N))

private def gradeProjection (n : ℤ) : N →ₗ[B] ordinaryGrade (B := B) (N := N) n :=
  (DirectSum.component B ℤ (fun i => ↥(ordinaryGrade (B := B) (N := N) i)) n).comp
    (decomposeLinearEquiv (ordinaryGrade (B := B) (N := N))).toLinearMap

private theorem gradeProjection_apply (n : ℤ) (x : N) :
    (gradeProjection (B := B) n x : N) = decompose (grading (M := N)) x n := rfl

private theorem mem_degreeZero {X : Type*} [AddCommGroup X] [DGAddCommGroup X]
    [Fact (∀ x : X, x ∈ grading 0)] (x : X) : x ∈ grading 0 :=
  (Fact.out : ∀ x : X, x ∈ grading 0) x

private theorem eq_zero_of_mem_ne {X : Type*} [AddCommGroup X] [DGAddCommGroup X]
    [Fact (∀ x : X, x ∈ grading 0)] {n : ℤ} {x : X} (hx : x ∈ grading n) (hn : n ≠ 0) :
    x = 0 := by
  have h := decompose_of_mem_ne (grading (M := X)) hx hn
  rw [decompose_of_mem_same _ (mem_degreeZero x)] at h
  exact h

private theorem d_eq_zero_of_degreeZero {X : Type*} [AddCommGroup X] [DGAddCommGroup X]
    [Fact (∀ x : X, x ∈ grading 0)] (x : X) : d x = 0 :=
  eq_zero_of_mem_ne (d_mem (mem_degreeZero x)) one_ne_zero

open TensorProductOver

private def tensorGradeInclusion (n : ℤ) :
    TensorProductOver B M (ordinaryGrade (B := B) (N := N) n) →+
      TensorProductOver B M N :=
  map LinearMap.id (ordinaryGrade n).subtype

section HomogeneousTensor

variable [DGRightModule B M]

/-- The tensor product's degree-`n` piece is the tensor of the degree-`n` input piece. -/
def tensorGradeAddEquiv (n : ℤ) :
    TensorProductOver B M (ordinaryGrade (B := B) (N := N) n) ≃+
      grading (M := TensorProductOver B M N) n := by
  let g := tensorGradeInclusion (B := B) (M := M) (N := N) n
  let p := map (LinearMap.id : M →ₗ[Bᵐᵒᵖ] M)
    (gradeProjection (B := B) (N := N) n)
  let G := g.codRestrict (grading (M := TensorProductOver B M N) n) (by
    intro y
    induction y using TensorProductOver.induction_on with
    | zero => exact zero_mem _
    | tmul m x =>
      change tmul B m (x : N) ∈ grading n
      have hm : m ∈ grading 0 := mem_degreeZero _
      simpa using TensorProductOver.tmul_mem_grading hm x.2
    | add x y hx hy => rw [map_add]; exact add_mem hx hy)
  refine AddEquiv.ofBijective G ⟨?_, ?_⟩
  · have h : p.comp g = AddMonoidHom.id _ := by
      apply TensorProductOver.addHom_ext
      intro m x
      change tmul B m (gradeProjection n (x : N)) = tmul B m x
      congr 1
      apply Subtype.ext
      have hx : (x : N) ∈ grading n := x.2
      rw [gradeProjection_apply, decompose_of_mem_same (grading (M := N)) hx]
    intro x y hxy
    have hxy' : g x = g y := congrArg Subtype.val hxy
    exact (DFunLike.congr_fun h x).symm.trans
      ((congrArg p hxy').trans (DFunLike.congr_fun h y))
  · intro y
    refine ⟨p y.1, Subtype.ext ?_⟩
    change g (p y.1) = y.1
    refine induction_on_mem_grading (P := fun y => g (p y) = y) (by simp) ?_ ?_ ?_ y.2
    · intro i j m x hm hx hij
      by_cases hi : i = 0
      · subst i
        simp only [zero_add] at hij
        subst j
        change tmul B m (gradeProjection (B := B) n x : N) = tmul B m x
        rw [gradeProjection_apply, decompose_of_mem_same _ hx]
      · rw [eq_zero_of_mem_ne hm hi, zero_tmul, map_zero, map_zero]
    · intro x y hx hy
      rw [map_add, map_add, hx, hy]
    · intro x hx
      rw [map_neg, map_neg, hx]


@[simp]
theorem tensorGradeAddEquiv_tmul (n : ℤ) (m : M)
    (x : ordinaryGrade (B := B) (N := N) n) :
    (tensorGradeAddEquiv n (tmul B m x) : TensorProductOver B M N) = tmul B m (x : N) := rfl

end HomogeneousTensor

private def ordinaryGradeDM1 : ordinaryGrade (B := B) (N := N) (-1) →ₗ[B]
    ordinaryGrade (B := B) (N := N) 0 where
  toFun x := ⟨d (x : N), by
    have hx : (x : N) ∈ grading (-1 : ℤ) := x.2
    change d (x : N) ∈ grading (0 : ℤ)
    simpa using d_mem hx⟩
  map_add' x y := Subtype.ext (d_add (x : N) (y : N))
  map_smul' b x := Subtype.ext (by
    change d (b • (x : N)) = b • d (x : N)
    have hb : b ∈ grading 0 := DG.DegreeZero.mem_grading_iff.mpr (Or.inl rfl)
    rw [d_smul_of_mem_zero hb, DG.DegreeZero.d_apply, zero_smul, zero_add])

variable {A P : Type*} [Ring A] [Module A M] [DGBimodule A B M]
  [AddCommGroup P] [DGAddCommGroup P] [Module B P] [DGModule B P]
  [Fact (∀ p : P, p ∈ grading 0)]

private theorem d_tmul_of_degreeZero (m : M) (x : N) :
    d (tmul B m x) = tmul B m (d x) := by
  rw [TensorProductOver.d_tmul_of_mem (mem_degreeZero m), d_eq_zero_of_degreeZero m,
    zero_tmul, zero_add, koszulSign_zero, one_smul]

private theorem d_tmul_tensor_degreeZero (y : TensorProductOver B M P) : d y = 0 := by
  induction y using TensorProductOver.induction_on with
  | zero => exact d_zero
  | tmul m p =>
    rw [TensorProductOver.d_tmul_of_mem (mem_degreeZero m), d_eq_zero_of_degreeZero m,
      d_eq_zero_of_degreeZero p, zero_tmul, tmul_zero, smul_zero, add_zero]
  | add x y hx hy => rw [d_add, hx, hy, add_zero]

omit [DGModule B P] in
private theorem exact_aug (q : N →ᵈᵍ[B] P)
    (hq : Function.Bijective (cohomology.map q 0))
    (hN : ∀ x : N, x ∈ grading (1 : ℤ) → x = 0) :
    Function.Exact (ordinaryGradeDM1 (B := B) (N := N))
      (q.toLinearMap.comp (ordinaryGrade 0).subtype) := by
  intro x
  change q (x : N) = 0 ↔ _
  constructor
  · intro hx
    have hc : d (x : N) = 0 := hN _ (d_mem (show (x : N) ∈ grading 0 from x.2))
    have hb : q (x : N) ∈ coboundaries P 0 := hx ▸ zero_mem _
    obtain ⟨z, hz, hdz⟩ := mem_coboundaries.mp
      ((cohomology.map_injective_iff q 0).mp hq.1 _ x.2 hc hb)
    exact ⟨⟨z, hz⟩, Subtype.ext hdz⟩
  · rintro ⟨z, rfl⟩
    change q (d (z : N)) = 0
    rw [q.map_d, d_eq_zero_of_degreeZero]

omit [DGModule B P] in
private theorem surjective_aug (q : N →ᵈᵍ[B] P)
    (hq : Function.Bijective (cohomology.map q 0)) :
    Function.Surjective (q.toLinearMap.comp (ordinaryGrade 0).subtype) := by
  intro y
  have hy : y ∈ grading 0 := mem_degreeZero _
  obtain ⟨x, hx, _, hb⟩ :=
    (cohomology.map_surjective_iff q 0).mp hq.2 y hy (d_eq_zero_of_degreeZero y)
  obtain ⟨z, _, hz⟩ := mem_coboundaries.mp hb
  rw [d_eq_zero_of_degreeZero] at hz
  exact ⟨⟨x, hx⟩, sub_eq_zero.mp hz.symm⟩

/-- Tensoring with an ordinary bimodule preserves the degree-zero cohomology of a
map from a model with zero degree-one component to a degree-zero module. -/
theorem tensor_aug_bijective_H0 (q : N →ᵈᵍ[B] P)
    (hq : Function.Bijective (cohomology.map q 0))
    (hN : ∀ x : N, x ∈ grading (1 : ℤ) → x = 0) :
    Function.Bijective (cohomology.map (DGModuleHom.lTensor A M q) 0) := by
  let R := DGModuleHom.lTensor A M q
  let g := q.toLinearMap.comp (ordinaryGrade 0).subtype
  let G := map (LinearMap.id : M →ₗ[Bᵐᵒᵖ] M) g
  let L := map (LinearMap.id : M →ₗ[Bᵐᵒᵖ] M)
    (ordinaryGradeDM1 (B := B) (N := N))
  let J (n : ℤ) := tensorGradeInclusion (B := B) (M := M) (N := N) n
  have hRG : R.toLinearMap.toAddMonoidHom.comp (J 0) = G := by
    apply TensorProductOver.addHom_ext
    intro m n
    rfl
  have hJL : (J 0).comp L = (d : TensorProductOver B M N →+ _).comp (J (-1)) := by
    apply TensorProductOver.addHom_ext
    intro m n
    change tmul B m (d (n : N)) = d (tmul B m (n : N))
    rw [d_tmul_of_degreeZero (A := A)]
  have dJ0 (x : TensorProductOver B M (ordinaryGrade (B := B) (N := N) 0)) :
      d (J 0 x) = 0 := by
    induction x using TensorProductOver.induction_on with
    | zero => simp
    | tmul m n =>
      change d (tmul B m (n : N)) = 0
      rw [d_tmul_of_degreeZero (A := A), hN _ (d_mem (show (n : N) ∈ grading 0 from n.2)),
        tmul_zero]
    | add x y hx hy => rw [map_add, d_add, hx, hy, add_zero]
  constructor
  · rw [cohomology.map_injective_iff]
    intro x hx _ hRx
    obtain ⟨z, _, hz⟩ := mem_coboundaries.mp hRx
    have h0 : R x = 0 := hz.symm.trans (d_tmul_tensor_degreeZero (A := A) z)
    obtain ⟨u, hu⟩ := (tensorGradeAddEquiv (B := B) (M := M) (N := N) 0).surjective ⟨x, hx⟩
    have hu' : J 0 u = x := congrArg Subtype.val hu
    have hGu : G u = 0 := by
      rw [← DFunLike.congr_fun hRG u]
      exact (congrArg R hu').trans h0
    obtain ⟨v, hv⟩ := (DG.TensorProductOver.exact_map_id_of_surjective (M := M)
      (ordinaryGradeDM1 (B := B) (N := N)) g (exact_aug q hq hN) (surjective_aug q hq) u).mp hGu
    apply mem_coboundaries.mpr
    refine ⟨J (-1) v, (tensorGradeAddEquiv (B := B) (M := M) (N := N) (-1) v).2, ?_⟩
    exact (DFunLike.congr_fun hJL v).symm.trans
      ((congrArg (J 0) hv).trans hu')
  · rw [cohomology.map_surjective_iff]
    intro y _ _
    have hg : Function.Surjective G := by
      intro y
      induction y using TensorProductOver.induction_on with
      | zero => exact ⟨0, map_zero _⟩
      | tmul m p =>
        obtain ⟨n, hn⟩ := surjective_aug q hq p
        exact ⟨tmul B m n, by change tmul B m (g n) = _; rw [hn]⟩
      | add y z hy hz =>
        obtain ⟨u, rfl⟩ := hy
        obtain ⟨v, rfl⟩ := hz
        exact ⟨u + v, map_add _ _ _⟩
    obtain ⟨x, hx⟩ := hg y
    refine ⟨J 0 x, (tensorGradeAddEquiv (B := B) (M := M) (N := N) 0 x).2, dJ0 x, ?_⟩
    have hRy : R (J 0 x) = y := (DFunLike.congr_fun hRG x).trans hx
    rw [hRy, sub_self]
    exact zero_mem _

end

end DG
