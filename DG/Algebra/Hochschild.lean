import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.Quotient.Basic
import DG.Graded.Basic
import DG.Graded.Commutative
import DG.Module.Right

/-!
# The Hochschild cochain complex of a graded algebra

Let `A` be a dg `R`-algebra and `M` a dg `A`-bimodule (`DG.DGBimodule A A M`) whose `R`-module
structure is compatible with both actions. This file constructs the Hochschild cochain complex of
the underlying graded algebra of `A` with coefficients in the underlying graded bimodule of `M`,
with the Koszul sign rule. When `A` and `M` have zero differential (the case `d = 0` of the
roadmap) this is the Hochschild cochain complex of `A` with coefficients in `M`; for a general dg
algebra the Hochschild complex is the product total complex of this bicomplex with the internal
differentials, which is not formalized here.

## Main definitions and results

* `DG.HochschildCochain R A M n`: the `R`-multilinear maps `f : Aⁿ → M`; the cochains of internal
  degree `k` form the submodule `DG.hochschildCochains R A M k n` of the `f` with
  `f (a₁, …, aₙ) ∈ M^(k + |a₁| + ⋯ + |aₙ|)` for homogeneous `aᵢ`.
* `DG.DGAlgebra.twist R A k`: the sign twist `a ↦ (-1)^(|a| k) • a`, an `R`-linear ring
  endomorphism of `A` (`DG.DGAlgebra.twist_mul`).
* `DG.hochschildDiff k f` (and the `R`-linear map `DG.hochschildD k n`): the Hochschild
  differential for internal degree `k`,
  `(δ f)(a₀, …, aₙ) = (-1)^(|a₀| k) a₀ • f (a₁, …, aₙ)
    + ∑ᵢ (-1)^(i + 1) f (a₀, …, aᵢ aᵢ₊₁, …, aₙ) + (-1)^(n + 1) f (a₀, …, aₙ₋₁) • aₙ`
  (`DG.hochschildDiff_apply`); it preserves the internal degree (`DG.hochschildD_mem`) and
  squares to zero (`DG.hochschildDiff_hochschildDiff`).
* `DG.hochschildComplex R A M k`: the Hochschild complex of internal degree `k` as a
  `CochainComplex (ModuleCat R) ℕ`.
* `DG.hochschildCocycles`, `DG.hochschildCoboundaries`, `DG.HochschildCohomology R A M k n`: the
  Hochschild cohomology `HHⁿ(A, M)ᵏ`.
* `DG.gradedCenter R A M k`: the `m ∈ Mᵏ` with `m • a = (-1)^(|a| k) • (a • m)` for homogeneous
  `a`; for `M = A` the degree-`k` graded center of `A` (`DG.mem_gradedCenter_self_iff`).
* `DG.hochschildCohomologyZeroEquiv`: `HH⁰(A, M)ᵏ ≃ₗ[R] Z(A, M)ᵏ`; for `M = A`, `HH⁰(A, A)` is the
  graded center `Z(A)`, degree by degree.
* `DG.HochschildTotal R A M`: the total Hochschild complex `⨁_N ∏ₙ Cⁿ(A, M)^(N - n)` (graded by
  total degree `N`), a dg abelian group (`DG.HochschildTotal.instDGAddCommGroup`) with `R`-linear
  differential (`DG.HochschildTotal.d_smul`).

## Proof of `δ² = 0`

We extend a cochain `f` to the function
`(a₀, …, aₙ₊₁) ↦ (-1)^(|a₀| k) a₀ • f (a₁, …, aₙ) • aₙ₊₁` (`DG.Hochschild.extend`); this turns `δ`
into the alternating sum of the merges of adjacent entries, `DG.Hochschild.barD`
(`DG.Hochschild.extend_hochschildDiff`), which squares to zero by the simplicial identities for
merges (`DG.Hochschild.merge_merge`, `DG.Hochschild.barD_barD`). A cochain is recovered from its
extension by evaluating at `(1, a₁, …, aₙ, 1)`.

## Conventions

The sign `(-1)^(|a₀| k)` in the first term is the Koszul sign of moving the cochain, of internal
degree `k`, past `a₀`; all signs are `koszulSign n = Int.negOnePow n : ℤˣ`. The right action is
written `op a • m` (`Module Aᵐᵒᵖ M`), as in `DG.Module.Right`.
-/

namespace DG.Hochschild

/-! ### Merging adjacent entries of tuples -/

variable {A : Type*} [Ring A]

/-- Multiply the adjacent entries `i` and `i + 1` of a tuple. -/
def merge {n : ℕ} (i : Fin n) (a : Fin (n + 1) → A) : Fin n → A :=
  Fin.contractNth i.castSucc (· * ·) a

theorem merge_apply {n : ℕ} (i : Fin n) (a : Fin (n + 1) → A) (k : Fin n) :
    merge i a k = if (k : ℕ) < i then a k.castSucc
      else if (k : ℕ) = i then a k.castSucc * a k.succ else a k.succ := rfl

theorem merge_update_of_lt {n : ℕ} (i : Fin n) (a : Fin (n + 1) → A) (p : Fin (n + 1)) (x : A)
    (h : (p : ℕ) < i) :
    merge i (Function.update a p x) = Function.update (merge i a) ⟨p, by omega⟩ x := by
  ext k
  simp only [merge_apply, Function.update_apply, Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ]
  split_ifs <;> first | rfl | omega

theorem merge_update_of_gt {n : ℕ} (i : Fin n) (a : Fin (n + 1) → A) (p : Fin (n + 1)) (x : A)
    (h : (i : ℕ) + 1 < p) :
    merge i (Function.update a p x) = Function.update (merge i a) ⟨p - 1, by omega⟩ x := by
  ext k
  simp only [merge_apply, Function.update_apply, Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ]
  split_ifs <;> first | rfl | omega

theorem merge_update_castSucc {n : ℕ} (i : Fin n) (a : Fin (n + 1) → A) (x : A) :
    merge i (Function.update a i.castSucc x) =
      Function.update (merge i a) i (x * a i.succ) := by
  ext k
  simp only [merge_apply, Function.update_apply, Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ]
  split_ifs <;> first | rfl | omega | (obtain rfl : k = i := Fin.ext (by omega); rfl)

theorem merge_update_succ {n : ℕ} (i : Fin n) (a : Fin (n + 1) → A) (x : A) :
    merge i (Function.update a i.succ x) =
      Function.update (merge i a) i (a i.castSucc * x) := by
  ext k
  simp only [merge_apply, Function.update_apply, Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ]
  split_ifs <;> first | rfl | omega | (obtain rfl : k = i := Fin.ext (by omega); rfl)

/-- The simplicial identity for merges: for `i < j`, merging at `j` and then at `i` is the same
as merging at `i` and then at `j - 1`. For `j = i + 1` this is associativity. -/
theorem merge_merge {m : ℕ} (a : Fin (m + 3) → A) (i : Fin (m + 1)) (j : Fin (m + 2))
    (h : (i : ℕ) < j) :
    merge i (merge j a) = merge ⟨j - 1, by omega⟩ (merge i.castSucc a) := by
  ext k
  simp only [merge_apply, Fin.coe_castSucc, Fin.val_succ]
  split_ifs <;> first | rfl | omega | (rw [mul_assoc]; rfl)

/-! Merges and the outer entries of a tuple. -/

section Outer

variable {n : ℕ} (a : Fin (n + 3) → A)

theorem merge_zero_apply_zero : merge 0 a 0 = a 0 * a 1 := rfl

theorem merge_zero_apply_last : merge 0 a (Fin.last (n + 1)) = a (Fin.last (n + 2)) := by
  rw [merge_apply, if_neg (by simp), if_neg (by simp)]; rfl

theorem init_tail_merge_zero :
    Fin.init (Fin.tail (merge 0 a)) = Fin.tail (Fin.init (Fin.tail a)) := by
  ext k
  simp only [Fin.init, Fin.tail, merge_apply]
  rw [if_neg (by simp), if_neg (by simp)]; rfl

theorem merge_succ_apply_zero (i : Fin n) : merge i.castSucc.succ a 0 = a 0 := by
  rw [merge_apply, if_pos (by simp)]; rfl

theorem merge_succ_apply_last (i : Fin n) :
    merge i.castSucc.succ a (Fin.last (n + 1)) = a (Fin.last (n + 2)) := by
  rw [merge_apply, if_neg (by simp), if_neg (by simp; omega)]; rfl

theorem init_tail_merge_succ (i : Fin n) :
    Fin.init (Fin.tail (merge i.castSucc.succ a)) = merge i (Fin.init (Fin.tail a)) := by
  ext k
  simp only [Fin.init, Fin.tail, merge_apply, Fin.val_succ, Fin.coe_castSucc]
  split_ifs <;> first | rfl | omega

theorem merge_last_apply_zero : merge (Fin.last n).succ a 0 = a 0 := by
  rw [merge_apply, if_pos (by simp)]; rfl

theorem merge_last_apply_last :
    merge (Fin.last n).succ a (Fin.last (n + 1)) =
      a (Fin.last (n + 1)).castSucc * a (Fin.last (n + 2)) := by
  rw [merge_apply, if_neg (by simp), if_pos (by simp)]; rfl

theorem init_tail_merge_last :
    Fin.init (Fin.tail (merge (Fin.last n).succ a)) = Fin.init (Fin.init (Fin.tail a)) := by
  ext k
  simp only [Fin.init, Fin.tail, merge_apply, Fin.val_succ, Fin.coe_castSucc, Fin.val_last]
  rw [if_pos (by omega)]; rfl

end Outer

/-! Degrees of merged tuples. -/

/-- Merging adjacent entries of a tuple of integers by addition does not change the sum. -/
theorem sum_contractNth_add {n : ℕ} (i : Fin n) (p : Fin (n + 1) → ℤ) :
    ∑ k, Fin.contractNth i.castSucc (· + ·) p k = ∑ k, p k := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ (f := p)]
    cases i using Fin.cases with
    | zero =>
      rw [Fin.sum_univ_succ (f := fun k => p k.succ)]
      simp only [Fin.contractNth, Fin.castSucc_zero, Fin.val_zero, Fin.val_succ,
        lt_self_iff_false, if_false, if_true, Nat.not_lt_zero, add_assoc, Nat.add_one_ne_zero]
    | succ i =>
      have h0 : Fin.contractNth i.succ.castSucc (· + ·) p 0 = p 0 := by
        rw [Fin.contractNth, if_pos (by simp)]; rfl
      rw [h0, ← ih i (fun k => p k.succ)]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Fin.contractNth, Fin.val_succ, Fin.coe_castSucc]
      split_ifs <;> first | rfl | omega

variable {M : Type*} [AddCommGroup M]

/-- The alternating sum of merges, `(∂ g)(a₀, …, aₘ₊₁) = ∑ⱼ (-1)^j g(a₀, …, aⱼ aⱼ₊₁, …, aₘ₊₁)`,
on arbitrary functions of tuples. -/
def barD {m : ℕ} (g : (Fin (m + 1) → A) → M) : (Fin (m + 2) → A) → M :=
  fun a => ∑ j : Fin (m + 1), koszulSign ((j : ℕ) : ℤ) • g (merge j a)

theorem barD_barD {m : ℕ} (g : (Fin (m + 1) → A) → M) : barD (barD g) = 0 := by
  ext a
  simp only [barD, Finset.smul_sum, smul_smul, Pi.zero_apply]
  rw [← Finset.sum_product']
  let S : Finset (Fin (m + 2) × Fin (m + 1)) := Finset.univ.filter fun p => (p.2 : ℕ) < p.1
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_nbij' (fun p => (p.2.castSucc, ⟨p.1 - 1, by omega⟩))
    (fun p => (⟨p.2 + 1, by omega⟩, ⟨min p.1 m, by omega⟩)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨j, i⟩ h
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl] at h ⊢
    simp only [Fin.coe_castSucc]
    omega
  · rintro ⟨j, i⟩ h
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl] at h ⊢
    simp only [Finset.mem_coe, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
      not_lt] at h
    omega
  · rintro ⟨j, i⟩ h
    simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at h
    simp only [Fin.coe_castSucc, Prod.mk.injEq, Fin.ext_iff]
    omega
  · rintro ⟨j, i⟩ h
    simp only [S, Finset.mem_coe, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
      not_lt] at h
    simp only [Fin.coe_castSucc, Prod.mk.injEq, Fin.ext_iff]
    omega
  · rintro ⟨j, i⟩ h
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at h
    simp only [Fin.coe_castSucc]
    rw [merge_merge a i j h, ← Units.neg_smul]
    congr 1
    have hj : ((j : ℕ) : ℤ) = ((j - 1 : ℕ) : ℤ) + 1 := by omega
    rw [hj, koszulSign_add, koszulSign_odd odd_one]
    simp only [mul_neg, mul_one, neg_mul, neg_inj]
    exact mul_comm _ _

end DG.Hochschild

noncomputable section

namespace DG

open DirectSum MulOpposite

/-! ### The sign twist -/

section Twist

variable (R A : Type*) [CommRing R] [Ring A] [Algebra R A] [DGAddCommGroup A] [DGRing A]
  [DGAlgebra R A]

/-- The sign twist by `k : ℤ`, the `R`-linear map `a ↦ (-1)^(|a| k) • a` on homogeneous
elements. It is the Koszul sign of moving a symbol of degree `k` past `a`. -/
def DGAlgebra.twist (k : ℤ) : A →ₗ[R] A :=
  DirectSum.toModule R ℤ A
      (fun i => (koszulSign (i * k) : ℤ) • (DGAlgebra.gradingSubmodule R A i).subtype) ∘ₗ
    (decomposeLinearEquiv (DGAlgebra.gradingSubmodule R A)).toLinearMap

variable {R A}

theorem DGAlgebra.twist_of_mem (k : ℤ) {i : ℤ} {a : A} (ha : a ∈ grading i) :
    DGAlgebra.twist R A k a = koszulSign (i * k) • a := by
  rw [DGAlgebra.twist, LinearMap.comp_apply, LinearEquiv.coe_coe, decomposeLinearEquiv_apply,
    decompose_of_mem (DGAlgebra.gradingSubmodule R A) (i := i) ha, ← lof_eq_of R,
    toModule_lof, LinearMap.smul_apply, Submodule.subtype_apply, Units.smul_def]

@[simp]
theorem DGAlgebra.twist_one (k : ℤ) : DGAlgebra.twist R A k 1 = 1 := by
  rw [DGAlgebra.twist_of_mem k one_mem_grading, zero_mul, koszulSign_zero, one_smul]

theorem DGAlgebra.twist_mul (k : ℤ) (a b : A) :
    DGAlgebra.twist R A k (a * b) = DGAlgebra.twist R A k a * DGAlgebra.twist R A k b := by
  refine map_mul_of_homogeneous (DGAlgebra.gradingSubmodule R A) (DGAlgebra.twist R A k)
    (fun {i j} a b => ?_) a b
  rw [DGAlgebra.twist_of_mem k (mul_mem_grading a.2 b.2), DGAlgebra.twist_of_mem k a.2,
    DGAlgebra.twist_of_mem k b.2, add_mul, koszulSign_add, mul_smul]
  simp only [Units.smul_def, smul_mul_assoc, mul_smul_comm]
  exact smul_comm _ _ _

theorem DGAlgebra.twist_mem (k : ℤ) {i : ℤ} {a : A} (ha : a ∈ grading i) :
    DGAlgebra.twist R A k a ∈ grading i := by
  rw [DGAlgebra.twist_of_mem k ha, Units.smul_def]
  exact zsmul_mem ha _

end Twist

/-! ### Hochschild cochains and the Hochschild differential -/

section Differential

variable (R A M : Type*) [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- The Hochschild `n`-cochains `Cⁿ(A, M)`: the `R`-multilinear maps `Aⁿ → M`. -/
abbrev HochschildCochain (n : ℕ) : Type _ := MultilinearMap R (fun _ : Fin n => A) M

namespace Hochschild

variable {R A M}

/-- The multilinear map `(a₀, …, aₙ) ↦ f (a₀, …, aᵢ aᵢ₊₁, …, aₙ)`. -/
def compMerge {n : ℕ} (f : HochschildCochain R A M n) (i : Fin n) :
    HochschildCochain R A M (n + 1) :=
  MultilinearMap.mk' (fun a => f (merge i a))
    (fun a p x y => by
      rcases lt_trichotomy (p : ℕ) i with h | h | h
      · simp only [merge_update_of_lt i a p _ h, f.map_update_add]
      · obtain rfl : p = i.castSucc := Fin.ext h
        simp only [merge_update_castSucc, add_mul, f.map_update_add]
      · rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with h' | h'
        · obtain rfl : p = i.succ := Fin.ext h'.symm
          simp only [merge_update_succ, mul_add, f.map_update_add]
        · simp only [merge_update_of_gt i a p _ h', f.map_update_add])
    (fun a p c x => by
      rcases lt_trichotomy (p : ℕ) i with h | h | h
      · simp only [merge_update_of_lt i a p _ h, f.map_update_smul]
      · obtain rfl : p = i.castSucc := Fin.ext h
        simp only [merge_update_castSucc, smul_mul_assoc, f.map_update_smul]
      · rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with h' | h'
        · obtain rfl : p = i.succ := Fin.ext h'.symm
          simp only [merge_update_succ, mul_smul_comm, f.map_update_smul]
        · simp only [merge_update_of_gt i a p _ h', f.map_update_smul])

@[simp]
theorem compMerge_apply {n : ℕ} (f : HochschildCochain R A M n) (i : Fin n)
    (a : Fin (n + 1) → A) : compMerge f i a = f (merge i a) := rfl

section Left

variable [DGAddCommGroup A] [DGRing A] [DGAlgebra R A] [Module A M] [IsScalarTower R A M]

variable (R A M) in
/-- The left action of `A` on `M`, as an `R`-bilinear map. -/
def leftAct : A →ₗ[R] M →ₗ[R] M :=
  LinearMap.mk₂ R (fun a m => a • m) (fun _ _ _ => add_smul _ _ _) (fun _ _ _ => smul_assoc _ _ _)
    (fun _ _ _ => smul_add _ _ _) (fun _ _ _ => smul_comm _ _ _)

variable (k : ℤ)

/-- The multilinear map `(a₀, …, aₙ) ↦ (-1)^(|a₀| k) a₀ • f (a₁, …, aₙ)`. -/
def leftTerm {n : ℕ} (f : HochschildCochain R A M n) : HochschildCochain R A M (n + 1) :=
  LinearMap.uncurryLeft
    { toFun := fun a => (leftAct R A M (DGAlgebra.twist R A k a)).compMultilinearMap f
      map_add' := fun a b => by ext; simp [leftAct, add_smul]
      map_smul' := fun r a => by ext; simp [leftAct, smul_assoc] }

@[simp]
theorem leftTerm_apply {n : ℕ} (f : HochschildCochain R A M n) (a : Fin (n + 1) → A) :
    leftTerm k f a = DGAlgebra.twist R A k (a 0) • f (Fin.tail a) := rfl

end Left

section Right

variable [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]

variable (R A M) in
/-- The right action of `A` on `M`, `(m, a) ↦ m • a = op a • m`, as an `R`-bilinear map. -/
def rightAct : M →ₗ[R] A →ₗ[R] M :=
  LinearMap.mk₂ R (fun m a => op a • m) (fun _ _ _ => smul_add _ _ _)
    (fun _ _ _ => smul_comm _ _ _) (fun _ _ _ => by simp only [op_add, add_smul])
    (fun _ _ _ => by simp only [op_smul, smul_assoc])

/-- The multilinear map `(a₀, …, aₙ) ↦ f (a₀, …, aₙ₋₁) • aₙ`. -/
def rightTerm {n : ℕ} (f : HochschildCochain R A M n) : HochschildCochain R A M (n + 1) :=
  MultilinearMap.uncurryRight ((rightAct R A M).compMultilinearMap f)

@[simp]
theorem rightTerm_apply {n : ℕ} (f : HochschildCochain R A M n) (a : Fin (n + 1) → A) :
    rightTerm f a = op (a (Fin.last n)) • f (Fin.init a) := rfl

end Right

end Hochschild

open Hochschild

variable {R A M} [DGAddCommGroup A] [DGRing A] [DGAlgebra R A] [Module A M] [Module Aᵐᵒᵖ M]
  [IsScalarTower R A M] [IsScalarTower R Aᵐᵒᵖ M]

/-- The Hochschild differential with the Koszul sign rule for cochains of internal degree `k`:
`(δ f)(a₀, …, aₙ) = (-1)^(|a₀| k) a₀ • f (a₁, …, aₙ)
  + ∑ᵢ (-1)^(i + 1) f (a₀, …, aᵢ aᵢ₊₁, …, aₙ) + (-1)^(n + 1) f (a₀, …, aₙ₋₁) • aₙ`. -/
def hochschildDiff (k : ℤ) {n : ℕ} (f : HochschildCochain R A M n) :
    HochschildCochain R A M (n + 1) :=
  leftTerm k f + ∑ i : Fin n, koszulSign ((i : ℕ) + 1 : ℤ) • compMerge f i +
    koszulSign ((n : ℤ) + 1) • rightTerm f

theorem hochschildDiff_apply (k : ℤ) {n : ℕ} (f : HochschildCochain R A M n)
    (a : Fin (n + 1) → A) :
    hochschildDiff k f a = DGAlgebra.twist R A k (a 0) • f (Fin.tail a) +
      ∑ i : Fin n, koszulSign ((i : ℕ) + 1 : ℤ) • f (merge i a) +
        koszulSign ((n : ℤ) + 1) • (op (a (Fin.last n)) • f (Fin.init a)) := by
  simp [hochschildDiff, MultilinearMap.sum_apply, Units.smul_def]

section Square

variable [SMulCommClass A Aᵐᵒᵖ M]

namespace Hochschild

variable (k : ℤ)

/-- The extension of a cochain `f` to the function
`(a₀, …, aₙ₊₁) ↦ (-1)^(|a₀| k) a₀ • f (a₁, …, aₙ) • aₙ₊₁`, which turns the Hochschild
differential into the alternating sum of merges (`DG.Hochschild.extend_hochschildDiff`). -/
def extend {n : ℕ} (f : HochschildCochain R A M n) : (Fin (n + 2) → A) → M :=
  fun a => DGAlgebra.twist R A k (a 0) • op (a (Fin.last (n + 1))) • f (Fin.init (Fin.tail a))

private theorem units_smul_comm {X : Type*} [SMul X M] [SMulCommClass X ℤ M] (x : X) (u : ℤˣ)
    (m : M) : x • (u • m) = u • (x • m) := by
  rw [Units.smul_def, Units.smul_def, smul_comm]

theorem extend_hochschildDiff {n : ℕ} (f : HochschildCochain R A M n) :
    extend k (hochschildDiff k f) = barD (extend k f) := by
  funext a
  simp only [extend, barD, hochschildDiff_apply]
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [merge_zero_apply_zero, merge_zero_apply_last, init_tail_merge_zero,
    merge_succ_apply_zero, merge_succ_apply_last, init_tail_merge_succ, merge_last_apply_zero,
    merge_last_apply_last, init_tail_merge_last, DGAlgebra.twist_mul, op_mul, mul_smul,
    smul_add, Finset.smul_sum, units_smul_comm, Fin.val_zero, Nat.cast_zero, koszulSign_zero,
    one_smul, Fin.val_succ, Fin.coe_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one,
    add_assoc]
  rw [← smul_comm (DGAlgebra.twist R A k (Fin.init (Fin.tail a) 0)) (op (a (Fin.last (n + 1 + 1))))]
  rfl

omit [IsScalarTower R A M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M] in
theorem extend_cons_snoc {n : ℕ} (f : HochschildCochain R A M n) (b : Fin n → A) :
    extend k f (Fin.cons (1 : A) (Fin.snoc b (1 : A) : Fin (n + 1) → A)) = f b := by
  simp only [extend, Fin.cons_zero, Fin.tail_cons, Fin.init_snoc, ← Fin.succ_last, Fin.cons_succ,
    Fin.snoc_last, DGAlgebra.twist_one, op_one, one_smul]

end Hochschild

/-- The Hochschild differential squares to zero. -/
theorem hochschildDiff_hochschildDiff (k : ℤ) {n : ℕ} (f : HochschildCochain R A M n) :
    hochschildDiff k (hochschildDiff k f) = 0 := by
  ext b
  rw [← extend_cons_snoc k (hochschildDiff k (hochschildDiff k f)) b, extend_hochschildDiff,
    extend_hochschildDiff, barD_barD]
  rfl

end Square

/-- The Hochschild differential `Cⁿ(A, M) → Cⁿ⁺¹(A, M)` for internal degree `k`, as an
`R`-linear map. -/
def hochschildD (k : ℤ) (n : ℕ) :
    HochschildCochain R A M n →ₗ[R] HochschildCochain R A M (n + 1) where
  toFun := hochschildDiff k
  map_add' f g := by
    ext a
    simp only [hochschildDiff_apply, MultilinearMap.add_apply, smul_add, Finset.sum_add_distrib]
    abel
  map_smul' r f := by
    ext a
    simp only [hochschildDiff_apply, MultilinearMap.smul_apply, RingHom.id_apply, smul_add,
      Finset.smul_sum, Units.smul_def, smul_comm r]

theorem hochschildD_apply (k : ℤ) {n : ℕ} (f : HochschildCochain R A M n) :
    hochschildD k n f = hochschildDiff k f := rfl

section Square

variable [SMulCommClass A Aᵐᵒᵖ M]

theorem hochschildD_comp_hochschildD (k : ℤ) (n : ℕ) :
    hochschildD (R := R) (A := A) (M := M) k (n + 1) ∘ₗ hochschildD k n = 0 :=
  LinearMap.ext fun f => hochschildDiff_hochschildDiff k f

end Square

end Differential

/-! ### Homogeneous cochains -/

section Homogeneous

variable (R A M : Type*) [CommRing R] [Ring A] [Algebra R A] [DGAddCommGroup A] [DGRing A]
  [DGAlgebra R A] [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Aᵐᵒᵖ M]
  [DGBimodule A A M] [Module R M] [IsScalarTower R A M] [IsScalarTower R Aᵐᵒᵖ M]

/-- The Hochschild cochains of internal degree `k`, `Cⁿ(A, M)ᵏ`: the multilinear maps `f` with
`f (a₁, …, aₙ) ∈ M^(k + |a₁| + ⋯ + |aₙ|)` for homogeneous `aᵢ`. -/
def hochschildCochains (k : ℤ) (n : ℕ) : Submodule R (HochschildCochain R A M n) where
  carrier := {f | ∀ (p : Fin n → ℤ) (a : Fin n → A), (∀ i, a i ∈ grading (p i)) →
    f a ∈ grading (k + ∑ i, p i)}
  add_mem' hf hg p a ha := add_mem (hf p a ha) (hg p a ha)
  zero_mem' _ _ _ := zero_mem _
  smul_mem' r _ hf p a ha := DGModule.ground_smul_mem A r (hf p a ha)

variable {R A M}

omit [IsScalarTower R Aᵐᵒᵖ M] in
theorem mem_hochschildCochains {k : ℤ} {n : ℕ} {f : HochschildCochain R A M n} :
    f ∈ hochschildCochains R A M k n ↔ ∀ (p : Fin n → ℤ) (a : Fin n → A),
      (∀ i, a i ∈ grading (p i)) → f a ∈ grading (k + ∑ i, p i) :=
  Iff.rfl

private theorem mem_grading_of_eq {X : Type*} [AddCommGroup X] [DGAddCommGroup X] {i j : ℤ}
    (h : i = j) {x : X} (hx : x ∈ grading i) : x ∈ grading j :=
  h ▸ hx

theorem Hochschild.merge_mem_grading {n : ℕ} (i : Fin n) {p : Fin (n + 1) → ℤ}
    {a : Fin (n + 1) → A} (ha : ∀ j, a j ∈ grading (p j)) (k : Fin n) :
    Hochschild.merge i a k ∈ grading (Fin.contractNth i.castSucc (· + ·) p k) := by
  simp only [Hochschild.merge_apply, Fin.contractNth, Fin.coe_castSucc]
  split_ifs
  · exact ha _
  · exact mul_mem_grading (ha _) (ha _)
  · exact ha _

/-- The Hochschild differential preserves the internal degree. -/
theorem hochschildD_mem {k : ℤ} {n : ℕ} {f : HochschildCochain R A M n}
    (hf : f ∈ hochschildCochains R A M k n) :
    hochschildD k n f ∈ hochschildCochains R A M k (n + 1) := by
  intro p a ha
  rw [hochschildD_apply, hochschildDiff_apply]
  refine add_mem (add_mem ?_ (sum_mem fun i _ => ?_)) ?_
  · refine mem_grading_of_eq ?_ (smul_mem_grading (DGAlgebra.twist_mem k (ha 0))
      (hf (Fin.tail p) (Fin.tail a) fun i => ha i.succ))
    rw [Fin.sum_univ_succ]
    simp only [Fin.tail]
    ring
  · rw [Units.smul_def]
    refine zsmul_mem (mem_grading_of_eq ?_
      (hf _ _ (Hochschild.merge_mem_grading i ha))) _
    rw [Hochschild.sum_contractNth_add]
  · rw [Units.smul_def]
    refine zsmul_mem (mem_grading_of_eq ?_ (op_smul_mem_grading (ha (Fin.last n))
      (hf (Fin.init p) (Fin.init a) fun i => ha i.castSucc))) _
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.init]
    ring

/-! ### The Hochschild complex and its cohomology -/

variable (R A M)

/-- The Hochschild cochain complex `C^•(A, M)ᵏ` of internal degree `k`, as a cochain complex of
`R`-modules indexed by `ℕ`. -/
def hochschildComplex (k : ℤ) : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (hochschildCochains R A M k n))
    (fun n => ModuleCat.ofHom ((hochschildD k n).restrict fun _ hf => hochschildD_mem hf))
    fun n => by
      ext f a
      exact congrArg (fun g : HochschildCochain R A M (n + 2) => g a)
        (hochschildDiff_hochschildDiff k f.1)

/-- The Hochschild cocycles `Zⁿ(A, M)ᵏ`: the cochains of internal degree `k` killed by the
Hochschild differential. -/
def hochschildCocycles (k : ℤ) (n : ℕ) : Submodule R (HochschildCochain R A M n) :=
  hochschildCochains R A M k n ⊓ LinearMap.ker (hochschildD k n)

/-- The Hochschild coboundaries `Bⁿ(A, M)ᵏ`: the image of the cochains of internal degree `k` under
the Hochschild differential (zero for `n = 0`). -/
def hochschildCoboundaries (k : ℤ) : (n : ℕ) → Submodule R (HochschildCochain R A M n)
  | 0 => ⊥
  | n + 1 => (hochschildCochains R A M k n).map (hochschildD k n)

theorem hochschildCoboundaries_le_cocycles (k : ℤ) (n : ℕ) :
    hochschildCoboundaries R A M k n ≤ hochschildCocycles R A M k n := by
  cases n with
  | zero => exact bot_le
  | succ n =>
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨hochschildD_mem hf, hochschildDiff_hochschildDiff k f⟩

/-- The Hochschild cohomology `HHⁿ(A, M)ᵏ = Zⁿ(A, M)ᵏ / Bⁿ(A, M)ᵏ` of internal degree `k`. -/
abbrev HochschildCohomology (k : ℤ) (n : ℕ) : Type _ :=
  hochschildCocycles R A M k n ⧸
    (hochschildCoboundaries R A M k n).comap (hochschildCocycles R A M k n).subtype

/-! ### `HH⁰` is the graded center -/

/-- The degree-`k` graded center of the bimodule `M`: the elements `m ∈ Mᵏ` with
`m • a = (-1)^(|a| k) • (a • m)` for all homogeneous `a ∈ A`. For `M = A` this is the degree-`k`
part of the graded center of `A` (`DG.mem_gradedCenter_self_iff`). -/
def gradedCenter (k : ℤ) : Submodule R M where
  carrier := {m | m ∈ grading k ∧
    ∀ (p : ℤ) (a : A), a ∈ grading p → op a • m = koszulSign (p * k) • (a • m)}
  add_mem' := fun {m m'} hm hm' => ⟨add_mem hm.1 hm'.1, fun p a ha => by
    rw [smul_add, hm.2 p a ha, hm'.2 p a ha, smul_add, smul_add]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ _ => by simp only [smul_zero]⟩
  smul_mem' := fun r m hm => ⟨DGModule.ground_smul_mem A r hm.1, fun p a ha => by
    rw [smul_comm (op a) r m, hm.2 p a ha, smul_comm a r m, Units.smul_def, Units.smul_def,
      smul_comm r]⟩

variable {R A M}

theorem mem_gradedCenter {k : ℤ} {m : M} :
    m ∈ gradedCenter R A M k ↔ m ∈ grading k ∧
      ∀ (p : ℤ) (a : A), a ∈ grading p → op a • m = koszulSign (p * k) • (a • m) :=
  Iff.rfl

omit [DGAddCommGroup M] [DGBimodule A A M] in
theorem hochschildD_zero_apply (k : ℤ) (f : HochschildCochain R A M 0) (a : Fin 1 → A) :
    hochschildD k 0 f a = DGAlgebra.twist R A k (a 0) • f 0 - op (a 0) • f 0 := by
  rw [hochschildD_apply, hochschildDiff_apply, Subsingleton.elim (Fin.tail a) 0,
    Subsingleton.elim (Fin.init a) 0, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  simp only [Nat.cast_zero, zero_add, koszulSign_odd odd_one, Units.neg_smul, one_smul,
    ← sub_eq_add_neg]
  rfl

/-- A `0`-cochain, i.e. an element `m ∈ M`, is a Hochschild cocycle of internal degree `k` if and
only if `m` lies in the degree-`k` graded center. -/
theorem constOfIsEmpty_mem_hochschildCocycles_zero_iff (k : ℤ) (m : M) :
    MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => A) m ∈ hochschildCocycles R A M k 0 ↔
      m ∈ gradedCenter R A M k := by
  constructor
  · rintro ⟨hdeg, hker⟩
    refine ⟨by simpa using hdeg 0 0 fun i => i.elim0, fun p a ha => ?_⟩
    have h := congrArg (fun g : HochschildCochain R A M 1 => g fun _ => a) hker
    simp only [hochschildD_zero_apply, MultilinearMap.zero_apply] at h
    change DGAlgebra.twist R A k a • m - op a • m = 0 at h
    rw [← sub_eq_zero.mp h, DGAlgebra.twist_of_mem k ha, Units.smul_def, Units.smul_def,
      smul_assoc]
  · rintro ⟨hm, hc⟩
    refine ⟨fun p a _ => by simpa using hm, ?_⟩
    have key : ∀ x : A, DGAlgebra.twist R A k x • m = op x • m := by
      intro x
      induction x using induction_on with
      | h_zero => simp
      | h_add x y hx hy => rw [map_add, add_smul, hx, hy, op_add, add_smul]
      | h_homogeneous x =>
        rw [DGAlgebra.twist_of_mem k x.2, hc _ _ x.2, Units.smul_def, Units.smul_def,
          smul_assoc]
    ext a
    rw [hochschildD_zero_apply, MultilinearMap.zero_apply]
    exact sub_eq_zero.mpr (key (a 0))

/-- The Hochschild `0`-cocycles of internal degree `k` are the degree-`k` graded center. -/
def hochschildCocyclesZeroEquiv (k : ℤ) :
    hochschildCocycles R A M k 0 ≃ₗ[R] gradedCenter R A M k where
  toFun f := ⟨f.1 0, (constOfIsEmpty_mem_hochschildCocycles_zero_iff k (f.1 0)).mp (by
    convert f.2
    ext a
    exact congrArg f.1 (Subsingleton.elim _ _))⟩
  invFun m := ⟨_, (constOfIsEmpty_mem_hochschildCocycles_zero_iff k m.1).mpr m.2⟩
  left_inv f := Subtype.ext (MultilinearMap.ext fun a => congrArg f.1 (Subsingleton.elim _ _))
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `HH⁰(A, M)ᵏ ≅ Z(A, M)ᵏ`: the Hochschild cohomology in degree `0` and internal degree `k` is the
degree-`k` graded center of `M`. -/
def hochschildCohomologyZeroEquiv (k : ℤ) :
    HochschildCohomology R A M k 0 ≃ₗ[R] gradedCenter R A M k :=
  (Submodule.quotEquivOfEqBot _ (by
    show Submodule.comap _ ⊥ = ⊥
    rw [Submodule.comap_bot, Submodule.ker_subtype])).trans (hochschildCocyclesZeroEquiv k)

omit [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Aᵐᵒᵖ M] [DGBimodule A A M]
  [Module R M] [IsScalarTower R A M] [IsScalarTower R Aᵐᵒᵖ M] in
/-- For `M = A`, the degree-`k` graded center consists of the `z ∈ Aᵏ` with
`z * a = (-1)^(|a| k) • (a * z)` for all homogeneous `a`; thus `HH⁰(A, A)ᵏ` is the degree-`k`
part of the graded center `Z(A)` (`DG.hochschildCohomologyZeroEquiv`). -/
theorem mem_gradedCenter_self_iff {k : ℤ} {z : A} :
    z ∈ gradedCenter R A A k ↔ z ∈ grading k ∧
      ∀ (p : ℤ) (a : A), a ∈ grading p → z * a = koszulSign (p * k) • (a * z) :=
  Iff.rfl

end Homogeneous

/-! ### The total Hochschild complex -/

section Total

variable (R A M : Type*) [CommRing R] [Ring A] [Algebra R A] [DGAddCommGroup A] [DGRing A]
  [DGAlgebra R A] [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Aᵐᵒᵖ M]
  [DGBimodule A A M] [Module R M] [IsScalarTower R A M] [IsScalarTower R Aᵐᵒᵖ M]

/-- The degree-`N` part of the total Hochschild complex: the families `(fₙ)_{n ≥ 0}` of cochains
with `fₙ ∈ Cⁿ(A, M)^(N - n)`, i.e. the product `∏ₙ Cⁿ(A, M)^(N - n)` over Hochschild degree `n`
and internal degree `N - n`. -/
def hochschildTotal (N : ℤ) : Submodule R ((n : ℕ) → HochschildCochain R A M n) where
  carrier := {f | ∀ n : ℕ, f n ∈ hochschildCochains R A M (N - n) n}
  add_mem' hf hg n := add_mem (hf n) (hg n)
  zero_mem' _ := zero_mem _
  smul_mem' r _ hf n := Submodule.smul_mem _ r (hf n)

variable {R A M}

/-- The total Hochschild differential on families of cochains: `(D f)₀ = 0` and
`(D f)ₙ₊₁ = δ fₙ`, with `δ` the Hochschild differential for internal degree `N - n`. -/
def hochschildTotalDFun (N : ℤ) (f : (n : ℕ) → HochschildCochain R A M n) :
    (n : ℕ) → HochschildCochain R A M n
  | 0 => 0
  | n + 1 => hochschildD (N - n) n (f n)

private theorem total_index (N : ℤ) (n : ℕ) : N + 1 - ((n + 1 : ℕ) : ℤ) = N - n := by
  push_cast; ring

variable (R A M) in
/-- The total Hochschild differential, of degree `1`. -/
def hochschildTotalD (N : ℤ) : hochschildTotal R A M N →ₗ[R] hochschildTotal R A M (N + 1) where
  toFun f := ⟨hochschildTotalDFun N f.1, fun n => by
    cases n with
    | zero => exact zero_mem _
    | succ n =>
      rw [total_index]
      exact hochschildD_mem (f.2 n)⟩
  map_add' f g := by
    ext1
    funext n
    cases n with
    | zero => exact (add_zero 0).symm
    | succ n => exact map_add (hochschildD (N - n) n) (f.1 n) (g.1 n)
  map_smul' r f := by
    ext1
    funext n
    cases n with
    | zero => exact (smul_zero r).symm
    | succ n => exact map_smul (hochschildD (N - n) n) r (f.1 n)

theorem hochschildTotalD_apply_zero (N : ℤ) (f : hochschildTotal R A M N) :
    (hochschildTotalD R A M N f).1 0 = 0 := rfl

theorem hochschildTotalD_apply_succ (N : ℤ) (f : hochschildTotal R A M N) (n : ℕ) :
    (hochschildTotalD R A M N f).1 (n + 1) = hochschildD (N - n) n (f.1 n) := rfl

theorem hochschildTotalD_hochschildTotalD (N : ℤ) (f : hochschildTotal R A M N) :
    hochschildTotalD R A M (N + 1) (hochschildTotalD R A M N f) = 0 := by
  ext1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => exact map_zero (hochschildD (N + 1 - ((0 : ℕ) : ℤ)) 0)
    | succ n =>
      change hochschildD (N + 1 - ((n + 1 : ℕ) : ℤ)) (n + 1)
        (hochschildD (N - n) n (f.1 n)) = 0
      rw [total_index]
      exact hochschildDiff_hochschildDiff _ _

variable (R A M)

/-- The degree-`N` part `∏ₙ Cⁿ(A, M)^(N - n)` of the total Hochschild complex, as a type (a
type synonym for `DG.hochschildTotal R A M N`). -/
def HochschildTotalDeg (N : ℤ) : Type _ := hochschildTotal R A M N

instance (N : ℤ) : AddCommGroup (HochschildTotalDeg R A M N) :=
  inferInstanceAs (AddCommGroup (hochschildTotal R A M N))

instance (N : ℤ) : Module R (HochschildTotalDeg R A M N) :=
  inferInstanceAs (Module R (hochschildTotal R A M N))

/-- The total Hochschild cochain complex `C(A, M) = ⨁_N ∏ₙ Cⁿ(A, M)^(N - n)` of a graded algebra
`A` (a dg algebra with `d = 0`) with coefficients in a graded bimodule `M`, graded by total
degree. Its differential is the Hochschild differential
(`DG.HochschildTotal.instDGAddCommGroup`). -/
abbrev HochschildTotal : Type _ := ⨁ N : ℤ, HochschildTotalDeg R A M N

namespace HochschildTotal

/-- The differential of the total Hochschild complex. -/
def dHom : HochschildTotal R A M →+ HochschildTotal R A M :=
  DirectSum.toAddMonoid fun N =>
    (DirectSum.of (fun N => HochschildTotalDeg R A M N) (N + 1)).comp
      ((hochschildTotalD R A M N).toAddMonoidHom :
        HochschildTotalDeg R A M N →+ HochschildTotalDeg R A M (N + 1))

variable {R A M}

theorem dHom_of (N : ℤ) (f : HochschildTotalDeg R A M N) :
    dHom R A M (DirectSum.of _ N f) =
      DirectSum.of (fun N => HochschildTotalDeg R A M N) (N + 1) (hochschildTotalD R A M N f) :=
  DirectSum.toAddMonoid_of _ _ _

variable (R A M)

/-- The total Hochschild complex is a dg abelian group, graded by total degree, with the Hochschild
differential. -/
instance instDGAddCommGroup : DGAddCommGroup (HochschildTotal R A M) where
  grading := summand fun N => HochschildTotalDeg R A M N
  d := dHom R A M
  d_mem' := by
    rintro n _ ⟨f, rfl⟩
    rw [dHom_of]
    exact of_mem_summand _ _
  d_d' x := by
    induction x using DirectSum.induction_on with
    | zero => rw [map_zero, map_zero]
    | of N f =>
      rw [dHom_of, dHom_of]
      erw [hochschildTotalD_hochschildTotalD]
      exact map_zero _
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

variable {R A M}

theorem d_of (N : ℤ) (f : HochschildTotalDeg R A M N) :
    d (DirectSum.of (fun N => HochschildTotalDeg R A M N) N f : HochschildTotal R A M) =
      DirectSum.of (fun N => HochschildTotalDeg R A M N) (N + 1) (hochschildTotalD R A M N f) :=
  dHom_of N f

/-- The differential of the total Hochschild complex is `R`-linear. -/
theorem d_smul (r : R) (x : HochschildTotal R A M) : d (r • x) = r • d x := by
  induction x using DirectSum.induction_on with
  | zero => rw [smul_zero, d_zero, smul_zero]
  | of N f =>
    have h : ∀ (K : ℤ) (g : HochschildTotalDeg R A M K),
        r • (DirectSum.of (fun N => HochschildTotalDeg R A M N) K g : HochschildTotal R A M) =
          DirectSum.of _ K (r • g) := fun K g => by
      rw [← DirectSum.lof_eq_of R, ← DirectSum.lof_eq_of R, map_smul]
    rw [h, d_of, d_of, h]
    congr 1
    exact map_smul (hochschildTotalD R A M N) r f
  | add x y hx hy => rw [smul_add, d_add, hx, hy, d_add, smul_add]

end HochschildTotal

end Total

end DG

end
