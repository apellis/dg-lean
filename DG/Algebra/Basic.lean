import Mathlib.RingTheory.GradedAlgebra.Basic
import DG.Basic

/-!
# Differential graded abelian groups, rings and algebras

This file defines the core objects of the library, with internal gradings in the style of
Mathlib's `GradedRing`.

* `DGAddCommGroup M`: a differential graded abelian group, i.e. an abelian group `M` with an
  internal `ℤ`-grading `grading : ℤ → AddSubgroup M` (a `DirectSum.Decomposition`) and a
  differential `d : M →+ M` of degree `1` with `d ∘ d = 0`. This is an internally graded
  cochain complex of abelian groups.
* `DGRing A`: a `Prop`-valued mixin saying that the ring structure of a `DGAddCommGroup A` is
  compatible with the grading (`1 ∈ A⁰`, `Aⁱ * Aʲ ⊆ Aⁱ⁺ʲ`) and with the differential
  (the graded Leibniz rule `d (a * b) = d a * b + (-1)^{|a|} • (a * d b)`).
* `DGAlgebra R A`: a `Prop`-valued mixin saying that an `R`-algebra structure on a dg ring `A`
  is compatible: the image of `R` lies in degree `0` and is killed by `d`. This makes `d`
  `R`-linear and every graded piece an `R`-submodule.

The data (grading and differential) live in `DGAddCommGroup`, so that the differential of a dg
ring and of a dg module are the same function `d`, and so that right modules and bimodules are
further `Prop` mixins on the same data (see `DG.Module.Basic`). This follows Mathlib's
separation of `Ring A` / `Module R M` / `IsScalarTower R A M`.

## Conventions

See `docs/CONVENTIONS.md`. Gradings are cohomological: `d` has degree `+1`. The Koszul sign
of degree `n` is `koszulSign n = Int.negOnePow n : ℤˣ`, used through the `ℤˣ`-action.
-/

open DirectSum

namespace DG

/-- A differential graded abelian group: an abelian group `M` with an internal `ℤ`-grading
`M = ⨁ n, grading n` and a differential `d : M →+ M` of degree `+1` squaring to zero. -/
class DGAddCommGroup (M : Type*) [AddCommGroup M] where
  /-- The homogeneous components `Mⁿ`. -/
  grading : ℤ → AddSubgroup M
  /-- The grading is an internal direct sum decomposition. -/
  [decomposition : DirectSum.Decomposition grading]
  /-- The differential. -/
  d : M →+ M
  d_mem' : ∀ {n : ℤ} {m : M}, m ∈ grading n → d m ∈ grading (n + 1)
  d_d' : ∀ m : M, d (d m) = 0

attribute [instance_reducible, instance] DGAddCommGroup.decomposition

export DGAddCommGroup (grading d)

section DGAddCommGroup

variable {M : Type*} [AddCommGroup M] [DGAddCommGroup M]

theorem d_mem {n : ℤ} {m : M} (hm : m ∈ grading n) : d m ∈ grading (n + 1) :=
  DGAddCommGroup.d_mem' hm

@[simp]
theorem d_d (m : M) : d (d m) = 0 :=
  DGAddCommGroup.d_d' m

@[simp]
theorem d_comp_d : (d : M →+ M).comp d = 0 := by
  ext m; exact d_d m

@[simp]
theorem d_zero : d (0 : M) = 0 :=
  map_zero d

theorem d_add (m m' : M) : d (m + m') = d m + d m' :=
  map_add d m m'

theorem d_neg (m : M) : d (-m) = -d m :=
  map_neg d m

theorem d_sub (m m' : M) : d (m - m') = d m - d m' :=
  map_sub d m m'

theorem d_zsmul (k : ℤ) (m : M) : d (k • m) = k • d m :=
  map_zsmul d k m

theorem d_nsmul (k : ℕ) (m : M) : d (k • m) = k • d m :=
  map_nsmul d k m

theorem d_units_smul (u : ℤˣ) (m : M) : d (u • m) = u • d m := by
  simp only [Units.smul_def, d_zsmul]

/-- The differential restricted to homogeneous components, `Mⁿ →+ Mⁿ⁺¹`. -/
def dHom (M : Type*) [AddCommGroup M] [DGAddCommGroup M] (n : ℤ) :
    grading (M := M) n →+ grading (M := M) (n + 1) where
  toFun m := ⟨d (m : M), d_mem m.2⟩
  map_zero' := by ext; simp
  map_add' m m' := by ext; simp [d_add]

@[simp]
theorem coe_dHom_apply (n : ℤ) (m : grading (M := M) n) : (dHom M n m : M) = d (m : M) := rfl

theorem dHom_comp_dHom (n : ℤ) :
    (dHom M (n + 1)).comp (dHom M n) = 0 := by
  ext m; simp

/-- Induction on the decomposition: to prove `P m` for all `m`, prove it for `0`, for homogeneous
elements, and show it is closed under addition. -/
theorem induction_on {P : M → Prop} (h_zero : P 0)
    (h_homogeneous : ∀ {n : ℤ} (m : grading (M := M) n), P m)
    (h_add : ∀ m m' : M, P m → P m' → P (m + m')) (m : M) : P m :=
  DirectSum.Decomposition.inductionOn (grading (M := M)) h_zero h_homogeneous h_add m

/-- The cocycles of degree `n`, `Zⁿ(M) = ker (d : Mⁿ → Mⁿ⁺¹)`. -/
def cocycles (M : Type*) [AddCommGroup M] [DGAddCommGroup M] (n : ℤ) : AddSubgroup M :=
  (grading (M := M) n) ⊓ (d : M →+ M).ker

/-- The coboundaries of degree `n`, `Bⁿ(M) = d (Mⁿ⁻¹)`. -/
def coboundaries (M : Type*) [AddCommGroup M] [DGAddCommGroup M] (n : ℤ) : AddSubgroup M :=
  (grading (M := M) (n - 1)).map d

theorem mem_cocycles {n : ℤ} {m : M} : m ∈ cocycles M n ↔ m ∈ grading n ∧ d m = 0 :=
  Iff.rfl

theorem mem_coboundaries {n : ℤ} {m : M} :
    m ∈ coboundaries M n ↔ ∃ m' ∈ grading (M := M) (n - 1), d m' = m :=
  Iff.rfl

theorem coboundaries_le_cocycles (n : ℤ) : coboundaries M n ≤ cocycles M n := by
  rintro _ ⟨m, hm, rfl⟩
  exact ⟨by simpa using d_mem hm, d_d m⟩

theorem coboundaries_le_grading (n : ℤ) : coboundaries M n ≤ grading n :=
  (coboundaries_le_cocycles n).trans inf_le_left

theorem cocycles_le_grading (n : ℤ) : cocycles M n ≤ grading n :=
  inf_le_left

variable {N : Type*} [AddCommGroup N] [DGAddCommGroup N]

/-- An additive map of degree `k` commutes with taking homogeneous components. -/
theorem decompose_map {k : ℤ} (f : M →+ N)
    (hf : ∀ {n : ℤ} {m : M}, m ∈ grading n → f m ∈ grading (n + k)) (m : M) (n : ℤ) :
    (decompose (grading (M := N)) (f m) (n + k) : N) =
      f (decompose (grading (M := M)) m n) := by
  induction m using induction_on with
  | h_zero => simp
  | h_homogeneous m =>
    obtain ⟨m, hm⟩ := m
    rename_i i
    by_cases h : i = n
    · subst h
      rw [decompose_of_mem_same _ hm, decompose_of_mem_same _ (hf hm)]
    · rw [decompose_of_mem_ne _ hm h, decompose_of_mem_ne _ (hf hm) (by omega), map_zero]
  | h_add m m' hm hm' =>
    simp only [map_add, decompose_add, DirectSum.add_apply, AddSubgroup.coe_add, hm, hm']

/-- The differential commutes with taking homogeneous components: the degree-`n + 1`
component of `d m` is `d` of the degree-`n` component of `m`. -/
theorem decompose_d (m : M) (n : ℤ) :
    (decompose (grading (M := M)) (d m) (n + 1) : M) =
      d (decompose (grading (M := M)) m n : M) :=
  decompose_map (k := 1) d (fun hm => d_mem hm) m n

/-- Induction over a homogeneous additive subgroup: a predicate which holds for `0`, for the
homogeneous elements of `S` and is closed under addition holds on all of `S`. -/
theorem induction_on_of_isHomogeneous {S : AddSubgroup M}
    (hS : SetLike.IsHomogeneous (grading (M := M)) S) {P : M → Prop} (h_zero : P 0)
    (h_homogeneous : ∀ {n : ℤ} {m : M}, m ∈ grading n → m ∈ S → P m)
    (h_add : ∀ m m' : M, P m → P m' → P (m + m')) {m : M} (hm : m ∈ S) : P m := by
  classical
  rw [← DirectSum.sum_support_decompose (grading (M := M)) m]
  refine Finset.sum_induction _ P h_add h_zero fun n _ => ?_
  exact h_homogeneous (decompose (grading (M := M)) m n).2 (hS n hm)

/-- The kernel of the differential is a homogeneous subgroup. -/
theorem isHomogeneous_ker_d : SetLike.IsHomogeneous (grading (M := M)) (d : M →+ M).ker := by
  intro n m hm
  rw [AddMonoidHom.mem_ker] at hm ⊢
  rw [← decompose_d, hm, decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]

/-- The image of the differential is a homogeneous subgroup. -/
theorem isHomogeneous_range_d :
    SetLike.IsHomogeneous (grading (M := M)) (d : M →+ M).range := by
  rintro n _ ⟨m, rfl⟩
  refine ⟨decompose (grading (M := M)) m (n - 1), ?_⟩
  rw [← decompose_d, sub_add_cancel]

/-- A cocycle has cocycle homogeneous components. -/
theorem d_decompose_eq_zero {m : M} (hm : d m = 0) (n : ℤ) :
    d (decompose (grading (M := M)) m n : M) = 0 :=
  isHomogeneous_ker_d n (AddMonoidHom.mem_ker.mpr hm)

end DGAddCommGroup

/-- A differential graded ring: a ring `A` which is a `DGAddCommGroup` such that the grading is
a ring grading (`1 ∈ A⁰`, `Aⁱ * Aʲ ⊆ Aⁱ⁺ʲ`) and the differential satisfies the graded Leibniz
rule `d (a * b) = d a * b + (-1)^{|a|} • (a * d b)` for `a` homogeneous of degree `|a|`. -/
class DGRing (A : Type*) [Ring A] [DGAddCommGroup A] : Prop
    extends SetLike.GradedMonoid (grading (M := A)) where
  d_mul' : ∀ {n : ℤ} {a : A}, a ∈ grading n → ∀ b : A,
    d (a * b) = d a * b + koszulSign n • (a * d b)

section DGRing

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]

instance DGRing.toGradedRing : GradedRing (grading (M := A)) :=
  { DGRing.toGradedMonoid (A := A), DGAddCommGroup.decomposition (M := A) with }

theorem one_mem_grading : (1 : A) ∈ grading (M := A) 0 :=
  SetLike.GradedOne.one_mem

theorem mul_mem_grading {i j : ℤ} {a b : A} (ha : a ∈ grading i) (hb : b ∈ grading j) :
    a * b ∈ grading (i + j) :=
  SetLike.GradedMul.mul_mem ha hb

/-- The graded Leibniz rule. -/
theorem d_mul {n : ℤ} {a : A} (ha : a ∈ grading n) (b : A) :
    d (a * b) = d a * b + koszulSign n • (a * d b) :=
  DGRing.d_mul' ha b

theorem d_mul_of_even {n : ℤ} {a : A} (ha : a ∈ grading n) (hn : Even n) (b : A) :
    d (a * b) = d a * b + a * d b := by
  rw [d_mul ha, koszulSign_even hn, one_smul]

theorem d_mul_of_odd {n : ℤ} {a : A} (ha : a ∈ grading n) (hn : Odd n) (b : A) :
    d (a * b) = d a * b - a * d b := by
  rw [d_mul ha, koszulSign_odd hn, Units.neg_smul, one_smul, sub_eq_add_neg]

@[simp]
theorem d_one : d (1 : A) = 0 := by
  have h := d_mul (one_mem_grading (A := A)) 1
  simp only [mul_one, one_mul, koszulSign, Int.negOnePow_zero, one_smul] at h
  exact left_eq_add.mp h

theorem d_intCast (k : ℤ) : d (k : A) = 0 := by
  rw [← zsmul_one, d_zsmul, d_one, smul_zero]

theorem d_natCast (k : ℕ) : d (k : A) = 0 := by
  rw [← nsmul_one, d_nsmul, d_one, smul_zero]

/-- `d` is a derivation on even elements: `d (a * b) = d a * b + a * d b` for `a ∈ A⁰`. -/
theorem d_mul_of_mem_zero {a : A} (ha : a ∈ grading 0) (b : A) :
    d (a * b) = d a * b + a * d b :=
  d_mul_of_even ha Even.zero b

/-- Right-handed form of the Leibniz rule, for `b` homogeneous: the sign is carried by `a`. -/
theorem d_mul_right {n : ℤ} {a : A} (ha : a ∈ grading n) (b : A) :
    koszulSign n • (a * d b) = d (a * b) - d a * b := by
  rw [d_mul ha, add_sub_cancel_left]

/-- If `b` is a cocycle then `d (a * b) = d a * b` for every `a`. -/
theorem d_mul_of_d_eq_zero_right {b : A} (hb : d b = 0) (a : A) : d (a * b) = d a * b := by
  induction a using induction_on with
  | h_zero => simp
  | h_homogeneous a => rw [d_mul a.2, hb, mul_zero, smul_zero, add_zero]
  | h_add a a' ha ha' => rw [add_mul, d_add, ha, ha', d_add, add_mul]

/-- If `a` is a homogeneous cocycle of degree `n` then `d (a * b) = (-1)^n • (a * d b)`. -/
theorem d_mul_of_d_eq_zero_left {n : ℤ} {a : A} (ha : a ∈ grading n) (hda : d a = 0) (b : A) :
    d (a * b) = koszulSign n • (a * d b) := by
  rw [d_mul ha, hda, zero_mul, zero_add]

/-- The Leibniz rule for powers: for `a` homogeneous of degree `n`,
`d (a ^ k) = ∑ i < k, (-1)^(i n) • (a ^ i * d a * a ^ (k - 1 - i))`. -/
theorem d_pow {n : ℤ} {a : A} (ha : a ∈ grading n) (k : ℕ) :
    d (a ^ k) = ∑ i ∈ Finset.range k, koszulSign (i * n) • (a ^ i * d a * a ^ (k - 1 - i)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', d_mul ha, ih, Finset.sum_range_succ', Finset.mul_sum, Finset.smul_sum,
      add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul_comm, smul_smul, ← koszulSign_add, pow_succ', mul_assoc a, mul_assoc a]
      congr 2
      · push_cast; ring
      · congr 2
        omega
    · simp

/-- For `a ∈ A⁰`, `d (a ^ k) = ∑ i < k, a ^ i * d a * a ^ (k - 1 - i)`. -/
theorem d_pow_of_mem_zero {a : A} (ha : a ∈ grading 0) (k : ℕ) :
    d (a ^ k) = ∑ i ∈ Finset.range k, a ^ i * d a * a ^ (k - 1 - i) := by
  rw [d_pow ha]
  simp

/-- For `a` homogeneous of even degree, `d (a ^ k) = ∑ i < k, a ^ i * d a * a ^ (k - 1 - i)`. -/
theorem d_pow_of_even {n : ℤ} {a : A} (ha : a ∈ grading n) (hn : Even n) (k : ℕ) :
    d (a ^ k) = ∑ i ∈ Finset.range k, a ^ i * d a * a ^ (k - 1 - i) := by
  rw [d_pow ha]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [koszulSign_even (hn.mul_left _), one_smul]

/-- For `a` homogeneous of even degree commuting with `d a`,
`d (a ^ k) = k • (a ^ (k - 1) * d a)`. -/
theorem d_pow_of_even_of_commute {n : ℤ} {a : A} (ha : a ∈ grading n) (hn : Even n)
    (hc : Commute a (d a)) (k : ℕ) : d (a ^ k) = k • (a ^ (k - 1) * d a) := by
  rw [d_pow_of_even ha hn, Finset.sum_range]
  rw [Finset.sum_eq_card_nsmul (b := a ^ (k - 1) * d a) fun i _ => ?_]
  · simp
  · have hi := i.isLt
    rw [(hc.pow_left _).eq, mul_assoc, ← pow_add, ← (hc.pow_left _).eq]
    congr 3
    omega

/-- For `a ∈ A⁰` commuting with `d a`, `d (a ^ k) = k • (a ^ (k - 1) * d a)`. -/
theorem d_pow_of_mem_zero_of_commute {a : A} (ha : a ∈ grading 0) (hc : Commute a (d a))
    (k : ℕ) : d (a ^ k) = k • (a ^ (k - 1) * d a) :=
  d_pow_of_even_of_commute ha Even.zero hc k

set_option backward.isDefEq.respectTransparency false in
/-- The graded Leibniz rule for `n`-fold products. For a list `l` of homogeneous elements
(each given with its degree), `d (l₁ ⋯ lₙ) = ∑ᵢ (-1)^{|l₁| + ⋯ + |lᵢ₋₁|} • (l₁ ⋯ d lᵢ ⋯ lₙ)`. -/
theorem d_list_prod (l : List (Σ n : ℤ, grading (M := A) n)) :
    d (l.map fun x => (x.2 : A)).prod =
      ∑ i : Fin l.length, koszulSign ((l.take i).map (·.1)).sum •
        (((l.take i).map fun x => (x.2 : A)).prod * d (l[i].2 : A) *
          ((l.drop (i + 1)).map fun x => (x.2 : A)).prod) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, d_mul x.2.2, ih]
    erw [Fin.sum_univ_succ]
    rw [Finset.mul_sum, Finset.smul_sum]
    congr 1
    · simp
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Fin.val_succ, List.take_succ_cons, List.map_cons, List.sum_cons, List.prod_cons,
        List.drop_succ_cons, Fin.getElem_fin, koszulSign_add, mul_smul,
        mul_assoc, mul_smul_comm]
      rfl

end DGRing

/-- A differential graded `R`-algebra: an `R`-algebra `A` which is a dg ring, such that the
structure map `R → A` lands in degree `0` and is killed by `d`. Then `d` is `R`-linear
(`DG.d_smul`) and each graded piece is an `R`-submodule (`DG.DGAlgebra.gradingSubmodule`). -/
class DGAlgebra (R : Type*) (A : Type*) [CommRing R] [Ring A] [Algebra R A]
    [DGAddCommGroup A] [DGRing A] : Prop where
  algebraMap_mem' : ∀ r : R, algebraMap R A r ∈ grading (M := A) 0
  d_algebraMap' : ∀ r : R, d (algebraMap R A r) = 0

section DGAlgebra

variable (R : Type*) {A : Type*} [CommRing R] [Ring A] [Algebra R A]
  [DGAddCommGroup A] [DGRing A] [DGAlgebra R A]

theorem algebraMap_mem_grading (r : R) : algebraMap R A r ∈ grading (M := A) 0 :=
  DGAlgebra.algebraMap_mem' r

@[simp]
theorem d_algebraMap (r : R) : d (algebraMap R A r) = 0 :=
  DGAlgebra.d_algebraMap' r

variable {R}

theorem DGAlgebra.smul_mem {n : ℤ} (r : R) {a : A} (ha : a ∈ grading n) :
    r • a ∈ grading n := by
  rw [Algebra.smul_def]
  simpa using mul_mem_grading (algebraMap_mem_grading R r) ha

theorem d_smul_algebra (r : R) (a : A) : d (r • a) = r • d a := by
  rw [Algebra.smul_def, d_mul (algebraMap_mem_grading R r), d_algebraMap, zero_mul, zero_add,
    koszulSign, Int.negOnePow_zero, one_smul, Algebra.smul_def]

variable (R A)

/-- The graded pieces of a dg `R`-algebra as `R`-submodules. -/
def DGAlgebra.gradingSubmodule (n : ℤ) : Submodule R A where
  __ := grading (M := A) n
  smul_mem' r _ ha := DGAlgebra.smul_mem r ha

@[simp]
theorem DGAlgebra.mem_gradingSubmodule {n : ℤ} {a : A} :
    a ∈ DGAlgebra.gradingSubmodule R A n ↔ a ∈ grading n :=
  Iff.rfl

@[simp]
theorem DGAlgebra.gradingSubmodule_toAddSubgroup (n : ℤ) :
    (DGAlgebra.gradingSubmodule R A n).toAddSubgroup = grading n := rfl

instance DGAlgebra.gradedAlgebra : GradedAlgebra (DGAlgebra.gradingSubmodule R A) where
  one_mem := one_mem_grading
  mul_mem _ _ _ _ ha hb := mul_mem_grading ha hb
  decompose' := DirectSum.decompose (grading (M := A))
  left_inv := DirectSum.Decomposition.left_inv (ℳ := grading (M := A))
  right_inv := DirectSum.Decomposition.right_inv (ℳ := grading (M := A))

/-- The differential of a dg `R`-algebra as an `R`-linear map. -/
def DGAlgebra.dLinear : A →ₗ[R] A where
  __ := (d : A →+ A)
  map_smul' := d_smul_algebra

@[simp]
theorem DGAlgebra.dLinear_apply (a : A) : DGAlgebra.dLinear R A a = d a := rfl

/-- A dg ring is a dg `ℤ`-algebra. -/
instance DGAlgebra.int : DGAlgebra ℤ A where
  algebraMap_mem' k := by simpa using zsmul_mem (one_mem_grading (A := A)) k
  d_algebraMap' k := by simpa using d_intCast (A := A) k

end DGAlgebra

end DG
