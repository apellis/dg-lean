import DG.Homotopy.SemiFree
import DG.Homotopy.Lifting
import DG.Derived.Resolution
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Finite-cell filtrations from finite triangular bases

Let `A` be a dg ring and `P` a left dg `A`-module which is free as a graded `A`-module on a finite
family of homogeneous elements `b_0, …, b_{m-1}` (degrees `k_j`) such that `d(b_j)` lies in the
`A`-span of `b_0, …, b_{j-1}` (`DG.TriangularBasis`). Then `P` is a finite-cell dg module:
`DG.TriangularBasis.finiteCellFiltration` is a `DG.FiniteCellFiltration A P` with
`F_i = span_A {b_l : l < i}` and subquotients `F_{j+1} / F_j ≅ A⟦-k_j⟧` (the cell of the degree-`0`
idempotent `1`, `DG.DGIdempotent.one`), the projection being `x ↦ (-1)^{k_j |c|} c` for `c` the
coefficient of `b_j`. Consequently `P` is K-projective and has the lifting property against
surjective quasi-isomorphisms: `DG.TriangularBasis.isKProjective`,
`DG.TriangularBasis.hasLiftingProperty`.

The basis is given by its coefficient functions `coeff x j ∈ A`, with `x = Σ_j coeff x j • b_j`
and uniqueness of the coefficients. `DG.FreeBasis A P ι` is a finite homogeneous basis indexed by
a finite type; one whose differential strictly decreases a key `ι → ℤ` is triangular
(`DG.FreeBasis.toTriangular`).
-/

open DirectSum

universe w

namespace DG

noncomputable section

section Generic

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  {P : Type*} [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]

/-- The degree-`0` idempotent cocycle `1` of a dg ring; its left corner `A · 1` is the regular
module. -/
def DGIdempotent.one (A : Type*) [Ring A] [DGAddCommGroup A] [DGRing A] : DGIdempotent A where
  val := 1
  mem_zero := one_mem_grading
  mul_self := one_mul 1
  d_eq_zero := d_one

/-- `d(a • y) = d(a) • y + ι(a) • d(y)` for arbitrary (not necessarily homogeneous) `a`, where
`ι = Shift.twist A 1` is the parity sign `a ↦ (-1)^{|a|} a`. -/
theorem d_smul_twist (a : A) (y : P) : d (a • y) = d a • y + Shift.twist A 1 a • d y := by
  induction a using DG.induction_on with
  | h_zero => simp
  | h_homogeneous a =>
    rename_i i
    rw [d_smul a.2, Shift.twist_of_mem a.2, one_mul, smul_assoc]
  | h_add a a' ha ha' => rw [add_smul, d_add, ha, ha', d_add, map_add, add_smul, add_smul]; abel

omit [DGRing A] in
/-- The homogeneous components of `a • m` for homogeneous `m ∈ Pᵏ`:
`(a • m)_p = a_{p-k} • m`. -/
theorem decompose_smul_of_mem {k : ℤ} {m : P} (hm : m ∈ grading k) (a : A) (p : ℤ) :
    (decompose (grading (M := P)) (a • m) p : P) = (decompose (grading (M := A)) a (p - k) : A) • m := by
  induction a using DG.induction_on with
  | h_zero => simp
  | h_homogeneous a =>
    rename_i i
    have ham := smul_mem_grading a.2 hm
    by_cases hi : i + k = p
    · subst hi
      rw [decompose_of_mem_same _ ham, add_sub_cancel_right, decompose_of_mem_same _ a.2]
    · rw [decompose_of_mem_ne _ ham hi, decompose_of_mem_ne _ a.2 (by omega), zero_smul]
  | h_add a a' ha ha' =>
    rw [add_smul, decompose_add, DirectSum.add_apply, AddMemClass.coe_add, ha, ha', decompose_add,
      DirectSum.add_apply, AddMemClass.coe_add, add_smul]

end Generic

section Basis

variable {A : Type*} [Ring A] {P : Type*} [AddCommGroup P] [DGAddCommGroup P] [Module A P]

variable (A P) in
/-- A finite triangular basis of a dg module `P` over a dg ring `A`: homogeneous elements
`b_0, …, b_{m-1}` (of degrees `deg j`) forming a basis of `P` as a graded `A`-module (with
coefficient functions `coeff`), such that `d(b_j) ∈ span_A {b_l : l < j}`. -/
structure TriangularBasis where
  /-- The number of basis elements. -/
  length : ℕ
  /-- The basis elements. -/
  b : Fin length → P
  /-- Their degrees. -/
  deg : Fin length → ℤ
  b_mem : ∀ j, b j ∈ grading (deg j)
  /-- The coefficients of an element. -/
  coeff : P → Fin length → A
  sum_coeff : ∀ x, ∑ j, coeff x j • b j = x
  coeff_sum : ∀ a : Fin length → A, coeff (∑ j, a j • b j) = a
  coeff_d : ∀ j l, j ≤ l → coeff (d (b j)) l = 0

namespace TriangularBasis

variable (T : TriangularBasis A P)

theorem coeff_add (x y : P) : T.coeff (x + y) = T.coeff x + T.coeff y := by
  conv_lhs => rw [← T.sum_coeff x, ← T.sum_coeff y, ← Finset.sum_add_distrib]
  simp only [← add_smul]
  exact T.coeff_sum (T.coeff x + T.coeff y)

theorem coeff_zero : T.coeff 0 = 0 := by
  have h := T.coeff_sum 0
  simpa using h

theorem coeff_smul (a : A) (x : P) : T.coeff (a • x) = fun j => a * T.coeff x j := by
  conv_lhs => rw [← T.sum_coeff x, Finset.smul_sum]
  simp only [smul_smul]
  exact T.coeff_sum _

theorem coeff_neg (x : P) : T.coeff (-x) = -T.coeff x := by
  have h := T.coeff_add x (-x)
  rw [add_neg_cancel, T.coeff_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem coeff_basis (j : Fin T.length) (a : A) : T.coeff (a • T.b j) = Pi.single j a := by
  have h := T.coeff_sum (Pi.single j a)
  rwa [Finset.sum_eq_single j (fun l _ hl => by rw [Pi.single_eq_of_ne hl, zero_smul])
    (by simp), Pi.single_eq_same] at h

theorem eq_zero_of_coeff (x : P) (h : T.coeff x = 0) : x = 0 := by
  rw [← T.sum_coeff x, h]
  simp

end TriangularBasis

end Basis

section Cells

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  {P : Type*} [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]

namespace TriangularBasis

variable (T : TriangularBasis A P)

omit [DGRing A] in
/-- The coefficient of a homogeneous component: `coeff (x_p) j = (coeff x j)_{p - k_j}`. -/
theorem coeff_decompose (x : P) (p : ℤ) (j : Fin T.length) :
    T.coeff (decompose (grading (M := P)) x p) j =
      decompose (grading (M := A)) (T.coeff x j) (p - T.deg j) := by
  have hx : (decompose (grading (M := P)) x p : P) =
      ∑ l, (decompose (grading (M := A)) (T.coeff x l) (p - T.deg l) : A) • T.b l := by
    conv_lhs => rw [← T.sum_coeff x]
    rw [decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun l _ => decompose_smul_of_mem (T.b_mem l) _ p
  rw [hx, T.coeff_sum]

omit [DGRing A] in
/-- Coefficients of homogeneous elements are homogeneous: `x ∈ Pᵖ ⟹ coeff x j ∈ A^{p - k_j}`. -/
theorem coeff_mem {x : P} {p : ℤ} (hx : x ∈ grading p) (j : Fin T.length) :
    T.coeff x j ∈ grading (p - T.deg j) := by
  have h := T.coeff_decompose x p j
  rw [decompose_of_mem_same _ hx] at h
  rw [h]
  exact (decompose (grading (M := A)) (T.coeff x j) (p - T.deg j)).2

/-- The coefficients of `d x`: `coeff (d x) l = d (coeff x l) + Σ_j ι(coeff x j) coeff (d b_j) l`. -/
theorem coeff_d_apply (x : P) (l : Fin T.length) :
    T.coeff (d x) l =
      d (T.coeff x l) + ∑ j, Shift.twist A 1 (T.coeff x j) * T.coeff (d (T.b j)) l := by
  have hx : d x = ∑ l, (d (T.coeff x l) +
      ∑ j, Shift.twist A 1 (T.coeff x j) * T.coeff (d (T.b j)) l) • T.b l := by
    conv_lhs => rw [← T.sum_coeff x]
    rw [map_sum]
    simp only [d_smul_twist, add_smul, Finset.sum_add_distrib, Finset.sum_smul, mul_smul]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.smul_sum, T.sum_coeff]
  rw [hx, T.coeff_sum]

/-- The members of the filtration: `F_i = {x | coeff x l = 0 for l ≥ i} = span_A {b_l : l < i}`. -/
def F (i : ℕ) : DGSubmodule A P where
  carrier := {x | ∀ l : Fin T.length, i ≤ l.val → T.coeff x l = 0}
  add_mem' {x y} hx hy l hl := by rw [T.coeff_add, Pi.add_apply, hx l hl, hy l hl, add_zero]
  zero_mem' l _ := by rw [T.coeff_zero, Pi.zero_apply]
  smul_mem' a x hx l hl := by
    change (T.coeff (a • x)) l = 0
    rw [T.coeff_smul]
    change a * T.coeff x l = 0
    rw [hx l hl, mul_zero]
  d_mem' {x} hx l hl := by
    rw [T.coeff_d_apply, hx l hl, d_zero, zero_add]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : i ≤ j.val
    · rw [hx j hj, map_zero, zero_mul]
    · rw [T.coeff_d j l (by rw [Fin.le_def]; omega), mul_zero]
  decompose_mem' p {x} hx l hl := by
    rw [T.coeff_decompose, hx l hl, decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]

theorem mem_F {i : ℕ} {x : P} : x ∈ T.F i ↔ ∀ l : Fin T.length, i ≤ l.val → T.coeff x l = 0 :=
  Iff.rfl

theorem basis_mem_F (j : Fin T.length) (a : A) : a • T.b j ∈ T.F (j.val + 1) := by
  intro l hl
  rw [T.coeff_basis, Pi.single_eq_of_ne (by intro h; subst h; omega)]

/-- On `F_{j+1}` the coefficient of `b_j` commutes with `d`. -/
theorem coeff_d_of_mem {j : Fin T.length} {x : P} (hx : x ∈ T.F (j.val + 1)) :
    T.coeff (d x) j = d (T.coeff x j) := by
  rw [T.coeff_d_apply, add_eq_left]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : j.val + 1 ≤ l.val
  · rw [hx l hl, map_zero, zero_mul]
  · rw [T.coeff_d l j (by rw [Fin.le_def]; omega), mul_zero]

/-- The coefficient of `b_j`, twisted by `(-1)^{k_j |c|}`, as an element of the cell
`(A · 1)⟦-k_j⟧`. -/
def πFun (j : Fin T.length) (x : T.F (j.val + 1)) :
    Shift (-T.deg j) (DGIdempotent.one A).LeftCorner :=
  Shift.mk _ ⟨Shift.twist A (-T.deg j) (T.coeff x j), mul_one _⟩

theorem unmk_πFun (j : Fin T.length) (x : T.F (j.val + 1)) :
    ((Shift.unmk _ (T.πFun j x) : (DGIdempotent.one A).LeftCorner) : A) =
      Shift.twist A (-T.deg j) (T.coeff x j) := rfl

/-- The projection `F_{j+1} → F_{j+1} / F_j ≅ (A · 1)⟦-k_j⟧`. -/
def π (j : Fin T.length) :
    T.F (j.val + 1) →ᵈᵍ[A] Shift (-T.deg j) (DGIdempotent.one A).LeftCorner where
  toFun := T.πFun j
  map_add' x y := by
    apply (Shift.unmk _).injective
    apply Subtype.ext
    simp only [map_add, unmk_πFun, DGSubmodule.coe_add, T.coeff_add, Pi.add_apply,
      Submodule.coe_add]
  map_smul' a x := by
    apply (Shift.unmk _).injective
    apply Subtype.ext
    change Shift.twist A (-T.deg j) (T.coeff (a • (x : P)) j) =
      Shift.twist A (-T.deg j) a * Shift.twist A (-T.deg j) (T.coeff x j)
    rw [T.coeff_smul, map_mul]
  map_mem' {p x} hx := by
    rw [Shift.mem_grading_iff', DGIdempotent.LeftCorner.mem_grading_iff, unmk_πFun]
    refine Shift.twist_mem ?_
    have hx' : (x : P) ∈ grading p := hx
    have := T.coeff_mem hx' j
    rwa [sub_eq_add_neg] at this
  map_d' x := by
    apply (Shift.unmk _).injective
    apply Subtype.ext
    change Shift.twist A (-T.deg j) (T.coeff (d (x : P)) j) =
      ((koszulSign (-T.deg j) • d (Shift.unmk _ (T.πFun j x)) : (DGIdempotent.one A).LeftCorner) : A)
    rw [T.coeff_d_of_mem x.2, Submodule.coe_smul_of_tower, DGIdempotent.LeftCorner.coe_d,
      unmk_πFun, Shift.d_twist, smul_smul, ← koszulSign_add, ← two_mul,
      koszulSign_even (even_two_mul _), one_smul]

theorem π_surjective (j : Fin T.length) : Function.Surjective (T.π j) := by
  intro y
  set y' : A := ((Shift.unmk _ y : (DGIdempotent.one A).LeftCorner) : A)
  refine ⟨⟨Shift.twist A (-T.deg j) y' • T.b j, T.basis_mem_F j _⟩, ?_⟩
  apply (Shift.unmk _).injective
  apply Subtype.ext
  change Shift.twist A (-T.deg j) (T.coeff (Shift.twist A (-T.deg j) y' • T.b j) j) = y'
  rw [T.coeff_basis, Pi.single_eq_same, Shift.twist_twist_self]

theorem π_eq_zero_iff (j : Fin T.length) (x : T.F (j.val + 1)) :
    T.π j x = 0 ↔ (x : P) ∈ T.F j.val := by
  constructor
  · intro h l hl
    rcases Nat.eq_or_lt_of_le hl with h' | h'
    · have hlj : l = j := Fin.ext h'.symm
      subst hlj
      have h2 := congrArg (fun y => ((Shift.unmk _ y : (DGIdempotent.one A).LeftCorner) : A)) h
      change Shift.twist A (-T.deg l) (T.coeff x l) = 0 at h2
      rw [← Shift.twist_twist_self (-T.deg l) (T.coeff (x : P) l), h2, map_zero]
    · exact x.2 l h'
  · intro h
    apply (Shift.unmk _).injective
    apply Subtype.ext
    change Shift.twist A (-T.deg j) (T.coeff x j) = 0
    rw [h j le_rfl, map_zero]

/-- **Finite-cell filtration** of a dg module with a finite triangular basis: `F_i = span{b_l : l < i}`,
with subquotients `F_{j+1} / F_j ≅ (A · 1)⟦-k_j⟧`. -/
def finiteCellFiltration : FiniteCellFiltration A P where
  length := T.length
  F := T.F
  mono i i' h x hx l hl := hx l (h.trans hl)
  eq_zero_of_mem_zero x hx := T.eq_zero_of_coeff x (funext fun l => hx l (Nat.zero_le _))
  mem_length x l hl := absurd l.isLt (by omega)
  e _ := DGIdempotent.one A
  shift j := -T.deg j
  π := T.π
  surjective_π := T.π_surjective
  π_eq_zero_iff := T.π_eq_zero_iff

include T in
/-- A dg module with a finite triangular basis is K-projective. -/
theorem isKProjective : IsKProjective.{w} A P := FiniteCellFiltration.isKProjective T.finiteCellFiltration

include T in
/-- A dg module with a finite triangular basis is cofibrant: it has the lifting property against
surjective quasi-isomorphisms. -/
theorem hasLiftingProperty : HasLiftingProperty.{w} A P := FiniteCellFiltration.hasLiftingProperty T.finiteCellFiltration

end TriangularBasis

end Cells
/-! ### Free bases indexed by a finite type, ordered by a key -/

section FreeBasis

variable {A : Type*} [Ring A] {P : Type*} [AddCommGroup P] [DGAddCommGroup P] [Module A P]

variable (A P) in
/-- A finite homogeneous basis of `P` as a graded `A`-module, indexed by a finite type `ι`, with
coefficient functions `coeff`. -/
structure FreeBasis (ι : Type*) [Fintype ι] where
  /-- The basis elements. -/
  b : ι → P
  /-- Their degrees. -/
  deg : ι → ℤ
  b_mem : ∀ i, b i ∈ grading (deg i)
  /-- The coefficients of an element. -/
  coeff : P → ι → A
  sum_coeff : ∀ x, ∑ i, coeff x i • b i = x
  coeff_sum : ∀ a : ι → A, coeff (∑ i, a i • b i) = a

namespace FreeBasis

variable {ι : Type*} [Fintype ι] (B : FreeBasis A P ι)

theorem coeff_add (x y : P) : B.coeff (x + y) = B.coeff x + B.coeff y := by
  conv_lhs => rw [← B.sum_coeff x, ← B.sum_coeff y, ← Finset.sum_add_distrib]
  simp only [← add_smul]
  exact B.coeff_sum (B.coeff x + B.coeff y)

theorem coeff_zero : B.coeff 0 = 0 := by
  have h := B.coeff_sum 0
  simpa using h

/-- The coefficients as an additive map. -/
def coeffHom : P →+ ι → A where
  toFun := B.coeff
  map_zero' := B.coeff_zero
  map_add' := B.coeff_add

theorem coeff_zsmul (k : ℤ) (x : P) : B.coeff (k • x) = k • B.coeff x :=
  map_zsmul B.coeffHom k x

theorem coeff_basis [DecidableEq ι] (i : ι) (a : A) : B.coeff (a • B.b i) = Pi.single i a := by
  have h := B.coeff_sum (Pi.single i a)
  rwa [Finset.sum_eq_single i (fun l _ hl => by rw [Pi.single_eq_of_ne hl, zero_smul])
    (by simp), Pi.single_eq_same] at h

/-- The ordering of `ι` by a key `ι → ℤ`: an enumeration `Fin (card ι) ≃ ι` along which the key
is monotone. -/
def order (key : ι → ℤ) : Fin (Fintype.card ι) ≃ ι :=
  (Tuple.sort (key ∘ (Fintype.equivFin ι).symm)).trans (Fintype.equivFin ι).symm

theorem order_monotone (key : ι → ℤ) : Monotone (key ∘ order key) :=
  Tuple.monotone_sort (key ∘ (Fintype.equivFin ι).symm)

/-- A free basis whose differential strictly decreases a key (`coeff (d b_i) l ≠ 0 ⟹
key l < key i`) is a triangular basis, for the enumeration by increasing key. -/
def toTriangular (key : ι → ℤ) (hkey : ∀ i l, B.coeff (d (B.b i)) l ≠ 0 → key l < key i) :
    TriangularBasis A P where
  length := Fintype.card ι
  b j := B.b (order key j)
  deg j := B.deg (order key j)
  b_mem j := B.b_mem _
  coeff x j := B.coeff x (order key j)
  sum_coeff x := by
    rw [← B.sum_coeff x]
    conv_rhs => rw [← (order key).sum_comp]
    rw [B.sum_coeff]
  coeff_sum a := by
    have h : ∑ j, a j • B.b (order key j) = ∑ i, a ((order key).symm i) • B.b i := by
      rw [← (order key).sum_comp]
      simp
    funext j
    rw [h, B.coeff_sum, Equiv.symm_apply_apply]
  coeff_d j l hjl := by
    by_contra h
    have h1 := hkey _ _ h
    have h2 := order_monotone key hjl
    simp only [Function.comp_apply] at h2
    omega

theorem toTriangular_length (key : ι → ℤ)
    (hkey : ∀ i l, B.coeff (d (B.b i)) l ≠ 0 → key l < key i) :
    (B.toTriangular key hkey).length = Fintype.card ι := rfl

end FreeBasis

end FreeBasis

end

end DG
