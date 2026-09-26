import DG.Algebra.Cohomology
import DG.Algebra.Constructions
import DG.Algebra.TensorProduct
import DG.Graded.Commutative

/-!
# Commutative dg algebras

A *commutative dg algebra* (CDGA) is a dg algebra whose grading is strictly graded commutative:
for homogeneous `a ∈ Aⁱ` and `b ∈ Aʲ`,

  `a * b = (-1)^(i * j) • (b * a)`,  and  `a * a = 0` if `i` is odd.

This file defines the predicate `DG.IsCDGA A` on a dg ring `A` and proves the basic closure
properties.

## Main definitions and results

* `DG.IsCDGA A`: the dg ring `A` is strictly graded commutative. The condition only involves the
  multiplication and the grading, so it does not depend on a choice of ground ring: for a dg
  `R`-algebra `A`, `IsCDGA A` is equivalent to `IsGradedCommStrict (DGAlgebra.gradingSubmodule R A)`
  (`DG.isCDGA_iff`), and the latter is available as an instance
  (`DG.IsCDGA.isGradedCommStrict`).
* `DG.IsGradedCommStrict.of_invertible_two`, `DG.isGradedCommStrict_iff_isGradedComm`: if `2` is
  invertible in the ground ring, graded commutativity is automatically strict; hence
  `DG.IsCDGA.of_isGradedComm` for dg algebras over such rings.
* `DG.d_mul_self_of_odd`: in a graded commutative dg algebra (strict or not) the differential of
  the square of a homogeneous element of odd degree vanishes; `DG.IsCDGA.d_mul_self_of_even`
  and `DG.IsCDGA.d_pow_of_even`: for `a` of even degree, `d (a * a) = 2 • (a * d a)` and
  `d (a ^ k) = k • (a ^ (k - 1) * d a)`.
* `DG.DGSubring.isCDGA`: a dg subring of a CDGA is a CDGA; in particular the cocycles `Z(A)` form
  a strictly graded commutative dg subring (`DG.isCDGA_cocyclesDGSubring`).
* `DG.Cohomology.isCDGA`: the cohomology ring `H(A)` of a CDGA is strictly graded commutative.
* `DG.GradedTensorProduct.isCDGA`: the graded tensor product of two CDGAs over `R` is a CDGA.

The Koszul complex is a CDGA: `DG.KoszulComplex.isCDGA` (in `DG.Examples.Koszul`).

## Choice of definition

We take the strict notion (`a * a = 0` for `a` of odd degree) as the definition of a CDGA: it is
the notion satisfied by exterior algebras, Koszul complexes, cochain algebras of Lie algebras and
free graded commutative algebras over arbitrary commutative rings. It differs from plain graded
commutativity only in the presence of `2`-torsion (`DG.IsCDGA.of_isGradedComm`).
-/

open DirectSum
open scoped TensorProduct

namespace DG

/-! ### Strict versus non-strict graded commutativity -/

section Invertible

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (𝒜 : ℤ → Submodule R A)

/-- If `2` is invertible in `R`, graded commutativity is automatically strict. -/
theorem IsGradedCommStrict.of_invertible_two [Invertible (2 : R)] [IsGradedComm 𝒜] :
    IsGradedCommStrict 𝒜 where
  mul_self_of_odd {i a} ha hi := by
    have h := IsGradedComm.two_nsmul_mul_self_of_odd ha hi
    rw [two_nsmul, ← two_smul R] at h
    rw [← one_smul R (a * a), ← invOf_mul_self (2 : R), mul_smul, h, smul_zero]

/-- If `2` is invertible in `R`, strict and non-strict graded commutativity agree. -/
theorem isGradedCommStrict_iff_isGradedComm [Invertible (2 : R)] :
    IsGradedCommStrict 𝒜 ↔ IsGradedComm 𝒜 :=
  ⟨fun _ => inferInstance, fun _ => IsGradedCommStrict.of_invertible_two 𝒜⟩

end Invertible

/-! ### Commutative dg algebras -/

/-- A *commutative dg algebra*: a dg ring `A` which is strictly graded commutative, i.e.
`a * b = (-1)^(i * j) • (b * a)` for `a ∈ Aⁱ`, `b ∈ Aʲ`, and `a * a = 0` for `a` homogeneous of
odd degree. For a dg `R`-algebra this is `IsGradedCommStrict (DGAlgebra.gradingSubmodule R A)`
(`DG.isCDGA_iff`). -/
class IsCDGA (A : Type*) [Ring A] [DGAddCommGroup A] [DGRing A] : Prop where
  mul_comm_of_mem' : ∀ {i j : ℤ} {a b : A}, a ∈ grading i → b ∈ grading j →
    a * b = koszulSign (i * j) • (b * a)
  mul_self_of_odd' : ∀ {i : ℤ} {a : A}, a ∈ grading i → Odd i → a * a = 0

namespace IsCDGA

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] [IsCDGA A]

/-- Homogeneous elements of a CDGA commute up to the Koszul sign. -/
theorem mul_comm_of_mem {i j : ℤ} {a b : A} (ha : a ∈ grading i) (hb : b ∈ grading j) :
    a * b = koszulSign (i * j) • (b * a) :=
  IsCDGA.mul_comm_of_mem' ha hb

/-- Homogeneous elements of odd degree of a CDGA square to zero. -/
theorem mul_self_of_odd {i : ℤ} {a : A} (ha : a ∈ grading i) (hi : Odd i) : a * a = 0 :=
  IsCDGA.mul_self_of_odd' ha hi

/-- A CDGA over `R` is strictly graded commutative as a graded `R`-algebra. -/
instance isGradedCommStrict (R : Type*) [CommRing R] [Algebra R A] [DGAlgebra R A] :
    IsGradedCommStrict (DGAlgebra.gradingSubmodule R A) where
  mul_comm_of_mem ha hb := mul_comm_of_mem ha hb
  mul_self_of_odd ha hi := mul_self_of_odd ha hi

/-- Homogeneous elements of even degree of a CDGA are central. -/
theorem commute_of_even {i : ℤ} {a : A} (ha : a ∈ grading i) (hi : Even i) (b : A) :
    Commute a b :=
  IsGradedComm.commute_of_even (𝒜 := DGAlgebra.gradingSubmodule ℤ A) ha hi b

/-- In a CDGA, a homogeneous element commutes with its differential. -/
theorem commute_d {i : ℤ} {a : A} (ha : a ∈ grading i) : Commute a (d a) := by
  rw [Commute, SemiconjBy, mul_comm_of_mem ha (d_mem ha),
    koszulSign_even (Int.even_mul_succ_self i), one_smul]

/-- For `a` of even degree in a CDGA, `d (a * a) = 2 • (a * d a)`. -/
theorem d_mul_self_of_even {i : ℤ} {a : A} (ha : a ∈ grading i) (hi : Even i) :
    d (a * a) = 2 • (a * d a) := by
  rw [d_mul_of_even ha hi, (commute_d ha).eq, two_nsmul]

/-- The power rule in a CDGA: for `a` of even degree, `d (a ^ k) = k • (a ^ (k - 1) * d a)`. -/
theorem d_pow_of_even {i : ℤ} {a : A} (ha : a ∈ grading i) (hi : Even i) (k : ℕ) :
    d (a ^ k) = k • (a ^ (k - 1) * d a) :=
  d_pow_of_even_of_commute ha hi (commute_d ha) k

end IsCDGA

section Ground

variable (R : Type*) {A : Type*} [CommRing R] [Ring A] [Algebra R A] [DGAddCommGroup A]
  [DGRing A] [DGAlgebra R A]

/-- A dg `R`-algebra whose grading is strictly graded commutative is a CDGA. -/
theorem IsCDGA.of_isGradedCommStrict [IsGradedCommStrict (DGAlgebra.gradingSubmodule R A)] :
    IsCDGA A where
  mul_comm_of_mem' ha hb := IsGradedComm.mul_comm_of_mem (𝒜 := DGAlgebra.gradingSubmodule R A) ha hb
  mul_self_of_odd' ha hi :=
    IsGradedCommStrict.mul_self_of_odd (𝒜 := DGAlgebra.gradingSubmodule R A) ha hi

/-- A dg `R`-algebra is a CDGA if and only if its grading is strictly graded commutative. -/
theorem isCDGA_iff : IsCDGA A ↔ IsGradedCommStrict (DGAlgebra.gradingSubmodule R A) :=
  ⟨fun _ => inferInstance, fun _ => IsCDGA.of_isGradedCommStrict R⟩

/-- Over a ground ring in which `2` is invertible, a graded commutative dg algebra is a CDGA. -/
theorem IsCDGA.of_isGradedComm [Invertible (2 : R)]
    [IsGradedComm (DGAlgebra.gradingSubmodule R A)] : IsCDGA A :=
  haveI := IsGradedCommStrict.of_invertible_two (DGAlgebra.gradingSubmodule R A)
  IsCDGA.of_isGradedCommStrict R

/-- In a graded commutative dg algebra (not necessarily strict), `d (a * a) = 0` for every
homogeneous element `a` of odd degree: `d (a * a) = d a * a - a * d a` and `a` commutes with `d a`,
which has even degree. -/
theorem d_mul_self_of_odd [IsGradedComm (DGAlgebra.gradingSubmodule R A)] {i : ℤ} {a : A}
    (ha : a ∈ grading i) (hi : Odd i) : d (a * a) = 0 := by
  rw [d_mul_of_odd ha hi,
    IsGradedComm.mul_comm_of_mem (𝒜 := DGAlgebra.gradingSubmodule R A) ha (d_mem ha),
    koszulSign_even (Int.even_mul_succ_self i), one_smul, sub_self]

end Ground

/-! ### Sub-CDGAs and cocycles -/

/-- A dg subring of a CDGA is a CDGA. -/
instance DGSubring.isCDGA {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] [IsCDGA A]
    (S : DGSubring A) : IsCDGA S where
  mul_comm_of_mem' {i j a b} ha hb := Subtype.ext <| by
    rw [Units.smul_def, AddSubgroupClass.coe_zsmul, MulMemClass.coe_mul, MulMemClass.coe_mul,
      ← Units.smul_def]
    exact IsCDGA.mul_comm_of_mem (A := A) ha hb
  mul_self_of_odd' ha hi := Subtype.ext <| by
    rw [MulMemClass.coe_mul, ZeroMemClass.coe_zero]
    exact IsCDGA.mul_self_of_odd (A := A) ha hi

/-- The cocycles `Z(A) = ker d` of a CDGA form a CDGA (with zero differential). -/
theorem isCDGA_cocyclesDGSubring (A : Type*) [Ring A] [DGAddCommGroup A] [DGRing A] [IsCDGA A] :
    IsCDGA (cocyclesDGSubring A) :=
  inferInstance

/-! ### Cohomology -/

namespace Cohomology

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The cohomology ring `H(A)` of a CDGA is a CDGA (with zero differential): it is strictly
graded commutative. -/
instance isCDGA [IsCDGA A] : IsCDGA (Cohomology A) where
  mul_comm_of_mem' {i j x y} hx hy := by
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    induction x using cohomology.induction_on with
    | h a =>
    induction y using cohomology.induction_on with
    | h b =>
    rw [of_mul_of, of_mul_of, cohomology.smulHom_mk_mk, cohomology.smulHom_mk_mk,
      Units.smul_def, ← map_zsmul, ← map_zsmul]
    refine DirectSum.of_eq_of_gradedMonoid_eq (Sigma.ext (add_comm i j) ?_)
    refine cohomology.mk_heq_mk (add_comm i j) ?_
    rw [AddSubgroup.coe_zsmul, cocycles.coe_smulHom_apply, cocycles.coe_smulHom_apply,
      smul_eq_mul, smul_eq_mul, ← Units.smul_def]
    exact IsCDGA.mul_comm_of_mem (cocycles.mem_grading a) (cocycles.mem_grading b)
  mul_self_of_odd' {i x} hx hi := by
    obtain ⟨x, rfl⟩ := hx
    induction x using cohomology.induction_on with
    | h a =>
    rw [of_mul_of, cohomology.smulHom_mk_mk]
    have h : cocycles.smulHom i i a a = 0 := Subtype.ext <| by
      rw [cocycles.coe_smulHom_apply, smul_eq_mul, ZeroMemClass.coe_zero]
      exact IsCDGA.mul_self_of_odd (cocycles.mem_grading a) hi
    rw [h, map_zero, map_zero]

end Cohomology

/-! ### Tensor products -/

namespace GradedTensorProduct

open _root_.GradedTensorProduct

variable {R A B : Type*} [CommRing R]
  [Ring A] [Algebra R A] [DGAddCommGroup A] [DGRing A] [DGAlgebra R A]
  [Ring B] [Algebra R B] [DGAddCommGroup B] [DGRing B] [DGAlgebra R B]

local notation "𝒜" => DGAlgebra.gradingSubmodule R A
local notation "ℬ" => DGAlgebra.gradingSubmodule R B

private theorem ks_eq {m n : ℤ} (h : Even (m - n)) : koszulSign m = koszulSign n :=
  (Int.negOnePow_eq_iff m n).mpr h

variable [IsCDGA A] [IsCDGA B]

/-- Homogeneous elements of the graded tensor product of two CDGAs commute up to the Koszul
sign. -/
theorem mul_comm_of_mem {n m : ℤ} {x y : 𝒜 ᵍ⊗[R] ℬ} (hx : x ∈ DG.grading n)
    (hy : y ∈ DG.grading m) :
    x * y = koszulSign (n * m) • (y * x) := by
  refine GradedTensorProduct.grading_induction 𝒜 ℬ hx
    (motive := fun x => x * y = koszulSign (n * m) • (y * x)) (by simp) ?_ ?_
  · intro i j a b hij
    refine GradedTensorProduct.grading_induction 𝒜 ℬ hy
      (motive := fun y => ((a : A) ᵍ⊗ₜ[R] (b : B) : 𝒜 ᵍ⊗[R] ℬ) * y =
        koszulSign (n * m) • (y * ((a : A) ᵍ⊗ₜ[R] (b : B)))) (by simp) ?_ ?_
    · intro i' j' a' b' hij'
      subst hij hij'
      rw [GradedTensorProduct.tmul_mul_tmul 𝒜 ℬ _ b.2 a'.2,
        GradedTensorProduct.tmul_mul_tmul 𝒜 ℬ _ b'.2 a.2,
        IsCDGA.mul_comm_of_mem (A := A) a'.2 a.2, IsCDGA.mul_comm_of_mem (A := B) b'.2 b.2,
        GradedTensorProduct.koszulSign_smul_tmul, GradedTensorProduct.tmul_koszulSign_smul,
        smul_smul, smul_smul, smul_smul, ← koszulSign_add, ← koszulSign_add,
        ← koszulSign_add]
      congr 1
      exact ks_eq ⟨-(i * i' + i * j' + j * j'), by ring⟩
    · intro y y' hy hy'
      rw [mul_add, add_mul, hy, hy', smul_add]
  · intro x x' hx hx'
    rw [add_mul, mul_add, hx, hx', smul_add]

/-- The graded tensor product of two CDGAs is a CDGA. -/
instance isCDGA : IsCDGA (𝒜 ᵍ⊗[R] ℬ) where
  mul_comm_of_mem' hx hy := mul_comm_of_mem hx hy
  mul_self_of_odd' {n x} hx hn := by
    suffices h : x ∈ GradedTensorProduct.grading 𝒜 ℬ n ∧ x * x = 0 from h.2
    refine GradedTensorProduct.grading_induction 𝒜 ℬ hx
      (motive := fun x => x ∈ GradedTensorProduct.grading 𝒜 ℬ n ∧ x * x = 0)
      ⟨zero_mem _, mul_zero 0⟩ ?_ ?_
    · intro i j a b hij
      refine ⟨GradedTensorProduct.tmul_mem_of_eq 𝒜 ℬ hij a.2 b.2, ?_⟩
      rw [GradedTensorProduct.tmul_mul_tmul 𝒜 ℬ _ b.2 a.2]
      rcases Int.even_or_odd i with hi | hi
      · have hj : Odd j := by
          rw [← hij] at hn
          exact (Int.odd_add'.mp hn).mpr hi
        rw [IsCDGA.mul_self_of_odd (A := B) b.2 hj, GradedTensorProduct.tmul_zero, smul_zero]
      · rw [IsCDGA.mul_self_of_odd (A := A) a.2 hi, GradedTensorProduct.zero_tmul, smul_zero]
    · rintro x y ⟨hx, hxx⟩ ⟨hy, hyy⟩
      refine ⟨add_mem hx hy, ?_⟩
      have hxy := mul_comm_of_mem (R := R) (A := A) (B := B) hx hy
      rw [koszulSign_odd (hn.mul hn), Units.neg_smul, one_smul] at hxy
      rw [add_mul, mul_add, mul_add, hxx, hyy, hxy]
      abel

end GradedTensorProduct

end DG
