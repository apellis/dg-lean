import Mathlib.RingTheory.GradedAlgebra.Basic
import DG.Basic

/-!
# Graded commutativity

For a `ℤ`-graded `R`-algebra `A` with grading `𝒜 : ℤ → Submodule R A`, this file defines the
predicate `DG.IsGradedComm 𝒜`, graded commutativity (also called supercommutativity or
commutativity in the graded sense): for homogeneous elements `a ∈ 𝒜 i` and `b ∈ 𝒜 j`,

  `a * b = (-1)^(i * j) • (b * a)`,

with the sign written `koszulSign (i * j) • _` (`DG.koszulSign n = Int.negOnePow n : ℤˣ`).

## Main definitions and results

* `DG.IsGradedComm 𝒜`: the graded commutativity predicate.
* `DG.IsGradedCommStrict 𝒜`: graded commutativity together with `a * a = 0` for every
  homogeneous `a` of odd degree (the "strict" version; the two differ only in the presence of
  `2`-torsion).
* `DG.IsGradedComm.mem_center_of_even`: homogeneous elements of even degree are central.
* `DG.IsGradedComm.two_nsmul_mul_self_of_odd`: for `a` homogeneous of odd degree,
  `2 • (a * a) = 0`.
* `DG.IsGradedCommStrict.of_noZeroSMulDivisors`: if `A` has no `2`-torsion (more precisely,
  `NoZeroSMulDivisors ℕ A`), graded commutativity implies strict graded commutativity.
* `DG.map_mul_of_homogeneous`: an additive map out of a graded algebra is multiplicative as soon
  as it is multiplicative on pairs of homogeneous elements.

The predicate only refers to the family `𝒜` and the multiplication; the consequences that
involve arbitrary (non-homogeneous) elements need `[GradedAlgebra 𝒜]`.
-/

namespace DG

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable (𝒜 : ℤ → Submodule R A)

/-- An additive map out of a graded algebra is multiplicative if it is multiplicative on pairs of
homogeneous elements. -/
theorem map_mul_of_homogeneous [GradedAlgebra 𝒜] {B F : Type*} [NonUnitalNonAssocSemiring B]
    [FunLike F A B] [AddMonoidHomClass F A B] (f : F)
    (h : ∀ {i j : ℤ} (a : 𝒜 i) (b : 𝒜 j), f (a * b) = f a * f b) (x y : A) :
    f (x * y) = f x * f y := by
  refine DirectSum.Decomposition.inductionOn 𝒜
    (motive := fun x => ∀ y, f (x * y) = f x * f y) ?_ ?_ ?_ x y
  · intro y
    rw [zero_mul, map_zero, zero_mul]
  · intro i a
    refine DirectSum.Decomposition.inductionOn 𝒜
      (motive := fun y => f (a * y) = f a * f y) ?_ ?_ ?_
    · show f (a * 0) = f a * f 0
      rw [mul_zero, map_zero, mul_zero]
    · intro j b
      exact h a b
    · intro y y' hy hy'
      show f (a * (y + y')) = f a * f (y + y')
      rw [mul_add, map_add, hy, hy', map_add, mul_add]
  · intro x x' hx hx' y
    rw [add_mul, map_add, hx, hx', map_add, add_mul]

/-- A `ℤ`-graded algebra is *graded commutative* if `a * b = (-1)^(i * j) • (b * a)` for all
homogeneous elements `a` of degree `i` and `b` of degree `j`. -/
class IsGradedComm : Prop where
  /-- Homogeneous elements commute up to the Koszul sign. -/
  mul_comm_of_mem : ∀ {i j : ℤ} {a b : A}, a ∈ 𝒜 i → b ∈ 𝒜 j →
    a * b = koszulSign (i * j) • (b * a)

/-- A `ℤ`-graded algebra is *strictly graded commutative* if it is graded commutative and every
homogeneous element of odd degree squares to zero. -/
class IsGradedCommStrict : Prop extends IsGradedComm 𝒜 where
  /-- Homogeneous elements of odd degree square to zero. -/
  mul_self_of_odd : ∀ {i : ℤ} {a : A}, a ∈ 𝒜 i → Odd i → a * a = 0

namespace IsGradedComm

variable {𝒜} [IsGradedComm 𝒜]

theorem mul_comm_of_mem' {i j : ℤ} {a b : A} (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 j) :
    b * a = koszulSign (i * j) • (a * b) := by
  rw [mul_comm_of_mem ha hb, smul_smul, Int.units_mul_self, one_smul]

theorem mul_comm_of_mem_of_even {i j : ℤ} {a b : A} (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 j)
    (h : Even (i * j)) : a * b = b * a := by
  rw [mul_comm_of_mem ha hb, koszulSign_even h, one_smul]

theorem mul_comm_of_mem_of_odd {i j : ℤ} {a b : A} (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 j)
    (h : Odd (i * j)) : a * b = -(b * a) := by
  rw [mul_comm_of_mem ha hb, koszulSign_odd h, Units.neg_smul, one_smul]

/-- Two homogeneous elements commute when one of them has even degree. -/
theorem mul_comm_of_mem_of_even_left {i j : ℤ} {a b : A} (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 j)
    (hi : Even i) : a * b = b * a :=
  mul_comm_of_mem_of_even ha hb (hi.mul_right j)

/-- Two homogeneous elements anticommute when both have odd degree. -/
theorem mul_comm_of_mem_of_odd_of_odd {i j : ℤ} {a b : A} (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 j)
    (hi : Odd i) (hj : Odd j) : a * b = -(b * a) :=
  mul_comm_of_mem_of_odd ha hb (hi.mul hj)

/-- A homogeneous element of odd degree anticommutes with itself: `a * a = -(a * a)`. -/
theorem mul_self_eq_neg_of_odd {i : ℤ} {a : A} (ha : a ∈ 𝒜 i) (hi : Odd i) :
    a * a = -(a * a) :=
  mul_comm_of_mem_of_odd_of_odd ha ha hi hi

/-- The square of a homogeneous element of odd degree is `2`-torsion. -/
theorem two_nsmul_mul_self_of_odd {i : ℤ} {a : A} (ha : a ∈ 𝒜 i) (hi : Odd i) :
    2 • (a * a) = 0 := by
  rw [two_nsmul, ← sub_neg_eq_add, ← mul_self_eq_neg_of_odd ha hi, sub_self]

/-- In a graded commutative algebra, every homogeneous element of even degree is central. -/
theorem mem_center_of_even [GradedAlgebra 𝒜] {i : ℤ} {a : A} (ha : a ∈ 𝒜 i) (hi : Even i) :
    a ∈ Subalgebra.center R A := by
  rw [Subalgebra.mem_center_iff]
  refine DirectSum.Decomposition.inductionOn 𝒜 ?_ ?_ ?_
  · simp
  · intro j b
    exact (mul_comm_of_mem_of_even_left ha b.2 hi).symm
  · intro b c hb hc
    rw [add_mul, mul_add, hb, hc]

/-- In a graded commutative algebra, a homogeneous element of even degree commutes with every
element. -/
theorem commute_of_even [GradedAlgebra 𝒜] {i : ℤ} {a : A} (ha : a ∈ 𝒜 i) (hi : Even i)
    (b : A) : Commute a b :=
  (Subalgebra.mem_center_iff.mp (mem_center_of_even ha hi) b).symm

end IsGradedComm

namespace IsGradedCommStrict

variable {𝒜}

/-- Without `2`-torsion, graded commutativity is automatically strict. -/
theorem of_noZeroSMulDivisors [IsGradedComm 𝒜] [NoZeroSMulDivisors ℕ A] :
    IsGradedCommStrict 𝒜 where
  mul_self_of_odd ha hi := by
    have h := IsGradedComm.two_nsmul_mul_self_of_odd ha hi
    rcases smul_eq_zero.mp h with h | h
    · exact absurd h two_ne_zero
    · exact h

end IsGradedCommStrict

end DG
