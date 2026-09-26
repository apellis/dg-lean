import DG.Bigraded.Basic
import DG.Positive.Basic

/-!
# Positive bigraded dg rings

A *positive bigraded* dg ring (Roadmap, item 7.2) is a dg ring `A` with an internal grading
making it a bigraded dg ring (`[DG.InternalGrading A] [DG.BigradedDGRing A]`) which is positive
in the sense of Schnürer (`DG.IsPositive A`: `Aⁿ = 0` for `n < 0`, `A⁰` semisimple, `d (A⁰) = 0`).
Positivity only involves the cohomological grading, so no new definition is needed: a positive
bigraded dg ring is given by the hypotheses `[InternalGrading A] [BigradedDGRing A]` and
`hA : IsPositive A`.

The degree-`0` part `A⁰ = ⨁ k, A^{0,k}` of a bigraded dg ring is a weight-graded ring: its
weight components are the bihomogeneous components `A^{0,k} = A⁰ ∩ A⟨k⟩`.

* `DG.degreeZeroWGrading A k`: the weight components of `A⁰` (`DG.degreeZeroSubring A`), with
  the `GradedRing` instance `DG.degreeZeroWGrading.gradedRing`.
* `DG.mem_degreeZeroWGrading_iff`: `A⁰ ∩ A⟨k⟩` is the bihomogeneous component
  `DG.bigrading A (0, k)`.
-/

open DirectSum

namespace DG

variable (A : Type*) [Ring A] [DGAddCommGroup A] [DGRing A] [InternalGrading A]

/-- The weight grading of the degree-`0` part `A⁰` of a dg ring with an internal grading:
`A⁰⟨k⟩ = A⁰ ∩ A⟨k⟩`. -/
def degreeZeroWGrading (k : ℤ) : AddSubgroup (degreeZeroSubring A) :=
  (wgrading (M := A) k).comap (degreeZeroSubring A).subtype.toAddMonoidHom

variable {A}

theorem mem_degreeZeroWGrading_iff {k : ℤ} {a : degreeZeroSubring A} :
    a ∈ degreeZeroWGrading A k ↔ (a : A) ∈ bigrading A (0, k) :=
  ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩

variable (A)

theorem isInternal_degreeZeroWGrading : DirectSum.IsInternal (degreeZeroWGrading A) :=
  isInternal_comap _ _ Subtype.val_injective fun k a =>
    ⟨⟨_, decompose_wgrading_mem_grading (M := A) a.2 k⟩, rfl⟩

/-- The decomposition `A⁰ = ⨁ k, A⁰⟨k⟩`. -/
noncomputable instance degreeZeroWGrading.decomposition :
    Decomposition (degreeZeroWGrading A) :=
  (isInternal_degreeZeroWGrading A).chooseDecomposition

variable {A}

/-- The weight components of an element of `A⁰` are its weight components in `A`. -/
theorem coe_decompose_degreeZeroWGrading (a : degreeZeroSubring A) (k : ℤ) :
    ((decompose (degreeZeroWGrading A) a k : degreeZeroSubring A) : A) =
      decompose (wgrading (M := A)) (a : A) k := by
  letI : Decomposition fun k =>
      (wgrading (M := A) k).comap (degreeZeroSubring A).subtype.toAddMonoidHom :=
    degreeZeroWGrading.decomposition A
  exact coe_decompose_comap _ (degreeZeroSubring A).subtype.toAddMonoidHom a k

variable (A) [BigradedDGRing A]

instance degreeZeroWGrading.gradedMonoid : SetLike.GradedMonoid (degreeZeroWGrading A) where
  one_mem := one_mem_wgrading (A := A)
  mul_mem _ _ _ _ ha hb := mul_mem_wgrading (A := A) ha hb

/-- The degree-`0` part `A⁰` of a bigraded dg ring is a weight-graded ring. -/
noncomputable instance degreeZeroWGrading.gradedRing : GradedRing (degreeZeroWGrading A) :=
  { degreeZeroWGrading.gradedMonoid A, degreeZeroWGrading.decomposition A with }

end DG
