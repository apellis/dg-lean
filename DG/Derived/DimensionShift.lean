/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DG.Derived.ShortExactTriangle
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Cohomological dimension shift for Webster's derived tensor calculation

In the proof of (6.21) in Lemma 6.8, Webster uses the cohomology long exact sequence
for a triangle obtained by applying the derived braid functor to a short exact sequence.
Concentration in degree zero for the first two terms
and a monomorphism on their degree-zero cohomology imply concentration in degree zero
for the third term. Cohomology takes values in modules over the chosen scalar ring.

Reference: B. Webster, *Knot invariants and higher representation theory*,
[arXiv:1309.3796v2](https://arxiv.org/abs/1309.3796v2), Lemma 6.8, proof of (6.21).
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DG.DerivedCategory

universe w v u r

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [HasDerivedCategory.{w, v} A]
  (R : Type r) [CommRing R] [Algebra R A] [DGAlgebra R A]

noncomputable local instance : (homologyFunctor (A := A) R 0).ShiftSequence ℤ := by
  letI : (HomotopyCategory.homologyFunctor.{v} R A 0).ShiftSequence ℤ := by
    change (HomotopyCategory.forget.{v} R A ⋙
      _root_.HomotopyCategory.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) 0).ShiftSequence ℤ
    infer_instance
  exact Functor.ShiftSequence.induced (homologyFunctorFactorsh R 0) ℤ
    (homologyFunctor R) (homologyFunctorFactorsh R)

/-- Dimension shift for Webster, arXiv:1309.3796v2, Lemma 6.8, proof of (6.21). A
triangle with the first two terms concentrated in degree zero has its third term concentrated
in degree zero when the induced map in degree zero is a monomorphism. -/
theorem isZero_homology_obj₃_of_concentrated_triangle
    (T : Triangle (DerivedCategory.{w, v} A)) (hT : T ∈ distTriang (DerivedCategory.{w, v} A))
    (hK : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor R n).obj T.obj₁))
    (hP : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor R n).obj T.obj₂))
    (h₀ : Mono ((homologyFunctor R 0).map T.mor₁))
    (n : ℤ) (hn : n ≠ 0) : IsZero ((homologyFunctor R n).obj T.obj₃) := by
  let F := homologyFunctor (A := A) R 0
  have e (j : ℤ) : F.shift j = homologyFunctor R j := rfl
  rw [← e]
  apply (F.homologySequence_exact₃ T hT n (n + 1) rfl).isZero_X₂
  · change (F.shift n).map T.mor₂ = 0
    rw [e]
    exact (hP n hn).eq_of_src _ _
  · change F.homologySequenceδ T n (n + 1) rfl = 0
    by_cases h : n + 1 = 0
    · apply (F.homologySequence_mono_shift_map_mor₁_iff T hT n (n + 1) rfl).1
      rwa [e, h]
    · have h' : IsZero ((F.shift (n + 1)).obj T.obj₁) := by rw [e]; exact hK _ h
      exact h'.eq_of_tgt _ _

end DG.DerivedCategory

namespace DG.DerivedCategory

universe w v u r

variable {A B : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [HasDerivedCategory.{w, v} A]
  [Ring B] [DGAddCommGroup B] [DGRing B] [HasDerivedCategory.{w, v} B]
  (R : Type r) [CommRing R] [Algebra R A] [DGAlgebra R A]

/-- Dimension shift for the image of a short exact sequence under a triangulated functor.
This is the cohomological implication in the proof of (6.21) in Webster's Lemma 6.8. -/
theorem isZero_homology_obj_of_shortExact (F : DerivedCategory.{w, v} B ⥤ DerivedCategory.{w, v} A)
    [F.CommShift ℤ] [F.IsTriangulated] (S : ShortComplex (DGModuleCat.{v} B)) (hS : S.ShortExact)
    (hK : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor R n).obj (F.obj (Q.obj S.X₁))))
    (hP : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor R n).obj (F.obj (Q.obj S.X₂))))
    (h₀ : Mono ((homologyFunctor R 0).map (F.map (Q.map S.f))))
    (n : ℤ) (hn : n ≠ 0) : IsZero ((homologyFunctor R n).obj (F.obj (Q.obj S.X₃))) := by
  obtain ⟨δ, hT⟩ := exists_distinguished_of_shortExact S hS
  exact isZero_homology_obj₃_of_concentrated_triangle R _ (F.map_distinguished _ hT) hK hP h₀ n hn

end DG.DerivedCategory
