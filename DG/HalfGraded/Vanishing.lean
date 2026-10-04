import DG.HalfGraded.SuperK0Linear

/-!
# Vanishing for half-graded dg rings with a contracting element

Let `H` be a half-graded dg ring with parameter `k` such that `hd x = 1` for some `x`. Comparing
components, the `(-k, 1̄)`-component `y` of `x` also satisfies `hd y = 1`
(`DG.HalfGradedDGRing.exists_mem_hd_eq_one`). Placed in cohomological degree `-1` and weight `0`
of the regraded ring, `y` is an endomorphism `h` of every object of the weight dg category `C_H`
with `d h = 1`, a contracting homotopy for every dg module over `C_H`:
`d (h • m) = m` for every cocycle `m`. Hence

* every dg module over `C_H` is acyclic (`DG.HalfGradedDGRing.isAcyclic_of_hd_eq_one`);
* every object of `D(C_H)` is zero (`DG.HalfGradedDGRing.isZero_of_hd_eq_one`);
* `K₀(D(C_H)^c)` and the compact super Grothendieck group `SuperK0c H` vanish
  (`DG.HalfGradedDGRing.compactK0_subsingleton`, `DG.HalfGradedDGRing.superK0c_subsingleton`).

This is the half-graded form of `D(A) = 0` when `d x = 1` for some `x`.
-/

open CategoryTheory Limits DirectSum

universe w' w u

noncomputable section

namespace DG

namespace HalfGradedDGRing

variable {A : Type u} [Ring A] {k : ℤ} (H : HalfGradedDGRing A k)

/-- `hd` maps the `p`-component to the `(p + (k, 1̄))`-component. -/
theorem decompose_hd (x : A) (p : ℤ × ZMod 2) :
    (decompose H.hgrading (H.hd x) (p + (k, 1)) : A) = H.hd (decompose H.hgrading x p) := by
  induction x using DirectSum.Decomposition.inductionOn H.hgrading with
  | zero => simp
  | @homogeneous q m =>
    obtain ⟨x, hx⟩ := m
    obtain ⟨q₁, q₂⟩ := q
    have hdx : H.hd x ∈ H.hgrading ((q₁, q₂) + (k, 1)) := H.hd_mem hx
    change (decompose H.hgrading (H.hd x) (p + (k, 1)) : A) = H.hd (decompose H.hgrading x p)
    by_cases hq : (q₁, q₂) = p
    · subst hq
      rw [decompose_of_mem_same _ hdx, decompose_of_mem_same _ hx]
    · have hq' : (q₁, q₂) + (k, 1) ≠ p + (k, 1) := fun h => hq (add_right_cancel h)
      rw [decompose_of_mem_ne _ hdx hq', decompose_of_mem_ne _ hx hq, map_zero]
  | add x y hx hy => rw [map_add, decompose_add, add_apply, AddSubgroup.coe_add, hx, hy,
      decompose_add, add_apply, AddSubgroup.coe_add, map_add]

/-- If `hd x = 1`, then the `(-k, 1̄)`-component `y` of `x` satisfies `hd y = 1`. -/
theorem exists_mem_hd_eq_one {x : A} (hx : H.hd x = 1) :
    ∃ y ∈ H.hgrading (-k, 1), H.hd y = 1 := by
  refine ⟨decompose H.hgrading x (-k, 1), (decompose H.hgrading x (-k, 1)).2, ?_⟩
  rw [← decompose_hd, hx, show ((-k, 1) : ℤ × ZMod 2) + (k, 1) = 0 by
    ext
    · simp
    · show (1 : ZMod 2) + 1 = 0
      rfl]
  exact decompose_of_mem_same _ (SetLike.GradedOne.one_mem (A := H.hgrading))

theorem halfDegree_neg_one_zero : halfDegree k (-1, 0) = (-k, 1) := by
  ext
  · simp
  · show ((-1 : ℤ) : ZMod 2) = 1
    rfl

/-- The element `y ∈ H^{-k, 1̄}`, placed in cohomological degree `-1` and weight `0`. -/
def contraction {y : A} (hy : y ∈ H.hgrading (-k, 1)) : H.Regraded :=
  H.place (-1, 0) y (by rw [halfDegree_neg_one_zero]; exact hy)

theorem d_contraction {y : A} (hy : y ∈ H.hgrading (-k, 1)) (h1 : H.hd y = 1) :
    d (H.contraction hy) = 1 := by
  rw [contraction, d_place, one_eq_place]
  exact place_congr (by simp) h1 _ _

/-- The contraction as an endomorphism of every object of the weight dg category. -/
def contractionHom {y : A} (hy : y ∈ H.hgrading (-k, 1)) (i : WeightCategory H.Regraded) :
    i ⟶ i :=
  WeightCategory.homMk (H.contraction hy) (by
    rw [sub_self]
    exact place_mem_wgrading (-1, 0) _)

theorem contractionHom_mem {y : A} (hy : y ∈ H.hgrading (-k, 1)) (i : WeightCategory H.Regraded) :
    H.contractionHom hy i ∈ grading (-1) :=
  WeightCategory.mem_grading_iff.mpr (place_mem_grading (-1, 0) _)

theorem d_contractionHom {y : A} (hy : y ∈ H.hgrading (-k, 1)) (h1 : H.hd y = 1)
    (i : WeightCategory H.Regraded) : d (H.contractionHom hy i) = 𝟙 i :=
  WeightCategory.hom_ext ((WeightCategory.d_val _).trans (H.d_contraction hy h1))

/-- **If `hd x = 1` for some `x`, every dg module over `C_H` is acyclic.** -/
theorem isAcyclic_of_hd_eq_one {x : A} (hx : H.hd x = 1)
    (M : CatModule.{w} (WeightCategory H.Regraded)) : CatModule.IsAcyclic M := by
  obtain ⟨y, hy, h1⟩ := H.exists_mem_hd_eq_one hx
  intro i
  refine isAcyclic_iff.mpr fun n m hm hdm => ⟨H.contractionHom hy i • m, ?_, ?_⟩
  · have := CatModule.smul_mem_grading (H.contractionHom_mem hy i) hm
    rwa [show -1 + n = n - 1 by ring] at this
  · rw [CatModule.d_smul (H.contractionHom_mem hy i), d_contractionHom H hy h1, hdm,
      CatModule.smul_zero, smul_zero, add_zero, CatModule.id_smul]

variable [CatModule.HasDerivedCategory.{w', max u w} (WeightCategory H.Regraded)]

/-- **If `hd x = 1` for some `x`, every object of `D(C_H)` is zero.** -/
theorem isZero_of_hd_eq_one {x : A} (hx : H.hd x = 1)
    (X : CatModule.DerivedCategory.{w', max u w} (WeightCategory H.Regraded)) : IsZero X := by
  obtain ⟨M, ⟨e⟩⟩ := CatModule.DerivedCategory.exists_iso_Q_obj X
  exact ((CatModule.DerivedCategory.isZero_Q_obj_iff M).mpr
    (H.isAcyclic_of_hd_eq_one hx M)).of_iso e

/-- If `hd x = 1` for some `x`, then `K₀(D(C_H)^c) = 0`. -/
theorem compactK0_subsingleton {x : A} (hx : H.hd x = 1) : Subsingleton (CompactK0.{w', w} H) := by
  refine subsingleton_of_forall_eq 0 fun z => ?_
  induction z using K0.induction_on with
  | zero => rfl
  | mk X => exact K0.mk_eq_zero_of_isZero (IsZero.of_full_of_faithful_of_isZero
      (compactSubcategory _).ι X (H.isZero_of_hd_eq_one hx X.obj))
  | neg z hz => rw [hz, neg_zero]
  | add z z' hz hz' => rw [hz, hz', add_zero]

/-- If `hd x = 1` for some `x`, then the compact super Grothendieck group vanishes. -/
theorem superK0c_subsingleton {x : A} (hx : H.hd x = 1) : Subsingleton (SuperK0c.{w', w} H) := by
  have := H.compactK0_subsingleton hx
  refine subsingleton_of_forall_eq 0 fun s => ?_
  obtain ⟨z, rfl⟩ := superK0cMk_surjective H s
  rw [Subsingleton.elim z 0, map_zero]

end HalfGradedDGRing

end DG
