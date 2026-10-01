import DG.HalfGraded.SuperK0
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Linear structure on the compact super Grothendieck group

For every half-graded dg ring with integer parameter `k`, parity relations are
exactly `(1 + qᵏ) K₀`. The existing `SuperK0c` therefore carries both Laurent-polynomial
scalars and scalars modulo `(1 + qᵏ)`. No field, positivity, or nonzero-parameter
hypothesis is used. Monomials act by the existing internal-shift action.
-/

open CategoryTheory Category Limits Pretriangulated LaurentPolynomial

universe w' w u

noncomputable section

namespace DG.HalfGradedDGRing

variable {A : Type u} [Ring A] {k : ℤ} (H : HalfGradedDGRing A k)
  [CatModule.HasDerivedCategory.{w', max u w} (WeightCategory H.Regraded)]

/-- The ordinary Grothendieck group of compact half-graded dg modules. -/
abbrev CompactK0 := K0 (compactSubcategory.{max u w}
  (CatModule.DerivedCategory.{w', max u w} (WeightCategory H.Regraded))).FullSubcategory

/-- For every half-graded dg ring, `[Π X] = -q⁻ᵏ [X]`. -/
theorem mk_parityShiftCompact
    (X : (compactSubcategory.{max u w}
      (CatModule.DerivedCategory.{w', max u w} (WeightCategory H.Regraded))).FullSubcategory) :
    K0.mk (parityShiftCompact H X) =
      -((T (-k) : LaurentPolynomial ℤ) • K0.mk X) := by
  rw [CatModule.DerivedCategory.T_smul_mk_compact, ← K0.mk_shift_one]
  exact K0.mk_eq_of_iso ((compactSubcategory _).fullyFaithfulι.preimageIso
    (((compactSubcategory _).ι.commShiftIso (1 : ℤ)).app
      (((CatModule.DerivedCategory.compactInternalShiftAction _).functor (-k)).obj X)).symm)

/-- The submodule `(1 + qᵏ) K₀`, as the image of scalar multiplication. -/
def paritySubmodule : Submodule (LaurentPolynomial ℤ) (CompactK0.{w', w} H) :=
  LinearMap.range (LinearMap.lsmul (LaurentPolynomial ℤ) (CompactK0 H) (1 + T k))

/-- The negative-exponent parity polynomial sends every class into the parity relations. -/
theorem smul_mem_parityRelations (y : CompactK0.{w', w} H) :
    (T (-k) + 1 : LaurentPolynomial ℤ) • y ∈
      K0Rel.parityRelations (parityShiftCompact H) := by
  induction y using K0.induction_on with
  | zero => rw [_root_.smul_zero]; exact zero_mem _
  | mk X =>
    have h : (T (-k) + 1 : LaurentPolynomial ℤ) • K0.mk X =
        -(K0.mk (parityShiftCompact H X) - K0.mk X) := by
      rw [mk_parityShiftCompact, _root_.add_smul, one_smul]; abel
    rw [h]
    exact neg_mem (AddSubgroup.subset_closure ⟨X, rfl⟩)
  | neg x hx => rw [_root_.smul_neg]; exact neg_mem hx
  | add x y hx hy => rw [_root_.smul_add]; exact add_mem hx hy

/-- Parity relations are exactly the image of multiplication by `1 + qᵏ`. -/
theorem parityRelations_eq : K0Rel.parityRelations (parityShiftCompact H) =
    (paritySubmodule.{w', w} H).toAddSubgroup := by
  apply le_antisymm
  · refine (AddSubgroup.closure_le _).mpr ?_
    rintro _ ⟨X, rfl⟩
    refine ⟨-((T (-k) : LaurentPolynomial ℤ) • K0.mk X), ?_⟩
    change (1 + T k : LaurentPolynomial ℤ) • (-((T (-k) : LaurentPolynomial ℤ) • K0.mk X)) = _
    rw [mk_parityShiftCompact, _root_.smul_neg, smul_smul,
      add_mul, one_mul, ← T_add, add_neg_cancel, T_zero, _root_.add_smul, one_smul]
    abel
  · rintro _ ⟨y, rfl⟩
    have h := smul_mem_parityRelations H ((T k : LaurentPolynomial ℤ) • y)
    rwa [smul_smul, add_mul, one_mul, ← T_add, neg_add_cancel, T_zero] at h

/-- The original super Grothendieck group, identified with `K₀ / (1 + qᵏ) K₀`. -/
def superK0cQuotientEquiv : SuperK0c.{w', w} H ≃+
    CompactK0 H ⧸ paritySubmodule H :=
  (superK0cEquiv H).trans (QuotientAddGroup.quotientAddEquivOfEq (parityRelations_eq H))

/-- Laurent-polynomial scalars on the existing super Grothendieck group. -/
instance superK0cModule : Module (LaurentPolynomial ℤ) (SuperK0c.{w', w} H) :=
  (superK0cQuotientEquiv H).module _

/-- The quotient comparison respects Laurent-polynomial scalars. -/
def superK0cLinearEquiv : SuperK0c.{w', w} H ≃ₗ[LaurentPolynomial ℤ]
    CompactK0 H ⧸ paritySubmodule H :=
  (superK0cQuotientEquiv H).linearEquiv _

@[simp]
theorem superK0cLinearEquiv_mk
    (X : (compactSubcategory.{max u w}
      (CatModule.DerivedCategory.{w', max u w} (WeightCategory H.Regraded))).FullSubcategory) :
    superK0cLinearEquiv H (K0Rel.mk X) = Submodule.Quotient.mk (K0.mk X) := rfl

/-- The quotient coefficient polynomial annihilates the super Grothendieck group. -/
theorem superK0c_isTorsionBy : Module.IsTorsionBy (LaurentPolynomial ℤ)
    (SuperK0c.{w', w} H) (1 + T k) := by
  intro x
  apply (superK0cLinearEquiv H).injective
  rw [map_smul, map_zero]
  obtain ⟨y, hy⟩ := Submodule.mkQ_surjective (paritySubmodule H) (superK0cLinearEquiv H x)
  rw [← hy]
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y, rfl⟩

/-- The coefficient ideal for the super Grothendieck group, for any integer parameter. -/
abbrev superIdeal (k : ℤ) : Ideal (LaurentPolynomial ℤ) := Ideal.span {1 + T k}

/-- Scalars descend to `ℤ[q,q⁻¹] / (1 + qᵏ)`, without restrictions on `k`. -/
instance superK0cQuotientModule :
    Module (LaurentPolynomial ℤ ⧸ superIdeal k) (SuperK0c.{w', w} H) :=
  (superK0c_isTorsionBy H).module

@[simp]
theorem superK0c_mk_smul (p : LaurentPolynomial ℤ) (x : SuperK0c.{w', w} H) :
    Ideal.Quotient.mk (superIdeal k) p • x = p • x := rfl

/-- The canonical Laurent-linear quotient map onto the original super Grothendieck group. -/
def superK0cMk : CompactK0.{w', w} H →ₗ[LaurentPolynomial ℤ] SuperK0c H :=
  (superK0cLinearEquiv H).symm.toLinearMap.comp (paritySubmodule H).mkQ

@[simp]
theorem superK0cMk_mk
    (X : (compactSubcategory.{max u w}
      (CatModule.DerivedCategory.{w', max u w} (WeightCategory H.Regraded))).FullSubcategory) :
    superK0cMk H (K0.mk X) = K0Rel.mk X := by
  apply (superK0cLinearEquiv H).injective
  exact (superK0cLinearEquiv H).apply_symm_apply _

theorem superK0cMk_surjective : Function.Surjective (superK0cMk.{w', w} H) :=
  (superK0cLinearEquiv H).symm.surjective.comp (paritySubmodule H).mkQ_surjective

/-- Laurent monomials act by the actual internal shift on compact classes. -/
theorem T_smul_superK0c_mk (n : ℤ)
    (X : (compactSubcategory.{max u w}
      (CatModule.DerivedCategory.{w', max u w} (WeightCategory H.Regraded))).FullSubcategory) :
    (T n : LaurentPolynomial ℤ) • (K0Rel.mk X : SuperK0c H) =
      K0Rel.mk (((CatModule.DerivedCategory.compactInternalShiftAction H.Regraded).functor n).obj X) := by
  rw [← superK0cMk_mk H, ← map_smul, CatModule.DerivedCategory.T_smul_mk_compact,
    superK0cMk_mk]

end DG.HalfGradedDGRing
