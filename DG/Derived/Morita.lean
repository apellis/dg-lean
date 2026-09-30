import DG.Category.Derived.Comparison
import DG.Category.Derived.Morita
import DG.Positive.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Morita theory for an idempotent of a dg ring

Let `A` be a dg ring and `e ∈ A⁰` an idempotent cocycle (`DG.DGIdempotent A`), with corner dg ring
`e A e` (`DG.DGIdempotent.Corner e`). If `e` is *full up to homotopy*,

  `1 = ∑ₖ aₖ e bₖ + d s` with `aₖ, bₖ ∈ Z⁰(A)`, `s ∈ A⁻¹` (`DG.DGIdempotent.IsFullH0`),

i.e. the class of `e` generates `H⁰(A)` as a two-sided ideal, then the derived categories of
`e A e` and `A` are equivalent (`DG.DGIdempotent.moritaEquivalence : D(e A e) ≌ D(A)`). The
equivalence is the composite of the equivalences `D(e A e) ≌ D(SingleObj (e A e))` and
`D(SingleObj A) ≌ D(A)` of the one-object comparison, Keller's equivalence along the isomorphism
of dg categories `SingleObj (e A e) ≅ P.Corner` (`DG.DGIdempotent.cornerFunctor`), and the Morita
equivalence `D(P.Corner) ≌ D(SingleObj A)` for the family `P = DG.DGIdempotent.family e`
consisting of the single idempotent `e` of `SingleObj A`
(`DG.IdempotentFamily.moritaEquivalence`); each of these is an equivalence of triangulated
categories. Its functor is derived induction along the dg `(A, e A e)`-bimodule `A e`, i.e.
`A e ⊗^L_{eAe} -`, and its inverse is `e A ⊗^L_A - = e (-)`.

The hypothesis holds when `A e A = A` and `A` is non-negatively graded with `d (A⁰) = 0` (for
instance a positive dg ring in the sense of Schnürer), since the degree-`0` projection `A → A⁰` is
then multiplicative (`DG.DGIdempotent.isFullH0_of_one_mem_span`).

## The literal statement with `A e A = A` is false

The condition `A e A = A` on the underlying ring alone does *not* suffice: for
`V = k x ⊕ k y ⊕ k z` over a field with `|x| = |z| = 0`, `|y| = 1`, `d x = y`, the dg algebra
`A = END_k(V)` is `M₃(k)` as a ring, so the projection `e` onto the subcomplex `k x ⊕ k y`
satisfies `A e A = A`; but `e A e = END(k x ⊕ k y)` is acyclic, so `D(e A e) = 0`, while
`H⁰(A) = k`, so `D(A) ≠ 0` (`DG.Examples.MoritaCounterexample`). The writing
`1 = ∑ₖ aₖ e bₖ` must be possible with cocycles `aₖ`, `bₖ` up to a coboundary.

## Main definitions and results

* `DG.DGIdempotent.family`, `DG.DGIdempotent.IsFullH0`, `DG.DGIdempotent.isFullH0_family`,
  `DG.DGIdempotent.isFullH0_of_one_mem_span`.
* `DG.DGIdempotent.cornerFunctor`, `DG.DGIdempotent.isQuasiEquivalence_cornerFunctor`.
* `DG.DGIdempotent.moritaEquivalence : D(e A e) ≌ D(A)`.
-/

open CategoryTheory

universe t w₁ w₂ u

set_option backward.isDefEq.respectTransparency false

namespace DG

namespace DGIdempotent

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] (e : DGIdempotent A)

/-- The family of idempotents of `SingleObj A` consisting of `e` alone. -/
def family : IdempotentFamily Unit (SingleObj A) where
  obj _ := SingleObj.star A
  idem _ := (e.val : A)
  idem_mem _ := e.mem_zero
  idem_comp_idem _ := e.mul_self
  d_idem _ := e.d_eq_zero

/-- The idempotent `e` is *full up to homotopy*: `1 = ∑ₖ aₖ e bₖ + d s` with `aₖ, bₖ` cocycles of
degree `0`, i.e. the class of `e` generates `H⁰(A)` as a two-sided ideal. -/
def IsFullH0 : Prop :=
  ∃ (n : ℕ) (a b : Fin n → A), (∀ k, a k ∈ cocycles A 0) ∧ (∀ k, b k ∈ cocycles A 0) ∧
    ∑ k, a k * e.val * b k - 1 ∈ coboundaries A 0

omit [DGRing A] in
theorem isFullH0_family (he : e.IsFullH0) : e.family.IsFullH0 := by
  intro _
  obtain ⟨n, a, b, ha, hb, h⟩ := he
  refine ⟨n, fun _ => (), fun k => (b k : A), fun k => (a k : A), hb, ha, ?_⟩
  exact h

/-- If `A` is non-negatively graded with `d (A⁰) = 0` and `A e A = A`, then `e` is full up to
homotopy: the degree-`0` components of a decomposition `1 = ∑ₖ aₖ e bₖ` are cocycles. -/
theorem isFullH0_of_one_mem_span (hneg : ∀ n < 0, grading (M := A) n = ⊥)
    (hd : ∀ a ∈ grading (M := A) 0, d a = 0) (h : (1 : A) ∈ TwoSidedIdeal.span {e.val}) :
    e.IsFullH0 := by
  classical
  let π : A → A := fun a => DirectSum.decompose (grading (M := A)) a 0
  have hπ0 (a : A) : π a ∈ grading (M := A) 0 := (DirectSum.decompose (grading (M := A)) a 0).2
  -- every element of `A e A` is a finite sum `∑ₖ aₖ e bₖ`
  have key : ∀ z ∈ TwoSidedIdeal.span ({e.val} : Set A),
      ∃ (n : ℕ) (a b : Fin n → A), z = ∑ k, a k * e.val * b k := by
    intro z hz
    rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure] at hz
    induction hz using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨y, ⟨a, -, e', he', rfl⟩, b, -, rfl⟩ := hx
      rw [Set.mem_singleton_iff] at he'
      exact ⟨1, fun _ => a, fun _ => b, by simp [he']⟩
    | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨n, a, b, rfl⟩ := hx
      obtain ⟨m, a', b', rfl⟩ := hy
      exact ⟨n + m, Fin.append a a', Fin.append b b', by simp [Fin.sum_univ_add]⟩
    | neg x _ hx =>
      obtain ⟨n, a, b, rfl⟩ := hx
      exact ⟨n, fun k => -a k, b, by simp [Finset.sum_neg_distrib]⟩
  obtain ⟨n, a, b, hab⟩ := key 1 h
  refine ⟨n, fun k => π (a k), fun k => π (b k), fun k => ⟨hπ0 _, hd _ (hπ0 _)⟩,
    fun k => ⟨hπ0 _, hd _ (hπ0 _)⟩, ?_⟩
  have hπmul (x y : A) : π (x * y) = π x * π y := coe_decompose_mul_zero hneg x y
  have hπe : π e.val = e.val := DirectSum.decompose_of_mem_same _ e.mem_zero
  have hπsum : π (∑ k, a k * e.val * b k) = ∑ k, π (a k) * e.val * π (b k) := by
    simp only [π, DirectSum.decompose_sum, DirectSum.sum_apply, AddSubgroup.val_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change π (a k * e.val * b k) = _
    rw [hπmul, hπmul, hπe]
  have hπ1 : π 1 = 1 := DirectSum.decompose_of_mem_same _ one_mem_grading
  rw [← hπsum, ← hab, hπ1, sub_self]
  exact zero_mem _

/-! ### The corner dg category of `e` and the one-object dg category of `e A e` -/

/-- The dg functor `SingleObj (e A e) ⥤ P.Corner` (for `P = e.family`), `x ↦ x`; it is an
isomorphism of dg categories. -/
def cornerFunctor : SingleObj e.Corner ⥤ e.family.Corner where
  obj _ := ⟨()⟩
  map x := ⟨((show e.Corner from x) : A), Corner.coe_mul_val e x, Corner.val_mul_coe e x⟩
  map_id _ := rfl
  map_comp _ _ := rfl

omit [DGRing A] in
@[simp]
theorem cornerFunctor_map_val {X Y : SingleObj e.Corner} (x : X ⟶ Y) :
    (e.cornerFunctor.map x).1 = ((show e.Corner from x) : A) :=
  rfl

instance : e.cornerFunctor.Additive where
  map_add := IdempotentFamily.hom_ext rfl

instance : e.cornerFunctor.IsDGFunctor where
  map_mem' hf := IdempotentFamily.mem_grading_iff.mpr ((Corner.mem_grading_iff e).mp hf)
  map_d' _ := IdempotentFamily.hom_ext rfl

omit [DGRing A] in
theorem cornerFunctor_map_bijective (X Y : SingleObj e.Corner) :
    Function.Bijective (e.cornerFunctor.map : (X ⟶ Y) → _) := by
  refine ⟨fun x y h => ?_, fun f => ?_⟩
  · have h' := congrArg Subtype.val h
    exact Corner.coe_injective e h'
  refine ⟨show e.Corner from ⟨f.1, (Corner.mem_iff e).mpr ⟨f.2.2, f.2.1⟩⟩, ?_⟩
  exact IdempotentFamily.hom_ext rfl

/-- The dg functor `SingleObj (e A e) ⥤ P.Corner` is a quasi-equivalence. -/
theorem isQuasiEquivalence_cornerFunctor : IsQuasiEquivalence e.cornerFunctor where
  toIsQuasiFullyFaithful := IsQuasiFullyFaithful.of_bijective _ e.cornerFunctor_map_bijective
    fun hf => (Corner.mem_grading_iff e).mpr (IdempotentFamily.mem_grading_iff.mp hf)
  exists_iso := by
    rintro ⟨⟨⟩⟩
    refine ⟨SingleObj.star _, 𝟙 _, 𝟙 _, id_mem_cocycles _, id_mem_cocycles _, ?_, ?_⟩ <;>
    · rw [Category.id_comp, sub_self]
      exact zero_mem _

/-! ### The Morita equivalence -/

variable [DG.HasDerivedCategory.{w₁, max u t} e.Corner] [DG.HasDerivedCategory.{w₂, max u t} A]

/-- **Morita theory for an idempotent of a dg ring.** For a degree-`0` idempotent cocycle `e` of a
dg ring `A` which is full up to homotopy (`1 = ∑ₖ aₖ e bₖ + d s` with `aₖ, bₖ ∈ Z⁰(A)`), the
derived categories of `e A e` and `A` are equivalent. The equivalence is a composite of
triangulated equivalences; its functor is `A e ⊗^L_{eAe} -` and its inverse `e A ⊗^L_A -`.
The hypothesis cannot be weakened to `A e A = A` (see the module docstring). -/
noncomputable def moritaEquivalence (he : e.IsFullH0) :
    DG.DerivedCategory e.Corner ≌ DG.DerivedCategory A :=
  letI := CatModule.HasDerivedCategory.small.{max u t} (SingleObj e.Corner)
  letI := CatModule.HasDerivedCategory.small.{t} e.family.Corner
  letI := CatModule.HasDerivedCategory.small.{t} (SingleObj A)
  letI := CatModule.HasDerivedCategory.small.{t} e.family.augment.Corner
  (CatModule.DerivedCategory.singleObjEquivalence e.Corner).symm.trans
    ((CatModule.DerivedCategory.kellerEquivalence.{t} e.isQuasiEquivalence_cornerFunctor).trans
      ((e.family.moritaEquivalence.{t} (e.isFullH0_family he)).trans
        (CatModule.DerivedCategory.singleObjEquivalence A)))

end DGIdempotent

end DG
