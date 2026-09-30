import DG.Bigraded.Derived
import DG.Derived.Morita

/-!
# Graded Morita theory for an idempotent of a bigraded dg ring

Let `A` be a bigraded dg ring (a dg ring with an internal weight grading, `DG.BigradedDGRing A`)
and `e ∈ A` an idempotent cocycle of bidegree `(0, 0)` (`DG.DGIdempotent A` with
`e ∈ A⟨0⟩`). The derived category of bigraded dg `A`-modules is the derived category of the weight
dg category `C_A = DG.WeightCategory A` (objects `k : ℤ`, `C_A(k, l) = A⟨l - k⟩`), with internal
shift `⟨s⟩` given by restriction along `k ↦ k + s`
(`DG.CatModule.DerivedCategory.internalShift`).

The family of the idempotents `e ∈ A⟨0⟩ = C_A(k, k)` (`DG.DGIdempotent.weightFamily`) has corner
dg category `C_{eAe} = (e.weightFamily he).Corner`, with `C_{eAe}(k, l) = e A⟨l - k⟩ e`: the weight
dg category of the bigraded dg ring `e A e`. If `e` is full up to homotopy,
`1 = ∑ₖ aₖ e bₖ + d s` with `aₖ, bₖ ∈ Z⁰(A)` (`DG.DGIdempotent.IsFullH0`; no weight condition
is needed, see `DG.DGIdempotent.isFullH0_weightFamily`), the Morita equivalence of
`DG.Category.Derived.Morita` gives a triangulated equivalence

  `DG.DGIdempotent.weightMoritaEquivalence : D(C_{eAe}) ≌ D(C_A)`,

which commutes with the internal shifts
(`DG.DGIdempotent.weightMoritaEquivalenceInternalShiftIso`): the internal shift `⟨s⟩` of
`D(C_{eAe})` is restriction along `k ↦ k + s` (`DG.DGIdempotent.cornerInternalShift`).

## Main definitions and results

* `DG.DGIdempotent.weightFamily`, `DG.DGIdempotent.isFullH0_weightFamily`.
* `DG.DGIdempotent.cornerShiftFunctor`, `DG.DGIdempotent.cornerInternalShift`.
* `DG.DGIdempotent.weightMoritaEquivalence`,
  `DG.DGIdempotent.weightMoritaEquivalenceInternalShiftIso`.
-/

open CategoryTheory DirectSum

universe t w₂ u

set_option backward.isDefEq.respectTransparency false

namespace DG

namespace DGIdempotent

variable {A : Type u} [Ring A] [DGAddCommGroup A] [InternalGrading A] [BigradedDGRing A]
  [DGRing A] (e : DGIdempotent A) (he : e.val ∈ wgrading (M := A) 0)

/-- The family of the idempotents `e ∈ A⟨0⟩ = C_A(k, k)` of the weight dg category, for an
idempotent `e` of weight `0`. -/
def weightFamily : IdempotentFamily ℤ (WeightCategory A) where
  obj k := ⟨k⟩
  idem k := ⟨e.val, by simpa using he⟩
  idem_mem _ := e.mem_zero
  idem_comp_idem _ := WeightCategory.hom_ext e.mul_self
  d_idem _ := WeightCategory.hom_ext e.d_eq_zero

omit [DGRing A] in
@[simp]
theorem weightFamily_idem_val (k : ℤ) : ((e.weightFamily he).idem k).1 = e.val := rfl

omit [DGRing A] in
theorem weightFamily_hidem (s k : ℤ) :
    eqToHom (rfl : (WeightCategory.shiftFunctor A s).obj ((e.weightFamily he).obj k) =
        (e.weightFamily he).obj (k + s)).symm ≫
      (WeightCategory.shiftFunctor A s).map ((e.weightFamily he).idem k) ≫ eqToHom rfl =
      (e.weightFamily he).idem (k + s) := by
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact WeightCategory.hom_ext rfl

/-- The shift of weights `k ↦ k + s` on the corner dg category `C_{eAe}`. -/
noncomputable abbrev cornerShiftFunctor (s : ℤ) :
    (e.weightFamily he).Corner ⥤ (e.weightFamily he).Corner :=
  (e.weightFamily he).mapCorner (WeightCategory.shiftFunctor A s) (· + s) (fun _ => rfl)
    (e.weightFamily_hidem he s)

/-! ### Fullness up to homotopy in the weight dg category -/

open scoped Classical in
omit [DGRing A] in
include he in
/-- The weight-`0` component of `x e y` is `∑ₚ xₚ e y₋ₚ`. -/
theorem coe_decompose_wgrading_mul_val_mul_zero (x y : A) :
    (decompose (wgrading (M := A)) (x * e.val * y) 0 : A) =
      ∑ p ∈ (decompose (wgrading (M := A)) x).support,
        (decompose (wgrading (M := A)) x p : A) * e.val *
          (decompose (wgrading (M := A)) y (-p) : A) := by
  classical
  have hterm (p : ℤ) : (decompose (wgrading (M := A))
      ((decompose (wgrading (M := A)) x p : A) * e.val * y) 0 : A) =
      (decompose (wgrading (M := A)) x p : A) * e.val *
        (decompose (wgrading (M := A)) y (-p) : A) := by
    have h1 := coe_decompose_mul_add_of_left_mem (𝒜 := wgrading (M := A)) (j := -p)
      (b := e.val * y) (decompose (wgrading (M := A)) x p).2
    have h2 := coe_decompose_mul_add_of_left_mem (𝒜 := wgrading (M := A)) (j := -p) (b := y) he
    rw [add_neg_cancel] at h1
    rw [zero_add] at h2
    rw [mul_assoc, h1, h2, mul_assoc]
  conv_lhs => rw [← DirectSum.sum_support_decompose (wgrading (M := A)) x]
  rw [Finset.sum_mul, Finset.sum_mul, ← GradedRing.proj_apply, map_sum]
  exact Finset.sum_congr rfl fun p _ => hterm p

omit [DGRing A] in
include he in
/-- If `e` is full up to homotopy (`1 = ∑ₖ aₖ e bₖ + d s` with `aₖ, bₖ ∈ Z⁰(A)`), so is its family
in the weight dg category: the weight components of the `aₖ` and `bₖ` give, at each object `m`,
`𝟙 = ∑ aₖ,ₚ e bₖ,₋ₚ + d s₀`. No weight condition on the `aₖ`, `bₖ` is needed. -/
theorem isFullH0_weightFamily (h : e.IsFullH0) : (e.weightFamily he).IsFullH0 := by
  classical
  obtain ⟨n, a, b, ha, hb, ht⟩ := h
  obtain ⟨t, ht, hdt⟩ := mem_coboundaries.mp ht
  rintro ⟨m⟩
  let π : ℤ → A → A := fun p x => decompose (wgrading (M := A)) x p
  have hπ (p : ℤ) (x : A) : π p x ∈ wgrading (M := A) p := (decompose (wgrading (M := A)) x p).2
  have hπc {x : A} (hx : x ∈ cocycles A 0) (p : ℤ) : π p x ∈ cocycles A 0 :=
    ⟨decompose_wgrading_mem_grading hx.1 p, by
      change d (decompose (wgrading (M := A)) x p : A) = 0
      rw [← decompose_wgrading_d, hx.2]
      simp⟩
  -- the index set: pairs `(k, p)` with `p` in the weight support of `aₖ`
  let J := Σ k : Fin n, (decompose (wgrading (M := A)) (a k)).support
  let E := Fintype.equivFin J
  let i : J → ℤ := fun j => m - j.2
  let a' : ∀ j : J, (⟨m⟩ : WeightCategory A) ⟶ ⟨i j⟩ := fun j =>
    ⟨π (-j.2) (b j.1), by simpa [i, sub_sub_cancel_left] using hπ (-j.2) (b j.1)⟩
  let b' : ∀ j : J, (⟨i j⟩ : WeightCategory A) ⟶ ⟨m⟩ := fun j =>
    ⟨π j.2 (a j.1), by simpa [i] using hπ j.2 (a j.1)⟩
  refine ⟨Fintype.card J, fun r => i (E.symm r), fun r => a' (E.symm r),
    fun r => b' (E.symm r), fun r => ⟨(hπc (hb _) _).1, WeightCategory.hom_ext (hπc (hb _) _).2⟩,
    fun r => ⟨(hπc (ha _) _).1, WeightCategory.hom_ext (hπc (ha _) _).2⟩, ?_⟩
  refine ⟨⟨π 0 t, by simpa using hπ 0 t⟩, decompose_wgrading_mem_grading ht 0,
    WeightCategory.hom_ext ?_⟩
  have key : ∑ r, (a' (E.symm r) ≫ (e.weightFamily he).idem (i (E.symm r)) ≫ b' (E.symm r)).1 =
      π 0 (∑ k, a k * e.val * b k) := by
    rw [Equiv.sum_comp E.symm (fun j => (a' j ≫ (e.weightFamily he).idem (i j) ≫ b' j).1),
      Fintype.sum_sigma]
    simp only [π]
    rw [← GradedRing.proj_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [GradedRing.proj_apply, coe_decompose_wgrading_mul_val_mul_zero e he]
    exact Finset.sum_coe_sort _ fun p => (decompose (wgrading (M := A)) (a k) p : A) * e.val *
      (decompose (wgrading (M := A)) (b k) (-p) : A)
  change d (π 0 t) = (∑ r, a' (E.symm r) ≫ (e.weightFamily he).idem (i (E.symm r)) ≫
    b' (E.symm r)).1 - 1
  rw [AddSubgroup.val_finsetSum, key,
    show ∑ k, a k * e.val * b k = d t + 1 by rw [hdt]; abel]
  simp only [π]
  rw [decompose_add, add_apply, AddSubgroup.coe_add, decompose_wgrading_d,
    decompose_of_mem_same _ (one_mem_wgrading (A := A))]
  abel

variable [CatModule.HasDerivedCategory.{max u t, max u t} (e.weightFamily he).Corner]
  [CatModule.HasDerivedCategory.{max u t, max u t} (WeightCategory A)]
  [CatModule.HasDerivedCategory.{w₂, max u t} (e.weightFamily he).augment.Corner]

/-- The internal shift `⟨s⟩` on the derived category `D(C_{eAe})`: restriction along the shift
of weights `k ↦ k + s`. It is triangulated. -/
noncomputable def cornerInternalShift (s : ℤ) :
    CatModule.DerivedCategory.{max u t, max u t} (e.weightFamily he).Corner ⥤
      CatModule.DerivedCategory.{max u t, max u t} (e.weightFamily he).Corner :=
  CatModule.DerivedCategory.restrict (e.cornerShiftFunctor he s)

noncomputable instance (s : ℤ) : (e.cornerInternalShift.{t} he s).CommShift ℤ :=
  inferInstanceAs ((CatModule.DerivedCategory.restrict (e.cornerShiftFunctor he s)).CommShift ℤ)

instance (s : ℤ) : (e.cornerInternalShift.{t} he s).IsTriangulated :=
  inferInstanceAs (CatModule.DerivedCategory.restrict (e.cornerShiftFunctor he s)).IsTriangulated

variable {e}

/-- **Graded Morita theory for an idempotent** (repaired form of Roadmap 7.3). For a bigraded
dg ring `A` and an idempotent cocycle `e` of bidegree `(0, 0)` which is full up to homotopy
(`1 = ∑ₖ aₖ e bₖ + d s` with `aₖ, bₖ ∈ Z⁰(A)`), the derived category of the weight dg category
`C_{eAe}` of `e A e` is equivalent to that of `C_A`, i.e. to the derived category of bigraded dg
`A`-modules. The functor and its inverse are triangulated, and they commute with the internal
shifts (`weightMoritaEquivalenceInternalShiftIso`). -/
noncomputable def weightMoritaEquivalence (h : e.IsFullH0) :
    CatModule.DerivedCategory.{max u t, max u t} (e.weightFamily he).Corner ≌
      CatModule.DerivedCategory.{max u t, max u t} (WeightCategory A) :=
  IdempotentFamily.moritaEquivalence.{t, w₂} (e.isFullH0_weightFamily he h)

noncomputable instance weightMoritaEquivalence_functor_commShift (h : e.IsFullH0) :
    (weightMoritaEquivalence.{t, w₂} he h).functor.CommShift ℤ :=
  inferInstanceAs ((IdempotentFamily.moritaEquivalence.{t, w₂}
    (e.isFullH0_weightFamily he h)).functor.CommShift ℤ)

instance weightMoritaEquivalence_functor_isTriangulated (h : e.IsFullH0) :
    (weightMoritaEquivalence.{t, w₂} he h).functor.IsTriangulated :=
  inferInstanceAs (IdempotentFamily.moritaEquivalence.{t, w₂}
    (e.isFullH0_weightFamily he h)).functor.IsTriangulated

/-- The graded Morita equivalence commutes with the internal shifts:
`F(M)⟨s⟩ ≅ F(M⟨s⟩)`. -/
noncomputable def weightMoritaEquivalenceInternalShiftIso (h : e.IsFullH0) (s : ℤ) :
    (weightMoritaEquivalence.{t, w₂} he h).functor ⋙
        CatModule.DerivedCategory.internalShift A s ≅
      e.cornerInternalShift he s ⋙ (weightMoritaEquivalence.{t, w₂} he h).functor :=
  IdempotentFamily.moritaEquivalenceFunctorCompRestrictIso.{t, w₂} _ _ _ _
    (e.isFullH0_weightFamily he h)

end DGIdempotent

end DG
