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

The corner `e A e` is again a bigraded dg ring (`DG.DGIdempotent.Corner.instInternalGrading`,
`DG.DGIdempotent.Corner.instBigradedDGRing`, for `[Fact (e.val ∈ wgrading 0)]`). The family of
the idempotents `e ∈ A⟨0⟩ = C_A(k, k)` (`DG.DGIdempotent.weightFamily`) has corner dg category
with Hom complexes `e A⟨l - k⟩ e`, isomorphic to `C_{eAe} = DG.WeightCategory (e A e)`
(`DG.DGIdempotent.weightCornerFunctor`).

If `e` is full up to homotopy, `1 = ∑ₖ aₖ e bₖ + d s` with `aₖ, bₖ ∈ Z⁰(A)`
(`DG.DGIdempotent.IsFullH0`; no weight condition is needed, the weight components of the `aₖ`
and `bₖ` are used, `DG.DGIdempotent.isFullH0_weightFamily`), the Morita equivalence of
`DG.Category.Derived.Morita` and Keller's theorem give a triangulated equivalence

  `DG.DGIdempotent.gradedMoritaEquivalence : D(C_{eAe}) ≌ D(C_A)`

between the derived categories of bigraded dg modules over `e A e` and over `A`, which commutes
with the internal shifts (`DG.DGIdempotent.gradedMoritaEquivalenceInternalShiftIso`).

As for dg rings (`DG.Derived.Morita`), the hypothesis `A e A = A` alone is not sufficient.

## Main definitions and results

* `DG.DGIdempotent.Corner.instInternalGrading`, `DG.DGIdempotent.Corner.instBigradedDGRing`.
* `DG.DGIdempotent.weightFamily`, `DG.DGIdempotent.isFullH0_weightFamily`.
* `DG.DGIdempotent.cornerShiftFunctor`, `DG.DGIdempotent.cornerInternalShift`,
  `DG.DGIdempotent.weightMoritaEquivalence`,
  `DG.DGIdempotent.weightMoritaEquivalenceInternalShiftIso`.
* `DG.DGIdempotent.weightCornerFunctor`, `DG.DGIdempotent.weightCornerEquivalence`.
* `DG.DGIdempotent.gradedMoritaEquivalence`, with triangulated functor
  (`DG.DGIdempotent.gradedMoritaEquivalence_functor_isTriangulated`), and
  `DG.DGIdempotent.gradedMoritaEquivalenceInternalShiftIso`.
-/

open CategoryTheory DirectSum

universe t w₂ u

set_option backward.isDefEq.respectTransparency false

namespace DG

namespace DGIdempotent

variable {A : Type u} [Ring A] [DGAddCommGroup A] [InternalGrading A] [BigradedDGRing A]
  [DGRing A] (e : DGIdempotent A) (he : e.val ∈ wgrading (M := A) 0)

/-! ### The corner `e A e` as a bigraded dg ring -/

namespace Corner

omit [DGRing A] in
include he in
/-- The weight components of an element of `e A e` lie in `e A e`. -/
theorem decompose_wgrading_mem {a : A} (ha : a ∈ Subsemigroup.corner e.val) (k : ℤ) :
    (decompose (wgrading (M := A)) a k : A) ∈ Subsemigroup.corner e.val := by
  obtain ⟨h₁, h₂⟩ := (mem_iff e).mp ha
  refine (mem_iff e).mpr ⟨?_, ?_⟩
  · have h := coe_decompose_mul_add_of_left_mem (𝒜 := wgrading (M := A)) (j := k) (b := a) he
    rw [zero_add, h₁] at h
    exact h.symm
  · have h := coe_decompose_mul_add_of_right_mem (𝒜 := wgrading (M := A)) (i := k) (a := a) he
    rw [add_zero, h₂] at h
    exact h.symm

/-- The weight grading of `e A e`, restricted from that of `A`. -/
def wgradingCorner (k : ℤ) : AddSubgroup e.Corner :=
  (wgrading (M := A) k).comap (valAddHom e)

omit [DGRing A] in
include he in
theorem isInternal_wgradingCorner : DirectSum.IsInternal (wgradingCorner e) :=
  isInternal_comap _ _ (coe_injective e) fun k x =>
    ⟨⟨_, decompose_wgrading_mem e he (coe_mem e x) k⟩, rfl⟩

/-- The decomposition of `e A e` into weight components. -/
@[instance_reducible]
noncomputable def decompositionCorner : Decomposition (wgradingCorner e) :=
  (isInternal_wgradingCorner e he).chooseDecomposition

omit [DGRing A] in
/-- The weight components of an element of `e A e` are its weight components in `A`. -/
theorem coe_decompose_wgradingCorner (x : e.Corner) (k : ℤ) :
    letI := decompositionCorner e he
    ((decompose (wgradingCorner e) x k : e.Corner) : A) =
      decompose (wgrading (M := A)) (x : A) k := by
  let : Decomposition fun k => (wgrading (M := A) k).comap (valAddHom e) :=
    decompositionCorner e he
  exact coe_decompose_comap _ (valAddHom e) x k

/-- For an idempotent `e` of weight `0`, the corner `e A e` has an internal grading, restricted
from that of `A`. -/
noncomputable instance instInternalGrading [Fact (e.val ∈ wgrading (M := A) 0)] :
    InternalGrading e.Corner :=
  letI := decompositionCorner e Fact.out
  { wgrading := wgradingCorner e
    isHomogeneous_grading' := fun n k x hx => by
      change ((decompose (wgradingCorner e) x k : e.Corner) : A) ∈ grading n
      rw [coe_decompose_wgradingCorner e Fact.out]
      exact decompose_wgrading_mem_grading (M := A) (m := (x : A)) hx k
    d_mem_wgrading' := fun {_ x} hx => d_mem_wgrading (M := A) (m := (x : A)) hx }

variable [Fact (e.val ∈ wgrading (M := A) 0)]

theorem mem_wgrading_iff {k : ℤ} {x : e.Corner} :
    x ∈ wgrading (M := e.Corner) k ↔ (x : A) ∈ wgrading (M := A) k :=
  Iff.rfl

/-- `e A e` is a bigraded dg ring. -/
instance instBigradedDGRing : BigradedDGRing e.Corner where
  one_mem := (Fact.out : e.val ∈ wgrading (M := A) 0)
  mul_mem _ _ _ _ hx hy := mul_mem_wgrading (A := A) hx hy

end Corner

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

/-! ### The weight dg category of `e A e` -/

section WeightCorner

variable [Fact (e.val ∈ wgrading (M := A) 0)]

/-- The isomorphism of dg categories
`C_{eAe} = WeightCategory (e A e) ⥤ (e.weightFamily he).Corner`, the identity on objects and on
Hom complexes (`(e A e)⟨l - k⟩ = e A⟨l - k⟩ e`). -/
@[simps obj]
noncomputable def weightCornerFunctor : WeightCategory e.Corner ⥤ (e.weightFamily he).Corner where
  obj k := ⟨k.as⟩
  map f := ⟨⟨((f.1 : e.Corner) : A), f.2⟩, WeightCategory.hom_ext (Corner.coe_mul_val e f.1),
    WeightCategory.hom_ext (Corner.val_mul_coe e f.1)⟩
  map_id _ := IdempotentFamily.hom_ext (WeightCategory.hom_ext rfl)
  map_comp _ _ := IdempotentFamily.hom_ext (WeightCategory.hom_ext rfl)

@[simp]
theorem weightCornerFunctor_map_val_val {k l : WeightCategory e.Corner} (f : k ⟶ l) :
    ((e.weightCornerFunctor he).map f).1.1 = ((f.1 : e.Corner) : A) :=
  rfl

instance : (e.weightCornerFunctor he).Additive where
  map_add := IdempotentFamily.hom_ext (WeightCategory.hom_ext rfl)

instance : (e.weightCornerFunctor he).IsDGFunctor where
  map_mem' hf := hf
  map_d' _ := IdempotentFamily.hom_ext (WeightCategory.hom_ext rfl)

theorem weightCornerFunctor_map_bijective (k l : WeightCategory e.Corner) :
    Function.Bijective ((e.weightCornerFunctor he).map : (k ⟶ l) → _) := by
  refine ⟨fun x y h => ?_, fun f => ?_⟩
  · have h' := congrArg (fun g => g.1.1) h
    exact WeightCategory.hom_ext (Corner.coe_injective e h')
  · refine ⟨⟨⟨f.1.1, (Corner.mem_iff e).mpr ⟨?_, ?_⟩⟩, f.1.2⟩, rfl⟩
    · exact congrArg Subtype.val f.2.2
    · exact congrArg Subtype.val f.2.1

/-- `C_{eAe} ⥤ (e.weightFamily he).Corner` is a quasi-equivalence (in fact an isomorphism). -/
theorem isQuasiEquivalence_weightCornerFunctor :
    IsQuasiEquivalence (e.weightCornerFunctor he) where
  toIsQuasiFullyFaithful := IsQuasiFullyFaithful.of_bijective _
    (e.weightCornerFunctor_map_bijective he) fun hf => hf
  exists_iso := by
    rintro ⟨k⟩
    refine ⟨⟨k⟩, 𝟙 _, 𝟙 _, id_mem_cocycles _, id_mem_cocycles _, ?_, ?_⟩ <;>
    · rw [Category.id_comp]
      show 𝟙 ((e.weightCornerFunctor he).obj ⟨k⟩) - 𝟙 ((e.weightCornerFunctor he).obj ⟨k⟩) ∈ _
      rw [sub_self]
      exact zero_mem _

/-- `C_{eAe} ⥤ (e.weightFamily he).Corner` commutes with the shifts of weights. -/
noncomputable def weightCornerFunctorCompShiftIso (s : ℤ) :
    e.weightCornerFunctor he ⋙ e.cornerShiftFunctor he s ≅
      WeightCategory.shiftFunctor e.Corner s ⋙ e.weightCornerFunctor he :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun {k l} f => IdempotentFamily.hom_ext (by
    change (eqToHom _ ≫ (WeightCategory.shiftFunctor A s).map ((e.weightCornerFunctor he).map f).1 ≫
      eqToHom _) ≫ (e.weightFamily he).idem (l.as + s) =
        (e.weightFamily he).idem (k.as + s) ≫ ((e.weightCornerFunctor he).map
          ((WeightCategory.shiftFunctor e.Corner s).map f)).1
    erw [eqToHom_refl, eqToHom_refl]
    simp only [Category.id_comp, Category.comp_id]
    exact WeightCategory.hom_ext ((Corner.val_mul_coe e _).trans (Corner.coe_mul_val e _).symm))

end WeightCorner

section Derived

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

section WeightCorner

variable [Fact (e.val ∈ wgrading (M := A) 0)]
  [CatModule.HasDerivedCategory.{max u t, max u t} (WeightCategory e.Corner)]


/-- Keller's equivalence `D(C_{eAe}) ≌ D((e.weightFamily he).Corner)` along the isomorphism of dg
categories `weightCornerFunctor`. -/
noncomputable def weightCornerEquivalence :
    CatModule.DerivedCategory.{max u t, max u t} (WeightCategory e.Corner) ≌
      CatModule.DerivedCategory.{max u t, max u t} (e.weightFamily he).Corner :=
  CatModule.DerivedCategory.kellerEquivalence.{t} (e.isQuasiEquivalence_weightCornerFunctor he)

noncomputable instance weightCornerEquivalence_functor_commShift :
    (e.weightCornerEquivalence.{t} he).functor.CommShift ℤ :=
  inferInstanceAs ((CatModule.DerivedCategory.kellerEquivalence.{t}
    (e.isQuasiEquivalence_weightCornerFunctor he)).functor.CommShift ℤ)

instance weightCornerEquivalence_functor_isTriangulated :
    (e.weightCornerEquivalence.{t} he).functor.IsTriangulated :=
  inferInstanceAs (CatModule.DerivedCategory.kellerEquivalence.{t}
    (e.isQuasiEquivalence_weightCornerFunctor he)).functor.IsTriangulated

/-- Keller's equivalence `D(C_{eAe}) ≌ D((e.weightFamily he).Corner)` commutes with the internal
shifts. -/
noncomputable def weightCornerEquivalenceInternalShiftIso (s : ℤ) :
    (e.weightCornerEquivalence.{t} he).functor ⋙ e.cornerInternalShift he s ≅
      CatModule.DerivedCategory.internalShift e.Corner s ⋙
        (e.weightCornerEquivalence.{t} he).functor :=
  (e.weightCornerEquivalence.{t} he).functorCompIsoOfInverseCompIso
    ((CatModule.DerivedCategory.restrictCompIso (e.weightCornerFunctor he) _).symm ≪≫
      CatModule.DerivedCategory.restrictNatIso (e.weightCornerFunctorCompShiftIso he s)
        (fun _ => id_mem_grading _) (fun _ => d_id _) (fun _ => id_mem_grading _)
        (fun _ => d_id _) ≪≫
      CatModule.DerivedCategory.restrictCompIso _ (e.weightCornerFunctor he))


/-- **Graded Morita theory for an idempotent** (repaired form of Roadmap 7.3). Let `A` be a
bigraded dg ring and `e` an idempotent cocycle of bidegree `(0, 0)` which is full up to homotopy
(`1 = ∑ₖ aₖ e bₖ + d s` with `aₖ, bₖ ∈ Z⁰(A)`). Then the derived categories of bigraded dg
modules over `e A e` and over `A`, i.e. of the weight dg categories `C_{eAe}` and `C_A`, are
equivalent; the functor is triangulated (`gradedMoritaEquivalence_functor_isTriangulated`) and
commutes with the internal shifts (`gradedMoritaEquivalenceInternalShiftIso`). -/
noncomputable def gradedMoritaEquivalence (h : e.IsFullH0) :
    CatModule.DerivedCategory.{max u t, max u t} (WeightCategory e.Corner) ≌
      CatModule.DerivedCategory.{max u t, max u t} (WeightCategory A) :=
  (e.weightCornerEquivalence.{t} he).trans (weightMoritaEquivalence.{t, w₂} he h)

noncomputable instance gradedMoritaEquivalence_functor_commShift (h : e.IsFullH0) :
    (gradedMoritaEquivalence.{t, w₂} he h).functor.CommShift ℤ :=
  inferInstanceAs (((e.weightCornerEquivalence.{t} he).trans
    (weightMoritaEquivalence.{t, w₂} he h)).functor.CommShift ℤ)

instance gradedMoritaEquivalence_functor_isTriangulated (h : e.IsFullH0) :
    (gradedMoritaEquivalence.{t, w₂} he h).functor.IsTriangulated :=
  isTriangulated_trans_functor (e.weightCornerEquivalence.{t} he)
    (weightMoritaEquivalence.{t, w₂} he h) inferInstance inferInstance

/-- The graded Morita equivalence `D(C_{eAe}) ≌ D(C_A)` commutes with the internal shifts:
`F(M)⟨s⟩ ≅ F(M⟨s⟩)`. -/
noncomputable def gradedMoritaEquivalenceInternalShiftIso (h : e.IsFullH0) (s : ℤ) :
    (gradedMoritaEquivalence.{t, w₂} he h).functor ⋙
        CatModule.DerivedCategory.internalShift A s ≅
      CatModule.DerivedCategory.internalShift e.Corner s ⋙
        (gradedMoritaEquivalence.{t, w₂} he h).functor :=
  Functor.isoWhiskerLeft (e.weightCornerEquivalence.{t} he).functor
      (weightMoritaEquivalenceInternalShiftIso.{t, w₂} he h s) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (e.weightCornerEquivalenceInternalShiftIso.{t} he s)
      (weightMoritaEquivalence.{t, w₂} he h).functor ≪≫
    Functor.associator _ _ _

end WeightCorner

end Derived

end DGIdempotent

end DG
