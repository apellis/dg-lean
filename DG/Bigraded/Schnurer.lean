import DG.Bigraded.GradedSemisimple
import DG.Bigraded.Positive
import DG.Category.Derived.Schnurer
import DG.Category.Weight

/-!
# Schnürer's theorem for positive bigraded dg rings

Let `A` be a bigraded dg ring (a dg ring with an internal weight grading, `DG.BigradedDGRing A`)
and `C_A = DG.WeightCategory A` its weight dg category (objects `k : ℤ`, `C_A(k, l) = A⟨l - k⟩`),
whose dg modules are the bigraded dg `A`-modules (`DG.CatModule.weightEquivalence`); `D(C_A)` is
the derived category of bigraded dg `A`-modules. This file proves Roadmap 7.2 in both versions,
by applying Schnürer's theorem for positive dg categories
(`DG.DGCategory.IsPositive.isCompact_iff`) to `C_A`.

## (a) The graded version

`A` is *graded positive* (`DG.IsGradedPositive A`) if `Aⁿ = 0` for `n < 0`, `d = 0` on `A⁰`, and
the weight-graded ring `A⁰ = ⨁ k, A^{0,k}` is graded semisimple (`DG.IsGradedSemisimpleRing`: its
lattice of homogeneous left ideals is complemented, equivalently every graded `A⁰`-module is a
direct sum of graded simple modules).

* `DG.WeightCategory.idempotent_isSimple_iff`: a degree-`0` idempotent of an object of `C_A` is
  simple in the degree-`0` category of `C_A` iff it is a graded simple idempotent of `A⁰`.
* `DG.WeightCategory.isPositive_iff`: `C_A` is a positive dg category iff `A` is graded
  positive; the degree-`0` category of `C_A` is semisimple exactly when `A⁰` is graded
  semisimple.
* `DG.IsGradedPositive.isCompact_iff`: **Schnürer's theorem for bigraded dg rings**: an object of
  `D(C_A)` is compact iff it is isomorphic to a finite-cell module with ordered cells
  `(e · C_A(k, -))⟦n⟧`. Under `DG.CatModule.weightEquivalence` the cell `e · C_A(k, -)`, for an
  idempotent `e ∈ A^{0,0}`, is the bigraded module `A e` with its weights shifted by `k`
  (`(e · C_A(k, -))(l) = (A e)^{l - k}` in weight `l`), so the cells are shifted in both gradings.
* `DG.IsGradedPositive.closure_simpleCell_eq_top`: `K₀(D(C_A)^c)` is generated as an abelian group
  by the classes of the cells `Q (e · C_A(k, -))` with `e` graded simple.

Note that `K₀(A⁰)` need not be free over `ℤ[q, q⁻¹]` here: a graded simple module isomorphic to
its shift `⟨d⟩` (e.g. over a graded division ring with a unit of weight `d`) contributes
`ℤ[q, q⁻¹]/(q^d - 1)`.

## (b) The ungraded version

* `DG.IsPositive.isGradedPositive`: a positive bigraded dg ring (`A⁰` semisimple as a ring) is
  graded positive, since a semisimple ring is graded semisimple for every grading
  (`DG.isGradedSemisimpleRing_of_isSemisimpleRing`).
* `DG.IsPositive.isCompact_iff_weight`: Schnürer's theorem for `D(C_A)` under this hypothesis.
* `DG.isGradedPositive_iff_isPositive`: for `A⁰` finite-dimensional over a field the two
  hypotheses coincide (more generally when the weight grading of `A⁰` is bounded below,
  `DG.isGradedPositive_iff_isPositive_of_bddBelow`): a graded simple idempotent then generates a
  simple left ideal (`DG.isSimpleModule_of_isGradedSimpleIdempotent`).
-/

open CategoryTheory Limits Pretriangulated DirectSum

universe w u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace DG

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [InternalGrading A]
  [BigradedDGRing A]

variable (A) in
/-- A bigraded dg ring is *graded positive* (Roadmap 7.2 (a)): `Aⁿ = 0` for `n < 0`, `d = 0` on
`A⁰`, and the weight-graded ring `A⁰` is graded semisimple. -/
structure IsGradedPositive : Prop where
  /-- `A` is non-negatively graded (cohomologically). -/
  grading_eq_bot : ∀ n < 0, grading (M := A) n = ⊥
  /-- `A⁰`, graded by weight, is graded semisimple. -/
  isGradedSemisimple : IsGradedSemisimpleRing (degreeZeroWGrading A)
  /-- `d (A⁰) = 0`. -/
  d_eq_zero_of_mem_zero : ∀ a ∈ grading (M := A) 0, d a = 0

/-- A positive bigraded dg ring (with `A⁰` semisimple as a ring) is graded positive: a
semisimple ring is graded semisimple (Roadmap 7.2 (b)). -/
theorem IsPositive.isGradedPositive (hA : IsPositive A) : IsGradedPositive A where
  grading_eq_bot := hA.grading_eq_bot
  isGradedSemisimple := by
    have := hA.isSemisimple
    exact isGradedSemisimpleRing_of_isSemisimpleRing _
  d_eq_zero_of_mem_zero := hA.d_eq_zero_of_mem_zero

/-- If the weight grading of `A⁰` is bounded below, graded positivity and positivity coincide
(Roadmap 7.2: the two hypotheses of (a) and (b) agree in this case). -/
theorem isGradedPositive_iff_isPositive_of_bddBelow
    (hbdd : ∃ N : ℤ, ∀ k < N, ∀ x ∈ degreeZeroWGrading A k, x = 0) :
    IsGradedPositive A ↔ IsPositive A :=
  ⟨fun h => ⟨h.grading_eq_bot, isSemisimpleRing_of_isGradedSemisimpleRing h.isGradedSemisimple hbdd,
    h.d_eq_zero_of_mem_zero⟩, fun h => h.isGradedPositive⟩

/-- **The finite-dimensional coincidence** (Roadmap 7.2): if `A⁰` is finite-dimensional over a
field `K` (with weight components stable under `K`), then `A` is graded positive (`A⁰` graded
semisimple) iff it is positive (`A⁰` semisimple). -/
theorem isGradedPositive_iff_isPositive (K : Type*) [Field K] [Algebra K (degreeZeroSubring A)]
    [FiniteDimensional K (degreeZeroSubring A)]
    (hK : ∀ k (c : K) {x : degreeZeroSubring A}, x ∈ degreeZeroWGrading A k →
      c • x ∈ degreeZeroWGrading A k) :
    IsGradedPositive A ↔ IsPositive A :=
  isGradedPositive_iff_isPositive_of_bddBelow
    (exists_forall_lt_eq_zero_of_finiteDimensional K hK)

namespace WeightCategory

/-! ### Simple idempotents of `C_A` -/

omit [DGRing A] in
theorem val_congr {k l : WeightCategory A} {f g : k ⟶ l} (h : f = g) : (f.1 : A) = g.1 :=
  congrArg (fun f : k ⟶ l => (f.1 : A)) h

omit [DGRing A] [BigradedDGRing A] in
theorem mem_wgrading_of_eq {a : A} {m n : ℤ} (h : m = n) (ha : a ∈ wgrading (M := A) m) :
    a ∈ wgrading (M := A) n :=
  h ▸ ha

/-- A degree-`0` idempotent cocycle of an object of `C_A`, as an element of `A⁰`. -/
def idempotentToZero {k : WeightCategory A} (e : DGCategory.Idempotent k) :
    degreeZeroSubring A :=
  ⟨e.val.1, e.mem_grading⟩

@[simp]
theorem coe_idempotentToZero {k : WeightCategory A} (e : DGCategory.Idempotent k) :
    (idempotentToZero e : A) = e.val.1 :=
  rfl

theorem idempotentToZero_mem {k : WeightCategory A} (e : DGCategory.Idempotent k) :
    idempotentToZero e ∈ degreeZeroWGrading A 0 :=
  mem_wgrading_of_eq (sub_self k.as) e.val.2

theorem isIdempotentElem_idempotentToZero {k : WeightCategory A} (e : DGCategory.Idempotent k) :
    IsIdempotentElem (idempotentToZero e) :=
  Subtype.ext (val_congr e.comp_self)

/-- A degree-`0` idempotent `e` of an object of `C_A` is simple in the degree-`0` category of
`C_A` iff it is a graded simple idempotent of the weight-graded ring `A⁰`. -/
theorem idempotent_isSimple_iff {k : WeightCategory A} (e : DGCategory.Idempotent k) :
    e.IsSimple ↔ IsGradedSimpleIdempotent (degreeZeroWGrading A) (idempotentToZero e) := by
  constructor
  · rintro ⟨hne, hs⟩
    refine ⟨fun h => hne (hom_ext (show e.val.1 = 0 from congrArg Subtype.val h)),
      fun j h hh hhe hh0 => ?_⟩
    have hmem : (h : A) ∈ wgrading (M := A) ((⟨k.as + j⟩ : WeightCategory A).as - k.as) :=
      mem_wgrading_of_eq (add_sub_cancel_left k.as j).symm hh
    obtain ⟨g, hg, hgh⟩ := hs (Y := ⟨k.as + j⟩) (homMk (h : A) hmem) h.2
      (hom_ext (show (h : A) * e.val.1 = h from congrArg Subtype.val hhe))
      (fun h' => hh0 (Subtype.ext (val_congr h')))
    refine ⟨⟨g.1, hg⟩, mem_wgrading_of_eq (by ring) g.2, Subtype.ext (val_congr hgh)⟩
  · rintro ⟨hne, hs⟩
    refine ⟨fun h => hne (Subtype.ext (val_congr h)), fun Y h hh hhe hh0 => ?_⟩
    obtain ⟨g, hg, hgh⟩ := hs (j := Y.as - k.as) (h := ⟨h.1, hh⟩) h.2
      (Subtype.ext (val_congr hhe))
      (fun h' => hh0 (hom_ext (show (h.1 : A) = 0 from congrArg Subtype.val h')))
    have hgw : (g : A) ∈ wgrading (M := A) (k.as - Y.as) := mem_wgrading_of_eq (neg_sub _ _) hg
    exact ⟨homMk (g : A) hgw, g.2, hom_ext (show (g : A) * h.1 = e.val.1 from
      congrArg Subtype.val hgh)⟩

/-! ### Positivity of `C_A` -/

omit [DGRing A] in
theorem eq_zero_of_mem_wgrading_of_isPositive (hC : DGCategory.IsPositive (WeightCategory A))
    {n k : ℤ} (hn : n < 0) {a : A} (ha : a ∈ grading n) (hk : a ∈ wgrading (M := A) k) :
    a = 0 := by
  have hk' : a ∈ wgrading (M := A) ((⟨k⟩ : WeightCategory A).as - (⟨0⟩ : WeightCategory A).as) :=
    by rwa [sub_zero]
  have := hC.eq_zero_of_neg hn (f := homMk (k := ⟨0⟩) (l := ⟨k⟩) a hk') ha
  exact congrArg Subtype.val this

/-- `C_A` is a positive dg category iff `A` is graded positive: the degree-`0` category of `C_A`
is semisimple iff the weight-graded ring `A⁰` is graded semisimple (Roadmap 7.2 (a)). -/
theorem isPositive_iff : DGCategory.IsPositive (WeightCategory A) ↔ IsGradedPositive A := by
  classical
  constructor
  · intro hC
    refine ⟨fun n hn => (AddSubgroup.eq_bot_iff_forall _).mpr fun a ha => ?_, ?_, fun a ha => ?_⟩
    · rw [← DirectSum.sum_support_decompose (wgrading (M := A)) a]
      exact Finset.sum_eq_zero fun k _ => eq_zero_of_mem_wgrading_of_isPositive hC hn
        (decompose_wgrading_mem_grading ha k) (SetLike.coe_mem _)
    · obtain ⟨l, hs, hl, hsum⟩ := hC.semisimple ⟨0⟩
      refine isGradedSemisimpleRing_iff_exists_list.mpr
        ⟨l.map idempotentToZero, fun x hx => ?_, ?_, ?_⟩
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
        exact ⟨idempotentToZero_mem e, isIdempotentElem_idempotentToZero e,
          (idempotent_isSimple_iff e).mp (hs e he)⟩
      · rw [List.pairwise_map]
        exact hl.imp fun h => ⟨Subtype.ext (val_congr h.2), Subtype.ext (val_congr h.1)⟩
      · apply Subtype.ext
        have h1 := map_list_sum (degreeZeroSubring A).subtype (l.map idempotentToZero)
        have h2 := map_list_sum (AddSubgroup.subtype (wgrading (M := A)
          ((⟨0⟩ : WeightCategory A).as - (⟨0⟩ : WeightCategory A).as)))
          (l.map DGCategory.Idempotent.val)
        rw [List.map_map] at h1 h2
        rw [hsum] at h2
        exact h1.trans h2.symm
    · rw [← DirectSum.sum_support_decompose (wgrading (M := A)) a, map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      have hk : (decompose (wgrading (M := A)) a k : A) ∈
          wgrading (M := A) ((⟨k⟩ : WeightCategory A).as - (⟨0⟩ : WeightCategory A).as) := by
        rw [sub_zero]
        exact SetLike.coe_mem _
      exact congrArg Subtype.val (hC.d_eq_zero (X := ⟨0⟩) (Y := ⟨k⟩) (f := homMk _ hk)
        (decompose_wgrading_mem_grading ha k))
  · intro hA
    refine ⟨fun hn f hf => ?_, fun X => ?_, fun hf => hom_ext (hA.d_eq_zero_of_mem_zero _ hf)⟩
    · have := hA.grading_eq_bot _ hn
      rw [mem_grading_iff, this] at hf
      exact hom_ext hf
    · obtain ⟨l, hl, hlp, hlsum⟩ := hA.isGradedSemisimple.exists_list_sum_eq_one
      have hw : ∀ s ∈ l, (s : A) ∈ wgrading (M := A) (X.as - X.as) := fun s hs => by
        rw [sub_self]
        exact (hl s hs).1
      let E : ∀ s ∈ l, DGCategory.Idempotent X := fun s hs =>
        { val := homMk (s : A) (hw s hs)
          mem_cocycles := ⟨s.2, hom_ext (hA.d_eq_zero_of_mem_zero _ s.2)⟩
          comp_self := hom_ext (show (s : A) * s = s from congrArg Subtype.val (hl s hs).2.1.eq) }
      refine ⟨l.pmap E fun _ h => h, fun e he => ?_, ?_, ?_⟩
      · obtain ⟨s, hs, rfl⟩ := List.mem_pmap.mp he
        rw [idempotent_isSimple_iff]
        exact (hl s hs).2.2
      · rw [List.pairwise_pmap]
        refine hlp.imp_of_mem fun {a b} _ _ hab _ _ => ?_
        exact ⟨hom_ext (show (b : A) * a = 0 from congrArg Subtype.val hab.2),
          hom_ext (show (a : A) * b = 0 from congrArg Subtype.val hab.1)⟩
      · rw [List.map_pmap]
        apply hom_ext
        have h1 := map_list_sum (AddSubgroup.subtype (wgrading (M := A) (X.as - X.as)))
          (l.pmap (fun (s : degreeZeroSubring A) (hs : s ∈ l) => homMk (s : A) (hw s hs))
            fun _ h => h)
        rw [List.map_pmap] at h1
        refine h1.trans ?_
        change (l.pmap (fun (s : degreeZeroSubring A) (_ : s ∈ l) => (s : A))
          fun _ h => h).sum = (1 : A)
        rw [List.pmap_eq_map]
        have h2 := map_list_sum (degreeZeroSubring A).subtype l
        rw [hlsum] at h2
        exact h2.symm.trans (map_one _)

end WeightCategory

/-! ### Schnürer's theorem for `D(C_A)` -/

open CatModule CatModule.DerivedCategory

namespace IsGradedPositive

/-- For `A` graded positive, the weight dg category `C_A` is positive. -/
theorem isPositive_weightCategory (hA : IsGradedPositive A) :
    DGCategory.IsPositive (WeightCategory A) :=
  WeightCategory.isPositive_iff.mpr hA

variable (hA : IsGradedPositive A)
  [CatModule.HasDerivedCategory.{max u w, max u w} (WeightCategory A)]
include hA

/-- **Schnürer's theorem for graded positive bigraded dg rings** (Roadmap 7.2 (a)): an object of
the derived category `D(C_A)` of bigraded dg modules is compact iff it is isomorphic to the image
of a finite-cell dg module over `C_A` with ordered cells `(eᵢ · C_A(kᵢ, -))⟦nᵢ⟧`, which are
shifted in both gradings; the idempotents `eᵢ ∈ A^{0,0}` can moreover be taken graded simple. -/
theorem exists_finiteCellFiltration_of_isCompact
    {Y : CatModule.DerivedCategory.{max u w, max u w} (WeightCategory A)}
    (hY : IsCompact.{max u w} Y) :
    ∃ (P : CatModule.{max u w} (WeightCategory A)) (S : FiniteCellFiltration.{max u w} P),
      S.IsOrdered ∧ (∀ i, IsGradedSimpleIdempotent (degreeZeroWGrading A)
        (WeightCategory.idempotentToZero (S.e i))) ∧ Nonempty (Y ≅ Q.obj P) := by
  obtain ⟨P, S, hS, he, hY⟩ :=
    hA.isPositive_weightCategory.exists_finiteCellFiltration_of_isCompact.{max u w} hY
  exact ⟨P, S, hS, fun i => (WeightCategory.idempotent_isSimple_iff _).mp (he i), hY⟩

/-- **Schnürer's theorem for graded positive bigraded dg rings** (Roadmap 7.2 (a)): an object of
`D(C_A)` is compact iff it is isomorphic to a finite-cell module with ordered cells. -/
theorem isCompact_iff {Y : CatModule.DerivedCategory.{max u w, max u w} (WeightCategory A)} :
    IsCompact.{max u w} Y ↔ ∃ (P : CatModule.{max u w} (WeightCategory A))
      (S : FiniteCellFiltration.{max u w} P), S.IsOrdered ∧ Nonempty (Y ≅ Q.obj P) :=
  hA.isPositive_weightCategory.isCompact_iff.{max u w}

end IsGradedPositive

namespace IsPositive

variable (hA : IsPositive A) [CatModule.HasDerivedCategory.{max u w, max u w} (WeightCategory A)]
include hA

/-- **Schnürer's theorem for positive bigraded dg rings** (Roadmap 7.2 (b), `A⁰` semisimple as a
ring): an object of `D(C_A)` is compact iff it is isomorphic to a finite-cell module with ordered
cells. -/
theorem isCompact_iff_weight
    {Y : CatModule.DerivedCategory.{max u w, max u w} (WeightCategory A)} :
    IsCompact.{max u w} Y ↔ ∃ (P : CatModule.{max u w} (WeightCategory A))
      (S : FiniteCellFiltration.{max u w} P), S.IsOrdered ∧ Nonempty (Y ≅ Q.obj P) :=
  hA.isGradedPositive.isCompact_iff

end IsPositive

end DG

end
