import DG.K0.CellFamily
import DG.K0.Field
import DG.K0.LeftCorner
import DG.Positive.K0

/-!
# `K₀` of a positive dg ring is `K₀` of its degree-`0` part, and is free

Let `A` be a positive dg ring (`DG.IsPositive A`: `Aⁿ = 0` for `n < 0`, `A⁰` semisimple,
`d (A⁰) = 0`). This file proves Roadmap 6.3:

* `DG.IsPositive.K0DegreeZeroEquiv : K₀(A) ≃+ K₀(A⁰)`, induced by the projection
  `A → A⁰` (`DG.IsPositive.projZero`), with inverse induced by the inclusion `A⁰ → A`; it sends
  `[A e]` to `[A⁰ e]` (`DG.IsPositive.K0DegreeZeroEquiv_leftCorner`). The two composites are
  the identity: one is `K₀` of `projZero ∘ subtype = id`, the other is the identity on the
  generators `[A e]` (`DG.IsPositive.closure_leftCorner_eq_top`).
* `DG.IsPositive.basis`: `K₀(A)` is free on the classes `[A e]`, `e` running over a set of
  representatives of the simple idempotents of `A⁰` up to equivalence
  (`DG.DGIdempotent.Equiv`), i.e. of the simple `A⁰`-modules `A⁰ e` up to isomorphism
  (`DG.idemEquiv_iff_nonempty_linearEquiv`).
  For `A` concentrated in degree `0` this is `DG.IsPositive.basisOfConcentrated`; the general
  case is transported along the first isomorphism.
* `DG.IsPositive.K0EquivIntOfDivisionRing`: `K₀(A) ≃+ ℤ`, `[A] ↦ 1`, when `A⁰` is a division
  ring; `DG.IsPositive.K0EquivIntOfField` for a dg algebra over a field `k` with `A⁰ = k`.

No field or finiteness hypothesis is needed: the number of isomorphism classes of simple
`A⁰`-modules is finite since `A⁰` is semisimple, but this is not used.

## Proof of freeness

Generation is Schnürer's theorem (`DG.IsPositive.closure_leftCorner_eq_top`). For linear
independence it suffices, by the first isomorphism, to treat `A⁰`, a positive dg ring
concentrated in degree `0`. Its derived category has the semisimple cell family
(`DG.IsSemisimpleCellFamily`) of the cells `(A⁰ e)⟦n⟧`, `e` simple: there are no nonzero
morphisms between cells of different shifts, since `A⁰` has no nonzero components in nonzero
degrees (`DG.IsPositive.cell_hom_eq_zero_of_gt`). For each simple `e`, the Euler characteristic
`X ↦ ∑ₙ (-1)ⁿ dim Hom(A⁰ e, X⟦n⟧)`, dimensions over the division ring `End(A⁰ e)ᵐᵒᵖ`, is additive
on distinguished triangles and separates the classes `[A⁰ f]`
(`DG.IsSemisimpleCellFamily.basis`). This realizes the invariant "alternating sum of the
multiplicities of the simple module `A⁰ e` in the cohomology".

## Equivalence of idempotents

Two idempotents `e`, `f` of a ring `R` are *equivalent* (`DG.IdemEquiv R e f`) if there are
`b ∈ e R f` and `c ∈ f R e` with `b c = e` and `c b = f`; equivalently `R e ≅ R f` as left
`R`-modules (`DG.idemEquiv_iff_nonempty_linearEquiv`). For degree-`0` idempotent cocycles of a
dg ring this is `DG.DGIdempotent.Equiv`, taken in `A⁰`; for a positive dg ring and simple `e`,
`f`, it holds iff `Q (A e) ≅ Q (A f)` in `D(A)` (`DG.IsPositive.equiv_iff_nonempty_cell_iso`).
-/

open CategoryTheory Limits Pretriangulated DirectSum

universe u

namespace DG

/-! ### Equivalence of idempotents in a ring -/

section Ring

variable (R : Type*) [Ring R]

/-- Two idempotents `e`, `f` of a ring are *equivalent* if there are `b ∈ e R f` and
`c ∈ f R e` with `b c = e` and `c b = f`. -/
def IdemEquiv (e f : R) : Prop :=
  ∃ b c : R, e * b = b ∧ b * f = b ∧ f * c = c ∧ c * e = c ∧ b * c = e ∧ c * b = f

variable {R}

theorem IdemEquiv.refl {e : R} (he : IsIdempotentElem e) : IdemEquiv R e e :=
  ⟨e, e, he.eq, he.eq, he.eq, he.eq, he.eq, he.eq⟩

theorem IdemEquiv.symm {e f : R} (h : IdemEquiv R e f) : IdemEquiv R f e := by
  obtain ⟨b, c, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨c, b, h3, h4, h1, h2, h6, h5⟩

theorem IdemEquiv.map {S : Type*} [Ring S] (φ : R →+* S) {e f : R} (h : IdemEquiv R e f) :
    IdemEquiv S (φ e) (φ f) := by
  obtain ⟨b, c, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨φ b, φ c, by rw [← map_mul, h1], by rw [← map_mul, h2], by rw [← map_mul, h3],
    by rw [← map_mul, h4], by rw [← map_mul, h5], by rw [← map_mul, h6]⟩

theorem idemEquiv_ringEquiv_iff {S : Type*} [Ring S] (φ : R ≃+* S) {e f : R} :
    IdemEquiv S (φ e) (φ f) ↔ IdemEquiv R e f := by
  refine ⟨fun h => ?_, fun h => h.map (φ : R →+* S)⟩
  simpa using h.map (φ.symm : S →+* R)

/-- Equivalent idempotents are those with isomorphic left ideals: `R e ≅ R f`. -/
theorem idemEquiv_iff_nonempty_linearEquiv {e f : R} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) :
    IdemEquiv R e f ↔ Nonempty (Submodule.span R {e} ≃ₗ[R] Submodule.span R {f}) := by
  constructor
  · rintro ⟨b, c, h1, h2, h3, h4, h5, h6⟩
    let ρ : Submodule.span R {e} →ₗ[R] Submodule.span R {f} :=
      { toFun := fun x => ⟨x * b, (mem_span_singleton_iff_mul_eq hf).mpr (by
          rw [mul_assoc, h2])⟩
        map_add' := fun x y => Subtype.ext (add_mul _ _ _)
        map_smul' := fun a x => Subtype.ext (mul_assoc _ _ _) }
    let σ : Submodule.span R {f} →ₗ[R] Submodule.span R {e} :=
      { toFun := fun x => ⟨x * c, (mem_span_singleton_iff_mul_eq he).mpr (by
          rw [mul_assoc, h4])⟩
        map_add' := fun x y => Subtype.ext (add_mul _ _ _)
        map_smul' := fun a x => Subtype.ext (mul_assoc _ _ _) }
    refine ⟨{ ρ with
      invFun := σ
      left_inv := fun x => Subtype.ext ?_
      right_inv := fun x => Subtype.ext ?_ }⟩
    · change (x : R) * b * c = x
      rw [mul_assoc, h5]
      exact (mem_span_singleton_iff_mul_eq he).mp x.2
    · change (x : R) * c * b = x
      rw [mul_assoc, h6]
      exact (mem_span_singleton_iff_mul_eq hf).mp x.2
  · rintro ⟨φ⟩
    have heS : e ∈ Submodule.span R {e} := Submodule.subset_span rfl
    have hfS : f ∈ Submodule.span R {f} := Submodule.subset_span rfl
    set b : R := ((φ ⟨e, heS⟩ : Submodule.span R {f}) : R)
    set c : R := ((φ.symm ⟨f, hfS⟩ : Submodule.span R {e}) : R)
    have hφ : ∀ x : Submodule.span R {e}, (φ x : R) = x * b := fun x => by
      have hx : x = (x : R) • (⟨e, heS⟩ : Submodule.span R {e}) :=
        Subtype.ext ((mem_span_singleton_iff_mul_eq he).mp x.2).symm
      conv_lhs => rw [hx]
      rw [map_smul]
      rfl
    have hψ : ∀ y : Submodule.span R {f}, (φ.symm y : R) = y * c := fun y => by
      have hy : y = (y : R) • (⟨f, hfS⟩ : Submodule.span R {f}) :=
        Subtype.ext ((mem_span_singleton_iff_mul_eq hf).mp y.2).symm
      conv_lhs => rw [hy]
      rw [map_smul]
      rfl
    have hb : b * f = b := (mem_span_singleton_iff_mul_eq hf).mp (φ ⟨e, heS⟩).2
    have hc : c * e = c := (mem_span_singleton_iff_mul_eq he).mp (φ.symm ⟨f, hfS⟩).2
    have hbc : b * c = e := by
      have := hψ (φ ⟨e, heS⟩)
      rw [LinearEquiv.symm_apply_apply] at this
      exact this.symm
    have hcb : c * b = f := by
      have := hφ (φ.symm ⟨f, hfS⟩)
      rw [LinearEquiv.apply_symm_apply] at this
      exact this.symm
    refine ⟨b, c, ?_, hb, ?_, hc, hbc, hcb⟩
    · rw [← hbc, mul_assoc, hcb, hb]
    · rw [← hcb, mul_assoc, hbc, hc]

/-- Simplicity of `R x` is invariant under ring isomorphisms. -/
theorem isSimpleModule_span_singleton_ringEquiv_iff {S : Type*} [Ring S] (φ : R ≃+* S) (x : R) :
    IsSimpleModule S (Submodule.span S {φ x}) ↔ IsSimpleModule R (Submodule.span R {x}) := by
  let l : Submodule.span R {x} →ₛₗ[(φ : R →+* S)] Submodule.span S {φ x} :=
    { toFun := fun y => ⟨φ y, by
        obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp y.2
        rw [← hr, smul_eq_mul, map_mul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)⟩
      map_add' := fun y z => Subtype.ext (map_add φ _ _)
      map_smul' := fun r y => Subtype.ext (map_mul φ _ _) }
  refine (l.isSimpleModule_iff_of_bijective ⟨fun y z h => ?_, fun z => ?_⟩).symm
  · exact Subtype.ext (φ.injective (congrArg Subtype.val h))
  · obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp z.2
    refine ⟨⟨φ.symm r * x, Submodule.smul_mem _ _ (Submodule.subset_span rfl)⟩,
      Subtype.ext ?_⟩
    change φ (φ.symm r * x) = z
    rw [map_mul, RingEquiv.apply_symm_apply, ← hr, smul_eq_mul]

end Ring

/-! ### Equivalence of degree-`0` idempotent cocycles -/

namespace DGIdempotent

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]

omit [DGRing A] in
theorem eq_of_val_eq {e f : DGIdempotent A} (h : e.val = f.val) : e = f := by
  cases e
  cases f
  cases h
  rfl

/-- Two degree-`0` idempotent cocycles are *equivalent* if they are equivalent idempotents of
`A⁰`, i.e. `A⁰ e ≅ A⁰ f`. -/
def Equiv (e f : DGIdempotent A) : Prop :=
  IdemEquiv (degreeZeroSubring A) e.toZero f.toZero

theorem Equiv.symm {e f : DGIdempotent A} (h : e.Equiv f) : f.Equiv e :=
  IdemEquiv.symm h

theorem Equiv.refl (e : DGIdempotent A) : e.Equiv e :=
  IdemEquiv.refl e.isIdempotentElem_toZero

theorem equiv_iff_nonempty_linearEquiv {e f : DGIdempotent A} :
    e.Equiv f ↔ Nonempty (Submodule.span (degreeZeroSubring A) {e.toZero} ≃ₗ[degreeZeroSubring A]
      Submodule.span (degreeZeroSubring A) {f.toZero}) :=
  idemEquiv_iff_nonempty_linearEquiv e.isIdempotentElem_toZero f.isIdempotentElem_toZero

end DGIdempotent

namespace IsPositive

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] (hA : IsPositive A)
include hA

open _root_.DG.DerivedCategory

/-! ### Cells of equivalent idempotents -/

section Cells

variable [HasDerivedCategory.{u, u} A]

/-- Equivalent idempotents have isomorphic cells: right multiplication by `b` and `c` are
inverse isomorphisms `(A e)⟦n⟧ ≅ (A f)⟦n⟧` of dg modules. -/
theorem nonempty_cell_iso_of_equiv {e f : DGIdempotent A} (h : e.Equiv f) (n : ℤ) :
    Nonempty (cell A e n ≅ cell A f n) := by
  obtain ⟨b, c, h1, h2, h3, h4, h5, h6⟩ := h
  have h2' : (b : A) * f.val = b := congrArg Subtype.val h2
  have h4' : (c : A) * e.val = c := congrArg Subtype.val h4
  have h5' : (b : A) * c = e.val := congrArg Subtype.val h5
  have h6' : (c : A) * b = f.val := congrArg Subtype.val h6
  let β : DGModuleCat.of A (Shift n e.LeftCorner) ⟶ DGModuleCat.of A (Shift n f.LeftCorner) :=
    DGModuleCat.ofHom ((e.rightMul f b b.2 (hA.d_eq_zero b.2) h2').shift n)
  let γ : DGModuleCat.of A (Shift n f.LeftCorner) ⟶ DGModuleCat.of A (Shift n e.LeftCorner) :=
    DGModuleCat.ofHom ((f.rightMul e c c.2 (hA.d_eq_zero c.2) h4').shift n)
  refine ⟨Q.mapIso
    { hom := β
      inv := γ
      hom_inv_id := DGModuleCat.hom_ext (e.shift_hom_ext n ?_)
      inv_hom_id := DGModuleCat.hom_ext (f.shift_hom_ext n ?_) }⟩
  · change Shift.mk n (f.rightMul e c c.2 (hA.d_eq_zero c.2) h4'
      (e.rightMul f b b.2 (hA.d_eq_zero b.2) h2' (DGIdempotent.LeftCorner.idem e))) =
        Shift.mk n (DGIdempotent.LeftCorner.idem e)
    congr 1
    refine Subtype.ext ?_
    change e.val * b * c = e.val
    rw [mul_assoc, h5', e.mul_self]
  · change Shift.mk n (e.rightMul f b b.2 (hA.d_eq_zero b.2) h2'
      (f.rightMul e c c.2 (hA.d_eq_zero c.2) h4' (DGIdempotent.LeftCorner.idem f))) =
        Shift.mk n (DGIdempotent.LeftCorner.idem f)
    congr 1
    refine Subtype.ext ?_
    change f.val * c * b = f.val
    rw [mul_assoc, h6', f.mul_self]

omit hA in
/-- A nonzero morphism `(A e)⟦n⟧ ⟶ (A f)⟦n⟧` between cells of simple idempotents forces `e` and
`f` to be equivalent (Schur's lemma over `A⁰`). -/
theorem _root_.DG.DGIdempotent.equiv_of_cell_hom_ne_zero {e f : DGIdempotent A}
    (he : e.IsSimple) (hf : f.IsSimple) {n : ℤ} (φ : cell A e n ⟶ cell A f n) (hφ : φ ≠ 0) :
    e.Equiv f := by
  obtain ⟨g, rfl⟩ := exists_Q_map_eq (e.isKProjective_leftCorner.shift n) φ
  set x := Shift.mk n (DGIdempotent.LeftCorner.idem e)
  set y : f.LeftCorner := Shift.unmk n (g.hom x) with hydef
  have hy0 : (y : A) ∈ grading 0 := by
    have hmem := g.hom.map_mem (e.mk_idem_mem_grading n)
    rw [Shift.mem_grading_iff', DGIdempotent.LeftCorner.mem_grading_iff, neg_add_cancel] at hmem
    exact hmem
  have hyf : (y : A) * f.val = y := y.2
  have hsm : e.val • x = x := by
    rw [e.smul_mk_idem n e.mem_zero]
    congr 1
    exact Subtype.ext e.mul_self
  have hey : e.val * (y : A) = y := by
    have h1 : g.hom x = e.val • g.hom x := by rw [← map_smul, hsm]
    have h2 := congrArg (fun z => ((Shift.unmk n z : f.LeftCorner) : A)) h1
    simp only [Shift.unmk_smul_eq, Shift.twist_of_mem e.mem_zero, mul_zero, koszulSign_zero,
      one_smul, Submodule.coe_smul, smul_eq_mul] at h2
    exact h2.symm
  have hyne : (y : A) ≠ 0 := by
    intro h
    apply hφ
    have : g = 0 := DGModuleCat.hom_ext (e.shift_hom_ext n (by
      rw [DGModuleCat.hom_zero, DGModuleHom.zero_apply]
      exact Shift.unmk_inj.mp (Subtype.ext h)))
    rw [this, Functor.map_zero]
  obtain ⟨c, hfc, hce, hyc, hcy⟩ := exists_mul_eq_of_isSimpleModule
    e.isIdempotentElem_toZero f.isIdempotentElem_toZero he hf (b := ⟨y, hy0⟩)
    (show e.toZero * ⟨y, hy0⟩ = ⟨y, hy0⟩ from Subtype.ext hey)
    (show ⟨y, hy0⟩ * f.toZero = ⟨y, hy0⟩ from Subtype.ext hyf)
    (fun h => hyne (congrArg Subtype.val h))
  exact ⟨⟨y, hy0⟩, c, Subtype.ext hey, Subtype.ext hyf, hfc, hce, hyc, hcy⟩

/-- For simple idempotents `e`, `f` of a positive dg ring, `(A e)⟦n⟧ ≅ (A f)⟦n⟧` in `D(A)` iff
`e` and `f` are equivalent, i.e. iff `A⁰ e ≅ A⁰ f`. -/
theorem equiv_iff_nonempty_cell_iso {e f : DGIdempotent A} (he : e.IsSimple) (hf : f.IsSimple)
    (n : ℤ) : e.Equiv f ↔ Nonempty (cell A e n ≅ cell A f n) := by
  refine ⟨fun h => hA.nonempty_cell_iso_of_equiv h n, fun ⟨ι⟩ => ?_⟩
  refine DGIdempotent.equiv_of_cell_hom_ne_zero he hf ι.hom fun h => hA.not_isZero_cell he n ?_
  exact (IsZero.iff_id_eq_zero _).mpr (by rw [← ι.hom_inv_id, h, zero_comp])

end Cells

/-! ### Positive dg rings concentrated in degree `0` -/

section Concentrated

variable [HasDerivedCategory.{u, u} A]

omit hA in
/-- If `A` has no components of positive degree, there are no nonzero morphisms
`(A e)⟦n⟧ ⟶ (A f)⟦m⟧` for `n < m`. -/
theorem cell_hom_eq_zero_of_gt (hA0 : ∀ n : ℤ, 0 < n → grading (M := A) n = ⊥)
    {e f : DGIdempotent A} {n m : ℤ} (h : n < m) (φ : cell A e n ⟶ cell A f m) : φ = 0 := by
  obtain ⟨g, rfl⟩ := exists_Q_map_eq (e.isKProjective_leftCorner.shift n) φ
  suffices hg : g = 0 by rw [hg, Functor.map_zero]
  refine DGModuleCat.hom_ext (e.shift_hom_ext n ?_)
  rw [DGModuleCat.hom_zero, DGModuleHom.zero_apply]
  have hmem := g.hom.map_mem (e.mk_idem_mem_grading n)
  rw [Shift.mem_grading_iff', DGIdempotent.LeftCorner.mem_grading_iff, hA0 _ (by omega),
    AddSubgroup.mem_bot] at hmem
  exact Shift.unmk_inj.mp (Subtype.ext hmem)

/-- For a positive dg ring without components of positive degree (i.e. concentrated in degree
`0`), the cells `(A e)⟦n⟧`, `e` simple, form a semisimple cell family. -/
theorem isSemisimpleCellFamily (hA0 : ∀ n : ℤ, 0 < n → grading (M := A) n = ⊥) :
    IsSemisimpleCellFamily (fun (i : SimpleIdempotent A) (n : ℤ) => cell A i.1 n) where
  toIsOrderedCellFamily := hA.isOrderedCellFamily
  eq_zero_of_gt h f := cell_hom_eq_zero_of_gt hA0 h f

/-- **`K₀` of a positive dg ring concentrated in degree `0` is free** on the classes `[A e]`,
`e` running over a set of representatives of the simple idempotents up to equivalence (i.e. of
the simple `A⁰`-modules up to isomorphism). -/
noncomputable def basisOfConcentrated (hA0 : ∀ n : ℤ, 0 < n → grading (M := A) n = ⊥)
    {ι : Type*} (s : ι → SimpleIdempotent A) (hs : ∀ a b, (s a).1.Equiv (s b).1 → a = b)
    (hs' : ∀ e : SimpleIdempotent A, ∃ a, e.1.Equiv (s a).1) :
    Module.Basis ι ℤ (DGRing.K0 A) :=
  (hA.isSemisimpleCellFamily hA0).basis (P := compactSubcategory.{u} (DerivedCategory A))
    (fun X hX => by
      obtain ⟨l, -, hl⟩ := hA.hasOrderedCellTower_of_isCompact (X := X) hX
      exact ⟨l, hl⟩)
    (fun i n => isCompact_cell i.1 n) s
    (fun a b ⟨e⟩ => hs a b (((hA.equiv_iff_nonempty_cell_iso (s a).2 (s b).2 0).mpr ⟨e⟩)))
    (fun i => by
      obtain ⟨a, ha⟩ := hs' i
      exact ⟨a, (hA.equiv_iff_nonempty_cell_iso i.2 (s a).2 0).mp ha⟩)

omit hA in
/-- The class of the cell `(A e)⟦0⟧` is `[A e]`. -/
theorem mk_cell_zero (e : DGIdempotent A) :
    DG.K0.mk (⟨cell A e 0, isCompact_cell e 0⟩ : PerfectDerivedCategory A) =
      DGRing.K0.leftCorner e :=
  DG.K0.mk_eq_of_iso_obj (Q.mapIso (Shift.zeroEquiv (A := A) (M := e.LeftCorner)).toDGModuleCatIso)

theorem basisOfConcentrated_apply (hA0 : ∀ n : ℤ, 0 < n → grading (M := A) n = ⊥)
    {ι : Type*} (s : ι → SimpleIdempotent A) (hs : ∀ a b, (s a).1.Equiv (s b).1 → a = b)
    (hs' : ∀ e : SimpleIdempotent A, ∃ a, e.1.Equiv (s a).1) (a : ι) :
    hA.basisOfConcentrated hA0 s hs hs' a = DGRing.K0.leftCorner (s a).1 := by
  rw [basisOfConcentrated]
  exact (IsSemisimpleCellFamily.basis_apply _ _ _ _ _ _ a).trans (mk_cell_zero _)

end Concentrated

/-! ### The degree-`0` part `A⁰` as a dg ring -/

section DegreeZero

/-- The degree-`0` part of the dg ring `A⁰` is all of `A⁰`: the ring isomorphism
`(A)⁰ ≃ (A⁰)⁰`. -/
def degreeZeroRingEquiv : degreeZeroSubring A ≃+* degreeZeroSubring hA.degreeZeroDGSubring where
  toFun a := ⟨⟨a.1, a.2⟩, mem_degreeZeroSubring.mpr
    (hA.mem_grading_degreeZeroDGSubring_iff.mpr (Or.inl rfl))⟩
  invFun x := ⟨x.1.1, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The dg ring `A⁰` has no components in nonzero degrees. -/
theorem grading_degreeZeroDGSubring_eq_bot {n : ℤ} (hn : n ≠ 0) :
    grading (M := hA.degreeZeroDGSubring) n = ⊥ :=
  eq_bot_iff.mpr fun x hx => by
    rcases hA.mem_grading_degreeZeroDGSubring_iff.mp hx with h | h
    · exact absurd h hn
    · exact (AddSubgroup.mem_bot).mpr h

/-- The degree-`0` part `A⁰` of a positive dg ring is a positive dg ring. -/
theorem isPositive_degreeZeroDGSubring : IsPositive hA.degreeZeroDGSubring where
  grading_eq_bot n hn := hA.grading_degreeZeroDGSubring_eq_bot (by omega)
  isSemisimple :=
    haveI := hA.isSemisimple
    hA.degreeZeroRingEquiv.isSemisimpleRing
  d_eq_zero_of_mem_zero a _ := hA.d_degreeZeroDGSubring a

theorem toZero_map_projZero (e : DGIdempotent A) :
    (e.map hA.projZero).toZero = hA.degreeZeroRingEquiv e.toZero :=
  Subtype.ext (Subtype.ext (hA.projZero_apply_of_mem_zero e.mem_zero))

theorem isSimple_map_projZero_iff (e : DGIdempotent A) :
    (e.map hA.projZero).IsSimple ↔ e.IsSimple := by
  unfold DGIdempotent.IsSimple
  rw [hA.toZero_map_projZero]
  exact isSimpleModule_span_singleton_ringEquiv_iff _ _

theorem equiv_map_projZero_iff (e f : DGIdempotent A) :
    (e.map hA.projZero).Equiv (f.map hA.projZero) ↔ e.Equiv f := by
  unfold DGIdempotent.Equiv
  rw [hA.toZero_map_projZero, hA.toZero_map_projZero]
  exact idemEquiv_ringEquiv_iff _

theorem map_subtype_map_projZero (e : DGIdempotent hA.degreeZeroDGSubring) :
    (e.map (DGSubring.subtype hA.degreeZeroDGSubring)).map hA.projZero = e :=
  DGIdempotent.eq_of_val_eq (Subtype.ext (hA.projZero_apply_of_mem_zero e.val.2))

theorem map_projZero_map_subtype (e : DGIdempotent A) :
    (e.map hA.projZero).map (DGSubring.subtype hA.degreeZeroDGSubring) = e :=
  DGIdempotent.eq_of_val_eq (hA.projZero_apply_of_mem_zero e.mem_zero)

end DegreeZero

/-! ### `K₀(A) ≅ K₀(A⁰)` -/

section K0

variable [HasDerivedCategory.{u, u} A] [HasDerivedCategory.{u, u} hA.degreeZeroDGSubring]

/-- **`K₀(A) ≅ K₀(A⁰)`** for a positive dg ring (Roadmap 6.3), induced by the projection
`A → A⁰`; the inverse is induced by the inclusion `A⁰ → A`. -/
noncomputable def K0DegreeZeroEquiv : DGRing.K0 A ≃+ DGRing.K0 hA.degreeZeroDGSubring where
  toFun := DGRing.K0.map hA.projZero
  invFun := DGRing.K0.map (DGSubring.subtype hA.degreeZeroDGSubring)
  left_inv x := by
    have h : (DGRing.K0.map (DGSubring.subtype hA.degreeZeroDGSubring)).comp
        (DGRing.K0.map hA.projZero) = AddMonoidHom.id _ := by
      refine AddMonoidHom.eq_of_eqOn_dense hA.closure_leftCorner_eq_top ?_
      rintro _ ⟨e, rfl⟩
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, DGRing.K0.map_leftCorner,
        hA.map_projZero_map_subtype]
    exact DFunLike.congr_fun h x
  right_inv x := by
    rw [← AddMonoidHom.comp_apply, ← DGRing.K0.map_comp, projZero_comp_subtype,
      DGRing.K0.map_id, AddMonoidHom.id_apply]
  map_add' := map_add _

@[simp]
theorem K0DegreeZeroEquiv_apply (x : DGRing.K0 A) :
    hA.K0DegreeZeroEquiv x = DGRing.K0.map hA.projZero x :=
  rfl

@[simp]
theorem K0DegreeZeroEquiv_symm_apply (x : DGRing.K0 hA.degreeZeroDGSubring) :
    hA.K0DegreeZeroEquiv.symm x = DGRing.K0.map (DGSubring.subtype hA.degreeZeroDGSubring) x :=
  rfl

/-- `K₀(A) ≅ K₀(A⁰)` sends `[A e]` to `[A⁰ e]`. -/
theorem K0DegreeZeroEquiv_leftCorner (e : DGIdempotent A) :
    hA.K0DegreeZeroEquiv (DGRing.K0.leftCorner e) = DGRing.K0.leftCorner (e.map hA.projZero) :=
  DGRing.K0.map_leftCorner _ e

/-- `K₀(A⁰) ≅ K₀(A)` sends `[A⁰ e]` to `[A e]`. -/
theorem K0DegreeZeroEquiv_symm_leftCorner (e : DGIdempotent hA.degreeZeroDGSubring) :
    hA.K0DegreeZeroEquiv.symm (DGRing.K0.leftCorner e) =
      DGRing.K0.leftCorner (e.map (DGSubring.subtype hA.degreeZeroDGSubring)) :=
  DGRing.K0.map_leftCorner _ e

/-- `K₀(A) ≅ K₀(A⁰)` sends `[A]` to `[A⁰]`. -/
theorem K0DegreeZeroEquiv_self :
    hA.K0DegreeZeroEquiv (DGRing.K0.self A) = DGRing.K0.self hA.degreeZeroDGSubring :=
  DGRing.K0.map_self _

/-- **`K₀` of a positive dg ring is free** (Roadmap 6.3): if `s` is a family of simple
degree-`0` idempotents of `A` containing exactly one representative of each equivalence class
(i.e. of each isomorphism class of simple `A⁰`-modules `A⁰ e`,
`DG.DGIdempotent.equiv_iff_nonempty_linearEquiv`), the classes `[A (s a)]` form a basis of
`K₀(A)`. -/
noncomputable def basis {ι : Type*} (s : ι → SimpleIdempotent A)
    (hs : ∀ a b, (s a).1.Equiv (s b).1 → a = b)
    (hs' : ∀ e : SimpleIdempotent A, ∃ a, e.1.Equiv (s a).1) :
    Module.Basis ι ℤ (DGRing.K0 A) :=
  (hA.isPositive_degreeZeroDGSubring.basisOfConcentrated
    (fun _ hn => hA.grading_degreeZeroDGSubring_eq_bot (by omega))
    (fun a => ⟨(s a).1.map hA.projZero, (hA.isSimple_map_projZero_iff _).mpr (s a).2⟩)
    (fun a b h => hs a b ((hA.equiv_map_projZero_iff _ _).mp h))
    (fun e => by
      let e' := e.1.map (DGSubring.subtype hA.degreeZeroDGSubring)
      have he' : e'.IsSimple := by
        rw [← hA.isSimple_map_projZero_iff, hA.map_subtype_map_projZero]
        exact e.2
      obtain ⟨a, ha⟩ := hs' ⟨e', he'⟩
      refine ⟨a, ?_⟩
      have := (hA.equiv_map_projZero_iff _ _).mpr ha
      rwa [hA.map_subtype_map_projZero] at this)).map
    hA.K0DegreeZeroEquiv.symm.toIntLinearEquiv

@[simp]
theorem basis_apply {ι : Type*} (s : ι → SimpleIdempotent A)
    (hs : ∀ a b, (s a).1.Equiv (s b).1 → a = b)
    (hs' : ∀ e : SimpleIdempotent A, ∃ a, e.1.Equiv (s a).1) (a : ι) :
    hA.basis s hs hs' a = DGRing.K0.leftCorner (s a).1 := by
  rw [basis, Module.Basis.map_apply, basisOfConcentrated_apply]
  change hA.K0DegreeZeroEquiv.symm _ = _
  rw [K0DegreeZeroEquiv_symm_leftCorner, hA.map_projZero_map_subtype]

end K0

/-! ### Division rings in degree `0` -/

section DivisionRing

variable (hdiv : ∀ a : degreeZeroSubring A, a ≠ 0 → IsUnit a)
include hdiv

omit hA in
/-- If `A⁰` is a division ring, every simple idempotent is `1`. -/
theorem val_eq_one_of_isSimple {e : DGIdempotent A} (he : e.IsSimple) : e.val = 1 := by
  have hne : e.toZero ≠ 0 := fun h => he.val_ne_zero (congrArg Subtype.val h)
  have h : e.toZero * e.toZero = e.toZero * 1 := by rw [mul_one, e.isIdempotentElem_toZero.eq]
  exact congrArg Subtype.val ((hdiv _ hne).mul_left_cancel h)

variable [Nontrivial A]

/-- If `A⁰` is a division ring, `1` is a simple idempotent. -/
theorem isSimple_one : (hA.dgIdempotent 1 IsIdempotentElem.one).IsSimple := by
  have hR : IsSimpleModule (degreeZeroSubring A) (degreeZeroSubring A) :=
    isSimpleModule_self_iff_isUnit.mpr ⟨inferInstance, hdiv⟩
  have h1 : (hA.dgIdempotent 1 IsIdempotentElem.one).toZero = 1 := rfl
  unfold DGIdempotent.IsSimple
  rw [h1, show Submodule.span (degreeZeroSubring A) {(1 : degreeZeroSubring A)} = ⊤ from
    Ideal.span_singleton_one]
  exact IsSimpleModule.congr Submodule.topEquiv

omit [Nontrivial A] in
/-- If `A⁰` is a division ring, every simple idempotent is equivalent to `1`. -/
theorem equiv_one_of_isSimple (e : SimpleIdempotent A) :
    e.1.Equiv (hA.dgIdempotent 1 IsIdempotentElem.one) := by
  rw [DGIdempotent.eq_of_val_eq (e := e.1) (f := hA.dgIdempotent 1 IsIdempotentElem.one)
    (by rw [val_eq_one_of_isSimple hdiv e.2]; rfl)]
  exact DGIdempotent.Equiv.refl _

variable [HasDerivedCategory.{u, u} A] [HasDerivedCategory.{u, u} hA.degreeZeroDGSubring]

/-- If `A⁰` is a division ring, `K₀(A)` is free on the single class `[A]`. -/
noncomputable def basisOfDivisionRing : Module.Basis Unit ℤ (DGRing.K0 A) :=
  hA.basis (fun _ : Unit => ⟨_, hA.isSimple_one hdiv⟩) (fun _ _ _ => rfl)
    fun e => ⟨(), hA.equiv_one_of_isSimple hdiv e⟩

theorem basisOfDivisionRing_apply (a : Unit) :
    hA.basisOfDivisionRing hdiv a = DGRing.K0.self A :=
  (hA.basis_apply _ _ _ a).trans
    (DGRing.K0.leftCorner_eq_self_of_val_eq_one (hA.dgIdempotent 1 IsIdempotentElem.one) rfl)

/-- **`K₀(A) ≅ ℤ` when `A⁰` is a division ring** (Roadmap 6.3), e.g. `A⁰ = k` a field, with
`[A] ↦ 1`. -/
noncomputable def K0EquivIntOfDivisionRing : DGRing.K0 A ≃+ ℤ :=
  ((hA.basisOfDivisionRing hdiv).equivFun.trans (LinearEquiv.funUnique Unit ℤ ℤ)).toAddEquiv

theorem K0EquivIntOfDivisionRing_self :
    hA.K0EquivIntOfDivisionRing hdiv (DGRing.K0.self A) = 1 := by
  rw [← hA.basisOfDivisionRing_apply hdiv ()]
  change LinearEquiv.funUnique Unit ℤ ℤ ((hA.basisOfDivisionRing hdiv).equivFun
    (hA.basisOfDivisionRing hdiv ())) = 1
  rw [LinearEquiv.funUnique_apply, Function.eval, Module.Basis.equivFun_self]
  rfl

theorem K0EquivIntOfDivisionRing_symm_apply (n : ℤ) :
    (hA.K0EquivIntOfDivisionRing hdiv).symm n = n • DGRing.K0.self A := by
  rw [AddEquiv.symm_apply_eq, map_zsmul, K0EquivIntOfDivisionRing_self, smul_eq_mul, mul_one]

end DivisionRing

/-! ### Connected dg algebras over a field -/

section Field

variable (k : Type*) [Field k] [Algebra k A] [DGAlgebra k A]
  (hk : ∀ a ∈ grading (M := A) 0, ∃ c : k, algebraMap k A c = a)
include hk

omit hA in
/-- If `A⁰` is the image of a field `k`, every nonzero element of `A⁰` is a unit. -/
theorem isUnit_of_forall_eq_algebraMap (a : degreeZeroSubring A) (ha : a ≠ 0) : IsUnit a := by
  obtain ⟨c, hc⟩ := hk a a.2
  have hc0 : c ≠ 0 := fun h => ha (Subtype.ext (by rw [← hc, h, map_zero]; rfl))
  let b : degreeZeroSubring A := ⟨algebraMap k A c⁻¹, algebraMap_mem_grading k c⁻¹⟩
  have h1 : a * b = 1 := Subtype.ext (by
    change (a : A) * algebraMap k A c⁻¹ = 1
    rw [← hc, ← map_mul, mul_inv_cancel₀ hc0, map_one])
  have h2 : b * a = 1 := Subtype.ext (by
    change algebraMap k A c⁻¹ * (a : A) = 1
    rw [← hc, ← map_mul, inv_mul_cancel₀ hc0, map_one])
  exact ⟨⟨a, b, h1, h2⟩, rfl⟩

variable [Nontrivial A] [HasDerivedCategory.{u, u} A]
  [HasDerivedCategory.{u, u} hA.degreeZeroDGSubring]

/-- **`K₀(A) ≅ ℤ` for a positive dg algebra with `A⁰ = k`** a field (Roadmap 6.3), with
`[A] ↦ 1`. -/
noncomputable def K0EquivIntOfField : DGRing.K0 A ≃+ ℤ :=
  hA.K0EquivIntOfDivisionRing (isUnit_of_forall_eq_algebraMap k hk)

theorem K0EquivIntOfField_self : hA.K0EquivIntOfField k hk (DGRing.K0.self A) = 1 :=
  hA.K0EquivIntOfDivisionRing_self _

end Field

end IsPositive

end DG
