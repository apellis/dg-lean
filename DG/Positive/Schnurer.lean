import DG.Derived.FiniteCell
import DG.Derived.Perfect
import DG.Positive.Basic
import DG.Positive.Idempotent
import Mathlib.RingTheory.FiniteLength

/-!
# Schnürer's theorem: compact objects over a positive dg ring

Let `A` be a positive dg ring (`DG.IsPositive A`: `Aⁿ = 0` for `n < 0`, `A⁰` semisimple,
`d (A⁰) = 0`). **Schnürer's theorem** [Sch, Thm. 1, proved as Thms. 13 and 16]: an object of
`D(A)` is compact iff it is isomorphic to the image of a finite-cell dg module whose cells
`(A eᵢ)⟦nᵢ⟧` are attached in order of non-decreasing generating degree `-n₁ ≤ -n₂ ≤ ⋯`
(`DG.FiniteCellFiltration.IsOrdered`), and the idempotents `eᵢ` can be taken simple, i.e. with
`A⁰ eᵢ` a simple `A⁰`-module (`DG.IsPositive.isCompact_iff`).

## Main definitions and results

* `DG.DGIdempotent.IsSimple`: `A⁰ e` is a simple left `A⁰`-module.
* `DG.IsPositive.isOrderedCellFamily`: the cells `Q (A e)⟦n⟧`, `e` simple, form an ordered cell
  family in `D(A)` (`DG.IsOrderedCellFamily`): there are no nonzero morphisms
  `Q (A e)⟦n⟧ ⟶ Q (A f)⟦m⟧` for `m < n` (as `A` has no negative degrees), and every nonzero
  morphism `Q (A e)⟦n⟧ ⟶ Q (A f)⟦n⟧` is an isomorphism (Schur's lemma over `A⁰`, [Sch, Lemma 5]).
* `DG.IsPositive.hasOrderedCellTower_Q_self`: `A` has an ordered cell tower (from a
  decomposition of `1` into orthogonal simple idempotents of `A⁰`).
* `DG.IsPositive.hasOrderedCellTower_of_isCompact`: every compact object has an ordered cell
  tower, since compact objects form the thick closure of `A` and objects with an ordered cell
  tower form a thick subcategory (`DG.IsOrderedCellFamily.isThick`).
* `DG.FiniteCellFiltration.isCompact_Q_obj`: finite-cell modules are compact (any dg ring).
* `DG.IsPositive.isCompact_iff`: **Schnürer's theorem**.

## Comparison with the source

[Sch] O. M. Schnürer, *Perfect derived categories of positively graded DG algebras*,
Appl. Categ. Structures 19 (2011), 757–782; arXiv:0809.4782v2.

* Schnürer works with a dg algebra over a commutative ring `k` and with *right* dg modules; its
  generators are `L̂_x = L_x ⊗_{A⁰} A ≅ e A` for the simple right `A⁰`-modules `L_x ≅ e A⁰`. We
  work with left dg modules over a dg ring (every dg ring is a dg `ℤ`-algebra); the generators
  are `A e` with `A⁰ e` simple, and a right dg module over `A` is a left dg module over the
  graded opposite `Aᵒᵖ`, which is positive iff `A` is. No field hypothesis is needed.
* Schnürer's `dgFilt` (§3) asks for filtrations with subquotients `{lᵢ} L̂_{xᵢ}`,
  `l₁ ≥ l₂ ≥ ⋯` (Remark 9); here these are `DG.FiniteCellFiltration`s with
  `DG.FiniteCellFiltration.IsOrdered` and simple idempotents. His Thm. 1 states
  `dgPrae = dgPer` and that `dgFilt → dgPer` is an equivalence; the essential surjectivity of
  the latter is `DG.IsPositive.isCompact_iff` (objects of `dgPer` are the compact objects,
  [Keller, Thm. 5.3], `DG.DerivedCategory.thickClosure_self_eq_isCompact`).
* The proof does not follow [Sch, Thm. 16]: closure of `dgPrae` under direct summands is not
  deduced from a bounded t-structure (Le–Chen), but proved directly in the triangulated category
  (`DG.IsOrderedCellFamily.hasOrderedCellTower_of_retract`), by induction on the number of cells,
  splitting off a nonzero morphism from the first cell. The closure under cones is Schnürer's
  Thm. 13, argued with the octahedral axiom on cell towers instead of explicit filtrations
  (`DG.IsOrderedCellFamily.exists_cone`); cell towers are then realized by finite-cell modules
  (`DG.exists_finiteCellFiltration_of_cellTower`).
-/

open CategoryTheory Limits Pretriangulated DirectSum

universe w u

namespace DG

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]

/-! ### Simple idempotents -/

namespace DGIdempotent

/-- A degree-`0` idempotent cocycle as an element of the degree-`0` subring `A⁰`. -/
def toZero (e : DGIdempotent A) : degreeZeroSubring A := ⟨e.val, e.mem_zero⟩

theorem isIdempotentElem_toZero (e : DGIdempotent A) : IsIdempotentElem e.toZero :=
  Subtype.ext e.mul_self

/-- A degree-`0` idempotent cocycle `e` is *simple* if `A⁰ e` is a simple left `A⁰`-module
(Schnürer's `L_x`, [Sch, §2]). -/
def IsSimple (e : DGIdempotent A) : Prop :=
  IsSimpleModule (degreeZeroSubring A) (Submodule.span (degreeZeroSubring A) {e.toZero})

theorem IsSimple.val_ne_zero {e : DGIdempotent A} (he : e.IsSimple) : e.val ≠ 0 := fun h =>
  ne_zero_of_isSimpleModule he (Subtype.ext h)

/-- Right multiplication `A e → A f`, `x ↦ x b`, by a degree-`0` cocycle `b` with `b f = b`, as a
morphism of dg modules. -/
def rightMul (e f : DGIdempotent A) (b : A) (hb : b ∈ grading 0) (hdb : d b = 0)
    (hbf : b * f.val = b) : e.LeftCorner →ᵈᵍ[A] f.LeftCorner where
  toFun x := ⟨x * b, show x * b * f.val = x * b by rw [mul_assoc, hbf]⟩
  map_add' x y := Subtype.ext (add_mul _ _ _)
  map_smul' a x := Subtype.ext (mul_assoc _ _ _)
  map_mem' {n x} hx := by
    rw [LeftCorner.mem_grading_iff] at hx ⊢
    simpa using mul_mem_grading hx hb
  map_d' x := Subtype.ext (by
    rw [LeftCorner.coe_d, LeftCorner.coe_d]
    exact (d_mul_of_d_eq_zero_right hdb _).symm)

@[simp]
theorem coe_rightMul_apply (e f : DGIdempotent A) (b : A) (hb : b ∈ grading 0) (hdb : d b = 0)
    (hbf : b * f.val = b) (x : e.LeftCorner) :
    (rightMul e f b hb hdb hbf x : A) = x * b := rfl

/-- A morphism out of `(A e)⟦n⟧` is determined by the image of the generator `e`. -/
theorem shift_hom_ext (e : DGIdempotent A) (n : ℤ) {N : Type*} [AddCommGroup N]
    [DGAddCommGroup N] [Module A N] {f g : Shift n e.LeftCorner →ᵈᵍ[A] N}
    (h : f (Shift.mk n (LeftCorner.idem e)) = g (Shift.mk n (LeftCorner.idem e))) : f = g := by
  ext y
  rw [← e.twist_unmk_smul_mk_idem n y, map_smul, map_smul, h]

theorem mk_idem_mem_grading (e : DGIdempotent A) (n : ℤ) :
    Shift.mk n (LeftCorner.idem e) ∈ grading (-n) := by
  simpa using Shift.mk_mem_grading (n := n) (LeftCorner.idem_mem_grading e)

/-- For `a ∈ A⁰`, `a • e = a e` in `(A e)⟦n⟧`. -/
theorem smul_mk_idem (e : DGIdempotent A) (n : ℤ) {a : A} (ha : a ∈ grading 0) :
    a • Shift.mk n (LeftCorner.idem e) =
      Shift.mk n (⟨a * e.val, e.mul_val_mem_leftIdeal a⟩ : e.LeftCorner) := by
  rw [Shift.smul_mk ha, mul_zero, koszulSign_zero, one_smul]
  rfl

end DGIdempotent

/-! ### Finite-cell modules are compact -/

section Compact

variable [HasDerivedCategory.{w, u} A]

open _root_.DG.DerivedCategory

/-- `Q (A e)⟦n⟧` is compact: `A e` is a direct summand of `A`, which is compact. -/
theorem DerivedCategory.isCompact_cell (e : DGIdempotent A) (n : ℤ) :
    IsCompact.{u} (cell A e n) := by
  have h0 : IsCompact.{u} (Q.obj (DGModuleCat.of A e.LeftCorner)) :=
    IsCompact.of_retract
      ⟨Q.map (DGModuleCat.ofHom e.leftCornerInclusion),
        Q.map (DGModuleCat.ofHom e.leftCornerProjection), by
        rw [← Q.map_comp, ← Q.map_id]
        congr 1
        exact DGModuleCat.hom_ext e.leftCornerProjection_comp_inclusion⟩
      isCompact_Q_self
  exact (h0.shift n).of_iso ((Q.commShiftIso n).app (DGModuleCat.of A e.LeftCorner))

/-- Finite-cell dg modules are compact in `D(A)`, for every dg ring `A` (roadmap 5.2). -/
theorem FiniteCellFiltration.isCompact_Q_obj {P : Type u} [AddCommGroup P] [DGAddCommGroup P]
    [Module A P] [DGModule A P] (C : FiniteCellFiltration A P) :
    IsCompact.{u} (Q.obj (DGModuleCat.of A P)) :=
  C.Q_obj_mem_of_isThick (isThick_isCompact _) fun _ => isCompact_cell _ _

end Compact

/-! ### Positive dg rings -/

variable (A) in
/-- The simple degree-`0` idempotent cocycles, indexing the cells of Schnürer's theorem. -/
abbrev SimpleIdempotent : Type u := {e : DGIdempotent A // e.IsSimple}

namespace IsPositive

variable (hA : IsPositive A)
include hA

open _root_.DG.DerivedCategory

section Cells

variable [HasDerivedCategory.{w, u} A]

/-- There are no nonzero morphisms `Q (A e)⟦n⟧ ⟶ Q (A f)⟦m⟧` for `m < n`, since `A` has no
components of negative degree. -/
theorem cell_hom_eq_zero_of_lt {e f : DGIdempotent A} {n m : ℤ} (h : m < n)
    (φ : cell A e n ⟶ cell A f m) : φ = 0 := by
  obtain ⟨g, rfl⟩ := exists_Q_map_eq (e.isKProjective_leftCorner.shift n) φ
  suffices hg : g = 0 by rw [hg, Functor.map_zero]
  refine DGModuleCat.hom_ext (e.shift_hom_ext n ?_)
  rw [DGModuleCat.hom_zero, DGModuleHom.zero_apply]
  have hmem := g.hom.map_mem (e.mk_idem_mem_grading n)
  rw [Shift.mem_grading_iff', DGIdempotent.LeftCorner.mem_grading_iff] at hmem
  exact Shift.unmk_inj.mp (Subtype.ext (hA.eq_zero_of_mem_grading (by omega) hmem))

/-- **Schur's lemma for cells** ([Sch, Lemma 5]): a nonzero morphism
`Q (A e)⟦n⟧ ⟶ Q (A f)⟦n⟧` between cells with `e`, `f` simple is an isomorphism. It is the image
of the right multiplication by a nonzero `b ∈ e A⁰ f`, which is invertible by Schur's lemma
over the semisimple ring `A⁰`. -/
theorem isIso_cell_hom {e f : DGIdempotent A} (he : e.IsSimple) (hf : f.IsSimple) {n : ℤ}
    (φ : cell A e n ⟶ cell A f n) (hφ : φ ≠ 0) : IsIso φ := by
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
  have hce' : (c : A) * e.val = c := congrArg Subtype.val hce
  have hfc' : f.val * (c : A) = c := congrArg Subtype.val hfc
  have hyc' : (y : A) * c = e.val := congrArg Subtype.val hyc
  have hcy' : (c : A) * y = f.val := congrArg Subtype.val hcy
  let h : DGModuleCat.of A (Shift n f.LeftCorner) ⟶ DGModuleCat.of A (Shift n e.LeftCorner) :=
    DGModuleCat.ofHom ((f.rightMul e c c.2 (hA.d_eq_zero c.2) hce').shift n)
  have hgx : g.hom x = Shift.mk n y := rfl
  refine ⟨⟨Q.map h, ?_, ?_⟩⟩
  · rw [← Q.map_comp, ← Q.map_id]
    congr 1
    refine DGModuleCat.hom_ext (e.shift_hom_ext n ?_)
    change h.hom (g.hom x) = x
    rw [hgx]
    change Shift.mk n (f.rightMul e c c.2 (hA.d_eq_zero c.2) hce' y) = x
    congr 1
    exact Subtype.ext (show (y : A) * c = e.val from hyc')
  · rw [← Q.map_comp, ← Q.map_id]
    congr 1
    refine DGModuleCat.hom_ext (f.shift_hom_ext n ?_)
    change g.hom (h.hom (Shift.mk n (DGIdempotent.LeftCorner.idem f))) = _
    have hx : h.hom (Shift.mk n (DGIdempotent.LeftCorner.idem f)) = (c : A) • x := by
      change Shift.mk n (f.rightMul e c c.2 (hA.d_eq_zero c.2) hce' _) = _
      rw [e.smul_mk_idem n c.2]
      congr 1
      exact Subtype.ext (show f.val * (c : A) = (c : A) * e.val by rw [hfc', hce'])
    rw [hx, map_smul, hgx, Shift.smul_mk c.2, mul_zero,
      koszulSign_zero, one_smul]
    change _ = Shift.mk n (DGIdempotent.LeftCorner.idem f)
    congr 1
    exact Subtype.ext hcy'

/-- The cells `Q (A e)⟦n⟧` of a positive dg ring are nonzero for `e` simple: the generator `e`
is a cocycle of degree `-n` which is not a coboundary, as `(A e)⁻¹ = 0`. -/
theorem not_isZero_cell {e : DGIdempotent A} (he : e.IsSimple) (n : ℤ) :
    ¬ IsZero (cell A e n) := by
  intro hZ
  rw [isZero_Q_obj_iff] at hZ
  have hd : d (Shift.mk n (DGIdempotent.LeftCorner.idem e)) = 0 := by
    rw [Shift.d_mk]
    have : d (DGIdempotent.LeftCorner.idem e) = 0 := Subtype.ext e.d_eq_zero
    rw [this, smul_zero]
    rfl
  obtain ⟨z, hz, hdz⟩ := hZ.exists_d_eq (e.mk_idem_mem_grading n) hd
  rw [Shift.mem_grading_iff', DGIdempotent.LeftCorner.mem_grading_iff] at hz
  have hz0 : z = 0 :=
    Shift.unmk_inj.mp (Subtype.ext (hA.eq_zero_of_mem_grading (by omega) hz))
  rw [hz0, d_zero] at hdz
  apply he.val_ne_zero
  have := congrArg (fun x => ((Shift.unmk n x : e.LeftCorner) : A)) hdz
  exact this.symm

/-- The cells `Q (A e)⟦n⟧`, `e` simple, of a positive dg ring form an ordered cell family. -/
theorem isOrderedCellFamily :
    IsOrderedCellFamily (fun (i : SimpleIdempotent A) (n : ℤ) => cell A i.1 n) where
  nonempty_shiftIso i n k := nonempty_cellShiftIso i.1 n k
  eq_zero_of_lt h f := hA.cell_hom_eq_zero_of_lt h f
  isIso_of_ne_zero {i j} _ f hf := hA.isIso_cell_hom i.2 j.2 f hf
  not_isZero i n := hA.not_isZero_cell i.2 n

end Cells

/-! #### Decomposition of `A` into simple cells -/

section Decomposition

variable [HasDerivedCategory.{w, u} A]

omit hA in
theorem isZero_Q_leftCorner {g : DGIdempotent A} (hg : g.val = 0) :
    IsZero (Q.obj (DGModuleCat.of A g.LeftCorner)) := by
  have : Subsingleton g.LeftCorner := ⟨fun x y => Subtype.ext (by
    have hx : (x : A) * g.val = x := x.2
    have hy : (y : A) * g.val = y := y.2
    rw [← hx, ← hy, hg, mul_zero, mul_zero])⟩
  exact Functor.map_isZero _ (DGModuleCat.isZero_of_subsingleton _)

omit hA in
/-- For orthogonal degree-`0` idempotent cocycles `s`, `t` with `s + t = g`, there is a
distinguished triangle `Q (A t) → Q (A g) → Q (A s)⟦0⟧ → (Q (A t))⟦1⟧` (from the graded-split,
indeed split, sequence `A t → A g → A s`). -/
theorem exists_distinguished_of_add (s t g : DGIdempotent A) (hst : s.val * t.val = 0)
    (hts : t.val * s.val = 0) (hsum : s.val + t.val = g.val) :
    ∃ (u : Q.obj (DGModuleCat.of A t.LeftCorner) ⟶ Q.obj (DGModuleCat.of A g.LeftCorner))
      (v : Q.obj (DGModuleCat.of A g.LeftCorner) ⟶ cell A s 0)
      (δ : cell A s 0 ⟶ (Q.obj (DGModuleCat.of A t.LeftCorner))⟦(1 : ℤ)⟧),
      Triangle.mk u v δ ∈ distTriang (DerivedCategory A) := by
  have hsg : s.val * g.val = s.val := by rw [← hsum, mul_add, s.mul_self, hst, add_zero]
  have htg : t.val * g.val = t.val := by rw [← hsum, mul_add, t.mul_self, hts, zero_add]
  let i := t.rightMul g g.val g.mem_zero g.d_eq_zero g.mul_self
  let p := (Shift.zeroEquiv (A := A) (M := s.LeftCorner)).symm.toDGModuleHom.comp
    (g.rightMul s s.val s.mem_zero s.d_eq_zero s.mul_self)
  let σ : GradedSplitting i p :=
    { r := Cochain.ofHom (g.rightMul t t.val t.mem_zero t.d_eq_zero t.mul_self)
      s := Cochain.ofHom ((s.rightMul g s.val s.mem_zero s.d_eq_zero hsg).comp
        (Shift.zeroEquiv (A := A) (M := s.LeftCorner)).toDGModuleHom)
      r_i := fun x => Subtype.ext (by
        have hx : (x : A) * t.val = x := x.2
        change (x : A) * g.val * t.val = x
        rw [mul_assoc, ← hsum, add_mul, hst, t.mul_self, zero_add, hx])
      p_s := fun y => by
        apply Shift.unmk_inj.mp
        apply Subtype.ext
        have hy : ((Shift.unmk 0 y : s.LeftCorner) : A) * s.val = Shift.unmk 0 y :=
          (Shift.unmk 0 y).2
        change ((Shift.unmk 0 y : s.LeftCorner) : A) * s.val * s.val = _
        rw [hy, hy]
      i_r_add_s_p := fun x => Subtype.ext (by
        have hx : (x : A) * g.val = x := x.2
        change (x : A) * t.val * g.val + (x : A) * s.val * s.val = x
        rw [mul_assoc, htg, mul_assoc, s.mul_self, add_comm, ← mul_add, hsum, hx]) }
  obtain ⟨δ, hδ⟩ := σ.exists_distinguished
  exact ⟨_, _, δ, hδ⟩

omit hA [HasDerivedCategory.{w, u} A] in
theorem cellsOrdered_of_forall_eq_zero {l : List (SimpleIdempotent A × ℤ)}
    (hl : ∀ c ∈ l, c.2 = 0) : CellsOrdered l := by
  induction l with
  | nil => exact cellsOrdered_nil
  | cons a l ih =>
    refine List.pairwise_cons.mpr ⟨fun b hb => ?_, ih fun c hc => hl c (by simp [hc])⟩
    rw [hl a (by simp), hl b (by simp [hb])]

/-- For every degree-`0` idempotent cocycle `g` of a positive dg ring, `Q (A g)` has a cell
tower whose cells are `Q (A s)` for simple idempotents `s` (all of shift `0`): split off simple
idempotents from `g` ([Sch, §3]: `A⁰` is a finite direct sum of simple modules). -/
theorem exists_cellTower_leftCorner (g : DGIdempotent A) :
    ∃ l : List (SimpleIdempotent A × ℤ), (∀ c ∈ l, c.2 = 0) ∧
      CellTower (fun (i : SimpleIdempotent A) n => cell A i.1 n) l
        (Q.obj (DGModuleCat.of A g.LeftCorner)) := by
  have := hA.isSemisimple
  have : IsArtinianRing (degreeZeroSubring A) := inferInstance
  suffices H : ∀ N : Submodule (degreeZeroSubring A) (degreeZeroSubring A),
      ∀ g : DGIdempotent A, Submodule.span _ {g.toZero} = N →
      ∃ l : List (SimpleIdempotent A × ℤ), (∀ c ∈ l, c.2 = 0) ∧
        CellTower (fun (i : SimpleIdempotent A) n => cell A i.1 n) l
          (Q.obj (DGModuleCat.of A g.LeftCorner)) from H _ g rfl
  intro N
  induction N using WellFoundedLT.induction with
  | _ N ih =>
  intro g hN
  by_cases h0 : Submodule.span (degreeZeroSubring A) {g.toZero} = ⊥
  · have hg : g.val = 0 := congrArg Subtype.val (Submodule.span_singleton_eq_bot.mp h0)
    exact ⟨[], by simp, .zero (isZero_Q_leftCorner hg)⟩
  obtain ⟨s, t, hs, ht, hst, hts, hsum, hsimple, hlt⟩ :=
    exists_isSimpleModule_add_of_isSemisimpleRing g.isIdempotentElem_toZero h0
  let S := hA.dgIdempotent s hs
  let T := hA.dgIdempotent t ht
  obtain ⟨l, hl0, hl⟩ := ih _ (hN ▸ hlt) T rfl
  obtain ⟨u, v, δ, hT⟩ := exists_distinguished_of_add S T g (congrArg Subtype.val hst)
    (congrArg Subtype.val hts) (congrArg Subtype.val hsum)
  refine ⟨l ++ [(⟨S, hsimple⟩, 0)], fun c hc => ?_, .ext _ hT hl ⟨Iso.refl _⟩⟩
  rcases List.mem_append.mp hc with hc | hc
  · exact hl0 c hc
  · simp at hc
    rw [hc]

/-- `A` itself has an ordered cell tower, with cells `Q (A e)` for simple idempotents `e`. -/
theorem hasOrderedCellTower_Q_self :
    HasOrderedCellTower (fun (i : SimpleIdempotent A) n => cell A i.1 n)
      (Q.obj (DGModuleCat.of A A)) := by
  let one := hA.dgIdempotent 1 IsIdempotentElem.one
  obtain ⟨l, hl0, hl⟩ := hA.exists_cellTower_leftCorner one
  let e : DGModuleCat.of A one.LeftCorner ≅ DGModuleCat.of A A :=
    { hom := DGModuleCat.ofHom one.leftCornerInclusion
      inv := DGModuleCat.ofHom one.leftCornerProjection
      hom_inv_id := DGModuleCat.hom_ext one.leftCornerProjection_comp_inclusion
      inv_hom_id := DGModuleCat.hom_ext_apply fun a => mul_one (a : A) }
  exact ⟨l, cellsOrdered_of_forall_eq_zero hl0, hl.of_iso (Q.mapIso e)⟩

end Decomposition

/-! #### Schnürer's theorem -/

section Main

variable [HasDerivedCategory.{u, u} A]

/-- Every compact object of `D(A)` has an ordered cell tower with simple cells: compact objects
form the thick closure of `A` (Keller–Neeman), `A` has such a tower, and objects with such a
tower form a thick subcategory. -/
theorem hasOrderedCellTower_of_isCompact {X : DerivedCategory.{u, u} A}
    (hX : IsCompact.{u} X) :
    HasOrderedCellTower (fun (i : SimpleIdempotent A) n => cell A i.1 n) X := by
  rw [← thickClosure_self_eq_isCompact] at hX
  exact hA.isOrderedCellFamily.thickClosure_le
    (by rintro _ ⟨-, rfl⟩; exact hA.hasOrderedCellTower_Q_self) X hX

/-- **Schnürer's theorem**, the hard direction ([Sch, Thm. 1 (2)], via Thms. 13 and 16; the
closure under direct summands is proved differently, see the module docstring): every compact
object of `D(A)` is isomorphic to the image of a finite-cell dg module whose cells
`(A eᵢ)⟦nᵢ⟧` have simple idempotents `eᵢ` (`A⁰ eᵢ` simple) and shifts `n₁ ≥ n₂ ≥ ⋯`
(Schnürer's `dgFilt`, [Sch, §3, Remark 9]). -/
theorem exists_finiteCellFiltration_of_isCompact {X : DerivedCategory.{u, u} A}
    (hX : IsCompact.{u} X) :
    ∃ (P : DGModuleCat.{u} A) (C : FiniteCellFiltration A P),
      C.IsOrdered ∧ (∀ i, (C.e i).IsSimple) ∧ Nonempty (X ≅ Q.obj P) := by
  obtain ⟨l, hlo, hl⟩ := hA.hasOrderedCellTower_of_isCompact hX
  obtain ⟨P, C, hC, he⟩ := exists_finiteCellFiltration_of_cellTower Subtype.val hl
  refine ⟨P, C, ?_, fun i => ?_, he⟩
  · rw [C.isOrdered_iff_cellsOrdered, hC]
    unfold CellsOrdered at hlo ⊢
    rw [List.pairwise_map]
    exact hlo
  · have hi : (C.e i, C.shift i) ∈ C.cells := List.mem_ofFn.mpr ⟨i, rfl⟩
    rw [hC, List.mem_map] at hi
    obtain ⟨c, -, hc⟩ := hi
    have : (c.1 : DGIdempotent A) = C.e i := congrArg Prod.fst hc
    exact this ▸ c.1.2

/-- **Schnürer's theorem** [Sch, Thm. 1]: for a positive dg ring `A`, an object of `D(A)` is
compact iff it is isomorphic to the image of a finite-cell dg module with ordered cells
(`n₁ ≥ n₂ ≥ ⋯`); the idempotents of the cells can moreover be taken simple
(`DG.IsPositive.exists_finiteCellFiltration_of_isCompact`). -/
theorem isCompact_iff {X : DerivedCategory.{u, u} A} :
    IsCompact.{u} X ↔ ∃ (P : DGModuleCat.{u} A) (C : FiniteCellFiltration A P),
      C.IsOrdered ∧ Nonempty (X ≅ Q.obj P) := by
  constructor
  · intro hX
    obtain ⟨P, C, hC, -, he⟩ := hA.exists_finiteCellFiltration_of_isCompact hX
    exact ⟨P, C, hC, he⟩
  · rintro ⟨P, C, -, ⟨e⟩⟩
    exact C.isCompact_Q_obj.of_iso e

/-- Schnürer's theorem for dg modules: a dg module over a positive dg ring is compact in `D(A)`
iff it is quasi-isomorphic (isomorphic in `D(A)`) to a finite-cell module with ordered cells. -/
theorem isCompact_Q_obj_iff (M : DGModuleCat.{u} A) :
    IsCompact.{u} (Q.obj M : DerivedCategory.{u, u} A) ↔
      ∃ (P : DGModuleCat.{u} A) (C : FiniteCellFiltration A P),
        C.IsOrdered ∧ Nonempty ((Q.obj M : DerivedCategory.{u, u} A) ≅ Q.obj P) :=
  hA.isCompact_iff

end Main

end IsPositive

end DG
