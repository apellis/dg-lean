import DG.Category.Derived.InductionCell
import DG.K0.CellFamily
import DG.K0.PositiveCategory

/-!
# Cells of positive dg categories and freeness of `K₀`

Let `C` be a positive dg category (`DG.DGCategory.IsPositive C`). This file compares cells and
computes `K₀(C) = K₀(D^c(C))` when the Hom complexes of `C` are concentrated in degree `0`.

## Equivalent idempotents

Two degree-`0` idempotent cocycles `e` of `X` and `f` of `Y` are *equivalent*
(`DG.DGCategory.Idempotent.Equiv e f`) if there are degree-`0` morphisms `b : Y ⟶ X` and
`c : X ⟶ Y` with `b ∈ f · C(Y, X) · e`, `c ∈ e · C(X, Y) · f`, `b ≫ c = f` and `c ≫ b = e`: the
modules `e · C⁰(X, -)` and `f · C⁰(Y, -)` over the degree-`0` category are isomorphic. For a
positive dg category and simple `e`, `f`, this holds iff the cells `Q (e · C(X, -))⟦n⟧` and
`Q (f · C(Y, -))⟦n⟧` are isomorphic in `D(C)` (`DG.DGCategory.IsPositive.nonempty_cell_iso_iff`),
by Schur's lemma.

## Freeness

If moreover `C(X, Y)ⁿ = 0` for `n > 0` (the Hom complexes are concentrated in degree `0`), there
are no nonzero morphisms between cells of different shifts, so the simple cells form a semisimple
cell family (`DG.DGCategory.IsPositive.isSemisimpleCellFamily`) and `K₀(C)` is free on the classes
`[e · C(X, -)]` of a set of representatives of the simple corners up to equivalence
(`DG.DGCategory.IsPositive.basisOfConcentrated`).

## Functoriality on cells

For a dg functor `F : C ⥤ D`, `K₀(F) [e · C(X, -)] = [F e · D(F X, -)]`
(`DG.DGCategory.K0.map_cell`), from `DG.CatModule.DerivedCategory.inductionCellIso`.
-/

open CategoryTheory Limits

universe w' w v u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace DG

namespace DGCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

/-! ### Equivalent idempotents -/

namespace Idempotent

/-- Degree-`0` idempotent cocycles `e` of `X` and `f` of `Y` are *equivalent* if there are
degree-`0` morphisms `b : Y ⟶ X`, `c : X ⟶ Y` with `f ≫ b = b = b ≫ e`, `e ≫ c = c = c ≫ f`,
`b ≫ c = f` and `c ≫ b = e`, i.e. `e · C⁰(X, -) ≅ f · C⁰(Y, -)` over the degree-`0` category. -/
def Equiv {X Y : C} (e : Idempotent X) (f : Idempotent Y) : Prop :=
  ∃ (b : Y ⟶ X) (c : X ⟶ Y), b ∈ grading 0 ∧ c ∈ grading 0 ∧ f.val ≫ b = b ∧ b ≫ e.val = b ∧
    e.val ≫ c = c ∧ c ≫ f.val = c ∧ b ≫ c = f.val ∧ c ≫ b = e.val

theorem Equiv.refl {X : C} (e : Idempotent X) : e.Equiv e :=
  ⟨e.val, e.val, e.mem_grading, e.mem_grading, e.comp_self, e.comp_self, e.comp_self,
    e.comp_self, e.comp_self, e.comp_self⟩

theorem Equiv.symm {X Y : C} {e : Idempotent X} {f : Idempotent Y} (h : e.Equiv f) :
    f.Equiv e := by
  obtain ⟨b, c, hb, hc, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨c, b, hc, hb, h3, h4, h1, h2, h6, h5⟩

theorem Equiv.trans [DGCategory C] {X Y Z : C} {e : Idempotent X} {f : Idempotent Y}
    {g : Idempotent Z} (h : e.Equiv f) (h' : f.Equiv g) : e.Equiv g := by
  obtain ⟨b, c, hb, hc, h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨b', c', hb', hc', h1', h2', h3', h4', h5', h6'⟩ := h'
  refine ⟨b' ≫ b, c ≫ c', by simpa using comp_mem_grading hb' hb,
    by simpa using comp_mem_grading hc hc', by rw [← Category.assoc, h1'],
    by rw [Category.assoc, h2], by rw [← Category.assoc, h3], by rw [Category.assoc, h4'], ?_, ?_⟩
  · rw [Category.assoc, ← Category.assoc b, h5, ← Category.assoc, h2', h5']
  · rw [Category.assoc, ← Category.assoc c', h6', ← Category.assoc, h4, h6]

end Idempotent

/-! ### Isomorphic cells -/

namespace IsPositive

open CatModule CatModule.DerivedCategory

variable [DGCategory C] [CatModule.HasDerivedCategory.{w', max v w} C] {X Y : C}
  {e : Idempotent X} {f : Idempotent Y}

/-- For equivalent idempotents of a dg category with `d = 0` on degree-`0` morphisms, the corners
`e · C(X, -)` and `f · C(Y, -)` are isomorphic. -/
def cornerIsoOfEquiv (hC : IsPositive C) (h : e.Equiv f) : corner e ≅ corner f := by
  choose b c hb hc h1 h2 h3 h4 h5 h6 using h
  exact
    { hom := cornerHom e f b ⟨hb, hC.d_eq_zero hb⟩ h1
      inv := cornerHom f e c ⟨hc, hC.d_eq_zero hc⟩ h3
      hom_inv_id := hom_ext fun _ h => Subtype.ext (by
        change c ≫ b ≫ h.1 = h.1
        rw [← Category.assoc, h6]
        exact h.2)
      inv_hom_id := hom_ext fun _ h => Subtype.ext (by
        change b ≫ c ≫ h.1 = h.1
        rw [← Category.assoc, h5]
        exact h.2) }

/-- For simple idempotents `e`, `f` of a positive dg category, the cells `Q (e · C(X, -))⟦n⟧` and
`Q (f · C(Y, -))⟦n⟧` are isomorphic iff `e` and `f` are equivalent. -/
theorem nonempty_cell_iso_iff (hC : IsPositive C) (he : e.IsSimple) (hf : f.IsSimple) (n : ℤ) :
    Nonempty (cell.{w', w} e n ≅ cell f n) ↔ e.Equiv f := by
  refine ⟨fun ⟨ι⟩ => ?_, fun h => ⟨Q.mapIso (cellIso n (hC.cornerIsoOfEquiv h))⟩⟩
  obtain ⟨g, hg⟩ := exists_Q_map_eq (isKProjective_cellModule e n) ι.hom
  set b := cellCoord (g.app X (cellGen e n)) with hbdef
  have hb0 : b ∈ grading 0 := by simpa using cellCoord_app_cellGen_mem g
  have hfb : f.val ≫ b = b := val_comp_cellCoord _
  have hbe : b ≫ e.val = b := cellCoord_app_cellGen_comp g
  have hbne : b ≠ 0 := by
    intro h0
    have : g = 0 := cellModule_hom_ext n (cellModule_ext (by
      rw [CatModule.zero_app, cellCoord_zero]
      exact h0))
    refine hC.not_isZero_cell he n ((IsZero.iff_id_eq_zero _).mpr ?_)
    rw [← ι.hom_inv_id, ← hg, this, Functor.map_zero, zero_comp]
  obtain ⟨c, hc0, hec, hcf, hbc, hcb⟩ := he.exists_inv hf hb0 hfb hbe hbne
  exact ⟨b, c, hb0, hc0, hfb, hbe, hec, hcf, hbc, hcb⟩

omit [CatModule.HasDerivedCategory.{w', max v w} C] in
/-- Equivalence of idempotents only depends on the degree-`0` part of the dg category, and
simplicity is invariant under it. -/
theorem isSimple_of_equiv (h : e.Equiv f) (he : e.IsSimple) : f.IsSimple := by
  obtain ⟨b, c, hb, hc, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun h0 => he.1 (by rw [← h6, ← h4, h0]; simp), fun Z k hk hfk hk0 => ?_⟩
  have hbk : e.val ≫ c ≫ k = c ≫ k := by rw [← Category.assoc, h3]
  have hck0 : c ≫ k ≠ 0 := fun h0 => hk0 (by rw [← hfk, ← h5, Category.assoc, h0, comp_zero])
  obtain ⟨g, hg, hgk⟩ := he.2 (c ≫ k) (by simpa using comp_mem_grading hc hk) hbk hck0
  have hkg : k ≫ g = b := by
    calc k ≫ g = (b ≫ c) ≫ k ≫ g := by rw [h5, ← Category.assoc, hfk]
      _ = b ≫ e.val := by rw [← hgk]; simp only [Category.assoc]
      _ = b := h2
  exact ⟨g ≫ c, by simpa using comp_mem_grading hg hc, by rw [← Category.assoc, hkg, h5]⟩

/-! ### Dg categories concentrated in degree `0` -/

/-- If the Hom complexes of `C` vanish in positive degrees, there are no nonzero morphisms
`Q (e · C(X, -))⟦n⟧ ⟶ Q (f · C(Y, -))⟦m⟧` for `n < m`. -/
theorem cell_hom_eq_zero_of_gt
    (h0 : ∀ {X Y : C} {n : ℤ}, 0 < n → ∀ {f : X ⟶ Y}, f ∈ grading n → f = 0) {n m : ℤ}
    (h : n < m) (φ : cell.{w', w} e n ⟶ cell f m) : φ = 0 := by
  obtain ⟨g, rfl⟩ := exists_Q_map_eq (isKProjective_cellModule e n) φ
  suffices hg : g = 0 by rw [hg, Functor.map_zero]
  refine cellModule_hom_ext n (cellModule_ext ?_)
  rw [CatModule.zero_app, cellCoord_zero]
  exact h0 (by omega) (cellCoord_app_cellGen_mem g)

/-- For a positive dg category whose Hom complexes vanish in positive degrees, the cells
`Q (e · C(X, -))⟦n⟧`, `e` simple, form a semisimple cell family. -/
theorem isSemisimpleCellFamily (hC : IsPositive C)
    (h0 : ∀ {X Y : C} {n : ℤ}, 0 < n → ∀ {f : X ⟶ Y}, f ∈ grading n → f = 0) :
    IsSemisimpleCellFamily (fun (i : SimpleCorner C) (n : ℤ) => cell.{w', w} i.1.2 n) where
  toIsOrderedCellFamily := hC.isOrderedCellFamily
  eq_zero_of_gt h φ := cell_hom_eq_zero_of_gt h0 h φ

end IsPositive

namespace IsPositive

open CatModule CatModule.DerivedCategory

variable [DGCategory C] [CatModule.HasDerivedCategory.{max u v w, max u v w} C]

/-- **`K₀` of a positive dg category concentrated in degree `0` is free** on the classes
`[e · C(X, -)]` of a family `s` of simple corners containing exactly one representative of each
equivalence class (`DG.DGCategory.Idempotent.Equiv`). -/
def basisOfConcentrated (hC : IsPositive C)
    (h0 : ∀ {X Y : C} {n : ℤ}, 0 < n → ∀ {f : X ⟶ Y}, f ∈ grading n → f = 0) {κ : Type*}
    (s : κ → SimpleCorner C) (hs : ∀ a b, (s a).1.2.Equiv (s b).1.2 → a = b)
    (hs' : ∀ c : SimpleCorner C, ∃ a, c.1.2.Equiv (s a).1.2) :
    Module.Basis κ ℤ (K0.{max u v w, max u v w} C) :=
  (hC.isSemisimpleCellFamily.{max u v w, max u w} h0).basis
    (P := compactSubcategory.{max u v w} (CatModule.DerivedCategory C))
    (fun X hX => by
      obtain ⟨l, -, hl⟩ := hC.hasOrderedCellTower_of_isCompact.{w} (Y := X) hX
      exact ⟨l, hl⟩)
    (fun i n => isCompact_cell i.1.2 n) s
    (fun a b ⟨ι⟩ => hs a b ((hC.nonempty_cell_iso_iff (s a).2 (s b).2 0).mp ⟨ι⟩))
    (fun i => by
      obtain ⟨a, ha⟩ := hs' i
      exact ⟨a, (hC.nonempty_cell_iso_iff i.2 (s a).2 0).mpr ha⟩)

theorem basisOfConcentrated_apply (hC : IsPositive C)
    (h0 : ∀ {X Y : C} {n : ℤ}, 0 < n → ∀ {f : X ⟶ Y}, f ∈ grading n → f = 0) {κ : Type*}
    (s : κ → SimpleCorner C) (hs : ∀ a b, (s a).1.2.Equiv (s b).1.2 → a = b)
    (hs' : ∀ c : SimpleCorner C, ∃ a, c.1.2.Equiv (s a).1.2) (a : κ) :
    hC.basisOfConcentrated h0 s hs hs' a = K0.cell.{w} (s a).1.2 0 :=
  IsSemisimpleCellFamily.basis_apply _ _ _ _ _ _ a

end IsPositive

/-! ### Functoriality of `K₀` on cells -/

namespace K0

open CatModule CatModule.DerivedCategory

variable [DGCategory C] {D : Type u} [Category.{v} D] [Preadditive D]
  [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] [DGCategory D] (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]
  [CatModule.HasDerivedCategory.{max u v w, max u v w} C]
  [CatModule.HasDerivedCategory.{max u v w, max u v w} D]

/-- `K₀(F) [e · C(X, -)] = [F e · D(F X, -)]` for a dg functor `F`. -/
theorem map_cell {X : C} (e : Idempotent X) :
    map.{max u v w, w} F (cell.{max v w} e 0) = cell.{max v w} (e.map F) 0 := by
  rw [cell, map_mk]
  exact DG.K0.mk_eq_of_iso_obj (inductionCellIso.{w} F e)

end K0

end DGCategory

end DG

end
