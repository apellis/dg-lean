import DG.K0.Field
import DG.Positive.K0Basis

/-!
# Objects built from semisimple cells are sums of cells

Let `cell : ι → ℤ → C` be a semisimple cell family in a pretriangulated category
(`DG.IsSemisimpleCellFamily`: in particular there are no nonzero morphisms from a cell to a cell
of larger shift). Then every object with an ordered cell tower `n₁ ≥ n₂ ≥ ⋯` is isomorphic to the
finite direct sum of its cells (`DG.IsSemisimpleCellFamily.nonempty_iso_cellSum`): attaching a
cell `cell i n` to a sum of cells of shifts `≥ n` is a split extension, since its connecting
morphism `cell i n ⟶ (⊕ cell j mⱼ)⟦1⟧` vanishes (`mⱼ + 1 > n`).

For a field `k` in degree `0`, the cells are the shifts `k⟦n⟧`, and Schnürer's theorem gives
(Roadmap 5.6, refinement): **every compact object of `D(k)` is isomorphic to a finite direct sum
of shifts of `k`** (`DG.DerivedCategory.nonempty_iso_shiftSum_of_isCompact`).
-/

open CategoryTheory Limits Pretriangulated

universe w v u

namespace DG

section CellSum

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] {ι : Type w} (cell : ι → ℤ → C)

open ZeroObject in
/-- The direct sum `cell i₁ n₁ ⊞ (cell i₂ n₂ ⊞ (⋯ ⊞ 0))` of a list of cells. -/
noncomputable def cellSum : List (ι × ℤ) → C
  | [] => 0
  | c :: l => cell c.1 c.2 ⊞ cellSum l

variable {cell}

omit [HasZeroObject C] [Pretriangulated C] in
/-- A morphism into `(A ⊞ B)⟦1⟧` vanishes if its two components vanish. -/
theorem eq_zero_of_comp_shift_fst_snd [HasBinaryBiproducts C] {X A B : C}
    (f : X ⟶ (A ⊞ B)⟦(1 : ℤ)⟧) (h₁ : f ≫ (shiftFunctor C (1 : ℤ)).map biprod.fst = 0)
    (h₂ : f ≫ (shiftFunctor C (1 : ℤ)).map biprod.snd = 0) : f = 0 := by
  have htot : f = f ≫ (shiftFunctor C (1 : ℤ)).map biprod.fst ≫
        (shiftFunctor C (1 : ℤ)).map biprod.inl +
      f ≫ (shiftFunctor C (1 : ℤ)).map biprod.snd ≫ (shiftFunctor C (1 : ℤ)).map biprod.inr := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Preadditive.comp_add, ← Functor.map_add,
      biprod.total, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [htot, reassoc_of% h₁, reassoc_of% h₂, zero_comp, zero_comp, add_zero]

namespace IsSemisimpleCellFamily

variable (hc : IsSemisimpleCellFamily cell)
include hc

open ZeroObject in
/-- There are no nonzero morphisms from `cell i n` to `(⊕ cell jₖ mₖ)⟦1⟧` when all `mₖ ≥ n`. -/
theorem eq_zero_of_forall_le {i : ι} {n : ℤ} :
    ∀ (l : List (ι × ℤ)), (∀ c ∈ l, n ≤ c.2) →
      ∀ f : cell i n ⟶ (cellSum cell l)⟦(1 : ℤ)⟧, f = 0
  | [], _, f => ((shiftFunctor C (1 : ℤ)).map_isZero (isZero_zero C)).eq_of_tgt _ _
  | c :: l, h, f => by
    have h₁ : f ≫ (shiftFunctor C (1 : ℤ)).map biprod.fst = 0 := by
      have e := (hc.nonempty_shiftIso c.1 c.2 1).some
      rw [← cancel_mono e.hom, zero_comp]
      exact hc.eq_zero_of_gt (by have := h c (List.mem_cons_self ..); omega) _
    have h₂ : f ≫ (shiftFunctor C (1 : ℤ)).map biprod.snd = 0 :=
      eq_zero_of_forall_le l (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')) _
    exact eq_zero_of_comp_shift_fst_snd f h₁ h₂

/-- **An object with an ordered cell tower is the direct sum of its cells**, for a semisimple
cell family. -/
theorem nonempty_iso_cellSum {l : List (ι × ℤ)} {X : C} (h : CellTower cell l X)
    (hl : CellsOrdered l) : Nonempty (X ≅ cellSum cell l.reverse) := by
  induction h with
  | zero hX => exact ⟨hX.isoZero⟩
  | @ext l c T hT h₁ h₃ ih =>
    obtain ⟨hl₁, -, hlc⟩ := cellsOrdered_append.mp hl
    obtain ⟨e₁⟩ := ih hl₁
    obtain ⟨e₃⟩ := h₃
    have hδ : T.mor₃ = 0 := by
      have h0 := hc.eq_zero_of_forall_le l.reverse
        (fun a ha => hlc a (List.mem_reverse.mp ha) c (List.mem_singleton_self _))
        (e₃.inv ≫ T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map e₁.hom)
      rw [← cancel_epi e₃.inv, comp_zero, ← cancel_mono ((shiftFunctor C (1 : ℤ)).map e₁.hom),
        zero_comp, Category.assoc, h0]
    obtain ⟨e, -⟩ := exists_iso_binaryBiproduct_of_distTriang T hT hδ
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
    exact ⟨e ≪≫ biprod.mapIso e₁ e₃ ≪≫ biprod.braiding _ _⟩

/-- Every object with an ordered cell tower is isomorphic to a finite direct sum of cells. -/
theorem exists_iso_cellSum {X : C} (h : HasOrderedCellTower cell X) :
    ∃ l : List (ι × ℤ), Nonempty (X ≅ cellSum cell l) := by
  obtain ⟨l, hl, h⟩ := h
  exact ⟨l.reverse, hc.nonempty_iso_cellSum h hl⟩

end IsSemisimpleCellFamily

end CellSum

/-! ### Compact objects over a field -/

section Field

open DegreeZero ZeroObject

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The direct sum `Y⟦n₁⟧ ⊞ (Y⟦n₂⟧ ⊞ (⋯ ⊞ 0))` of shifts of an object. -/
noncomputable def shiftSum (Y : C) : List ℤ → C
  | [] => 0
  | n :: l => Y⟦n⟧ ⊞ shiftSum Y l

variable (k : Type u) [Field k] [HasDerivedCategory.{u, u} k]

open _root_.DG.DerivedCategory in
/-- For a field `k` in degree `0`, the cell `(k e)⟦n⟧` of a simple idempotent `e` (necessarily
`e = 1`) is `k⟦n⟧`. -/
noncomputable def DerivedCategory.cellIsoShiftSelf (e : SimpleIdempotent k) (n : ℤ) :
    cell k e.1 n ≅ (Q.obj (DGModuleCat.of k k))⟦n⟧ :=
  have he : e.1.val = 1 :=
    (IsIdempotentElem.iff_eq_zero_or_one.mp e.1.mul_self).resolve_left e.2.val_ne_zero
  (Q.commShiftIso n).app (DGModuleCat.of k e.1.LeftCorner) ≪≫
    (shiftFunctor _ n).mapIso (Q.mapIso
      { hom := DGModuleCat.ofHom e.1.leftCornerInclusion
        inv := DGModuleCat.ofHom e.1.leftCornerProjection
        hom_inv_id := DGModuleCat.hom_ext_apply fun x => Subtype.ext x.2
        inv_hom_id := DGModuleCat.hom_ext_apply fun x => by
          change x * e.1.val = x
          rw [he, mul_one] })

open _root_.DG.DerivedCategory in
theorem DerivedCategory.nonempty_cellSum_iso_shiftSum (l : List (SimpleIdempotent k × ℤ)) :
    Nonempty (cellSum (fun (i : SimpleIdempotent k) n => cell k i.1 n) l ≅
      shiftSum (Q.obj (DGModuleCat.of k k)) (l.map Prod.snd)) := by
  induction l with
  | nil => exact ⟨Iso.refl _⟩
  | cons c l ih => exact ⟨biprod.mapIso (cellIsoShiftSelf k c.1 c.2) ih.some⟩

open _root_.DG.DerivedCategory in
/-- **Compact objects over a field** (Roadmap 5.6, refinement): for a field `k` in degree `0`,
every compact object of `D(k)` is isomorphic to a finite direct sum `k⟦n₁⟧ ⊞ ⋯ ⊞ k⟦nᵣ⟧` of shifts
of `k`. -/
theorem DerivedCategory.nonempty_iso_shiftSum_of_isCompact {X : DerivedCategory.{u, u} k}
    (hX : IsCompact.{u} X) :
    ∃ l : List ℤ, Nonempty (X ≅ shiftSum (Q.obj (DGModuleCat.of k k)) l) := by
  have hk : IsPositive k := IsPositive.degreeZero k
  have hk0 : ∀ n : ℤ, 0 < n → grading (M := k) n = ⊥ :=
    fun n hn => degreeZeroGrading_of_ne k (by omega)
  obtain ⟨l, ⟨e⟩⟩ := (hk.isSemisimpleCellFamily hk0).exists_iso_cellSum
    (hk.hasOrderedCellTower_of_isCompact hX)
  exact ⟨l.map Prod.snd, ⟨e ≪≫ (nonempty_cellSum_iso_shiftSum k l).some⟩⟩

end Field

end DG
