import DG.Category.Derived.FiniteCell
import DG.Category.Positive

/-!
# Schnürer's theorem for positive dg categories

Let `C` be a positive dg category (`DG.DGCategory.IsPositive C`: the Hom complexes vanish in
negative degrees, the degree-`0` category is semisimple, and `d` vanishes on degree-`0`
morphisms). **Schnürer's theorem** [Sch, Thm. 1], for dg categories: an object of `D(C)` is
compact iff it is isomorphic to the image of a finite-cell dg module whose cells
`(eᵢ · C(Xᵢ, -))⟦nᵢ⟧` are attached in order of non-decreasing generating degree
`-n₁ ≤ -n₂ ≤ ⋯` (`DG.CatModule.FiniteCellFiltration.IsOrdered`), and the idempotents `eᵢ` can be
taken simple (`DG.DGCategory.IsPositive.isCompact_iff`,
`DG.DGCategory.IsPositive.exists_finiteCellFiltration_of_isCompact`).

## Main results

* `DG.DGCategory.IsPositive.isOrderedCellFamily`: the cells `Q (e · C(X, -))⟦n⟧`, `e` simple,
  form an ordered cell family in `D(C)` (`DG.IsOrderedCellFamily`): there are no nonzero
  morphisms `Q (e · C(X, -))⟦n⟧ ⟶ Q (f · C(Y, -))⟦m⟧` for `m < n` (as `C` has no negative
  degrees), and every nonzero morphism `Q (e · C(X, -))⟦n⟧ ⟶ Q (f · C(Y, -))⟦n⟧` is an isomorphism
  (Schur's lemma in the degree-`0` category, `DG.DGCategory.Idempotent.IsSimple.exists_inv`).
* `DG.DGCategory.IsPositive.hasOrderedCellTower_representable`: every representable module has an
  ordered cell tower (from a decomposition of `𝟙 X` into orthogonal simple idempotents).
* `DG.DGCategory.IsPositive.hasOrderedCellTower_of_isCompact`: every compact object has an ordered
  cell tower, since compact objects form the thick closure of the representable modules and
  objects with an ordered cell tower form a thick subcategory (`DG.IsOrderedCellFamily.isThick`).
* `DG.DGCategory.IsPositive.isCompact_iff`: **Schnürer's theorem** for positive dg categories.

The proof is that of `DG.IsPositive.isCompact_iff` (the case of a dg ring), with the free module
`A` replaced by the representable modules and the modules `A e` by the corners `e · C(X, -)`.

## Universes

For `C : Type u` with `[Category.{v} C]`, compactness refers to coproducts indexed by types in
the universe of the morphisms of `D(C)`; as for the compact generation of `D(C)` by the
representable modules, the statements are made for dg modules in `Type (max u v w)` and a
derived category with morphisms in the same universe.

## References

* [Sch] O. M. Schnürer, *Perfect derived categories of positively graded DG algebras*,
  Appl. Categ. Structures 19 (2011), 757–782; arXiv:0809.4782v2.
-/

open CategoryTheory Limits Pretriangulated

universe w' w v u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace DG

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C]

open DGCategory

/-- A list of cells all of whose shifts vanish is ordered. -/
theorem cellsOrdered_of_forall_snd_eq_zero {ι : Type*} {l : List (ι × ℤ)}
    (hl : ∀ c ∈ l, c.2 = 0) : CellsOrdered l := by
  induction l with
  | nil => exact cellsOrdered_nil
  | cons a l ih =>
    refine List.pairwise_cons.mpr ⟨fun b hb => ?_, ih fun c hc => hl c (by simp [hc])⟩
    rw [hl a (by simp), hl b (by simp [hb])]

namespace CatModule

/-! ### Morphisms between cells -/

section CellMap

variable {X Y Z : C} {e : Idempotent X} {f : Idempotent Y} {g : Idempotent Z}

/-- The morphism `(e · C(X, -))⟦n⟧ ⟶ (f · C(Y, -))⟦n⟧` induced by a morphism of corners. -/
abbrev cellMap (n : ℤ) (φ : corner e ⟶ corner f) : cellModule.{w} e n ⟶ cellModule.{w} f n :=
  shiftMap n (uliftMap φ)

theorem cellMap_comp (n : ℤ) (φ : corner e ⟶ corner f) (ψ : corner f ⟶ corner g) :
    cellMap.{w} n (φ ≫ ψ) = cellMap n φ ≫ cellMap n ψ := rfl

theorem cellMap_id (n : ℤ) : cellMap.{w} n (𝟙 (corner e)) = 𝟙 _ := rfl

theorem cellMap_add (n : ℤ) (φ ψ : corner e ⟶ corner f) :
    cellMap.{w} n (φ + ψ) = cellMap n φ + cellMap n ψ :=
  hom_ext fun _ _ => rfl

/-- The isomorphism `(e · C(X, -))⟦n⟧ ≅ (f · C(Y, -))⟦n⟧` induced by an isomorphism of
corners. -/
def cellIso (n : ℤ) (φ : corner e ≅ corner f) : cellModule.{w} e n ≅ cellModule.{w} f n where
  hom := cellMap n φ.hom
  inv := cellMap n φ.inv
  hom_inv_id := by rw [← cellMap_comp, φ.hom_inv_id, cellMap_id]
  inv_hom_id := by rw [← cellMap_comp, φ.inv_hom_id, cellMap_id]

/-- The coordinate of an element of `(f · C(Y, -))⟦m⟧` at `X`: the underlying morphism
`Y ⟶ X`. -/
abbrev cellCoord {m : ℤ} (x : (cellModule.{w} f m).obj X) : Y ⟶ X :=
  (shift.unmk m x).down.1

theorem cellModule_ext {m : ℤ} {x x' : (cellModule.{w} f m).obj X}
    (h : cellCoord x = cellCoord x') : x = x' :=
  shift.unmk_injective (ULift.ext _ _ (Subtype.ext h))

theorem cellCoord_zero {m : ℤ} : cellCoord (0 : (cellModule.{w} f m).obj X) = 0 := rfl

theorem mem_grading_cellModule_iff {m k : ℤ} {x : (cellModule.{w} f m).obj X} :
    x ∈ grading k ↔ cellCoord x ∈ grading (k + m) :=
  shift.mem_grading_iff'

theorem val_comp_cellCoord {m : ℤ} (x : (cellModule.{w} f m).obj X) :
    f.val ≫ cellCoord x = cellCoord x :=
  (shift.unmk m x).down.2

theorem cellCoord_smul {m : ℤ} {X' : C} (h : X ⟶ X') (x : (cellModule.{w} f m).obj X) :
    cellCoord (h • x) = cellCoord x ≫ twist m h := rfl

theorem cellCoord_cellGen (n : ℤ) : cellCoord (cellGen.{w} e n) = e.val := rfl

@[simp]
theorem cellCoord_cellMap_app {n : ℤ} (φ : corner e ⟶ corner f) (x : (cellModule.{w} e n).obj Z) :
    cellCoord ((cellMap n φ).app Z x) = (φ.app Z (shift.unmk n x).down).1 := rfl

/-- A morphism out of `(e · C(X, -))⟦n⟧` is determined by the image of the generator. -/
theorem cellModule_hom_ext (n : ℤ) {N : CatModule.{max v w} C} {φ ψ : cellModule.{w} e n ⟶ N}
    (h : φ.app X (cellGen e n) = ψ.app X (cellGen e n)) : φ = ψ := by
  have := (isCornerGenerator_cellModule.{w} e n).ext_gen (z := Cochain.ofHom φ)
    (z' := Cochain.ofHom ψ) h
  exact hom_ext fun Y r => congrArg (fun z : Cochain _ _ 0 => z.app Y r) this

/-- The coordinate of the image of the generator under a morphism
`(e · C(X, -))⟦n⟧ ⟶ (f · C(Y, -))⟦m⟧` satisfies `b ≫ e = b`. -/
theorem cellCoord_app_cellGen_comp {n m : ℤ} (φ : cellModule.{w} e n ⟶ cellModule.{w} f m) :
    cellCoord (φ.app X (cellGen e n)) ≫ e.val = cellCoord (φ.app X (cellGen e n)) := by
  have h := (isCornerGenerator_cellModule.{w} e n).val_smul
  conv_rhs => rw [← h, φ.map_smul]
  rw [cellCoord_smul, e.twist_val]

theorem cellCoord_app_cellGen_mem {n m : ℤ} (φ : cellModule.{w} e n ⟶ cellModule.{w} f m) :
    cellCoord (φ.app X (cellGen e n)) ∈ grading (0 - n + m) :=
  mem_grading_cellModule_iff.mp (φ.map_mem (isCornerGenerator_cellModule.{w} e n).mem_grading)

end CellMap

/-! ### Graded splittings from split sequences -/

/-- A split short exact sequence of dg modules (with splitting morphisms of dg modules) is
graded-split. -/
def GradedSplitting.ofRetract {F G K : CatModule.{w} C} {i : F ⟶ G} {p : G ⟶ K} (r : G ⟶ F)
    (s : K ⟶ G) (hri : i ≫ r = 𝟙 F) (hps : s ≫ p = 𝟙 K) (hsum : r ≫ i + p ≫ s = 𝟙 G) :
    GradedSplitting i p where
  r := Cochain.ofHom r
  s := Cochain.ofHom s
  r_i {X} x := congrArg (fun φ : F ⟶ F => φ.app X x) hri
  p_s {X} y := congrArg (fun φ : K ⟶ K => φ.app X y) hps
  i_r_add_s_p {X} x := congrArg (fun φ : G ⟶ G => φ.app X x) hsum

end CatModule

namespace DGCategory

namespace IsPositive

open CatModule CatModule.DerivedCategory

variable (hC : IsPositive C)
include hC

/-! ### The cells form an ordered cell family -/

section Cells

variable [CatModule.HasDerivedCategory.{w', max v w} C] {X Y : C} {e : Idempotent X}
  {f : Idempotent Y}

/-- There are no nonzero morphisms `Q (e · C(X, -))⟦n⟧ ⟶ Q (f · C(Y, -))⟦m⟧` for `m < n`, since
the Hom complexes of `C` have no components of negative degree. -/
theorem cell_hom_eq_zero_of_lt {n m : ℤ} (h : m < n) (φ : cell.{w', w} e n ⟶ cell f m) :
    φ = 0 := by
  obtain ⟨g, rfl⟩ := exists_Q_map_eq (isKProjective_cellModule e n) φ
  suffices hg : g = 0 by rw [hg, Functor.map_zero]
  refine cellModule_hom_ext n (cellModule_ext ?_)
  rw [CatModule.zero_app, cellCoord_zero]
  exact hC.eq_zero_of_neg (by omega) (cellCoord_app_cellGen_mem g)

/-- **Schur's lemma for cells** ([Sch, Lemma 5]): a nonzero morphism
`Q (e · C(X, -))⟦n⟧ ⟶ Q (f · C(Y, -))⟦n⟧` between cells with `e`, `f` simple is an isomorphism.
It is the image of the morphism `h ↦ b ≫ h` for a nonzero degree-`0` `b ∈ f · C(Y, X) · e`,
which is invertible by Schur's lemma in the degree-`0` category. -/
theorem isIso_cell_hom (he : e.IsSimple) (hf : f.IsSimple) {n : ℤ}
    (φ : cell.{w', w} e n ⟶ cell f n) (hφ : φ ≠ 0) : IsIso φ := by
  obtain ⟨g, rfl⟩ := exists_Q_map_eq (isKProjective_cellModule e n) φ
  set b := cellCoord (g.app X (cellGen e n)) with hbdef
  have hb0 : b ∈ grading 0 := by simpa using cellCoord_app_cellGen_mem g
  have hb : b ∈ cocycles (Y ⟶ X) 0 := ⟨hb0, hC.d_eq_zero hb0⟩
  have hfb : f.val ≫ b = b := val_comp_cellCoord _
  have hbe : b ≫ e.val = b := cellCoord_app_cellGen_comp g
  have hbne : b ≠ 0 := by
    intro h0
    apply hφ
    have : g = 0 := cellModule_hom_ext n (cellModule_ext (by
      rw [CatModule.zero_app, cellCoord_zero]
      exact h0))
    rw [this, Functor.map_zero]
  obtain ⟨c, hc0, hec, -, hbc, hcb⟩ := he.exists_inv hf hb0 hfb hbe hbne
  have hc : c ∈ cocycles (X ⟶ Y) 0 := ⟨hc0, hC.d_eq_zero hc0⟩
  let E : corner e ≅ corner f :=
    { hom := cornerHom e f b hb hfb
      inv := cornerHom f e c hc hec
      hom_inv_id := hom_ext fun _ h => Subtype.ext (by
        change c ≫ b ≫ h.1 = h.1
        rw [← Category.assoc, hcb]
        exact h.2)
      inv_hom_id := hom_ext fun _ h => Subtype.ext (by
        change b ≫ c ≫ h.1 = h.1
        rw [← Category.assoc, hbc]
        exact h.2) }
  have hg : g = (cellIso n E).hom := by
    refine cellModule_hom_ext n (cellModule_ext ?_)
    change b = b ≫ e.val
    rw [hbe]
  rw [hg]
  exact inferInstanceAs (IsIso (Q.mapIso (cellIso n E)).hom)

/-- The cells `Q (e · C(X, -))⟦n⟧` of a positive dg category are nonzero for `e` simple: the
generator `e` is a cocycle of degree `-n` which is not a coboundary, as `C(X, X)⁻¹ = 0`. -/
theorem not_isZero_cell (he : e.IsSimple) (n : ℤ) : ¬ IsZero (cell.{w', w} e n) := by
  intro hZ
  rw [isZero_Q_obj_iff] at hZ
  have hg := isCornerGenerator_cellModule.{w} e n
  obtain ⟨z, hz, hdz⟩ := hZ.exists_d_eq hg.mem_grading hg.d_eq_zero
  have hz0 : z = 0 := cellModule_ext (by
    rw [cellCoord_zero]
    exact hC.eq_zero_of_neg (by omega) (mem_grading_cellModule_iff.mp hz))
  rw [hz0, d_zero] at hdz
  exact he.1 (congrArg cellCoord hdz).symm

/-- The cells `Q (e · C(X, -))⟦n⟧`, `e` simple, of a positive dg category form an ordered cell
family. -/
theorem isOrderedCellFamily :
    IsOrderedCellFamily (fun (i : SimpleCorner C) (n : ℤ) => cell.{w', w} i.1.2 n) where
  nonempty_shiftIso i n k := nonempty_cellShiftIso i.1.2 n k
  eq_zero_of_lt h f := hC.cell_hom_eq_zero_of_lt h f
  isIso_of_ne_zero {i j} _ f hf := hC.isIso_cell_hom i.2 j.2 f hf
  not_isZero i n := hC.not_isZero_cell i.2 n

end Cells

/-! ### Decomposition of the representable modules into simple cells -/

section Decomposition

variable [CatModule.HasDerivedCategory.{w', max v w} C] {X : C}

omit hC in
theorem isZero_cell_of_val_eq_zero {g : Idempotent X} (hg : g.val = 0) (n : ℤ) :
    IsZero (cell.{w', w} g n) := by
  have : ∀ Y, Subsingleton ((cellModule.{w} g n).obj Y) := fun Y =>
    ⟨fun x y => cellModule_ext (by
      rw [← val_comp_cellCoord x, ← val_comp_cellCoord y, hg, Limits.zero_comp,
        Limits.zero_comp])⟩
  exact Functor.map_isZero _ (isZero_of_subsingleton _)

omit hC in
/-- For orthogonal degree-`0` idempotent cocycles `e`, `t` of `X` with sum `g`, there is a
distinguished triangle `Q (t · C(X, -)) → Q (g · C(X, -)) → Q (e · C(X, -)) → ⋯` (from the split
sequence `t · C(X, -) → g · C(X, -) → e · C(X, -)`). -/
theorem exists_distinguished_of_add (e t g : Idempotent X) (het : e.val ≫ t.val = 0)
    (hte : t.val ≫ e.val = 0) (hsum : e.val + t.val = g.val) :
    ∃ (u : cell.{w', w} t 0 ⟶ cell g 0) (v : cell g 0 ⟶ cell e 0)
      (δ : cell e 0 ⟶ (cell t 0)⟦(1 : ℤ)⟧), Triangle.mk u v δ ∈ distTriang _ := by
  have hgt : g.val ≫ t.val = t.val := by
    rw [← hsum, Preadditive.add_comp, het, t.comp_self, zero_add]
  have hge : g.val ≫ e.val = e.val := by
    rw [← hsum, Preadditive.add_comp, hte, e.comp_self, add_zero]
  let i := cornerHom t g t.val t.mem_cocycles hgt
  let p := cornerHom g e e.val e.mem_cocycles e.comp_self
  let r := cornerHom g t t.val t.mem_cocycles t.comp_self
  let s := cornerHom e g e.val e.mem_cocycles hge
  have hri : i ≫ r = 𝟙 _ := hom_ext fun _ h => Subtype.ext (by
    change t.val ≫ t.val ≫ h.1 = h.1
    rw [t.comp_self_assoc]
    exact h.2)
  have hps : s ≫ p = 𝟙 _ := hom_ext fun _ h => Subtype.ext (by
    change e.val ≫ e.val ≫ h.1 = h.1
    rw [e.comp_self_assoc]
    exact h.2)
  have hsum' : r ≫ i + p ≫ s = 𝟙 _ := hom_ext fun _ h => Subtype.ext (by
    change t.val ≫ t.val ≫ h.1 + e.val ≫ e.val ≫ h.1 = h.1
    rw [t.comp_self_assoc, e.comp_self_assoc, ← Preadditive.add_comp, add_comm, hsum]
    exact h.2)
  let σ : CatModule.GradedSplitting (cellMap.{w} 0 i) (cellMap 0 p) :=
    GradedSplitting.ofRetract (cellMap 0 r) (cellMap 0 s)
      (by rw [← cellMap_comp, hri, cellMap_id]) (by rw [← cellMap_comp, hps, cellMap_id])
      (by rw [← cellMap_comp, ← cellMap_comp, ← cellMap_add, hsum', cellMap_id])
  obtain ⟨δ, hδ⟩ := σ.exists_distinguished
  exact ⟨_, _, δ, hδ⟩

omit hC in
/-- For a list `l` of pairwise orthogonal simple idempotents of `X`, the cell
`Q (g · C(X, -))` of their sum `g` has a cell tower whose cells are the `Q (e · C(X, -))`,
`e ∈ l` (all of shift `0`). -/
theorem exists_cellTower_listSum (l : List (Idempotent X)) (hl : l.Pairwise Idempotent.Orthogonal)
    (hs : ∀ e ∈ l, e.IsSimple) :
    ∃ L : List (SimpleCorner C × ℤ), (∀ c ∈ L, c.2 = 0) ∧
      CellTower (fun (i : SimpleCorner C) n => cell.{w', w} i.1.2 n) L
        (cell (Idempotent.listSum l hl) 0) := by
  induction l with
  | nil => exact ⟨[], by simp, .zero (isZero_cell_of_val_eq_zero (by simp) 0)⟩
  | cons e l ih =>
    obtain ⟨he, hl'⟩ := List.pairwise_cons.mp hl
    obtain ⟨L, hL0, hL⟩ := ih hl' fun f hf => hs f (by simp [hf])
    obtain ⟨het, hte⟩ := Idempotent.orthogonal_listSum he hl'
    obtain ⟨u, v, δ, hT⟩ : ∃ (u : cell.{w', w} (Idempotent.listSum l hl') 0 ⟶
        cell (Idempotent.listSum (e :: l) hl) 0) (v : _ ⟶ cell e 0) (δ : _ ⟶ _),
        Triangle.mk u v δ ∈ distTriang _ :=
      exists_distinguished_of_add e _ _ het hte (by simp)
    refine ⟨L ++ [(⟨⟨X, e⟩, hs e (by simp)⟩, 0)], fun c hc => ?_, .ext _ hT hL ⟨Iso.refl _⟩⟩
    rcases List.mem_append.mp hc with hc | hc
    · exact hL0 c hc
    · simp at hc
      rw [hc]

end Decomposition

section Representable

variable [CatModule.HasDerivedCategory.{max u v w, max u v w} C]

omit hC in
/-- For an idempotent `g` with `g = 𝟙`, `Q C(X, -) ≅ Q (g · C(X, -))`. -/
def representableIsoCell {X : C} (g : Idempotent X) (hg : g.val = 𝟙 X) :
    Q.obj (representableW.{w} C X) ≅ cell.{max u v w, max u w} g 0 :=
  Q.mapIso
    ({ hom := uliftMap (cornerRetract g).r
       inv := uliftMap (cornerRetract g).i
       hom_inv_id := by
         rw [← uliftMap_comp]
         convert uliftMap_id (representable X)
         exact hom_ext fun _ h => by
           change g.val ≫ h = h
           rw [hg, Category.id_comp]
       inv_hom_id := by rw [← uliftMap_comp, (cornerRetract g).retract, uliftMap_id] } ≪≫
      (shiftZeroIso _).symm)

/-- Every representable module has an ordered cell tower with cells `Q (e · C(X, -))`, `e`
simple (all of shift `0`), from a decomposition of `𝟙 X` into orthogonal simple idempotents. -/
theorem hasOrderedCellTower_representable (X : C) :
    HasOrderedCellTower (fun (i : SimpleCorner C) n => cell.{max u v w, max u w} i.1.2 n)
      (Q.obj (representableW.{w} C X)) := by
  obtain ⟨l, hs, hl, hsum⟩ := hC.semisimple X
  obtain ⟨L, hL0, hL⟩ : ∃ L : List (SimpleCorner C × ℤ), (∀ c ∈ L, c.2 = 0) ∧
      CellTower (fun (i : SimpleCorner C) n => cell.{max u v w, max u w} i.1.2 n) L
        (cell (Idempotent.listSum l hl) 0) :=
    exists_cellTower_listSum l hl hs
  exact ⟨L, cellsOrdered_of_forall_snd_eq_zero hL0,
    hL.of_iso (representableIsoCell _ (by rw [Idempotent.listSum_val, hsum])).symm⟩

/-! ### Schnürer's theorem -/

/-- Every compact object of `D(C)` has an ordered cell tower with simple cells: compact objects
form the thick closure of the representable modules, which have such towers, and objects with
such a tower form a thick subcategory. -/
theorem hasOrderedCellTower_of_isCompact {Y : CatModule.DerivedCategory.{max u v w, max u v w} C}
    (hY : IsCompact.{max u v w} Y) :
    HasOrderedCellTower (fun (i : SimpleCorner C) n => cell.{max u v w, max u w} i.1.2 n) Y := by
  rw [← thickClosure_representable_eq_isCompact.{w}] at hY
  exact hC.isOrderedCellFamily.thickClosure_le
    (by rintro _ ⟨X, rfl⟩; exact hC.hasOrderedCellTower_representable X) Y hY

/-- **Schnürer's theorem** for positive dg categories, the hard direction ([Sch, Thm. 1 (2)] for
dg algebras): every compact object of `D(C)` is isomorphic to the image of a finite-cell dg
module whose cells `(eᵢ · C(Xᵢ, -))⟦nᵢ⟧` have simple idempotents `eᵢ` and shifts
`n₁ ≥ n₂ ≥ ⋯`. -/
theorem exists_finiteCellFiltration_of_isCompact
    {Y : CatModule.DerivedCategory.{max u v w, max u v w} C} (hY : IsCompact.{max u v w} Y) :
    ∃ (P : CatModule.{max u v w} C) (S : FiniteCellFiltration.{max u w} P),
      S.IsOrdered ∧ (∀ i, (S.e i).IsSimple) ∧ Nonempty (Y ≅ Q.obj P) := by
  obtain ⟨l, hlo, hl⟩ := hC.hasOrderedCellTower_of_isCompact hY
  obtain ⟨P, S, hS, he⟩ := exists_finiteCellFiltration_of_cellTower Subtype.val hl
  refine ⟨P, S, ?_, fun i => ?_, he⟩
  · rw [S.isOrdered_iff_cellsOrdered, hS]
    unfold CellsOrdered at hlo ⊢
    rw [List.pairwise_map]
    exact hlo
  · have hi : ((⟨S.obj i, S.e i⟩ : Corner C), S.deg i) ∈ S.cells := List.mem_ofFn.mpr ⟨i, rfl⟩
    rw [hS, List.mem_map] at hi
    obtain ⟨c, -, hc⟩ := hi
    have h1 : c.1.1 = ⟨S.obj i, S.e i⟩ := congrArg Prod.fst hc
    have := c.1.2
    rw [h1] at this
    exact this

/-- **Schnürer's theorem** for positive dg categories [Sch, Thm. 1]: an object of `D(C)` is
compact iff it is isomorphic to the image of a finite-cell dg module with ordered cells
(`n₁ ≥ n₂ ≥ ⋯`); the idempotents of the cells can moreover be taken simple
(`DG.DGCategory.IsPositive.exists_finiteCellFiltration_of_isCompact`). -/
theorem isCompact_iff {Y : CatModule.DerivedCategory.{max u v w, max u v w} C} :
    IsCompact.{max u v w} Y ↔ ∃ (P : CatModule.{max u v w} C)
      (S : FiniteCellFiltration.{max u w} P), S.IsOrdered ∧ Nonempty (Y ≅ Q.obj P) := by
  constructor
  · intro hY
    obtain ⟨P, S, hS, -, he⟩ := hC.exists_finiteCellFiltration_of_isCompact hY
    exact ⟨P, S, hS, he⟩
  · rintro ⟨P, S, -, ⟨e⟩⟩
    exact S.isCompact_Q_obj.of_iso e

/-- Schnürer's theorem for dg modules: a dg module over a positive dg category is compact in
`D(C)` iff it is quasi-isomorphic (isomorphic in `D(C)`) to a finite-cell module with ordered
cells. -/
theorem isCompact_Q_obj_iff (M : CatModule.{max u v w} C) :
    IsCompact.{max u v w} (Q.obj M : CatModule.DerivedCategory.{max u v w, max u v w} C) ↔
      ∃ (P : CatModule.{max u v w} C) (S : FiniteCellFiltration.{max u w} P),
        S.IsOrdered ∧ Nonempty ((Q.obj M : CatModule.DerivedCategory.{max u v w, max u v w} C) ≅
          Q.obj P) :=
  hC.isCompact_iff

end Representable

end IsPositive

end DGCategory

end DG

end
