import DG.Compact.CellTower
import DG.Category.Derived.Compact
import DG.Category.Derived.GradedSplitting
import DG.Category.Resolution.SemiFree

/-!
# Finite-cell dg modules over a dg category in the derived category

Let `C` be a dg category. A finite-cell dg module (`DG.CatModule.FiniteCellFiltration`) has a
finite filtration whose subquotients are shifts `(eᵢ · C(Xᵢ, -))⟦nᵢ⟧` of the direct summands of
representable modules cut out by degree-`0` idempotent cocycles `eᵢ`. This file relates
finite-cell modules to cell towers (`DG.CellTower`) in `D(C)`, with cells `Q (e · C(X, -))⟦n⟧`.
It is a port of `DG.Derived.FiniteCell` (the case of a dg ring).

## Main definitions and results

* `DG.DGCategory.Corner C`: pairs `(X, e)` of an object and a degree-`0` idempotent cocycle; they
  index the cells.
* `DG.CatModule.cornerHom`: the morphism `e · C(X, -) ⟶ f · C(Y, -)`, `h ↦ b ≫ h`, attached to a
  degree-`0` cocycle `b : Y ⟶ X` with `f ≫ b = b`.
* `DG.CatModule.cellModule e n = (e · C(X, -))⟦n⟧` (lifted to a larger universe) and the cells
  `DG.CatModule.DerivedCategory.cell e n = Q ((e · C(X, -))⟦n⟧)` of `D(C)`, with
  `DG.CatModule.DerivedCategory.cellShiftIso : (cell e n)⟦k⟧ ≅ cell e (n + k)`;
  `DG.CatModule.DerivedCategory.isCompact_cell`: the cells are compact.
* `DG.CatModule.FiniteCellFiltration.cells`: the list of cells of a finite-cell filtration;
  `DG.CatModule.FiniteCellFiltration.cellTower`: the image in `D(C)` of a finite-cell module has
  the cell tower given by its filtration (each step is a graded-split extension, hence a
  distinguished triangle, `DG.CatModule.GradedSplitting.exists_distinguished`);
  `DG.CatModule.FiniteCellFiltration.isCompact_Q_obj`: finite-cell modules are compact.
* `DG.CatModule.FiniteCellFiltration.snoc`: for a morphism `ψ : (e · C(X, -))⟦m⟧ → P` into a
  finite-cell module, the mapping cone of `ψ` is finite-cell, with the cells of `P` followed by
  `(e · C(X, -))⟦m + 1⟧`.
* `DG.CatModule.DerivedCategory.exists_finiteCellFiltration_of_cellTower`: conversely, every
  object of `D(C)` with a cell tower is isomorphic to the image of a finite-cell module with the
  same list of cells.
-/

open CategoryTheory Limits Pretriangulated DirectSum

universe w' w v u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace DG

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

namespace DGCategory

variable (C) in
/-- A *corner* of a dg category: an object `X` with a degree-`0` idempotent cocycle `e` of `X`,
the datum of the direct summand `e · C(X, -)` of the representable module `C(X, -)`. -/
abbrev Corner : Type (max u v) := Σ X : C, Idempotent X

end DGCategory

open DGCategory

namespace CatModule

/-! ### Universe lifts of morphisms -/

section ULiftMap

variable {M N P : CatModule.{w} C}

/-- The universe lift `ulift M ⟶ ulift N` of a morphism `M ⟶ N`. -/
@[simps]
def uliftMap (φ : M ⟶ N) : ulift.{w'} M ⟶ ulift.{w'} N where
  app X := (ULift.upAddHom _).comp ((φ.app X).comp (ULift.downAddHom _))
  map_mem' hm := φ.map_mem hm
  map_d' m := ULift.ext _ _ (φ.map_d m.down)
  map_smul' f m := ULift.ext _ _ (φ.map_smul f m.down)

theorem uliftMap_comp (φ : M ⟶ N) (ψ : N ⟶ P) :
    uliftMap.{w'} (φ ≫ ψ) = uliftMap φ ≫ uliftMap ψ := rfl

theorem uliftMap_id (M : CatModule.{w} C) : uliftMap.{w'} (𝟙 M) = 𝟙 _ := rfl

end ULiftMap

variable [DGCategory C]

/-! ### Morphisms between corners -/

section CornerHom

variable {X Y : C} (e : Idempotent X) (f : Idempotent Y)

/-- The morphism `e · C(X, -) ⟶ f · C(Y, -)`, `h ↦ b ≫ h`, attached to a degree-`0` cocycle
`b : Y ⟶ X` with `f ≫ b = b`. -/
@[simps]
def cornerHom (b : Y ⟶ X) (hb : b ∈ cocycles (Y ⟶ X) 0) (hfb : f.val ≫ b = b) :
    corner e ⟶ corner f where
  app Z :=
    { toFun h := ⟨b ≫ h.1, by
        change f.val ≫ b ≫ h.1 = b ≫ h.1
        rw [← Category.assoc, hfb]⟩
      map_zero' := Subtype.ext (Limits.comp_zero)
      map_add' h h' := Subtype.ext (Preadditive.comp_add _ _ _ _ _ _) }
  map_mem' {Z n h} hh := by
    have := comp_mem_grading hb.1 hh
    rwa [zero_add] at this
  map_d' h := Subtype.ext (d_comp_of_d_eq_zero_left hb.2 h.1).symm
  map_smul' g h := Subtype.ext (Category.assoc b h.1 g).symm

theorem cornerHom_comp {Z : C} (g : Idempotent Z) (b : Y ⟶ X) (hb : b ∈ cocycles (Y ⟶ X) 0)
    (hfb : f.val ≫ b = b) (c : Z ⟶ Y) (hc : c ∈ cocycles (Z ⟶ Y) 0) (hgc : g.val ≫ c = c) :
    cornerHom e f b hb hfb ≫ cornerHom f g c hc hgc =
      cornerHom e g (c ≫ b) (by simpa using comp_mem_cocycles hc hb)
        (by rw [← Category.assoc, hgc]) :=
  hom_ext fun _ h => Subtype.ext (Category.assoc c b h.1).symm

/-- `cornerHom e e e = 𝟙`. -/
theorem cornerHom_self : cornerHom e e e.val e.mem_cocycles e.comp_self = 𝟙 _ :=
  hom_ext fun _ h => Subtype.ext h.2

/-- The corner `e · C(X, -)` is a direct summand of the representable module `C(X, -)`. -/
def cornerRetract : Retract (corner e) (representable X) where
  i := (cornerSubmodule e).subtype
  r := yonedaHom ⟨cornerGen e, e.mem_cocycles.1, Subtype.ext e.d_val⟩
  retract := hom_ext fun _ h => Subtype.ext h.2

end CornerHom

/-! ### Cells -/

section Cells

variable {X : C} (e : Idempotent X)

/-- The dg module `(e · C(X, -))⟦n⟧`, lifted to the universe `max v w`: the subquotients of the
finite-cell filtrations (`DG.CatModule.FiniteCellFiltration`). -/
abbrev cellModule (n : ℤ) : CatModule.{max v w} C :=
  shift n (ulift.{w} (corner e))

/-- The generator of `(e · C(X, -))⟦n⟧`, of degree `-n`. -/
abbrev cellGen (n : ℤ) : (cellModule.{w} e n).obj X :=
  shift.mk n (ULift.up (cornerGen e))

theorem isCornerGenerator_cellModule (n : ℤ) :
    IsCornerGenerator (cellModule.{w} e n) e (0 - n) (cellGen.{w} e n) :=
  ((isCornerGenerator_corner e).ulift.{w}).shift n

theorem isKProjective_cellModule (n : ℤ) : IsKProjective (cellModule.{w} e n) :=
  (isCornerGenerator_cellModule e n).isKProjective

/-- The isomorphism `(e · C(X, -))⟦n⟧ ≅ (e' · C(X', -))⟦n'⟧` for equal corners and shifts. -/
def cellModuleCongr {c c' : Corner C × ℤ} (h : c = c') :
    cellModule.{w} c.1.2 c.2 ≅ cellModule.{w} c'.1.2 c'.2 := by
  subst h
  exact Iso.refl _

theorem bijective_cellModuleCongr_app {c c' : Corner C × ℤ} (h : c = c') (Y : C) :
    Function.Bijective ((cellModuleCongr.{w} h).hom.app Y) :=
  (isIso_iff_bijective _).mp inferInstance Y

end Cells

namespace DerivedCategory

variable [HasDerivedCategory.{w', max v w} C]

section Cells

variable {X : C} (e : Idempotent X)

/-- The cell `Q (e · C(X, -))⟦n⟧` of `D(C)` attached to a corner and `n : ℤ`. -/
abbrev cell (n : ℤ) : DerivedCategory.{w', max v w} C :=
  Q.obj (cellModule.{w} e n)

/-- `(Q (e · C(X, -))⟦n⟧)⟦k⟧ ≅ Q (e · C(X, -))⟦n + k⟧`. -/
def cellShiftIso (n k : ℤ) : (cell.{w'} e n)⟦k⟧ ≅ cell e (n + k) :=
  ((Q.commShiftIso k).app (cellModule.{w} e n)).symm ≪≫
    Q.mapIso (shiftShiftIso (M := ulift.{w} (corner e)) n k (n + k) rfl).symm

theorem nonempty_cellShiftIso (n k : ℤ) :
    Nonempty ((cell.{w'} e n)⟦k⟧ ≅ cell e (n + k)) :=
  ⟨cellShiftIso e n k⟩

end Cells

end DerivedCategory

/-! ### Finite-cell modules and cell towers -/

namespace FiniteCellFiltration

variable {P : CatModule.{max v w} C} (S : FiniteCellFiltration.{w} P)

/-- The list of cells `[((X₁, e₁), n₁), …, ((Xₖ, eₖ), nₖ)]` of a finite-cell filtration. -/
def cells : List (Corner C × ℤ) := List.ofFn fun i => (⟨S.obj i, S.e i⟩, S.deg i)

@[simp]
theorem length_cells : S.cells.length = S.length := by simp [cells]

/-- A finite-cell filtration is ordered iff its list of cells is. -/
theorem isOrdered_iff_cellsOrdered : S.IsOrdered ↔ CellsOrdered S.cells := by
  unfold IsOrdered CellsOrdered cells
  rw [List.pairwise_ofFn]
  constructor
  · intro h i j hij
    exact h i j hij.le
  · intro h i j hij
    rcases hij.lt_or_eq with hij | rfl
    · exact h hij
    · exact le_rfl

/-- The isomorphism `P ≅ F length` of a finite-cell module with the last member of its
filtration. -/
def isoF : P ≅ (S.F S.length).toCatModule where
  hom := CatSubmodule.codRestrict (𝟙 P) S.mem_length
  inv := (S.F S.length).subtype
  hom_inv_id := hom_ext fun _ _ => rfl
  inv_hom_id := hom_ext fun _ _ => rfl

theorem isZero_F_zero : IsZero (S.F 0).toCatModule := by
  have : ∀ X, Subsingleton ((S.F 0).toCatModule.obj X) := fun X =>
    ⟨fun x y => Subtype.ext (by
      rw [S.eq_zero_of_mem_zero X x.1 x.2, S.eq_zero_of_mem_zero X y.1 y.2])⟩
  exact isZero_of_subsingleton _

open _root_.DG.CatModule.DerivedCategory

variable [HasDerivedCategory.{w', max v w} C]

theorem cellTower_F {j : ℕ} (hj : j ≤ S.length) :
    CellTower (fun (c : Corner C) n => cell.{w'} c.2 n) (S.cells.take j)
      (Q.obj (S.F j).toCatModule) := by
  induction j with
  | zero => exact .zero (Functor.map_isZero _ S.isZero_F_zero)
  | succ j ih =>
    obtain ⟨δ, hδ⟩ := (S.gradedSplitting ⟨j, hj⟩).exists_distinguished
    have htake : S.cells.take (j + 1) =
        S.cells.take j ++ [(⟨S.obj ⟨j, hj⟩, S.e ⟨j, hj⟩⟩, S.deg ⟨j, hj⟩)] := by
      rw [List.take_add_one]
      congr 1
      simp [cells, show j < S.length by omega]
    rw [htake]
    exact .ext _ hδ (ih (by omega)) ⟨Iso.refl _⟩

/-- The image in `D(C)` of a finite-cell module has the cell tower given by its filtration. -/
theorem cellTower :
    CellTower (fun (c : Corner C) n => cell.{w'} c.2 n) S.cells (Q.obj P) := by
  have : CellTower (fun (c : Corner C) n => cell.{w'} c.2 n) (S.cells.take S.length)
      (Q.obj (S.F S.length).toCatModule) := S.cellTower_F le_rfl
  rw [List.take_of_length_le (by simp)] at this
  exact this.of_iso (Q.mapIso S.isoF).symm

/-- The image in `D(C)` of a finite-cell module lies in every thick subcategory containing its
cells. -/
theorem Q_obj_mem_of_isThick {T : ObjectProperty (DerivedCategory.{w', max v w} C)}
    (hT : IsThick T) (hS : ∀ i, T (cell (S.e i) (S.deg i))) : T (Q.obj P) :=
  S.cellTower.mem_of_isThick hT fun c hc => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    exact hS i

end FiniteCellFiltration

/-! ### Compactness -/

namespace DerivedCategory

section Compact

variable [HasDerivedCategory.{max u v w, max u v w} C]

/-- The cells `Q (e · C(X, -))⟦n⟧` are compact: `e · C(X, -)` is a direct summand of the
representable module `C(X, -)`, which is compact. -/
theorem isCompact_cell {X : C} (e : Idempotent X) (n : ℤ) :
    IsCompact.{max u v w} (cell.{max u v w, max u w} e n) := by
  have h0 : IsCompact.{max u v w} (Q.obj (ulift.{max u w} (corner e)) :
      DerivedCategory.{max u v w, max u v w} C) :=
    IsCompact.of_retract
      ⟨Q.map (uliftMap (cornerRetract e).i), Q.map (uliftMap (cornerRetract e).r), by
        rw [← Q.map_comp, ← uliftMap_comp, (cornerRetract e).retract, uliftMap_id,
          CategoryTheory.Functor.map_id]⟩
      (isCompact_Q_obj (isCornerGenerator_representableW.{w} X))
  exact (h0.shift n).of_iso ((Q.commShiftIso n).app _)

/-- Finite-cell dg modules are compact in `D(C)`. -/
theorem _root_.DG.CatModule.FiniteCellFiltration.isCompact_Q_obj
    {P : CatModule.{max u v w} C} (S : FiniteCellFiltration.{max u w} P) :
    IsCompact.{max u v w} (Q.obj P : DerivedCategory.{max u v w, max u v w} C) :=
  S.Q_obj_mem_of_isThick (isThick_isCompact _) fun _ => isCompact_cell _ _

end Compact

end DerivedCategory

/-! ### Attaching a cell to a finite-cell module -/

namespace FiniteCellFiltration

section Snoc

variable {P : CatModule.{max v w} C} (S : FiniteCellFiltration.{w} P) {X : C}
  {e : Idempotent X} {m : ℤ} (ψ : cellModule.{w} e m ⟶ P)

/-- The members of the filtration of `cone ψ` extending that of `P` by one cell. -/
def snocF (j : ℕ) : CatSubmodule (cone ψ) where
  carrier Y :=
    { carrier := {c | (j ≤ S.length → (cone.fstHom ψ).app Y c = 0) ∧
        cone.sndAddHom ψ Y c ∈ (S.F (min j S.length)).carrier Y}
      zero_mem' := ⟨fun _ => map_zero _, by rw [map_zero]; exact zero_mem _⟩
      add_mem' := fun {a b} ha hb => ⟨fun h => by rw [map_add, ha.1 h, hb.1 h, add_zero], by
        rw [map_add]
        exact add_mem ha.2 hb.2⟩
      neg_mem' := fun {a} ha => ⟨fun h => by
        change (cone.fstHom ψ).app Y (-a) = 0
        rw [map_neg, ha.1 h, neg_zero], by
        change cone.sndAddHom ψ Y (-a) ∈ _
        rw [map_neg]
        exact neg_mem ha.2⟩ }
  decompose_mem' {Y c} hc n := by
    refine ⟨fun h => ?_, ?_⟩
    · rw [← coe_decompose_map_of_map_mem ((cone.fstHom ψ).app Y)
        (fun h => (cone.fstHom ψ).map_mem h), hc.1 h, decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]
    · rw [← coe_decompose_map_of_map_mem (cone.sndAddHom ψ Y) (fun h => cone.sndAddHom_mem h)]
      exact (S.F _).decompose_mem hc.2 n
  d_mem' {Y c} hc := by
    refine ⟨fun h => by rw [cone.fstHom_d, hc.1 h, d_zero], ?_⟩
    rw [cone.sndAddHom_d]
    refine add_mem ?_ ((S.F _).d_mem hc.2)
    by_cases h : j ≤ S.length
    · rw [hc.1 h, map_zero, map_zero]
      exact zero_mem _
    · rw [min_eq_right (by omega)]
      exact S.mem_length _ _
  smul_mem' {Y Z} g c hc :=
    ⟨fun h => by rw [Hom.map_smul, hc.1 h, smul_zero], by
      rw [cone.sndAddHom_smul]
      exact (S.F _).smul_mem g hc.2⟩

theorem mem_snocF {j : ℕ} {Y : C} {c : (cone ψ).obj Y} : c ∈ (S.snocF ψ j).carrier Y ↔
    (j ≤ S.length → (cone.fstHom ψ).app Y c = 0) ∧
      cone.sndAddHom ψ Y c ∈ (S.F (min j S.length)).carrier Y :=
  Iff.rfl

/-- The cells of the extended filtration: those of `S`, followed by `c`. -/
def snocCell (c : Corner C × ℤ) (i : Fin (S.length + 1)) : Corner C × ℤ :=
  if h : i.1 < S.length then (⟨S.obj ⟨i, h⟩, S.e ⟨i, h⟩⟩, S.deg ⟨i, h⟩) else c

/-- The restriction `F (i + 1) → S.F (i + 1)` to the second component, for `i + 1 ≤ length`. -/
def snocRestrict (i : ℕ) (hi : i + 1 ≤ S.length) :
    (S.snocF ψ (i + 1)).toCatModule ⟶ (S.F (i + 1)).toCatModule where
  app Y :=
    { toFun c := ⟨cone.sndAddHom ψ Y c.1, by
        have := c.2.2
        rwa [min_eq_left hi] at this⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' _ _ := Subtype.ext (map_add _ _ _) }
  map_mem' hc := cone.sndAddHom_mem hc
  map_d' {Y} c := by
    apply Subtype.ext
    change cone.sndAddHom ψ Y (d c.1) = d (cone.sndAddHom ψ Y c.1)
    rw [cone.sndAddHom_d, c.2.1 hi, map_zero, map_zero, zero_add]
  map_smul' _ _ := rfl

/-- The projection `F (length + 1) → (e · C(X, -))⟦m + 1⟧` onto the last cell. -/
def snocLast : (S.snocF ψ (S.length + 1)).toCatModule ⟶ cellModule.{w} e (m + 1) :=
  (S.snocF ψ (S.length + 1)).subtype ≫ cone.fstHom ψ ≫
    (shiftShiftIso (M := ulift.{w} (corner e)) m 1 (m + 1) rfl).inv

/-- The projections of the extended filtration. -/
def snocπ (i : Fin (S.length + 1)) : (S.snocF ψ (i.1 + 1)).toCatModule ⟶
    cellModule.{w} (S.snocCell (⟨X, e⟩, m + 1) i).1.2 (S.snocCell (⟨X, e⟩, m + 1) i).2 :=
  if h : i.1 < S.length then
    S.snocRestrict ψ i h ≫ S.π ⟨i, h⟩ ≫
      (cellModuleCongr (show _ = S.snocCell (⟨X, e⟩, m + 1) i from (dite_eq_left h).symm)).hom
  else
    CatSubmodule.inclusion (fun Y => le_of_eq (by rw [show i.1 = S.length by omega])) ≫
      S.snocLast ψ ≫
        (cellModuleCongr (show _ = S.snocCell (⟨X, e⟩, m + 1) i from (dite_eq_right h).symm)).hom

theorem snocπ_eq_zero_iff (i : Fin (S.length + 1)) (Y : C)
    (x : (S.snocF ψ (i.1 + 1)).toCatModule.obj Y) :
    (S.snocπ ψ i).app Y x = 0 ↔ x.1 ∈ (S.snocF ψ i.1).carrier Y := by
  unfold snocπ
  split_ifs with h
  · rw [comp_app, comp_app, map_eq_zero_iff _ (bijective_cellModuleCongr_app _ Y).1,
      S.π_eq_zero_iff, mem_snocF]
    refine ⟨fun hx => ⟨fun _ => x.2.1 h, by rwa [min_eq_left h.le]⟩, fun hx => ?_⟩
    have := hx.2
    rwa [min_eq_left h.le] at this
  · have hi : i.1 = S.length := by omega
    rw [comp_app, comp_app, map_eq_zero_iff _ (bijective_cellModuleCongr_app _ Y).1]
    simp only [snocLast, comp_app, CatSubmodule.subtype_app]
    rw [map_eq_zero_iff _ ((isIso_iff_bijective _).mp inferInstance Y).1, mem_snocF]
    refine ⟨fun hx => ⟨fun _ => hx, ?_⟩, fun hx => hx.1 hi.le⟩
    rw [show min i.1 S.length = S.length by omega]
    exact S.mem_length _ _

theorem surjective_snocπ (i : Fin (S.length + 1)) (Y : C) :
    Function.Surjective ((S.snocπ ψ i).app Y) := by
  unfold snocπ
  split_ifs with h
  · refine (bijective_cellModuleCongr_app _ Y).2.comp ?_
    intro y
    obtain ⟨x, rfl⟩ := S.surjective_π ⟨i, h⟩ Y y
    refine ⟨⟨(cone.inr ψ).app Y x.1, fun _ => rfl, ?_⟩, rfl⟩
    rw [min_eq_left h]
    exact x.2
  · refine (bijective_cellModuleCongr_app _ Y).2.comp ?_
    intro y
    have hi : i.1 = S.length := by omega
    refine ⟨⟨cone.inlAddHom ψ Y
      ((shiftShiftIso (M := ulift.{w} (corner e)) m 1 (m + 1) rfl).hom.app Y y),
      fun h' => by omega, by
        change (0 : P.obj Y) ∈ _
        exact zero_mem _⟩, ?_⟩
    change (shiftShiftIso (M := ulift.{w} (corner e)) m 1 (m + 1) rfl).inv.app Y
      ((shiftShiftIso (M := ulift.{w} (corner e)) m 1 (m + 1) rfl).hom.app Y y) = y
    rw [← comp_app, Iso.hom_inv_id, id_app]

/-- The mapping cone of a morphism `ψ : (e · C(X, -))⟦m⟧ → P` into a finite-cell module is
finite-cell: its filtration is that of `P` (included by `cone.inr`) followed by the cell
`(e · C(X, -))⟦m + 1⟧`. -/
def snoc : FiniteCellFiltration.{w} (cone ψ) where
  length := S.length + 1
  F := S.snocF ψ
  le_succ j Y c hc := ⟨fun h => hc.1 (by omega),
    CatSubmodule.le_of_le_succ S.le_succ (min_le_min_right _ (Nat.le_succ j)) Y hc.2⟩
  eq_zero_of_mem_zero Y c hc := by
    refine cone.ext (hc.1 (Nat.zero_le _)) ?_
    have := hc.2
    rw [min_eq_left (Nat.zero_le _)] at this
    exact S.eq_zero_of_mem_zero Y _ this
  mem_length Y c := ⟨fun h => by omega, by
    rw [min_eq_right (by omega)]
    exact S.mem_length _ _⟩
  obj i := (S.snocCell (⟨X, e⟩, m + 1) i).1.1
  e i := (S.snocCell (⟨X, e⟩, m + 1) i).1.2
  deg i := (S.snocCell (⟨X, e⟩, m + 1) i).2
  π := S.snocπ ψ
  surjective_π := S.surjective_snocπ ψ
  π_eq_zero_iff := S.snocπ_eq_zero_iff ψ

theorem cells_snoc : (S.snoc ψ).cells = S.cells ++ [(⟨X, e⟩, m + 1)] := by
  simp only [cells, snoc]
  rw [List.ofFn_succ', List.concat_eq_append]
  congr 1
  · congr 1
    funext i
    simp [snocCell]
  · simp [snocCell]

end Snoc

/-- The zero dg module has the finite-cell filtration of length `0`. -/
def zero : FiniteCellFiltration.{w} (CatModule.zero.{max v w} (C := C)) where
  length := 0
  F _ := Hom.ker (𝟙 _)
  le_succ _ _ _ h := h
  eq_zero_of_mem_zero _ _ _ := Subsingleton.elim _ _
  mem_length _ _ := Subsingleton.elim _ _
  obj := Fin.elim0
  e := fun i => Fin.elim0 i
  deg := Fin.elim0
  π := fun i => Fin.elim0 i
  surjective_π := fun i => Fin.elim0 i
  π_eq_zero_iff := fun i => Fin.elim0 i

@[simp]
theorem cells_zero : (zero.{w} (C := C)).cells = [] :=
  rfl

end FiniteCellFiltration

namespace DerivedCategory

variable [HasDerivedCategory.{w', max v w} C]

/-- **Realization of cell towers**: an object of `D(C)` with a cell tower (cells
`Q (e · C(X, -))⟦n⟧`) is isomorphic to the image of a finite-cell module with the same list of
cells. The module is an iterated mapping cone, each cell attached by a morphism of dg modules
representing the attaching morphism of the tower (`DG.CatModule.FiniteCellFiltration.snoc`). -/
theorem exists_finiteCellFiltration_of_cellTower {ι : Type*} (φ : ι → Corner C)
    {l : List (ι × ℤ)} {Y : DerivedCategory.{w', max v w} C}
    (h : CellTower (fun i n => cell.{w'} (φ i).2 n) l Y) :
    ∃ (P : CatModule.{max v w} C) (S : FiniteCellFiltration.{w} P),
      S.cells = l.map (fun c => (φ c.1, c.2)) ∧ Nonempty (Y ≅ Q.obj P) := by
  induction h with
  | zero hY =>
    exact ⟨_, FiniteCellFiltration.zero, rfl,
      ⟨hY.iso (Functor.map_isZero _ (isZero_of_subsingleton _))⟩⟩
  | @ext l c T hT _ h₃ ih =>
    obtain ⟨P', S', hS', ⟨e'⟩⟩ := ih
    obtain ⟨e₃⟩ := h₃
    obtain ⟨i, n⟩ := c
    -- The attaching morphism `Q (e · C(X, -))⟦n - 1⟧ ⟶ Q P'`.
    let j : cell.{w'} (φ i).2 (n + -1) ≅ T.invRotate.obj₁ :=
      (cellShiftIso (φ i).2 n (-1)).symm ≪≫ (shiftFunctor _ (-1 : ℤ)).mapIso e₃.symm
    obtain ⟨ψ, hψ⟩ := exists_Q_map_eq (isKProjective_cellModule (φ i).2 (n + -1))
      (j.hom ≫ T.invRotate.mor₁ ≫ e'.hom)
    let T' := Q.mapTriangle.obj (cone.triangle ψ)
    have hT' : T' ∈ distTriang (DerivedCategory C) :=
      (mem_distTriang_iff _).mpr ⟨_, _, _, ⟨Iso.refl _⟩⟩
    obtain ⟨f, -, -⟩ := exists_iso_of_arrow_iso _ _ (inv_rot_of_distTriang T hT) hT'
      (Arrow.isoMk j.symm e' (by simp [T', hψ]))
    refine ⟨cone ψ, S'.snoc ψ, ?_, ⟨Triangle.π₃.mapIso f⟩⟩
    rw [FiniteCellFiltration.cells_snoc, hS', List.map_append]
    simp

end DerivedCategory

end CatModule

end DG

end
