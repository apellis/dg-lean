import DG.Compact.CellTower
import DG.K0.Compact
import DG.K0.Homological

/-!
# `K₀` of a triangulated category built from semisimple cells

Let `C` be a pretriangulated category and `cell : ι → ℤ → C` an ordered cell family
(`DG.IsOrderedCellFamily`: `(cell i n)⟦k⟧ ≅ cell i (n + k)`, no nonzero morphisms to cells of
smaller shift, Schur's lemma for cells of the same shift, cells nonzero). We call it
*semisimple* (`DG.IsSemisimpleCellFamily`) if moreover there are no nonzero morphisms to cells of
larger shift, so that `Hom(cell i n, cell j m) = 0` for `n ≠ m`. This is the situation of the
derived category of a semisimple ring in degree `0`, with cells the shifted simple modules.

For such a family, the Grothendieck group of a triangulated subcategory whose objects are
built from cells is free on the isomorphism classes of the cells `cell i 0`
(`DG.IsSemisimpleCellFamily.basis`). The coefficients of a class are computed by Euler
characteristics: for each `i`, the nonzero endomorphisms of `L = cell i 0` are invertible, so
`K = End(L)ᵐᵒᵖ` is a division ring and `Hom(L, -)` is a homological functor to `K`-vector spaces
(`DG.Homological`); its Euler characteristic
`χᵢ(X) = ∑ₙ (-1)ⁿ dim_K Hom(L, X⟦n⟧)` takes the value `(-1)ᵐ` on the cells `cell j m` with
`cell j 0 ≅ L` and `0` on the other cells (`DG.IsSemisimpleCellFamily.eulerChar_cell_of_iso`,
`DG.IsSemisimpleCellFamily.eulerChar_cell_of_isEmpty`).

## Main definitions and results

* `CategoryTheory.Pretriangulated.isHomological_preadditiveCoyonedaObj`: `Hom(P, -)`, with
  values in modules over `End(P)ᵐᵒᵖ`, is a homological functor.
* `DG.IsSemisimpleCellFamily.divisionRing i`: the division ring structure on
  `End(cell i 0)ᵐᵒᵖ`.
* `DG.IsSemisimpleCellFamily.eulerChar`, `DG.IsSemisimpleCellFamily.hasFiniteRank_of_cellTower`.
* `DG.CellTower.prop`, `DG.CellTower.mk_eq_sum_of_prop`: an object with a cell tower lies in any
  triangulated subcategory (closed under isomorphisms) containing the cells, and its class is
  the sum of the classes of its cells.
* `DG.IsSemisimpleCellFamily.linearIndependent`, `DG.IsSemisimpleCellFamily.basis`: `K₀` is
  free on the classes of a set of representatives of the cells `cell i 0` up to isomorphism.
-/

open CategoryTheory Limits Pretriangulated

universe w v u

namespace CategoryTheory.Pretriangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The functor `Hom(P, -) : C ⥤ ModuleCat (End P)ᵐᵒᵖ` is homological. -/
instance isHomological_preadditiveCoyonedaObj (P : C) :
    (preadditiveCoyonedaObj P).IsHomological where
  exact T hT := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro (x₂ : P ⟶ T.obj₂) (hx₂ : x₂ ≫ T.mor₂ = 0)
    obtain ⟨x₁, hx₁⟩ := T.coyoneda_exact₂ hT x₂ hx₂
    exact ⟨x₁, hx₁.symm⟩

end CategoryTheory.Pretriangulated

namespace DG

variable {C : Type u} [Category.{v} C] [HasShift C ℤ] [Preadditive C]

/-! ### Hom spaces out of an object -/

section HomSpace

/-- For an isomorphism `u : P ≅ Y`, `Hom(P, Y)` is free of rank one over `End(P)ᵐᵒᵖ`, with basis
`u`. -/
noncomputable def homLinearEquivOfIso {P Y : C} (u : P ≅ Y) :
    (End P)ᵐᵒᵖ ≃ₗ[(End P)ᵐᵒᵖ] (P ⟶ Y) :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ u.hom) ⟨fun a b h => by
    have h' : a.unop ≫ u.hom = b.unop ≫ u.hom := h
    exact MulOpposite.unop_injective (by simpa using h'), fun g =>
    ⟨MulOpposite.op (g ≫ u.inv), by
      change (g ≫ u.inv) ≫ u.hom = g
      simp⟩⟩

/-- Composition with an isomorphism `Y ≅ Y'` is an `End(P)ᵐᵒᵖ`-linear isomorphism
`Hom(P, Y) ≃ Hom(P, Y')`. -/
def homLinearEquivOfIsoRight (P : C) {Y Y' : C} (e : Y ≅ Y') :
    (P ⟶ Y) ≃ₗ[(End P)ᵐᵒᵖ] (P ⟶ Y') where
  toFun g := g ≫ e.hom
  invFun g := g ≫ e.inv
  map_add' _ _ := Preadditive.add_comp _ _ _ _ _ _
  map_smul' _ _ := Category.assoc _ _ _
  left_inv _ := by simp
  right_inv _ := by simp

/-- The dimension of `Hom(P, Y)` over `End(P)ᵐᵒᵖ`. -/
noncomputable def finrankHom (P Y : C) : ℕ :=
  Module.finrank (End P)ᵐᵒᵖ (P ⟶ Y)

omit [HasShift C ℤ] in
theorem finrankHom_eq_of_iso (P : C) {Y Y' : C} (e : Y ≅ Y') :
    finrankHom P Y = finrankHom P Y' :=
  (homLinearEquivOfIsoRight P e).finrank_eq

end HomSpace

/-! ### Cell towers in a triangulated subcategory -/

section CellTower

variable [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {ι : Type w} {cell : ι → ℤ → C} {P : ObjectProperty C} [P.IsTriangulated]
  [P.IsClosedUnderIsomorphisms] (hcell : ∀ i n, P (cell i n))
include hcell

/-- An object with a cell tower lies in every triangulated subcategory, closed under
isomorphisms, which contains the cells. -/
theorem CellTower.prop {l : List (ι × ℤ)} {X : C} (h : CellTower cell l X) : P X := by
  induction h with
  | zero hX => exact P.prop_of_isZero hX
  | ext T hT _ h₃ ih =>
    exact P.ext_of_isTriangulatedClosed₂ T hT ih (P.prop_of_iso h₃.some.symm (hcell _ _))

/-- Additivity of `K₀` over cell towers in a triangulated subcategory containing the cells. -/
theorem CellTower.mk_eq_sum_of_prop {l : List (ι × ℤ)} {X : C} (h : CellTower cell l X) :
    K0.mk (⟨X, h.prop hcell⟩ : P.FullSubcategory) =
      (l.map fun c : ι × ℤ => K0.mk (⟨cell c.1 c.2, hcell c.1 c.2⟩ :
        P.FullSubcategory)).sum := by
  induction h with
  | zero hX =>
    rw [List.map_nil, List.sum_nil]
    exact K0.mk_eq_zero_of_isZero ((IsZero.iff_id_eq_zero _).mpr (by
      ext
      exact hX.eq_of_src _ _))
  | ext R hR h₁ e ih =>
    rw [K0.mk_fullSubcategory_obj₂ (P := P) R hR (h₁.prop hcell) _
      (P.prop_of_iso e.some.symm (hcell _ _)), ih,
      List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    congr 1
    exact K0.mk_eq_of_iso_obj e.some

end CellTower

/-! ### Semisimple cell families -/

variable {ι : Type w} (cell : ι → ℤ → C)

/-- An ordered cell family is *semisimple* if there are also no nonzero morphisms from a cell to
a cell of larger shift; then `Hom(cell i n, cell j m) = 0` for `n ≠ m`. -/
structure IsSemisimpleCellFamily : Prop extends IsOrderedCellFamily cell where
  /-- There are no nonzero morphisms from a cell to a cell of larger shift. -/
  eq_zero_of_gt {i j : ι} {n m : ℤ} (h : n < m) (f : cell i n ⟶ cell j m) : f = 0

namespace IsSemisimpleCellFamily

variable {cell} (hc : IsSemisimpleCellFamily cell)
include hc

theorem eq_zero_of_ne {i j : ι} {n m : ℤ} (h : n ≠ m) (f : cell i n ⟶ cell j m) : f = 0 := by
  rcases lt_or_gt_of_ne h with h | h
  · exact hc.eq_zero_of_gt h f
  · exact hc.eq_zero_of_lt h f

/-- The nonzero endomorphisms of a cell are invertible, so `End(cell i 0)ᵐᵒᵖ` is a division
ring. -/
noncomputable abbrev divisionRing (i : ι) : DivisionRing (End (cell i 0))ᵐᵒᵖ :=
  haveI : Nontrivial (End (cell i 0)) :=
    ⟨⟨𝟙 _, 0, fun h => hc.not_isZero i 0 ((IsZero.iff_id_eq_zero _).mpr h)⟩⟩
  DivisionRing.ofIsUnitOrEqZero fun a => by
    by_cases ha : a = 0
    · exact Or.inr ha
    · refine Or.inl ?_
      have : IsIso a.unop := hc.isIso_of_ne_zero a.unop fun h =>
        ha (MulOpposite.unop_injective (by rw [h]; rfl))
      exact isUnit_op.mpr ((isUnit_iff_isIso a.unop).mpr this)

section Rank

variable (i : ι)

theorem finiteDimensional_hom_cell (j : ι) (m : ℤ) :
    letI := hc.divisionRing i
    FiniteDimensional (End (cell i 0))ᵐᵒᵖ (cell i 0 ⟶ cell j m) := by
  let := hc.divisionRing i
  by_cases h : ∃ u : cell i 0 ⟶ cell j m, u ≠ 0
  · obtain ⟨u, hu⟩ := h
    have hm : (0 : ℤ) = m := by
      by_contra hm
      exact hu (hc.eq_zero_of_ne hm u)
    subst hm
    have := hc.isIso_of_ne_zero u hu
    exact LinearEquiv.finiteDimensional (homLinearEquivOfIso (asIso u))
  · push Not at h
    have : Subsingleton (cell i 0 ⟶ cell j m) := ⟨fun a b => by rw [h a, h b]⟩
    infer_instance

theorem finrankHom_cell_of_iso {j : ι} (e : cell i 0 ≅ cell j 0) :
    finrankHom (cell i 0) (cell j 0) = 1 :=
  letI := hc.divisionRing i
  (homLinearEquivOfIso e).finrank_eq.symm.trans (Module.finrank_self _)

theorem finrankHom_cell_of_ne {j : ι} {m : ℤ} (h : m ≠ 0) :
    finrankHom (cell i 0) (cell j m) = 0 := by
  let := hc.divisionRing i
  have : Subsingleton (cell i 0 ⟶ cell j m) :=
    ⟨fun a b => by rw [hc.eq_zero_of_ne (Ne.symm h) a, hc.eq_zero_of_ne (Ne.symm h) b]⟩
  exact Module.finrank_zero_of_subsingleton

theorem finrankHom_cell_of_isEmpty {j : ι} (h : IsEmpty (cell i 0 ≅ cell j 0)) (m : ℤ) :
    finrankHom (cell i 0) (cell j m) = 0 := by
  let := hc.divisionRing i
  have : Subsingleton (cell i 0 ⟶ cell j m) := ⟨fun a b => by
    have H : ∀ u : cell i 0 ⟶ cell j m, u = 0 := fun u => by
      by_contra hu
      have hm : (0 : ℤ) = m := by
        by_contra hm
        exact hu (hc.eq_zero_of_ne hm u)
      subst hm
      have := hc.isIso_of_ne_zero u hu
      exact h.false (asIso u)
    rw [H a, H b]⟩
  exact Module.finrank_zero_of_subsingleton

end Rank

/-- The Euler characteristic `χᵢ(X) = ∑ₙ (-1)ⁿ dim Hom(cell i 0, X⟦n⟧)`, dimensions over the
division ring `End(cell i 0)ᵐᵒᵖ`. -/
noncomputable def eulerChar (i : ι) (X : C) : ℤ :=
  letI := hc.divisionRing i
  letI := Functor.ShiftSequence.tautological (preadditiveCoyonedaObj (cell i 0)) ℤ
  Homological.eulerChar (preadditiveCoyonedaObj (cell i 0)) X

/-- An object has *finite rank* with respect to `cell i 0`. -/
def HasFiniteRank (i : ι) (X : C) : Prop :=
  letI := hc.divisionRing i
  letI := Functor.ShiftSequence.tautological (preadditiveCoyonedaObj (cell i 0)) ℤ
  Homological.HasFiniteRank (preadditiveCoyonedaObj (cell i 0)) X

section Cells

variable (i : ι)

theorem finrankShift_eq (X : C) (n : ℤ) :
    letI := hc.divisionRing i
    letI := Functor.ShiftSequence.tautological (preadditiveCoyonedaObj (cell i 0)) ℤ
    Homological.finrankShift (preadditiveCoyonedaObj (cell i 0)) n X =
      finrankHom (cell i 0) (X⟦n⟧) :=
  rfl

theorem hasFiniteRank_cell (j : ι) (m : ℤ) : hc.HasFiniteRank i (cell j m) := by
  let := hc.divisionRing i
  let := Functor.ShiftSequence.tautological (preadditiveCoyonedaObj (cell i 0)) ℤ
  have e : ∀ n : ℤ, (cell j m)⟦n⟧ ≅ cell j (m + n) := fun n =>
    (hc.nonempty_shiftIso j m n).some
  refine ⟨fun n => ?_, ?_⟩
  · have := hc.finiteDimensional_hom_cell i j (m + n)
    exact LinearEquiv.finiteDimensional (homLinearEquivOfIsoRight (cell i 0) (e n)).symm
  · refine (Set.finite_singleton (-m)).subset fun n hn => ?_
    by_contra h
    apply hn
    change finrankHom (cell i 0) ((cell j m)⟦n⟧) = 0
    rw [finrankHom_eq_of_iso (cell i 0) (e n)]
    exact hc.finrankHom_cell_of_ne i fun h' => h (by simp only [Set.mem_singleton_iff]; omega)

theorem eulerChar_eq_of_iso {X Y : C} (e : X ≅ Y) : hc.eulerChar i X = hc.eulerChar i Y :=
  letI := hc.divisionRing i
  letI := Functor.ShiftSequence.tautological (preadditiveCoyonedaObj (cell i 0)) ℤ
  Homological.eulerChar_eq_of_iso _ e

/-- The Euler characteristic of a cell `cell j m` with `cell j 0 ≅ cell i 0` is `(-1)ᵐ`. -/
theorem eulerChar_cell_of_iso {j : ι} (e : cell i 0 ≅ cell j 0) (m : ℤ) :
    hc.eulerChar i (cell j m) = m.negOnePow := by
  let := hc.divisionRing i
  let := Functor.ShiftSequence.tautological (preadditiveCoyonedaObj (cell i 0)) ℤ
  have e' : ∀ n : ℤ, (cell j m)⟦n⟧ ≅ cell j (m + n) := fun n =>
    (hc.nonempty_shiftIso j m n).some
  have hr : ∀ n : ℤ, finrankHom (cell i 0) ((cell j m)⟦n⟧) = if n = -m then 1 else 0 :=
    fun n => by
      rw [finrankHom_eq_of_iso (cell i 0) (e' n)]
      split_ifs with h
      · subst h
        rw [add_neg_cancel]
        exact hc.finrankHom_cell_of_iso i e
      · exact hc.finrankHom_cell_of_ne i (by omega)
  change ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (finrankHom (cell i 0) ((cell j m)⟦n⟧) : ℤ) = _
  rw [finsum_eq_single _ (-m) fun n hn => by simp [hr n, hn], hr]
  simp [Int.negOnePow_neg]

/-- The Euler characteristic of a cell `cell j m` with `cell j 0 ≇ cell i 0` is `0`. -/
theorem eulerChar_cell_of_isEmpty {j : ι} (h : IsEmpty (cell i 0 ≅ cell j 0)) (m : ℤ) :
    hc.eulerChar i (cell j m) = 0 := by
  change ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (finrankHom (cell i 0) ((cell j m)⟦n⟧) : ℤ) = 0
  refine finsum_eq_zero_of_forall_eq_zero fun n => ?_
  rw [finrankHom_eq_of_iso (cell i 0) (hc.nonempty_shiftIso j m n).some,
    hc.finrankHom_cell_of_isEmpty i h]
  simp

end Cells

variable [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

theorem hasFiniteRank_of_cellTower (i : ι) {l : List (ι × ℤ)} {X : C}
    (h : CellTower cell l X) :
    hc.HasFiniteRank i X := by
  let := hc.divisionRing i
  let := Functor.ShiftSequence.tautological (preadditiveCoyonedaObj (cell i 0)) ℤ
  induction h with
  | zero hX => exact Homological.HasFiniteRank.of_isZero _ hX
  | ext T hT _ h₃ ih =>
    exact Homological.HasFiniteRank.obj₂ _ T hT ih
      (Homological.HasFiniteRank.of_iso _ h₃.some (hc.hasFiniteRank_cell i _ _))

/-! ### `K₀` of a subcategory built from cells -/

section K0

variable {P : ObjectProperty C} [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
  (hP : ∀ X, P X → ∃ l, CellTower cell l X)
include hP

/-- The Euler characteristic `χᵢ : K₀(P) →+ ℤ`, for a triangulated subcategory `P` whose objects
have cell towers. -/
noncomputable def eulerCharHom (i : ι) : K0 P.FullSubcategory →+ ℤ :=
  letI := hc.divisionRing i
  letI := Functor.ShiftSequence.tautological (preadditiveCoyonedaObj (cell i 0)) ℤ
  Homological.eulerCharHom (preadditiveCoyonedaObj (cell i 0)) P fun X hX =>
    hc.hasFiniteRank_of_cellTower i (hP X hX).choose_spec

omit [P.IsClosedUnderIsomorphisms] in
@[simp]
theorem eulerCharHom_mk (i : ι) (X : P.FullSubcategory) :
    hc.eulerCharHom hP i (K0.mk X) = hc.eulerChar i X.obj :=
  letI := hc.divisionRing i
  letI := Functor.ShiftSequence.tautological (preadditiveCoyonedaObj (cell i 0)) ℤ
  Homological.eulerCharHom_mk _ _ _ X

variable (hcell : ∀ i n, P (cell i n))

omit hP [P.IsClosedUnderIsomorphisms] in
/-- `[cell j n] = (-1)ⁿ [cell j 0]` in `K₀(P)`. -/
theorem mk_cell (j : ι) (n : ℤ) :
    K0.mk (⟨cell j n, hcell j n⟩ : P.FullSubcategory) =
      n.negOnePow • K0.mk (⟨cell j 0, hcell j 0⟩ : P.FullSubcategory) := by
  rw [← K0.mk_shift]
  exact K0.mk_eq_of_iso_obj (eqToIso (by rw [zero_add]) ≪≫
    (hc.nonempty_shiftIso j 0 n).some.symm ≪≫
    ((P.ι.commShiftIso n).app ⟨cell j 0, hcell j 0⟩).symm)

omit hc hP [P.IsClosedUnderIsomorphisms] in
theorem mk_cell_eq_of_iso {i j : ι} (e : cell i 0 ≅ cell j 0) :
    K0.mk (⟨cell i 0, hcell i 0⟩ : P.FullSubcategory) = K0.mk ⟨cell j 0, hcell j 0⟩ :=
  K0.mk_eq_of_iso_obj e

variable {κ : Type*} (s : κ → ι)

omit [P.IsClosedUnderIsomorphisms] in
/-- The classes of pairwise non-isomorphic cells `cell (s a) 0` are linearly independent in
`K₀(P)`. -/
theorem linearIndependent (hs : ∀ a b, Nonempty (cell (s a) 0 ≅ cell (s b) 0) → a = b) :
    LinearIndependent ℤ fun a => K0.mk (⟨cell (s a) 0, hcell _ 0⟩ : P.FullSubcategory) := by
  classical
  rw [linearIndependent_iff']
  intro S g hg a ha
  have h := congrArg (hc.eulerCharHom hP (s a)) hg
  rw [map_sum, map_zero, Finset.sum_eq_single a] at h
  · rw [map_zsmul, eulerCharHom_mk, hc.eulerChar_cell_of_iso _ (Iso.refl _)] at h
    simpa using h
  · intro b _ hb
    rw [map_zsmul, eulerCharHom_mk, hc.eulerChar_cell_of_isEmpty _
      ⟨fun e => hb (hs a b ⟨e⟩).symm⟩, smul_zero]
  · intro h'
    exact absurd ha h'

/-- If every cell `cell i 0` is isomorphic to one of the `cell (s a) 0`, the classes
`[cell (s a) 0]` span `K₀(P)`. -/
theorem span_eq_top (hs : ∀ i, ∃ a, Nonempty (cell i 0 ≅ cell (s a) 0)) :
    Submodule.span ℤ (Set.range fun a =>
      K0.mk (⟨cell (s a) 0, hcell _ 0⟩ : P.FullSubcategory)) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨X, rfl⟩ := K0.exists_mk_eq x
  obtain ⟨l, hl⟩ := hP X.obj X.property
  change K0.mk (⟨X.obj, hl.prop hcell⟩ : P.FullSubcategory) ∈ _
  rw [hl.mk_eq_sum_of_prop hcell]
  refine list_sum_mem fun y hy => ?_
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hy
  obtain ⟨a, ⟨e⟩⟩ := hs c.1
  rw [hc.mk_cell hcell, mk_cell_eq_of_iso hcell e, Units.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/-- **`K₀` is free on the isomorphism classes of cells**: for a triangulated subcategory `P`
(closed under isomorphisms) which contains the cells and whose objects have cell towers, and a
family `s` of representatives of the cells `cell i 0` up to isomorphism, the classes
`[cell (s a) 0]` form a basis of `K₀(P)`. -/
noncomputable def basis (hs : ∀ a b, Nonempty (cell (s a) 0 ≅ cell (s b) 0) → a = b)
    (hs' : ∀ i, ∃ a, Nonempty (cell i 0 ≅ cell (s a) 0)) :
    Module.Basis κ ℤ (K0 P.FullSubcategory) :=
  Module.Basis.mk (hc.linearIndependent hP hcell s hs) (hc.span_eq_top hP hcell s hs').ge

@[simp]
theorem basis_apply (hs : ∀ a b, Nonempty (cell (s a) 0 ≅ cell (s b) 0) → a = b)
    (hs' : ∀ i, ∃ a, Nonempty (cell i 0 ≅ cell (s a) 0)) (a : κ) :
    hc.basis hP hcell s hs hs' a = K0.mk (⟨cell (s a) 0, hcell _ 0⟩ : P.FullSubcategory) :=
  Module.Basis.mk_apply _ _ _

end K0

end IsSemisimpleCellFamily

end DG
