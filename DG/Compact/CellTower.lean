import DG.Compact.Thick
import Mathlib.CategoryTheory.Triangulated.Triangulated

/-!
# Cell towers in triangulated categories

Let `C` be a pretriangulated category and `cell : ι → ℤ → C` a family of objects ("cells"),
where `cell i n` should be thought of as the `n`-th shift of a basic object indexed by `i`.
A *cell tower* of an object `X` with cells `[(i₁, n₁), …, (iₖ, nₖ)]` (`DG.CellTower`) is a
sequence of distinguished triangles `Xⱼ₋₁ → Xⱼ → cell iⱼ nⱼ → Xⱼ₋₁⟦1⟧` with `X₀ = 0` and
`Xₖ ≅ X`: the triangulated shadow of a finite filtration with subquotients `cell iⱼ nⱼ`. It is
*ordered* if `n₁ ≥ n₂ ≥ ⋯ ≥ nₖ` (`DG.HasOrderedCellTower`).

The main result is an abstract form of the core of Schnürer's description of the perfect
derived category of a positive dg algebra [Sch, Thm. 13 and §6]. Suppose the cells satisfy
(`DG.IsOrderedCellFamily`):

* `(cell i n)⟦k⟧ ≅ cell i (n + k)`;
* `Hom(cell i n, cell j m) = 0` for `m < n`;
* every nonzero morphism `cell i n ⟶ cell j n` is an isomorphism (a Schur lemma);
* no cell is zero.

Then, in a triangulated category, the objects with an ordered cell tower form a thick
subcategory (`DG.IsOrderedCellFamily.isThick`): they are closed under shifts, extensions and
direct summands. In particular the thick closure of any family of objects with ordered cell
towers consists of objects with ordered cell towers.

## Main results

* `DG.IsOrderedCellFamily.exists_cone`: the cone of a morphism from a cell to an object with an
  ordered cell tower has an ordered cell tower, obtained either by inserting the shifted cell
  or by cancelling one cell. This is [Sch, Thm. 13, the case `λ(X̄) = 1`], argued with
  octahedra instead of explicit filtrations.
* `DG.IsOrderedCellFamily.hasOrderedCellTower_obj₃`: closure under cones [Sch, Thm. 13].
* `DG.IsOrderedCellFamily.hasOrderedCellTower_of_retract`: closure under direct summands. The
  argument peels off the first cell: a nonzero morphism from the first cell into the ambient
  object is either fixed or killed by the idempotent defining the summand (after splitting it
  into two parts), and in both cases the summand, or the cone of the peeled cell into it, is a
  summand of an object with a shorter ordered cell tower. This replaces Schnürer's use of the
  bounded t-structure [Sch, Thm. 16] and of homotopically minimal modules [Sch, Prop. 31,
  Cor. 32].
* `DG.IsOrderedCellFamily.isThick`, `DG.IsOrderedCellFamily.thickClosure_le`.

## References

* [Sch] O. M. Schnürer, *Perfect derived categories of positively graded DG algebras*,
  Appl. Categ. Structures 19 (2011), 757–782; arXiv:0809.4782v2.
-/

universe w v u

namespace DG

open CategoryTheory Limits Pretriangulated ZeroObject

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {ι : Type w} (cell : ι → ℤ → C)

/-- A cell tower of `X` with cells `l = [(i₁, n₁), …, (iₖ, nₖ)]`: `X` is zero if `l = []`, and
otherwise sits in a distinguished triangle `X' → X → cell iₖ nₖ → X'⟦1⟧` where `X'` has a cell
tower with cells `[(i₁, n₁), …, (iₖ₋₁, nₖ₋₁)]`. -/
inductive CellTower : List (ι × ℤ) → C → Prop
  /-- A zero object has the empty cell tower. -/
  | zero {X : C} : IsZero X → CellTower [] X
  /-- Extension by one cell at the end. -/
  | ext {l : List (ι × ℤ)} {c : ι × ℤ} (T : Triangle C) : T ∈ distTriang C →
      CellTower l T.obj₁ → Nonempty (T.obj₃ ≅ cell c.1 c.2) → CellTower (l ++ [c]) T.obj₂

/-- A list of cells is *ordered* if its shifts are non-increasing: `n₁ ≥ n₂ ≥ ⋯`. -/
def CellsOrdered (l : List (ι × ℤ)) : Prop :=
  l.Pairwise fun c c' => c'.2 ≤ c.2

/-- An object has an *ordered cell tower* if it has a cell tower with non-increasing shifts. -/
def HasOrderedCellTower (X : C) : Prop :=
  ∃ l : List (ι × ℤ), CellsOrdered l ∧ CellTower cell l X

variable {cell}

theorem cellsOrdered_append {l l' : List (ι × ℤ)} :
    CellsOrdered (l ++ l') ↔
      CellsOrdered l ∧ CellsOrdered l' ∧ ∀ a ∈ l, ∀ b ∈ l', b.2 ≤ a.2 :=
  List.pairwise_append

theorem cellsOrdered_singleton (c : ι × ℤ) : CellsOrdered [c] :=
  List.pairwise_singleton _ _

theorem cellsOrdered_nil : CellsOrdered ([] : List (ι × ℤ)) :=
  List.Pairwise.nil

namespace CellTower

theorem of_iso {l : List (ι × ℤ)} {X Y : C} (h : CellTower cell l X) (e : X ≅ Y) :
    CellTower cell l Y := by
  cases h with
  | zero hX => exact .zero (hX.of_iso e.symm)
  | ext T hT h₁ h₃ =>
    refine .ext (Triangle.mk (T.mor₁ ≫ e.hom) (e.inv ≫ T.mor₂) T.mor₃) ?_ h₁ h₃
    exact isomorphic_distinguished T hT _
      (Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _) (by simp) (by simp) (by simp))

theorem isZero {X : C} (h : CellTower cell [] X) : IsZero X := by
  generalize hl : ([] : List (ι × ℤ)) = l at h
  cases h with
  | zero hX => exact hX
  | ext T _ _ _ => simp at hl

/-- A cell has the cell tower consisting of itself. -/
theorem single (i : ι) (n : ℤ) : CellTower cell [(i, n)] (cell i n) := by
  simpa using CellTower.ext (c := (i, n)) (Triangle.mk (0 : 0 ⟶ cell i n) (𝟙 _) 0)
    (contractible_distinguished₁ _) (.zero (isZero_zero C)) ⟨Iso.refl _⟩

/-- Shifting a cell tower. -/
theorem shift (hs : ∀ i n k, Nonempty ((cell i n)⟦k⟧ ≅ cell i (n + k)))
    {l : List (ι × ℤ)} {X : C} (h : CellTower cell l X) (k : ℤ) :
    CellTower cell (l.map fun c => (c.1, c.2 + k)) (X⟦k⟧) := by
  induction h with
  | zero hX => exact .zero (Functor.map_isZero _ hX)
  | ext T hT _ h₃ ih =>
    rw [List.map_append, List.map_singleton]
    exact .ext ((Triangle.shiftFunctor C k).obj T) (Triangle.shift_distinguished T hT k) ih
      ⟨(shiftFunctor C k).mapIso h₃.some ≪≫ (hs _ _ _).some⟩

/-- An object with a cell tower belongs to every thick subcategory containing its cells. -/
theorem mem_of_isThick {P : ObjectProperty C} (hP : IsThick P) {l : List (ι × ℤ)} {X : C}
    (h : CellTower cell l X) (hl : ∀ c ∈ l, P (cell c.1 c.2)) : P X := by
  induction h with
  | zero hX => exact hP.of_isZero hX
  | ext T hT _ h₃ ih =>
    exact hP.ext₂ T hT (ih fun c hc => hl c (by simp [hc]))
      (hP.of_iso h₃.some (hl _ (by simp)))

end CellTower

namespace HasOrderedCellTower

theorem of_iso {X Y : C} (h : HasOrderedCellTower cell X) (e : X ≅ Y) :
    HasOrderedCellTower cell Y :=
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2.of_iso e⟩

theorem of_isZero {X : C} (hX : IsZero X) : HasOrderedCellTower cell X :=
  ⟨[], cellsOrdered_nil, .zero hX⟩

theorem of_cell (i : ι) (n : ℤ) : HasOrderedCellTower cell (cell i n) :=
  ⟨_, cellsOrdered_singleton _, .single i n⟩

theorem shift (hs : ∀ i n k, Nonempty ((cell i n)⟦k⟧ ≅ cell i (n + k))) {X : C}
    (h : HasOrderedCellTower cell X) (k : ℤ) : HasOrderedCellTower cell (X⟦k⟧) := by
  obtain ⟨l, hl, h⟩ := h
  refine ⟨_, ?_, h.shift hs k⟩
  unfold CellsOrdered at hl ⊢
  rw [List.pairwise_map]
  exact hl.imp fun h => by simpa using h

end HasOrderedCellTower

variable (cell) in
/-- The hypotheses on a family of cells under which the objects with an ordered cell tower form
a thick subcategory (`DG.IsOrderedCellFamily.isThick`). -/
structure IsOrderedCellFamily : Prop where
  /-- Shifting a cell shifts its index. -/
  nonempty_shiftIso (i : ι) (n k : ℤ) : Nonempty ((cell i n)⟦k⟧ ≅ cell i (n + k))
  /-- There are no nonzero morphisms from a cell to a cell of smaller shift. -/
  eq_zero_of_lt {i j : ι} {n m : ℤ} (h : m < n) (f : cell i n ⟶ cell j m) : f = 0
  /-- Schur's lemma: a nonzero morphism between cells of the same shift is an isomorphism. -/
  isIso_of_ne_zero {i j : ι} {n : ℤ} (f : cell i n ⟶ cell j n) (hf : f ≠ 0) : IsIso f
  /-- Cells are nonzero. -/
  not_isZero (i : ι) (n : ℤ) : ¬ IsZero (cell i n)

namespace IsOrderedCellFamily

variable (hc : IsOrderedCellFamily cell)
include hc

/-- Two ways to compute a cone of a morphism from a cell `cell i n` to an object `X` with an
ordered cell tower `l` ([Sch, Thm. 13, the case `λ(X̄) = 1`]): the cone has an ordered cell
tower `L` whose cells are cells of `l` or `(i, n + 1)`; if the morphism is nonzero and all
shifts of `l` are at most `n`, then `L` has one cell less than `l` (a cell is cancelled). -/
theorem exists_cone [IsTriangulated C] {l : List (ι × ℤ)} {X : C} (h : CellTower cell l X)
    (i : ι) (n : ℤ) : CellsOrdered l → ∀ φ : cell i n ⟶ X,
    ∃ (Z : C) (v : X ⟶ Z) (w : Z ⟶ (cell i n)⟦(1 : ℤ)⟧), Triangle.mk φ v w ∈ distTriang C ∧
      ∃ L : List (ι × ℤ), CellTower cell L Z ∧ CellsOrdered L ∧
        (∀ c ∈ L, c ∈ l ∨ c = (i, n + 1)) ∧
        (φ ≠ 0 → (∀ c ∈ l, c.2 ≤ n) → L.length + 1 = l.length) := by
  induction h with
  | @zero X hX =>
    intro _ φ
    obtain ⟨Z, v, w, hT⟩ := distinguished_cocone_triangle φ
    refine ⟨Z, v, w, hT, [(i, n + 1)], ?_, cellsOrdered_singleton _, by simp,
      fun hφ _ => (hφ (hX.eq_of_tgt _ _)).elim⟩
    simpa using CellTower.ext (c := (i, n + 1)) _ (rot_of_distTriang _ hT) (.zero hX)
      (hc.nonempty_shiftIso i n 1)
  | @ext l c T hT h₁ h₃ ih =>
    intro hl φ
    obtain ⟨e⟩ := h₃
    obtain ⟨hl', -, hlc⟩ := cellsOrdered_append.mp hl
    replace hlc : ∀ a ∈ l, c.2 ≤ a.2 := fun a ha => hlc a ha c (by simp)
    obtain ⟨Z, v, w, hTφ⟩ := distinguished_cocone_triangle φ
    by_cases hn : n < c.2
    · -- All cells have shift `> n`: insert the cell `(i, n + 1)` at the end.
      refine ⟨Z, v, w, hTφ, l ++ [c] ++ [(i, n + 1)],
        .ext _ (rot_of_distTriang _ hTφ) (.ext T hT h₁ ⟨e⟩) (hc.nonempty_shiftIso i n 1),
        ?_, fun a ha => ?_, fun _ hall => absurd (hall c (by simp)) (by omega)⟩
      swap
      · simp only [List.mem_append, List.mem_singleton] at ha ⊢
        tauto
      refine cellsOrdered_append.mpr ⟨hl, cellsOrdered_singleton _, fun a ha b hb => ?_⟩
      obtain rfl : b = (i, n + 1) := by simpa using hb
      rcases List.mem_append.mp ha with ha | ha
      · have := hlc a ha
        dsimp
        omega
      · obtain rfl : a = c := by simpa using ha
        dsimp
        omega
    rw [not_lt] at hn
    by_cases hg : c.2 = n ∧ φ ≫ T.mor₂ ≫ e.hom ≠ 0
    · -- The composition with the last cell is an isomorphism: cancel the last cell.
      obtain ⟨h2, hg⟩ := hg
      obtain ⟨c₁, c₂⟩ := c
      dsimp at h2 e hlc hg
      subst h2
      have hiso : IsIso (φ ≫ T.mor₂) := by
        have := hc.isIso_of_ne_zero _ hg
        rw [← Category.assoc] at this
        exact IsIso.of_isIso_comp_right _ e.hom
      obtain ⟨Z₁₃, v₁₃, w₁₃, h₁₃⟩ := distinguished_cocone_triangle (φ ≫ T.mor₂)
      have hZ : IsZero Z₁₃ := (Triangle.isZero₃_iff_isIso₁ _ h₁₃).2 hiso
      let o := Triangulated.someOctahedron rfl hTφ (rot_of_distTriang T hT) h₁₃
      have h3 : IsIso ((-(T.mor₁⟦(1 : ℤ)⟧')) ≫ v⟦(1 : ℤ)⟧') :=
        (Triangle.isZero₂_iff_isIso₃ _ o.mem).1 hZ
      let e' : T.obj₁ ≅ Z :=
        (shiftFunctor C (1 : ℤ)).preimageIso (asIso ((-(T.mor₁⟦(1 : ℤ)⟧')) ≫ v⟦(1 : ℤ)⟧'))
      refine ⟨Z, v, w, hTφ, l, h₁.of_iso e', hl', fun a ha => Or.inl (by simp [ha]),
        fun _ _ => by simp⟩
    · -- The composition with the last cell vanishes: recurse into `T.obj₁`.
      have hg0 : φ ≫ T.mor₂ = 0 := by
        rw [← cancel_mono e.hom, zero_comp, Category.assoc]
        by_cases h2 : c.2 = n
        · by_contra hne
          exact hg ⟨h2, hne⟩
        · exact hc.eq_zero_of_lt (lt_of_le_of_ne hn h2) _
      obtain ⟨φ', hφ'⟩ := Triangle.coyoneda_exact₂ T hT φ hg0
      obtain ⟨Z', v', w', hT', L', hL', hLo, hLm, hLl⟩ := ih hl' φ'
      let o := Triangulated.someOctahedron hφ'.symm hT' hT hTφ
      refine ⟨Z, v, w, hTφ, L' ++ [c], .ext _ o.mem hL' ⟨e⟩, ?_, ?_, ?_⟩
      · refine cellsOrdered_append.mpr ⟨hLo, cellsOrdered_singleton _, fun a ha b hb => ?_⟩
        obtain rfl : b = c := by simpa using hb
        rcases hLm a ha with ha | rfl
        · exact hlc a ha
        · dsimp
          omega
      · intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · rcases hLm a ha with ha | ha
          · exact Or.inl (by simp [ha])
          · exact Or.inr ha
        · exact Or.inl (by simp_all)
      · intro hφ hall
        have hφ'0 : φ' ≠ 0 := by
          rintro rfl
          exact hφ (by rw [hφ', zero_comp])
        have := hLl hφ'0 fun a ha => hall a (by simp [ha])
        simp [this]

/-- The objects with an ordered cell tower are closed under cones ([Sch, Thm. 13]): for a
morphism `f : X ⟶ Y` between such objects, some (hence every) cone of `f` has an ordered cell
tower. -/
theorem exists_cone_of_hasOrderedCellTower [IsTriangulated C] {l : List (ι × ℤ)} {X : C}
    (h : CellTower cell l X) : ∀ {Y : C} (f : X ⟶ Y), HasOrderedCellTower cell Y →
    ∃ (Z : C) (v : Y ⟶ Z) (w : Z ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f v w ∈ distTriang C ∧
      HasOrderedCellTower cell Z := by
  induction h with
  | @zero X hX =>
    intro Y f hY
    obtain ⟨Z, v, w, hT⟩ := distinguished_cocone_triangle f
    have : IsIso v := (Triangle.isZero₁_iff_isIso₂ _ hT).1 hX
    exact ⟨Z, v, w, hT, hY.of_iso (asIso v)⟩
  | @ext l c T hT h₁ h₃ ih =>
    intro Y f hY
    obtain ⟨e⟩ := h₃
    obtain ⟨Z'', v'', w'', h'', hZ''⟩ := ih (T.mor₁ ≫ f) hY
    obtain ⟨Z, v, w, hTf⟩ := distinguished_cocone_triangle f
    let o := Triangulated.someOctahedron rfl hT hTf h''
    obtain ⟨L, hLo, hL⟩ := hZ''
    obtain ⟨Z', v', w', hT', L', hL', hLo', -, -⟩ :=
      hc.exists_cone hL c.1 c.2 hLo (e.inv ≫ o.m₁)
    obtain ⟨e', -, -⟩ := exists_iso_of_arrow_iso _ _ o.mem hT'
      (Arrow.isoMk e (Iso.refl _) (by simp))
    exact ⟨Z, v, w, hTf, L', hLo', hL'.of_iso (Triangle.π₃.mapIso e').symm⟩

/-- The objects with an ordered cell tower are closed under shifts. -/
theorem hasOrderedCellTower_shift {X : C} (h : HasOrderedCellTower cell X) (k : ℤ) :
    HasOrderedCellTower cell (X⟦k⟧) :=
  h.shift hc.nonempty_shiftIso k

/-- Two-out-of-three for cones. -/
theorem hasOrderedCellTower_obj₃ [IsTriangulated C] (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : HasOrderedCellTower cell T.obj₁) (h₂ : HasOrderedCellTower cell T.obj₂) :
    HasOrderedCellTower cell T.obj₃ := by
  obtain ⟨l, -, hl⟩ := h₁
  obtain ⟨Z, v, w, hT', hZ⟩ := hc.exists_cone_of_hasOrderedCellTower hl T.mor₁ h₂
  obtain ⟨e, -, -⟩ := exists_iso_of_arrow_iso _ _ hT' hT (Iso.refl _)
  exact hZ.of_iso (Triangle.π₃.mapIso e)

/-- Two-out-of-three for extensions. -/
theorem hasOrderedCellTower_obj₂ [IsTriangulated C] (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : HasOrderedCellTower cell T.obj₁) (h₃ : HasOrderedCellTower cell T.obj₃) :
    HasOrderedCellTower cell T.obj₂ :=
  hc.hasOrderedCellTower_obj₃ _ (inv_rot_of_distTriang T hT) (hc.hasOrderedCellTower_shift h₃ _)
    h₁

/-- If the first cell of an ordered cell tower of `X` is `(i, n)`, there is a nonzero morphism
`cell i n ⟶ X` (the inclusion of the first step). -/
theorem exists_ne_zero {l : List (ι × ℤ)} {X : C} (h : CellTower cell l X) :
    ∀ {i : ι} {n : ℤ} {rest : List (ι × ℤ)}, l = (i, n) :: rest → CellsOrdered l →
      ∃ z : cell i n ⟶ X, z ≠ 0 := by
  induction h with
  | zero _ => intro _ _ _ h; simp at h
  | @ext l c T hT h₁ h₃ ih =>
    intro i n rest hl ho
    obtain ⟨e⟩ := h₃
    cases l with
    | nil =>
      obtain ⟨rfl, -⟩ : c = (i, n) ∧ rest = [] := by simpa using hl
      have : IsIso T.mor₂ := (Triangle.isZero₁_iff_isIso₂ _ hT).1 h₁.isZero
      refine ⟨e.inv ≫ inv T.mor₂, fun hz => hc.not_isZero i n ?_⟩
      rw [IsZero.iff_id_eq_zero]
      calc 𝟙 (cell i n) = (e.inv ≫ inv T.mor₂) ≫ T.mor₂ ≫ e.hom := by simp
        _ = 0 := by rw [hz, zero_comp]
    | cons a l =>
      obtain ⟨rfl, -⟩ : a = (i, n) ∧ l ++ [c] = rest := by simpa using hl
      have hcn : c.2 ≤ n := by
        have := (List.pairwise_cons.mp ho).1 c (by simp)
        exact this
      obtain ⟨z', hz'⟩ := ih rfl (cellsOrdered_append.mp ho).1
      refine ⟨z' ≫ T.mor₁, fun hz => hz' ?_⟩
      obtain ⟨g, rfl⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang T hT) z' hz
      have e₁ : T.obj₃⟦(-1 : ℤ)⟧ ≅ cell c.1 (c.2 + -1) :=
        (shiftFunctor C (-1 : ℤ)).mapIso e ≪≫ (hc.nonempty_shiftIso _ _ _).some
      have : g ≫ e₁.hom = 0 := hc.eq_zero_of_lt (by omega) _
      have hg : g = 0 := by
        have h' := (cancel_mono e₁.hom).1
          (show (g : cell i n ⟶ (shiftFunctor C (-1 : ℤ)).obj T.obj₃) ≫ e₁.hom = 0 ≫ e₁.hom by
            rw [zero_comp]; exact this)
        exact h'
      rw [hg]
      exact Limits.zero_comp

/-- The objects with an ordered cell tower are closed under direct summands. The proof is by
induction on the length of an ordered cell tower of the ambient object, peeling off its first
cell. -/
theorem hasOrderedCellTower_of_retract [IsTriangulated C] (k : ℕ) :
    ∀ {l : List (ι × ℤ)} {X : C}, CellTower cell l X → CellsOrdered l → l.length = k →
      ∀ {Y : C}, Retract Y X → HasOrderedCellTower cell Y := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro l X h ho hk Y r
  cases l with
  | nil =>
    refine HasOrderedCellTower.of_isZero ?_
    rw [IsZero.iff_id_eq_zero, ← r.retract, h.isZero.eq_of_tgt r.i 0, zero_comp]
  | cons a rest =>
    obtain ⟨i, n⟩ := a
    have hall : ∀ c ∈ (i, n) :: rest, c.2 ≤ n := by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact le_rfl
      · exact (List.pairwise_cons.mp ho).1 c hc
    obtain ⟨z₀, hz₀⟩ := hc.exists_ne_zero h rfl ho
    let E : X ⟶ X := r.r ≫ r.i
    have hE : E ≫ E = E := by
      simp only [E, Category.assoc, r.retract_assoc]
    -- A peeled cell `z` gives a cone with a shorter ordered cell tower.
    have key : ∀ z : cell i n ⟶ X, z ≠ 0 → ∃ (Z : C) (v : X ⟶ Z) (w : Z ⟶ (cell i n)⟦(1 : ℤ)⟧),
        Triangle.mk z v w ∈ distTriang C ∧ ∀ {Y' : C}, Retract Y' Z →
          HasOrderedCellTower cell Y' := by
      intro z hz
      obtain ⟨Z, v, w, hT, L, hL, hLo, -, hLl⟩ := hc.exists_cone h i n ho z
      refine ⟨Z, v, w, hT, fun r' => ih L.length ?_ hL hLo rfl r'⟩
      have := hLl hz hall
      simp only [List.length_cons] at this hk
      omega
    by_cases h₁ : z₀ ≫ E = 0
    · -- `z₀` is killed by the idempotent: `Y` is a summand of the cone of `z₀`.
      obtain ⟨Z, v, w, hT, hZ⟩ := key z₀ hz₀
      have hzr : z₀ ≫ r.r = 0 :=
        calc z₀ ≫ r.r = (z₀ ≫ E) ≫ r.r := by simp [E, r.retract]
          _ = 0 := by rw [h₁, zero_comp]
      obtain ⟨r', hr'⟩ := Triangle.yoneda_exact₂ _ hT r.r hzr
      exact hZ ⟨r.i ≫ v, r', by rw [Category.assoc, ← r.retract, hr']; rfl⟩
    · -- `z = z₀ ≫ E` is fixed by the idempotent: the cone of `z ≫ r` is a summand of the cone
      -- of `z`, and `Y` is an extension of it by the cell.
      set z := z₀ ≫ E with hzdef
      have hzE : z ≫ E = z := by rw [hzdef, Category.assoc, hE]
      obtain ⟨Z, v, w, hT, hZ⟩ := key z h₁
      obtain ⟨Z', v', w', hT'⟩ := distinguished_cocone_triangle (z ≫ r.r)
      obtain ⟨α, hα₁, hα₂⟩ := complete_distinguished_triangle_morphism _ _ hT' hT (𝟙 _) r.i
        (by simpa [E] using hzE)
      obtain ⟨β, hβ₁, hβ₂⟩ := complete_distinguished_triangle_morphism _ _ hT hT' (𝟙 _) r.r
        (by simp)
      let φ : Triangle.mk (z ≫ r.r) v' w' ⟶ Triangle.mk (z ≫ r.r) v' w' :=
        { hom₁ := 𝟙 _
          hom₂ := r.i ≫ r.r
          hom₃ := α ≫ β
          comm₁ := by simp
          comm₂ := by
            dsimp at hα₁ hβ₁ ⊢
            rw [reassoc_of% hα₁, hβ₁, Category.assoc]
          comm₃ := by
            have h1 : w' = α ≫ w := by simpa using hα₂
            have h2 : w = β ≫ w' := by simpa using hβ₂
            dsimp
            rw [Category.assoc, ← h2, ← h1]
            simp }
      have : IsIso φ.hom₃ := isIso₃_of_isIso₁₂ φ hT' hT' (by dsimp [φ]; infer_instance)
        (by dsimp [φ]; rw [r.retract]; infer_instance)
      have hZ' : HasOrderedCellTower cell Z' :=
        have : IsIso (α ≫ β) := this
        hZ ⟨α, β ≫ inv (α ≫ β), by rw [← Category.assoc, IsIso.hom_inv_id]⟩
      exact hc.hasOrderedCellTower_obj₂ _ hT' (HasOrderedCellTower.of_cell i n) hZ'

/-- **Thickness** of the objects with an ordered cell tower (abstract form of [Sch, Thm. 1]):
for an ordered cell family in a triangulated category, the objects with an ordered cell tower
form a thick subcategory. -/
theorem isThick [IsTriangulated C] : IsThick (HasOrderedCellTower cell) where
  zero := .of_isZero (isZero_zero C)
  shift X n h := hc.hasOrderedCellTower_shift h n
  ext₂ T hT h₁ h₃ := hc.hasOrderedCellTower_obj₂ T hT h₁ h₃
  retract r h := by
    obtain ⟨l, hlo, hl⟩ := h
    exact hc.hasOrderedCellTower_of_retract _ hl hlo rfl r

/-- The thick closure of a family of objects with ordered cell towers consists of objects with
ordered cell towers. -/
theorem thickClosure_le [IsTriangulated C] {S : ObjectProperty C}
    (hS : S ≤ HasOrderedCellTower cell) : ThickClosure S ≤ HasOrderedCellTower cell :=
  DG.thickClosure_le hc.isThick hS

end IsOrderedCellFamily

end DG
