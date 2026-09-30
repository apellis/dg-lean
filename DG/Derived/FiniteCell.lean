import DG.Compact.CellTower
import DG.Derived.GradedSplitting
import DG.Derived.KProjective
import DG.Homotopy.SemiFree

/-!
# Finite-cell dg modules in the derived category

Let `A` be a dg ring. A finite-cell dg module (`DG.FiniteCellFiltration`) has a finite filtration
whose subquotients are shifts `(A eᵢ)⟦nᵢ⟧` of the dg modules `A eᵢ` of degree-`0` idempotent
cocycles. This file relates finite-cell modules to cell towers (`DG.CellTower`) in `D(A)`, with
cells `Q (A e)⟦n⟧`:

* `DG.FiniteCellFiltration.cells`: the list `[(e₁, n₁), …, (eₖ, nₖ)]` of cells of a filtration.
* `DG.FiniteCellFiltration.cellTower`: the image in `D(A)` of a finite-cell module has the cell
  tower given by its filtration (each step of the filtration is a graded-split extension, hence a
  distinguished triangle, `DG.GradedSplitting.exists_distinguished`).
* `DG.FiniteCellFiltration.snoc`: for a morphism `ψ : (A e)⟦m⟧ → P` into a finite-cell module, the
  mapping cone `Cone ψ` is finite-cell, with the cells of `P` followed by `(A e)⟦m + 1⟧`.
* `DG.exists_finiteCellFiltration_of_cellTower`: conversely, every object of `D(A)` with a cell
  tower is isomorphic to the image of a finite-cell module with the same list of cells.
-/

open CategoryTheory Limits Pretriangulated DirectSum

universe w u

noncomputable section

namespace DG

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The dg modules `(A e)⟦n⟧` and `(A e')⟦n'⟧` are isomorphic when `e = e'` and `n = n'`
(transport along the equalities). -/
def DGIdempotent.shiftCongr {e e' : DGIdempotent A} {n n' : ℤ} (he : e = e') (hn : n = n') :
    Shift n e.LeftCorner ≃ᵈᵍ[A] Shift n' e'.LeftCorner := by
  subst he hn
  exact DGModuleEquiv.refl

theorem coe_decompose_of_map_mem {M N : Type*} [AddCommGroup M] [DGAddCommGroup M]
    [AddCommGroup N] [DGAddCommGroup N] (f : M →+ N)
    (hf : ∀ {k : ℤ} {m : M}, m ∈ grading k → f m ∈ grading k) (m : M) (j : ℤ) :
    (decompose (grading (M := N)) (f m) j : N) = f (decompose (grading (M := M)) m j) := by
  induction m using induction_on with
  | h_zero => simp
  | h_homogeneous x =>
    rename_i i
    rw [decompose_of_mem _ (hf x.2), decompose_coe]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [of_eq_of_ne _ _ _ (Ne.symm hij)]
  | h_add m m' hm hm' => simp [decompose_add, hm, hm']

namespace FiniteCellFiltration

variable {P : Type u} [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]
  (C : FiniteCellFiltration A P)

/-- The list of cells `[(e₁, n₁), …, (eₖ, nₖ)]` of a finite-cell filtration. -/
def cells : List (DGIdempotent A × ℤ) := List.ofFn fun i => (C.e i, C.shift i)

omit [DGModule A P] in
@[simp]
theorem length_cells : C.cells.length = C.length := by simp [cells]

omit [DGModule A P] in
/-- A finite-cell filtration is ordered iff its list of cells is. -/
theorem isOrdered_iff_cellsOrdered : C.IsOrdered ↔ CellsOrdered C.cells := by
  unfold IsOrdered CellsOrdered cells
  rw [List.pairwise_ofFn]
  constructor
  · intro h i j hij
    exact h i j hij.le
  · intro h i j hij
    rcases hij.lt_or_eq with hij | rfl
    · exact h hij
    · exact le_rfl

section Snoc

variable {e : DGIdempotent A} {m : ℤ} (ψ : Shift m e.LeftCorner →ᵈᵍ[A] P)

/-- The members of the filtration of `Cone ψ` extending that of `P` by one cell. -/
def snocF (j : ℕ) : DGSubmodule A (Cone ψ) where
  carrier := {c | (j ≤ C.length → Cone.fstHom ψ c = 0) ∧
    Cone.sndLinear ψ c ∈ C.F (min j C.length)}
  zero_mem' := ⟨fun _ => map_zero _, by simp⟩
  add_mem' {a b} ha hb := ⟨fun h => by rw [map_add, ha.1 h, hb.1 h, add_zero], by
    rw [map_add]
    exact add_mem ha.2 hb.2⟩
  smul_mem' r a ha := ⟨fun h => by rw [map_smul, ha.1 h, smul_zero], by
    rw [map_smul]
    exact (C.F _).toSubmodule.smul_mem r ha.2⟩
  d_mem' {c} hc := by
    refine ⟨fun h => by rw [Cone.fstHom_d, hc.1 h, d_zero], ?_⟩
    rw [Cone.sndLinear_d]
    refine add_mem ?_ ((C.F _).d_mem hc.2)
    by_cases h : j ≤ C.length
    · rw [hc.1 h, Shift.unmk_zero, map_zero]
      exact zero_mem _
    · rw [min_eq_right (by omega)]
      exact C.mem_length _
  decompose_mem' n {c} hc := by
    refine ⟨fun h => ?_, ?_⟩
    · rw [← DGModuleHom.coe_decompose_apply, hc.1 h, decompose_zero, DirectSum.zero_apply,
        ZeroMemClass.coe_zero]
    · have := coe_decompose_of_map_mem (Cone.sndLinear ψ).toAddMonoidHom Cone.sndLinear_mem c n
      simp only [LinearMap.toAddMonoidHom_coe] at this
      rw [← this]
      exact (C.F _).decompose_mem n hc.2

omit [DGModule A P] in
theorem mem_snocF {j : ℕ} {c : Cone ψ} : c ∈ C.snocF ψ j ↔
    (j ≤ C.length → Cone.fstHom ψ c = 0) ∧ Cone.sndLinear ψ c ∈ C.F (min j C.length) :=
  Iff.rfl

/-- The idempotents of the extended filtration. -/
def snocE (e : DGIdempotent A) (i : Fin (C.length + 1)) : DGIdempotent A :=
  if h : i.1 < C.length then C.e ⟨i, h⟩ else e

/-- The shifts of the extended filtration. -/
def snocShift (m : ℤ) (i : Fin (C.length + 1)) : ℤ :=
  if h : i.1 < C.length then C.shift ⟨i, h⟩ else m + 1

/-- The restriction `F (i + 1) → C.F (i + 1)` to the second component, for `i + 1 ≤ length`. -/
def snocRestrict (i : ℕ) (hi : i + 1 ≤ C.length) : C.snocF ψ (i + 1) →ᵈᵍ[A] C.F (i + 1) where
  toFun c := ⟨Cone.sndLinear ψ c, by
    have := c.2.2
    rwa [min_eq_left hi] at this⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mem' hc := Cone.sndLinear_mem hc
  map_d' c := by
    apply Subtype.ext
    change Cone.sndLinear ψ (d (c : Cone ψ)) = d (Cone.sndLinear ψ c)
    rw [Cone.sndLinear_d, c.2.1 hi, Shift.unmk_zero, map_zero, zero_add]

/-- The projection `F (k + 1) → (A e)⟦m + 1⟧` onto the last cell. -/
def snocLast : C.snocF ψ (C.length + 1) →ᵈᵍ[A] Shift (m + 1) e.LeftCorner :=
  (Shift.shiftShiftEquiv m 1 (m + 1) rfl).symm.toDGModuleHom.comp
    ((Cone.fstHom ψ).comp (C.snocF ψ (C.length + 1)).subtype)

/-- The projections of the extended filtration. -/
noncomputable def snocπ (i : Fin (C.length + 1)) :
    C.snocF ψ (i.1 + 1) →ᵈᵍ[A] Shift (C.snocShift m i) (C.snocE e i).LeftCorner :=
  if h : i.1 < C.length then
    (DGIdempotent.shiftCongr (by simp [snocE, h]) (by simp [snocShift, h])).toDGModuleHom.comp
      ((C.π ⟨i, h⟩).comp (C.snocRestrict ψ i h))
  else
    (DGIdempotent.shiftCongr (by simp [snocE, h]) (by simp [snocShift, h])).toDGModuleHom.comp
      ((C.snocLast ψ).comp (DGSubmodule.inclusion (le_of_eq (by
        rw [show i.1 = C.length by omega]))))

omit [DGModule A P] in
theorem snocπ_eq_zero_iff (i : Fin (C.length + 1)) (x : C.snocF ψ (i.1 + 1)) :
    C.snocπ ψ i x = 0 ↔ (x : Cone ψ) ∈ C.snocF ψ i.1 := by
  unfold snocπ
  split_ifs with h
  · rw [DGModuleHom.comp_apply, DGModuleEquiv.coe_toDGModuleHom,
      map_eq_zero_iff _ (DGModuleEquiv.injective _), DGModuleHom.comp_apply,
      C.π_eq_zero_iff, mem_snocF]
    refine ⟨fun hx => ⟨fun _ => x.2.1 h, by rwa [min_eq_left h.le]⟩, fun hx => ?_⟩
    have := hx.2
    rwa [min_eq_left h.le] at this
  · have hi : i.1 = C.length := by omega
    rw [DGModuleHom.comp_apply, DGModuleEquiv.coe_toDGModuleHom,
      map_eq_zero_iff _ (DGModuleEquiv.injective _)]
    simp only [snocLast, DGModuleHom.comp_apply, DGModuleEquiv.coe_toDGModuleHom]
    rw [map_eq_zero_iff _ (DGModuleEquiv.injective _), mem_snocF, DGSubmodule.subtype_apply,
      DGSubmodule.coe_inclusion_apply]
    refine ⟨fun hx => ⟨fun _ => hx, ?_⟩, fun hx => hx.1 hi.le⟩
    rw [show min i.1 C.length = C.length by omega]
    exact C.mem_length _

omit [DGModule A P] in
theorem surjective_snocπ (i : Fin (C.length + 1)) : Function.Surjective (C.snocπ ψ i) := by
  unfold snocπ
  split_ifs with h
  · refine (DGModuleEquiv.surjective _).comp ?_
    intro y
    obtain ⟨x, rfl⟩ := C.surjective_π ⟨i, h⟩ y
    refine ⟨⟨Cone.inr ψ x, fun _ => rfl, ?_⟩, rfl⟩
    rw [min_eq_left h]
    exact x.2
  · refine (DGModuleEquiv.surjective _).comp ?_
    intro y
    have hi : i.1 = C.length := by omega
    refine ⟨⟨Cone.inlLinear ψ ((Shift.shiftShiftEquiv (A := A) m 1 (m + 1) rfl) y),
      fun h' => by omega, by simp⟩, ?_⟩
    simp [snocLast, DGSubmodule.inclusion]

/-- The mapping cone of a morphism `ψ : (A e)⟦m⟧ → P` into a finite-cell module is finite-cell:
its filtration is that of `P` (included by `Cone.inr`) followed by the cell `(A e)⟦m + 1⟧`. -/
noncomputable def snoc : FiniteCellFiltration A (Cone ψ) where
  length := C.length + 1
  F := C.snocF ψ
  mono j j' hjj' c hc := ⟨fun h => hc.1 (hjj'.trans h), C.mono (min_le_min_right _ hjj') hc.2⟩
  eq_zero_of_mem_zero c hc := by
    refine Cone.ext (hc.1 (Nat.zero_le _)) ?_
    have := hc.2
    rw [min_eq_left (Nat.zero_le _)] at this
    exact C.eq_zero_of_mem_zero _ this
  mem_length c := ⟨fun h => by omega, by rw [min_eq_right (by omega)]; exact C.mem_length _⟩
  e := C.snocE e
  shift := C.snocShift m
  π := C.snocπ ψ
  surjective_π := C.surjective_snocπ ψ
  π_eq_zero_iff := C.snocπ_eq_zero_iff ψ

omit [DGModule A P] in
theorem cells_snoc : (C.snoc ψ).cells = C.cells ++ [(e, m + 1)] := by
  simp only [cells, snoc]
  rw [List.ofFn_succ', List.concat_eq_append]
  congr 1
  · congr 1
    funext i
    simp [snocE, snocShift]
  · simp [snocE, snocShift]

end Snoc

end FiniteCellFiltration

/-! ### Cells in the derived category -/

namespace DerivedCategory

variable [HasDerivedCategory.{w, u} A]

variable (A) in
/-- The cell `Q (A e)⟦n⟧` of `D(A)` attached to a degree-`0` idempotent cocycle `e` and `n : ℤ`. -/
abbrev cell (e : DGIdempotent A) (n : ℤ) : DerivedCategory.{w, u} A :=
  Q.obj (DGModuleCat.of A (Shift n e.LeftCorner))

/-- `(Q (A e)⟦n⟧)⟦k⟧ ≅ Q (A e)⟦n + k⟧`. -/
def cellShiftIso (e : DGIdempotent A) (n k : ℤ) : (cell A e n)⟦k⟧ ≅ cell A e (n + k) :=
  ((Q.commShiftIso k).app (DGModuleCat.of A (Shift n e.LeftCorner))).symm ≪≫
    Q.mapIso
      (Shift.shiftShiftEquiv (A := A) (M := e.LeftCorner) n k (n + k) rfl).symm.toDGModuleCatIso

theorem nonempty_cellShiftIso (e : DGIdempotent A) (n k : ℤ) :
    Nonempty ((cell A e n)⟦k⟧ ≅ cell A e (n + k)) :=
  ⟨cellShiftIso e n k⟩

end DerivedCategory

open _root_.DG.DerivedCategory

namespace FiniteCellFiltration

variable [HasDerivedCategory.{w, u} A]
  {P : Type u} [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]
  (C : FiniteCellFiltration A P)

omit [HasDerivedCategory.{w, u} A] in
/-- The isomorphism `P ≅ F length` of a finite-cell module with the last member of its
filtration. -/
def isoF : DGModuleCat.of A P ≅ DGModuleCat.of A (C.F C.length) where
  hom := DGModuleCat.ofHom (DGSubmodule.codRestrict DGModuleHom.id C.mem_length)
  inv := DGModuleCat.ofHom (C.F C.length).subtype
  hom_inv_id := DGModuleCat.hom_ext_apply fun _ => rfl
  inv_hom_id := DGModuleCat.hom_ext_apply fun _ => rfl

omit [HasDerivedCategory.{w, u} A] in
theorem isZero_F_zero : IsZero (DGModuleCat.of A (C.F 0)) := by
  have : Subsingleton (C.F 0) :=
    ⟨fun x y => Subtype.ext (by rw [C.eq_zero_of_mem_zero x x.2, C.eq_zero_of_mem_zero y y.2])⟩
  exact DGModuleCat.isZero_of_subsingleton _

theorem cellTower_F {j : ℕ} (hj : j ≤ C.length) :
    CellTower (cell A) (C.cells.take j) (Q.obj (DGModuleCat.of A (C.F j))) := by
  induction j with
  | zero => exact .zero (Functor.map_isZero _ C.isZero_F_zero)
  | succ j ih =>
    obtain ⟨δ, hδ⟩ := (C.gradedSplitting ⟨j, hj⟩).exists_distinguished
    have htake : C.cells.take (j + 1) = C.cells.take j ++ [(C.e ⟨j, hj⟩, C.shift ⟨j, hj⟩)] := by
      rw [List.take_add_one]
      congr 1
      simp [cells, show j < C.length by omega]
    rw [htake]
    exact .ext _ hδ (ih (by omega)) ⟨Iso.refl _⟩

/-- The image in `D(A)` of a finite-cell module has the cell tower given by its filtration. -/
theorem cellTower : CellTower (cell A) C.cells (Q.obj (DGModuleCat.of A P)) := by
  have := C.cellTower_F (j := C.length) le_rfl
  rw [List.take_of_length_le (by simp)] at this
  exact this.of_iso (Q.mapIso C.isoF).symm

/-- The image in `D(A)` of a finite-cell module lies in every thick subcategory containing its
cells. -/
theorem Q_obj_mem_of_isThick {S : ObjectProperty (DerivedCategory.{w, u} A)} (hS : IsThick S)
    (hC : ∀ i, S (cell A (C.e i) (C.shift i))) : S (Q.obj (DGModuleCat.of A P)) :=
  C.cellTower.mem_of_isThick hS fun c hc => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    exact hC i

end FiniteCellFiltration

/-- The zero dg module has the finite-cell filtration of length `0`. -/
def FiniteCellFiltration.punit : FiniteCellFiltration A PUnit.{u + 1} where
  length := 0
  F _ := (DGModuleHom.id : PUnit.{u + 1} →ᵈᵍ[A] PUnit).ker
  mono _ _ _ _ h := h
  eq_zero_of_mem_zero _ _ := rfl
  mem_length _ := rfl
  e := Fin.elim0
  shift := Fin.elim0
  π := fun i => Fin.elim0 i
  surjective_π := fun i => Fin.elim0 i
  π_eq_zero_iff := fun i => Fin.elim0 i

@[simp]
theorem FiniteCellFiltration.cells_punit : (FiniteCellFiltration.punit (A := A)).cells = [] :=
  rfl

variable [HasDerivedCategory.{w, u} A]

/-- **Realization of cell towers**: an object of `D(A)` with a cell tower (cells `Q (A e)⟦n⟧`)
is isomorphic to the image of a finite-cell module with the same list of cells. The module is
an iterated mapping cone, each cell attached by a morphism of dg modules representing the
attaching morphism of the tower (`DG.FiniteCellFiltration.snoc`). -/
theorem exists_finiteCellFiltration_of_cellTower {ι : Type*} (φ : ι → DGIdempotent A)
    {l : List (ι × ℤ)} {X : DerivedCategory.{w, u} A}
    (h : CellTower (fun i n => cell A (φ i) n) l X) :
    ∃ (P : DGModuleCat.{u} A) (C : FiniteCellFiltration A P),
      C.cells = l.map (fun c => (φ c.1, c.2)) ∧ Nonempty (X ≅ Q.obj P) := by
  induction h with
  | zero hX =>
    refine ⟨DGModuleCat.of A PUnit, FiniteCellFiltration.punit, rfl,
      ⟨hX.iso (Functor.map_isZero _ (DGModuleCat.isZero_of_subsingleton _))⟩⟩
  | @ext l c T hT _ h₃ ih =>
    obtain ⟨P', C', hC', ⟨e'⟩⟩ := ih
    obtain ⟨e₃⟩ := h₃
    obtain ⟨i, n⟩ := c
    let E := (φ i).LeftCorner
    -- The attaching morphism `Q (A e)⟦n - 1⟧ ⟶ Q P'`.
    let j : Q.obj (DGModuleCat.of A (Shift (n + -1) E)) ≅ T.invRotate.obj₁ :=
      (cellShiftIso (φ i) n (-1)).symm ≪≫ (shiftFunctor _ (-1 : ℤ)).mapIso e₃.symm
    have hK : IsKProjective.{u} A (Shift (n + -1) E) := (φ i).isKProjective_leftCorner.shift _
    obtain ⟨ψ, hψ⟩ := exists_Q_map_eq (P := DGModuleCat.of A (Shift (n + -1) E)) hK
      (j.hom ≫ T.invRotate.mor₁ ≫ e'.hom)
    let T' := Q.mapTriangle.obj (Cone.triangle ψ)
    have hT' : T' ∈ distTriang (DerivedCategory A) :=
      (mem_distTriang_iff _).mpr ⟨_, _, _, ⟨Iso.refl _⟩⟩
    obtain ⟨f, -, -⟩ := exists_iso_of_arrow_iso _ _ (inv_rot_of_distTriang T hT) hT'
      (Arrow.isoMk j.symm e' (by simp [T', hψ]))
    refine ⟨DGModuleCat.of A (Cone ψ.hom), C'.snoc ψ.hom, ?_, ⟨Triangle.π₃.mapIso f⟩⟩
    rw [FiniteCellFiltration.cells_snoc, hC', List.map_append]
    simp

end DG

end
