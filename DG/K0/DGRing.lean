import DG.Compact.CellTower
import DG.Derived.FiniteCell
import DG.Derived.Perfect
import DG.K0.DGCategory

/-!
# The Grothendieck group of a dg ring

For a dg ring `A`, `K₀(A) := K₀(D^c(A))` (`DG.DGRing.K0 A`) is the Grothendieck group of the
perfect derived category of compact objects of `D(A)` (roadmap 5.5).

## Main definitions and results

* `DG.CellTower.isCompact`, `DG.CellTower.mk_eq_sum`: an object with a cell tower of compact cells
  (`DG.CellTower`) is compact, and its class in `K₀` of the compact objects is the sum of the
  classes of its cells.
* `DG.DerivedCategory.isCompact_Q_leftCorner`: `A e` is compact (a direct summand of `A`), for a
  degree-`0` idempotent cocycle `e`; `DG.DerivedCategory.isCompact_cell`: so are its shifts;
  `DG.FiniteCellFiltration.isCompact_Q`: finite-cell dg modules are compact (roadmap 5.2).
* `DG.DGRing.K0 A`, `DG.DGRing.K0.self A = [A]`, `DG.DGRing.K0.leftCorner e = [A e]`.
* `DG.DGRing.K0.mk_finiteCell`: for a finite-cell module with subquotients `(A eᵢ)⟦nᵢ⟧`,
  `[M] = ∑ᵢ (-1)^{nᵢ} [A eᵢ]`, where `(-1)^{nᵢ}` is `Int.negOnePow nᵢ : ℤˣ` (from
  `DG.K0.mk_shift`, `[X⟦n⟧] = (-1)ⁿ [X]`).
* `DG.DGRing.K0.singleObjEquiv A : K₀(SingleObj A) ≃+ K₀(A)`, sending the representable to `[A]`.
* `DG.DGRing.K0.map φ : K₀(B) →+ K₀(A)` for a morphism of dg rings `φ : B → A` (derived
  induction along `SingleObj B ⥤ SingleObj A`), with `DG.DGRing.K0.map_self`: `[B] ↦ [A]`;
  `DG.DGRing.K0.mapEquivOfIsQuasiIso`: a quasi-isomorphism induces `K₀(B) ≃+ K₀(A)`.

## Universes

`DG.DGRing.K0.{w', v} A` is defined for dg modules in any universe `v`; the classes `[A]`, `[A e]`
and the functoriality are stated for dg modules in the universe `u` of `A` (and of `B`), with
derived categories whose morphisms lie in arbitrary universes.
-/

open CategoryTheory Limits Pretriangulated

universe w w' w'' w₁ w₂ v u

set_option backward.isDefEq.respectTransparency false

namespace DG

/-! ### `K₀` of the compact objects along cell towers -/

section CellTower

variable {T : Type*} [Category T] [HasZeroObject T] [HasShift T ℤ] [Preadditive T]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [HasCoproducts.{w} T]
  {ι : Type*} {cell : ι → ℤ → T} (hcell : ∀ i n, IsCompact.{w} (cell i n))

include hcell in
/-- An object with a cell tower of compact cells is compact. -/
theorem CellTower.isCompact {l : List (ι × ℤ)} {X : T} (h : CellTower cell l X) :
    IsCompact.{w} X := by
  induction h with
  | zero hX => exact IsCompact.of_isZero hX
  | ext R hR _ e ih => exact IsCompact.ext₂ R hR ih ((hcell _ _).of_iso e.some)

include hcell in
/-- Additivity of `K₀` over cell towers: the class of an object with a cell tower of compact
cells is the sum of the classes of its cells. -/
theorem CellTower.mk_eq_sum {l : List (ι × ℤ)} {X : T} (h : CellTower cell l X) :
    K0.mk (⟨X, h.isCompact hcell⟩ : (compactSubcategory.{w} T).FullSubcategory) =
      (l.map fun c : ι × ℤ => K0.mk (⟨cell c.1 c.2, hcell c.1 c.2⟩ :
        (compactSubcategory.{w} T).FullSubcategory)).sum := by
  induction h with
  | zero hX =>
    rw [List.map_nil, List.sum_nil]
    exact K0.mk_eq_zero_of_isZero ((IsZero.iff_id_eq_zero _).mpr (by
      ext
      exact hX.eq_of_src _ _))
  | ext R hR h₁ e ih =>
    rw [K0.mk_fullSubcategory_obj₂ (P := compactSubcategory.{w} T) R hR (h₁.isCompact hcell) _
      ((hcell _ _).of_iso e.some), ih,
      List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    congr 1
    exact K0.mk_eq_of_iso_obj e.some

end CellTower

/-! ### Compactness of corner modules and finite-cell modules -/

namespace DerivedCategory

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [HasDerivedCategory.{w', u} A]

/-- For a degree-`0` idempotent cocycle `e`, the dg module `A e` is compact in `D(A)`: it is a
direct summand of `A`. -/
theorem isCompact_Q_leftCorner (e : DGIdempotent A) :
    IsCompact.{u} (Q.obj (DGModuleCat.of A e.LeftCorner)) :=
  IsCompact.of_retract
    { i := Q.map (DGModuleCat.ofHom e.leftCornerInclusion)
      r := Q.map (DGModuleCat.ofHom e.leftCornerProjection)
      retract := by
        rw [← Q.map_comp, ← Q.map_id]
        congr 1
        exact DGModuleCat.hom_ext_apply fun x => Subtype.ext x.2 } isCompact_Q_self

/-- The cells `(A e)⟦n⟧` are compact in `D(A)`. -/
theorem isCompact_cell (e : DGIdempotent A) (n : ℤ) : IsCompact.{u} (cell A e n) :=
  ((isCompact_Q_leftCorner e).shift n).of_iso
    ((Q.commShiftIso n).app (DGModuleCat.of A e.LeftCorner))

end DerivedCategory

/-- A finite-cell dg module is compact in `D(A)` (roadmap 5.2). -/
theorem FiniteCellFiltration.isCompact_Q {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]
    [HasDerivedCategory.{w', u} A] {P : Type u} [AddCommGroup P] [DGAddCommGroup P]
    [Module A P] [DGModule A P] (C : FiniteCellFiltration A P) :
    IsCompact.{u} (DerivedCategory.Q.obj (DGModuleCat.of A P)) :=
  C.cellTower.isCompact fun _ _ => DerivedCategory.isCompact_cell _ _

/-! ### The Grothendieck group of a dg ring -/

namespace DGRing

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The Grothendieck group `K₀(A) := K₀(D^c(A))` of a dg ring `A` (roadmap 5.5), for dg
modules with values in `Type v`. -/
abbrev K0 [HasDerivedCategory.{w', v} A] : Type _ := DG.K0 (PerfectDerivedCategory.{w', v} A)

namespace K0

variable [HasDerivedCategory.{w', u} A]

/-- The class `[A] ∈ K₀(A)` of the free module of rank one. -/
noncomputable def self : K0 A :=
  DG.K0.mk (⟨DerivedCategory.Q.obj (DGModuleCat.of A A), DerivedCategory.isCompact_Q_self⟩ :
    PerfectDerivedCategory A)

variable {A}

/-- The class `[A e] ∈ K₀(A)` of the dg module `A e` of a degree-`0` idempotent cocycle `e`. -/
noncomputable def leftCorner (e : DGIdempotent A) : K0 A :=
  DG.K0.mk (⟨DerivedCategory.Q.obj (DGModuleCat.of A e.LeftCorner),
    DerivedCategory.isCompact_Q_leftCorner e⟩ : PerfectDerivedCategory A)

/-- The class of a cell: `[(A e)⟦n⟧] = (-1)ⁿ [A e]`. -/
theorem mk_cell (e : DGIdempotent A) (n : ℤ) :
    DG.K0.mk (⟨DerivedCategory.cell A e n, DerivedCategory.isCompact_cell e n⟩ :
      PerfectDerivedCategory A) = n.negOnePow • leftCorner e := by
  rw [leftCorner, ← DG.K0.mk_shift]
  exact DG.K0.mk_eq_of_iso_obj
    (((DerivedCategory.Q.commShiftIso n).app (DGModuleCat.of A e.LeftCorner)) ≪≫
    (((compactSubcategory.{u} (DerivedCategory A)).ι.commShiftIso n).app
      ⟨_, DerivedCategory.isCompact_Q_leftCorner e⟩).symm)

/-- **The class of a finite-cell module** (roadmap 5.5): if `P` has a finite-cell filtration
with subquotients `(A eᵢ)⟦nᵢ⟧`, then `[P] = ∑ᵢ (-1)^{nᵢ} [A eᵢ]` in `K₀(A)`. -/
theorem mk_finiteCell {P : Type u} [AddCommGroup P] [DGAddCommGroup P] [Module A P]
    [DGModule A P] (C : FiniteCellFiltration A P) :
    DG.K0.mk (⟨DerivedCategory.Q.obj (DGModuleCat.of A P), C.isCompact_Q⟩ :
      PerfectDerivedCategory A) = ∑ i, (C.shift i).negOnePow • leftCorner (C.e i) := by
  rw [C.cellTower.mk_eq_sum fun _ _ => DerivedCategory.isCompact_cell _ _,
    FiniteCellFiltration.cells, List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_congr rfl fun i _ => mk_cell _ _

/-! #### Comparison with the one-object dg category -/

section SingleObj

variable (A) [CatModule.HasDerivedCategory.{w'', u} (SingleObj A)]

/-- `K₀` of the dg ring `A` is `K₀` of the one-object dg category `SingleObj A`, via the
triangulated equivalence `D(SingleObj A) ≌ D(A)`. -/
noncomputable def singleObjEquiv : DGCategory.K0.{w'', u} (SingleObj A) ≃+ K0 A :=
  DG.K0.compactMapEquiv (CatModule.DerivedCategory.singleObjEquivalence A)

/-- Under `K₀(SingleObj A) ≃+ K₀(A)`, the representable module corresponds to `[A]`. -/
theorem singleObjEquiv_representable :
    singleObjEquiv A (DGCategory.K0.representable.{w'', u} (SingleObj.star A)) = self A := by
  rw [DGCategory.K0.representable, singleObjEquiv, DG.K0.compactMapEquiv_mk]
  exact DG.K0.mk_eq_of_iso_obj
    ((CatModule.DerivedCategory.singleObjEquivalence A).functor.mapIso
      (CatModule.DerivedCategory.Q.mapIso (CatModule.IsCornerGenerator.isoOfGen
        (CatModule.isCornerGenerator_representable (SingleObj.star A)).ulift
        CatModule.isCornerGenerator_toCatModuleObj_self)) ≪≫
      DerivedCategory.singleObjEquivalenceObjIso _)

end SingleObj

/-! #### Functoriality -/

section Functoriality

variable {B : Type u} [Ring B] [DGAddCommGroup B] [DGRing B] [HasDerivedCategory.{w₁, u} B]

/-- The homomorphism `K₀(B) →+ K₀(A)` induced by a morphism of dg rings `φ : B → A` (roadmap
5.5): derived induction along the dg functor `SingleObj B ⥤ SingleObj A` (i.e. `A ⊗ᴸ_B -`)
preserves compact objects. -/
noncomputable def map (φ : B →ᵈᵍ+* A) : K0 B →+ K0 A :=
  letI := CatModule.HasDerivedCategory.small.{u} (SingleObj B)
  letI := CatModule.HasDerivedCategory.small.{u} (SingleObj A)
  (singleObjEquiv A).toAddMonoidHom.comp ((DGCategory.K0.map φ.singleObjFunctor).comp
    (singleObjEquiv B).symm.toAddMonoidHom)

/-- `K₀(φ) [B] = [A]`. -/
theorem map_self (φ : B →ᵈᵍ+* A) : map φ (self B) = self A := by
  let := CatModule.HasDerivedCategory.small.{u} (SingleObj B)
  let := CatModule.HasDerivedCategory.small.{u} (SingleObj A)
  change singleObjEquiv A (DGCategory.K0.map φ.singleObjFunctor ((singleObjEquiv B).symm
    (self B))) = self A
  rw [← singleObjEquiv_representable B, AddEquiv.symm_apply_apply,
    DGCategory.K0.map_representable]
  exact singleObjEquiv_representable A

/-- **Invariance of `K₀` under quasi-isomorphisms** (roadmap 5.5): a quasi-isomorphism of dg
rings `φ : B → A` induces an isomorphism `K₀(B) ≃+ K₀(A)`, by Keller's theorem
(`DG.DGRingHom.derivedEquivalence`). -/
noncomputable def mapEquivOfIsQuasiIso (φ : B →ᵈᵍ+* A) (hφ : φ.IsQuasiIso) : K0 B ≃+ K0 A :=
  letI := CatModule.HasDerivedCategory.small.{u} (SingleObj B)
  letI := CatModule.HasDerivedCategory.small.{u} (SingleObj A)
  (singleObjEquiv B).symm.trans ((DGCategory.K0.mapEquivOfIsQuasiEquivalence φ.singleObjFunctor
    (φ.isQuasiEquivalence_singleObjFunctor hφ)).trans (singleObjEquiv A))

@[simp]
theorem mapEquivOfIsQuasiIso_apply (φ : B →ᵈᵍ+* A) (hφ : φ.IsQuasiIso) (x : K0 B) :
    mapEquivOfIsQuasiIso φ hφ x = map φ x :=
  rfl

end Functoriality

end K0

end DGRing

end DG
