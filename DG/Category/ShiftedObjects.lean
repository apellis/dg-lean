import DG.Category.Functor
import DG.Module.Shift

/-!
# Formal shifts of objects of a dg category

Let `C` be a dg category and `φ : ι → C × ℤ` a family of pairs `(Xᵢ, mᵢ)` of an object and an
integer. The dg category `DG.ShiftedObjects φ` has objects `ι`, and its Hom complexes are those of
`C`, regraded by the shifts: an element of `C(Xᵢ, Xⱼ)` of degree `n + mⱼ - mᵢ` is a morphism
`i ⟶ j` of degree `n`, and the differential is twisted by the sign of the shift of the target,

  `ShiftedObjects φ (i, j)ⁿ = C(Xᵢ, Xⱼ)^{n + mⱼ - mᵢ}`,  `d' f = (-1)^{mⱼ} d f`,

with the composition of `C`. The object `i` behaves as the formal shift `Xᵢ[mᵢ]`: the
representable module of `i` is the shift by `mᵢ` of the representable module of `Xᵢ` (up to the
usual signs), and for `C` the one-object dg category of a dg ring this is the dg category of the
shifted free modules `A[mᵢ]`. The sign of the differential is forced by the Leibniz rule of
`docs/CONVENTIONS.md`: for `f : i ⟶ j` and `g : j ⟶ l` homogeneous of degree `q` (so of degree
`q + mₗ - mⱼ` in `C`),
`(-1)^{mₗ} d (f ≫ g) = f ≫ (-1)^{mₗ} d g + (-1)^q ((-1)^{mⱼ} d f ≫ g)`.

## Main definitions

* `DG.ShiftedHom a b M`: a dg abelian group `M` regraded by `b - a` with differential
  `(-1)^b d` (the Hom complexes of `ShiftedObjects`).
* `DG.ShiftedObjects φ`, with `Category`, `Preadditive` and `DGCategory` instances.
* `DG.ShiftedObjects.reindexFunctor φ ψ : ShiftedObjects (φ ∘ ψ) ⥤ ShiftedObjects φ` for
  `ψ : κ → ι`, and `DG.ShiftedObjects.ofZeroFunctor φ s hs : C ⥤ ShiftedObjects φ` for a section
  `s` with `φ (s X) = (X, 0)`: dg functors which are the identity on Hom complexes.
* `DG.ShiftedObjects.mapFunctor F φ : ShiftedObjects φ ⥤ ShiftedObjects (F.obj ∘ φ)`: the dg
  functor induced by a dg functor `F : C ⥤ D`.
* `DG.ShiftedObjects.shiftHom`: the identity `𝟙 X` as a closed isomorphism of degree `m' - m`
  between objects with the same underlying object of `C` and shifts `m`, `m'`.
-/

open CategoryTheory DirectSum

universe v u u'

namespace DG

/-! ### Regraded Hom complexes -/

/-- A dg abelian group `M` regraded for the Hom complexes of `DG.ShiftedObjects`: the component
of degree `n` is `M^{n + (b - a)}` and the differential is `(-1)^b d`. -/
def ShiftedHom (_a _b : ℤ) (M : Type*) : Type _ := M

namespace ShiftedHom

variable (a b : ℤ) (M : Type*) [AddCommGroup M]

instance : AddCommGroup (ShiftedHom a b M) := inferInstanceAs (AddCommGroup M)

/-- The identity `ShiftedHom a b M → M`, as an additive equivalence. -/
def val : ShiftedHom a b M ≃+ M := AddEquiv.refl M

variable [DGAddCommGroup M]

instance : DGAddCommGroup (ShiftedHom a b M) where
  grading n := grading (M := M) (n + (b - a))
  decomposition := Decomposition.reindex (grading (M := M)) (Equiv.addRight (b - a))
  d := (val a b M).symm.toAddMonoidHom.comp
    ((DistribSMul.toAddMonoidHom M (koszulSign b)).comp
      ((d : M →+ M).comp (val a b M).toAddMonoidHom))
  d_mem' {n m} hm := by
    have hm' : val a b M m ∈ grading (M := M) (n + (b - a)) := hm
    change koszulSign b • d (val a b M m) ∈ grading (M := M) (n + 1 + (b - a))
    rw [add_right_comm, Units.smul_def]
    exact zsmul_mem (d_mem hm') _
  d_d' m := by
    change koszulSign b • d (koszulSign b • d (val a b M m)) = 0
    rw [d_units_smul, d_d, smul_zero, smul_zero]

variable {a b M}

theorem mem_grading_iff {n : ℤ} {m : ShiftedHom a b M} :
    m ∈ grading n ↔ val a b M m ∈ grading (M := M) (n + (b - a)) :=
  Iff.rfl

theorem val_d (m : ShiftedHom a b M) :
    val a b M (d m) = koszulSign b • d (val a b M m) :=
  rfl

end ShiftedHom

/-! ### The dg category -/

/-- The dg category of formal shifts `Xᵢ[mᵢ]` of objects of a dg category, for a family
`φ : ι → C × ℤ`, `φ i = (Xᵢ, mᵢ)`: objects `ι`, Hom complexes
`(i ⟶ j)ⁿ = C(Xᵢ, Xⱼ)^{n + mⱼ - mᵢ}` with differential `(-1)^{mⱼ} d`. -/
@[ext]
structure ShiftedObjects {C : Type u} {ι : Type u'} (_φ : ι → C × ℤ) where
  /-- The index underlying an object. -/
  as : ι

namespace ShiftedObjects

variable {C : Type u} [Category.{v} C] {ι : Type u'} (φ : ι → C × ℤ)

instance category : Category.{v} (ShiftedObjects φ) where
  Hom i j := ShiftedHom (φ i.as).2 (φ j.as).2 ((φ i.as).1 ⟶ (φ j.as).1)
  id i := (𝟙 (φ i.as).1 : (φ i.as).1 ⟶ (φ i.as).1)
  comp {i j l} f g :=
    ((f : (φ i.as).1 ⟶ (φ j.as).1) ≫ (g : (φ j.as).1 ⟶ (φ l.as).1) : (φ i.as).1 ⟶ (φ l.as).1)
  id_comp _ := Category.id_comp (obj := C) _
  comp_id _ := Category.comp_id (obj := C) _
  assoc _ _ _ := Category.assoc (obj := C) _ _ _

variable {φ}

/-- A morphism of `C` as a morphism of `ShiftedObjects φ`. -/
def homMk {i j : ShiftedObjects φ} (f : (φ i.as).1 ⟶ (φ j.as).1) : i ⟶ j := f

/-- The morphism of `C` underlying a morphism of `ShiftedObjects φ`. -/
def homVal {i j : ShiftedObjects φ} (f : i ⟶ j) : (φ i.as).1 ⟶ (φ j.as).1 := f

@[simp] theorem homVal_homMk {i j : ShiftedObjects φ} (f : (φ i.as).1 ⟶ (φ j.as).1) :
    homVal (homMk (i := i) (j := j) f) = f := rfl

@[simp] theorem homMk_homVal {i j : ShiftedObjects φ} (f : i ⟶ j) : homMk (homVal f) = f := rfl

theorem hom_ext {i j : ShiftedObjects φ} {f g : i ⟶ j} (h : homVal f = homVal g) : f = g := h

@[simp] theorem homVal_id (i : ShiftedObjects φ) : homVal (𝟙 i) = 𝟙 (φ i.as).1 := rfl

@[simp] theorem homVal_comp {i j l : ShiftedObjects φ} (f : i ⟶ j) (g : j ⟶ l) :
    homVal (f ≫ g) = homVal f ≫ homVal g := rfl

variable [Preadditive C]

instance (i j : ShiftedObjects φ) : AddCommGroup (i ⟶ j) :=
  inferInstanceAs (AddCommGroup (ShiftedHom (φ i.as).2 (φ j.as).2 ((φ i.as).1 ⟶ (φ j.as).1)))

/-- `homVal` as an additive equivalence. -/
def homValAddEquiv (i j : ShiftedObjects φ) : (i ⟶ j) ≃+ ((φ i.as).1 ⟶ (φ j.as).1) :=
  AddEquiv.refl _

@[simp] theorem homVal_add {i j : ShiftedObjects φ} (f g : i ⟶ j) :
    homVal (f + g) = homVal f + homVal g := rfl
@[simp] theorem homVal_zero (i j : ShiftedObjects φ) : homVal (0 : i ⟶ j) = 0 := rfl
@[simp] theorem homVal_neg {i j : ShiftedObjects φ} (f : i ⟶ j) : homVal (-f) = -homVal f := rfl
@[simp] theorem homVal_sub {i j : ShiftedObjects φ} (f g : i ⟶ j) :
    homVal (f - g) = homVal f - homVal g := rfl
@[simp] theorem homVal_zsmul {i j : ShiftedObjects φ} (n : ℤ) (f : i ⟶ j) :
    homVal (n • f) = n • homVal f := rfl
@[simp] theorem homVal_units_smul {i j : ShiftedObjects φ} (n : ℤˣ) (f : i ⟶ j) :
    homVal (n • f) = n • homVal f := rfl

@[simp] theorem homMk_add {i j : ShiftedObjects φ} (f g : (φ i.as).1 ⟶ (φ j.as).1) :
    homMk (i := i) (j := j) (f + g) = homMk f + homMk g := rfl

instance preadditive : Preadditive (ShiftedObjects φ) where
  add_comp _ _ _ f f' g := hom_ext (by
    rw [homVal_comp, homVal_add, homVal_add, homVal_comp, homVal_comp]
    exact Preadditive.add_comp _ _ _ _ _ _)
  comp_add _ _ _ f g g' := hom_ext (by
    rw [homVal_comp, homVal_add, homVal_add, homVal_comp, homVal_comp]
    exact Preadditive.comp_add _ _ _ _ _ _)

variable [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

instance instDGAddCommGroupHom (i j : ShiftedObjects φ) : DGAddCommGroup (i ⟶ j) :=
  inferInstanceAs
    (DGAddCommGroup (ShiftedHom (φ i.as).2 (φ j.as).2 ((φ i.as).1 ⟶ (φ j.as).1)))

theorem mem_grading_iff {i j : ShiftedObjects φ} {n : ℤ} {f : i ⟶ j} :
    f ∈ grading n ↔ homVal f ∈ grading (n + ((φ j.as).2 - (φ i.as).2)) :=
  Iff.rfl

theorem homVal_d {i j : ShiftedObjects φ} (f : i ⟶ j) :
    homVal (d f) = koszulSign (φ j.as).2 • d (homVal f) :=
  rfl

variable [DGCategory C]

instance instDGCategory : DGCategory (ShiftedObjects φ) where
  comp_mem' {i j l p q f g} hf hg := by
    rw [mem_grading_iff] at hf hg ⊢
    have := comp_mem_grading hf hg
    rw [homVal_comp]
    convert this using 2
    ring
  id_mem' i := by
    rw [mem_grading_iff, homVal_id, sub_self, add_zero]
    exact id_mem_grading _
  d_comp' {i j l q} f g hg := by
    rw [mem_grading_iff] at hg
    have hs : koszulSign (φ l.as).2 * koszulSign (q + ((φ l.as).2 - (φ j.as).2)) =
        koszulSign q * koszulSign (φ j.as).2 := by
      rw [← koszulSign_add, ← koszulSign_add]
      exact (Int.negOnePow_eq_iff _ _).mpr ⟨(φ l.as).2 - (φ j.as).2, by ring⟩
    refine hom_ext ?_
    simp only [homVal_d, homVal_comp, homVal_add, homVal_units_smul]
    rw [d_comp _ hg, smul_add, smul_smul, comp_units_smul, units_smul_comp, smul_smul, hs]

/-! ### Functors -/

section Functors

variable (φ) in
/-- For `ψ : κ → ι`, the dg functor `ShiftedObjects (φ ∘ ψ) ⥤ ShiftedObjects φ`, `k ↦ ψ k`, the
identity on Hom complexes. -/
@[simps obj]
def reindexFunctor {κ : Type*} (ψ : κ → ι) : ShiftedObjects (φ ∘ ψ) ⥤ ShiftedObjects φ where
  obj k := ⟨ψ k.as⟩
  map f := homMk (homVal f)
  map_id _ := rfl
  map_comp _ _ := rfl

omit [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C] in
@[simp]
theorem homVal_reindexFunctor_map {κ : Type*} (ψ : κ → ι) {k l : ShiftedObjects (φ ∘ ψ)}
    (f : k ⟶ l) : homVal ((reindexFunctor φ ψ).map f) = homVal f :=
  rfl

instance {κ : Type*} (ψ : κ → ι) : (reindexFunctor φ ψ).Additive where

instance {κ : Type*} (ψ : κ → ι) : (reindexFunctor φ ψ).IsDGFunctor where
  map_mem' hf := hf
  map_d' _ := rfl

variable (C) in
/-- The dg functor `C ⥤ ShiftedObjects (id : C × ℤ → C × ℤ)`, `X ↦ (X, 0)`, the identity on Hom
complexes. -/
@[simps obj]
def toClosure : C ⥤ ShiftedObjects (id : C × ℤ → C × ℤ) where
  obj X := ⟨(X, 0)⟩
  map f := homMk f
  map_id _ := rfl
  map_comp _ _ := rfl

omit [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C] in
@[simp]
theorem homVal_toClosure_map {X Y : C} (f : X ⟶ Y) : homVal ((toClosure C).map f) = f :=
  rfl

instance : (toClosure C).Additive where

instance : (toClosure C).IsDGFunctor where
  map_mem' {X Y n f} hf := by
    rw [mem_grading_iff]
    simp only [toClosure_obj, id_eq, sub_self, add_zero, homVal_toClosure_map]
    exact hf
  map_d' f := by
    refine hom_ext ?_
    rw [homVal_d, homVal_toClosure_map, homVal_toClosure_map]
    exact (one_smul _ _).symm

/-- The dg functor `ShiftedObjects φ ⥤ ShiftedObjects (Prod.map F.obj id ∘ φ)`, `(X, m) ↦ (F X, m)`,
induced by a dg functor `F : C ⥤ D`. -/
@[simps obj]
def mapFunctor {D : Type*} [Category D] [Preadditive D] [∀ X Y : D, DGAddCommGroup (X ⟶ Y)]
    (F : C ⥤ D) (φ : ι → C × ℤ) :
    ShiftedObjects φ ⥤ ShiftedObjects (Prod.map F.obj id ∘ φ) where
  obj i := ⟨i.as⟩
  map f := homMk (F.map (homVal f))
  map_id _ := F.map_id _
  map_comp _ _ := F.map_comp _ _

section MapFunctor

variable {D : Type*} [Category D] [Preadditive D] [∀ X Y : D, DGAddCommGroup (X ⟶ Y)]
  (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]

omit [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C] [F.Additive]
  [F.IsDGFunctor] in
@[simp]
theorem homVal_mapFunctor_map {i j : ShiftedObjects φ} (f : i ⟶ j) :
    homVal ((mapFunctor F φ).map f) = F.map (homVal f) :=
  rfl

instance : (mapFunctor F φ).Additive where
  map_add := hom_ext (F.map_add)

instance : (mapFunctor F φ).IsDGFunctor where
  map_mem' hf := F.map_mem_grading hf
  map_d' f := hom_ext (by
    rw [homVal_mapFunctor_map, homVal_d, homVal_d, Units.smul_def, Units.smul_def,
      Functor.map_zsmul, F.map_d]
    rfl)

end MapFunctor

/-! ### Shifting an object -/

omit [DGCategory C] in
theorem _root_.DG.eqToHom_mem_grading [DGCategory C] {X Y : C} (h : X = Y) :
    eqToHom h ∈ grading (M := X ⟶ Y) 0 := by
  subst h
  exact id_mem_grading X

omit [DGCategory C] in
theorem _root_.DG.d_eqToHom [DGCategory C] {X Y : C} (h : X = Y) : d (eqToHom h) = 0 := by
  subst h
  exact d_id X

/-- The identity of `X` as a morphism `i ⟶ j` of `ShiftedObjects φ` between objects with the same
underlying object `X` of `C`; it is a cocycle of degree `mᵢ - mⱼ`. -/
def shiftHom {i j : ShiftedObjects φ} (h : (φ i.as).1 = (φ j.as).1) : i ⟶ j :=
  homMk (eqToHom h)

theorem shiftHom_mem_cocycles {i j : ShiftedObjects φ} (h : (φ i.as).1 = (φ j.as).1) :
    shiftHom h ∈ cocycles (i ⟶ j) ((φ i.as).2 - (φ j.as).2) := by
  refine ⟨mem_grading_iff.mpr ?_, hom_ext ?_⟩
  · rw [show (φ i.as).2 - (φ j.as).2 + ((φ j.as).2 - (φ i.as).2) = 0 by ring]
    exact eqToHom_mem_grading h
  · rw [homVal_d]
    exact (congrArg _ (d_eqToHom h)).trans (smul_zero _)

omit [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C] in
theorem shiftHom_comp_shiftHom {i j l : ShiftedObjects φ} (h : (φ i.as).1 = (φ j.as).1)
    (h' : (φ j.as).1 = (φ l.as).1) : shiftHom h ≫ shiftHom h' = shiftHom (h.trans h') :=
  hom_ext (by simp [shiftHom])

omit [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C] in
theorem shiftHom_self (i : ShiftedObjects φ) : shiftHom (rfl : (φ i.as).1 = (φ i.as).1) = 𝟙 i :=
  rfl

end Functors

end ShiftedObjects

end DG
