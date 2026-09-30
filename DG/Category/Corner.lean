import DG.Category.Functor
import DG.Module.Corner

/-!
# Corner dg categories of families of idempotents

Let `C` be a dg category and let `eᵢ : Xᵢ ⟶ Xᵢ` (`i : ι`) be a family of degree-`0` cocycle
idempotents of objects of `C` (`DG.IdempotentFamily ι C`). The *corner dg category*
`P.Corner` has objects `ι` and Hom complexes

  `P.Corner(i, j) = eᵢ C(Xᵢ, Xⱼ) eⱼ = {f : Xᵢ ⟶ Xⱼ | eᵢ ≫ f = f ∧ f ≫ eⱼ = f}`,

with the grading and the differential restricted from `C` (both preserve these subgroups since
the `eᵢ` are cocycles of degree `0`), the composition of `C`, and identities `eᵢ`. It is the full
dg subcategory of the (dg) Karoubi envelope of `C` on the objects `(Xᵢ, eᵢ)`.

For a dg ring `A` (`C = SingleObj A`) and a single idempotent `e`, the corner dg category is the
one-object dg category of the corner ring `e A e`.

The family `P.augment` over `C ⊕ ι` consists of the identities `𝟙 X` of all objects of `C`
together with `P`; `C` and `P.Corner` embed into `P.augment.Corner` by the dg functors `P.inl`
and `P.inr`, which are isomorphisms on Hom complexes. This is the setting of Morita theory for
idempotents (`DG.Category.Derived.Morita`).

## Main definitions

* `DG.IdempotentFamily ι C`, `DG.IdempotentFamily.Corner`, with `Category`, `Preadditive`,
  `DGAddCommGroup` (on Hom groups) and `DGCategory` instances.
* `DG.IdempotentFamily.augment` (the family `P` together with all identities `𝟙 X`), and the dg
  functors `DG.IdempotentFamily.inl : C ⥤ P.augment.Corner`,
  `DG.IdempotentFamily.inr : P.Corner ⥤ P.augment.Corner`.
-/

open CategoryTheory DirectSum

universe w v u

namespace DG

variable (ι : Type w) (C : Type u) [Category.{v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

/-- A family of degree-`0` cocycle idempotents `eᵢ : Xᵢ ⟶ Xᵢ` of objects of a dg category `C`,
indexed by `ι`. -/
structure IdempotentFamily where
  /-- The object carrying the `i`-th idempotent. -/
  obj : ι → C
  /-- The `i`-th idempotent. -/
  idem : ∀ i, obj i ⟶ obj i
  idem_mem : ∀ i, idem i ∈ grading (M := obj i ⟶ obj i) 0
  idem_comp_idem : ∀ i, idem i ≫ idem i = idem i
  d_idem : ∀ i, d (idem i) = 0

namespace IdempotentFamily

variable {ι C} (P : IdempotentFamily ι C)

attribute [reassoc (attr := simp)] idem_comp_idem

theorem idem_mem_cocycles (i : ι) : P.idem i ∈ cocycles (P.obj i ⟶ P.obj i) 0 :=
  ⟨P.idem_mem i, P.d_idem i⟩

/-- The subgroup `eᵢ C(Xᵢ, Xⱼ) eⱼ` of `C(Xᵢ, Xⱼ)`. -/
def homSubgroup (i j : ι) : AddSubgroup (P.obj i ⟶ P.obj j) where
  carrier := {f | P.idem i ≫ f = f ∧ f ≫ P.idem j = f}
  zero_mem' := ⟨Limits.comp_zero, Limits.zero_comp⟩
  add_mem' {f g} hf hg := ⟨by rw [Preadditive.comp_add, hf.1, hg.1],
    by rw [Preadditive.add_comp, hf.2, hg.2]⟩
  neg_mem' {f} hf := ⟨by rw [Preadditive.comp_neg, hf.1], by rw [Preadditive.neg_comp, hf.2]⟩

theorem mem_homSubgroup {i j : ι} {f : P.obj i ⟶ P.obj j} :
    f ∈ P.homSubgroup i j ↔ P.idem i ≫ f = f ∧ f ≫ P.idem j = f :=
  Iff.rfl

theorem idem_comp_comp_idem_mem (i j : ι) (f : P.obj i ⟶ P.obj j) :
    P.idem i ≫ f ≫ P.idem j ∈ P.homSubgroup i j :=
  ⟨by simp, by simp⟩

/-- The objects of the corner dg category `P.Corner`: the indices `i : ι`. -/
@[ext]
structure Corner (P : IdempotentFamily ι C) where
  /-- The index underlying an object of the corner dg category. -/
  as : ι

/-- The corner category: `P.Corner(i, j) = eᵢ C(Xᵢ, Xⱼ) eⱼ`, with the composition of `C` and
identities `eᵢ`. -/
instance category : Category.{v} P.Corner where
  Hom i j := P.homSubgroup i.as j.as
  id i := ⟨P.idem i.as, by simp, by simp⟩
  comp f g := ⟨f.1 ≫ g.1, by rw [← Category.assoc, f.2.1], by rw [Category.assoc, g.2.2]⟩
  id_comp f := Subtype.ext f.2.1
  comp_id f := Subtype.ext f.2.2
  assoc f g h := Subtype.ext (Category.assoc f.1 g.1 h.1)

variable {P}

theorem hom_ext {i j : P.Corner} {f g : i ⟶ j} (h : f.1 = g.1) : f = g :=
  Subtype.ext h

@[simp] theorem id_val (i : P.Corner) : (𝟙 i : i ⟶ i).1 = P.idem i.as := rfl

@[simp] theorem comp_val {i j k : P.Corner} (f : i ⟶ j) (g : j ⟶ k) :
    (f ≫ g).1 = f.1 ≫ g.1 := rfl

theorem idem_comp_val {i j : P.Corner} (f : i ⟶ j) : P.idem i.as ≫ f.1 = f.1 := f.2.1

theorem val_comp_idem {i j : P.Corner} (f : i ⟶ j) : f.1 ≫ P.idem j.as = f.1 := f.2.2

instance (i j : P.Corner) : AddCommGroup (i ⟶ j) :=
  inferInstanceAs (AddCommGroup (P.homSubgroup i.as j.as))

@[simp] theorem add_val {i j : P.Corner} (f g : i ⟶ j) : (f + g).1 = f.1 + g.1 := rfl
@[simp] theorem neg_val {i j : P.Corner} (f : i ⟶ j) : (-f).1 = -f.1 := rfl
@[simp] theorem zero_val (i j : P.Corner) : (0 : i ⟶ j).1 = 0 := rfl
@[simp] theorem sub_val {i j : P.Corner} (f g : i ⟶ j) : (f - g).1 = f.1 - g.1 := rfl
@[simp] theorem zsmul_val {i j : P.Corner} (n : ℤ) (f : i ⟶ j) : (n • f).1 = n • f.1 := rfl

@[simp] theorem sum_val {i j : P.Corner} {J : Type*} (s : Finset J) (f : J → (i ⟶ j)) :
    (∑ a ∈ s, f a).1 = ∑ a ∈ s, (f a).1 :=
  map_sum (AddSubgroupClass.subtype (P.homSubgroup i.as j.as)) f s

instance preadditive : Preadditive P.Corner where
  add_comp _ _ _ f f' g := hom_ext (by simp only [comp_val, add_val, Preadditive.add_comp])
  comp_add _ _ _ f g g' := hom_ext (by simp only [comp_val, add_val, Preadditive.comp_add])

variable [DGCategory C]

variable (P) in
theorem d_mem_homSubgroup {i j : ι} {f : P.obj i ⟶ P.obj j} (hf : f ∈ P.homSubgroup i j) :
    d f ∈ P.homSubgroup i j := by
  constructor
  · rw [← d_comp_of_d_eq_zero_left (P.d_idem i), hf.1]
  · have h := d_comp_of_mem_zero f (P.idem_mem j)
    rw [P.d_idem, Limits.comp_zero, zero_add, hf.2] at h
    exact h.symm

variable (P) in
theorem decompose_mem_homSubgroup {i j : ι} {f : P.obj i ⟶ P.obj j}
    (hf : f ∈ P.homSubgroup i j) (n : ℤ) :
    (decompose (grading (M := P.obj i ⟶ P.obj j)) f n : P.obj i ⟶ P.obj j) ∈
      P.homSubgroup i j := by
  constructor
  · have h := decompose_comp_left (P.idem_mem i) f n
    rw [add_zero, hf.1] at h
    exact h.symm
  · have h := decompose_comp_right f (P.idem_mem j) n
    rw [add_zero, hf.2] at h
    exact h.symm

/-- The Hom complexes of the corner category: the subcomplexes `eᵢ C(Xᵢ, Xⱼ) eⱼ`. -/
noncomputable instance instDGAddCommGroupHom (i j : P.Corner) : DGAddCommGroup (i ⟶ j) :=
  DGAddCommGroup.ofInjective (AddSubgroupClass.subtype (P.homSubgroup i.as j.as))
    Subtype.val_injective
    (((d : (P.obj i.as ⟶ P.obj j.as) →+ _).comp (AddSubgroupClass.subtype _)).codRestrict _
      fun f => P.d_mem_homSubgroup f.2)
    (fun _ => rfl) fun n f => ⟨⟨_, P.decompose_mem_homSubgroup f.2 n⟩, rfl⟩

theorem mem_grading_iff {i j : P.Corner} {n : ℤ} {f : i ⟶ j} :
    f ∈ grading n ↔ f.1 ∈ grading (M := P.obj i.as ⟶ P.obj j.as) n :=
  Iff.rfl

@[simp]
theorem d_val {i j : P.Corner} (f : i ⟶ j) : (d f).1 = d f.1 := rfl

theorem mem_cocycles_iff {i j : P.Corner} {n : ℤ} {f : i ⟶ j} :
    f ∈ cocycles (i ⟶ j) n ↔ f.1 ∈ cocycles (P.obj i.as ⟶ P.obj j.as) n := by
  simp only [mem_cocycles, mem_grading_iff]
  exact and_congr_right fun _ => ⟨fun h => by rw [← d_val, h, zero_val],
    fun h => hom_ext (by rw [d_val, h, zero_val])⟩

/-- The corner category of a family of degree-`0` cocycle idempotents is a dg category. -/
instance instDGCategory : DGCategory P.Corner where
  comp_mem' hf hg := comp_mem_grading (C := C) hf hg
  id_mem' i := P.idem_mem i.as
  d_comp' f _ hg := hom_ext (d_comp (C := C) f.1 hg)

/-! ### The augmented family and the embeddings of `C` and of `P.Corner` -/

section Augment

variable (P)

/-- The family over `C ⊕ ι` consisting of the identities `𝟙 X` of all objects of `C` together with
the family `P`. -/
def augment : IdempotentFamily (C ⊕ ι) C where
  obj := Sum.elim id P.obj
  idem
    | .inl X => 𝟙 X
    | .inr i => P.idem i
  idem_mem
    | .inl X => id_mem_grading X
    | .inr i => P.idem_mem i
  idem_comp_idem
    | .inl _ => Category.id_comp _
    | .inr i => P.idem_comp_idem i
  d_idem
    | .inl X => d_id X
    | .inr i => P.d_idem i

@[simp] theorem augment_obj_inl (X : C) : P.augment.obj (.inl X) = X := rfl
@[simp] theorem augment_obj_inr (i : ι) : P.augment.obj (.inr i) = P.obj i := rfl
@[simp] theorem augment_idem_inl (X : C) : P.augment.idem (.inl X) = 𝟙 X := rfl
@[simp] theorem augment_idem_inr (i : ι) : P.augment.idem (.inr i) = P.idem i := rfl

/-- The dg functor `C ⥤ P.augment.Corner`, `X ↦ (X, 𝟙 X)`, the identity on Hom complexes. -/
@[simps obj]
def inl : C ⥤ P.augment.Corner where
  obj X := ⟨.inl X⟩
  map f := ⟨f, Category.id_comp f, Category.comp_id f⟩
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem inl_map_val {X Y : C} (f : X ⟶ Y) : ((P.inl).map f).1 = f := rfl

/-- The dg functor `P.Corner ⥤ P.augment.Corner`, `i ↦ (Xᵢ, eᵢ)`, the identity on Hom
complexes. -/
@[simps obj]
def inr : P.Corner ⥤ P.augment.Corner where
  obj i := ⟨.inr i.as⟩
  map f := ⟨f.1, f.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem inr_map_val {i j : P.Corner} (f : i ⟶ j) : ((P.inr).map f).1 = f.1 := rfl

instance : P.inl.Additive where
instance : P.inr.Additive where

instance : P.inl.IsDGFunctor where
  map_mem' hf := hf
  map_d' _ := rfl

instance : P.inr.IsDGFunctor where
  map_mem' hf := hf
  map_d' _ := rfl

end Augment

end IdempotentFamily

end DG
