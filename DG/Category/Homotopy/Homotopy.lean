import DG.Category.Homotopy.Hom
import DG.Module.Cohomology

/-!
# Homotopies between morphisms of dg modules over a dg category

Let `C` be a category with dg Hom groups and `M`, `N` dg modules over `C`. A homotopy between
two morphisms `f g : M ⟶ N` is a cochain `h` of degree `-1` of the Hom complex
(`DG.CatModule.Cochain M N (-1)`) with `f = δ h + g`, i.e. `f - g = d ∘ h + h ∘ d` objectwise.
This file is a port of `DG.Homotopy.Homotopy` (the case of a dg ring) with the same names in
the namespace `DG.CatModule`; composition of morphisms is written `f ≫ g`, for the dg-ring
version's `g.comp f`.

## Main definitions

* `DG.CatModule.DGHomotopy f g`: homotopies from `f` to `g`, with the API of Mathlib's
  `Homotopy` (`refl`, `symm`, `trans`, `add`, `neg`, `sub`, `zsmul`, `compLeft`, `compRight`,
  `comp`, `ofEq`, `equivSubZero`), and the null-homotopic morphism
  `DG.CatModule.DGHomotopy.nullHomotopicMap h` attached to a `(-1)`-cochain `h`.
* `DG.CatModule.Homotopic f g`, an equivalence relation compatible with composition and
  addition (`DG.CatModule.homotopic_equivalence`).
* `DG.CatModule.nullHomotopic M N`: the null-homotopic morphisms, an additive subgroup of
  `M ⟶ N`, closed under composition with arbitrary morphisms on both sides.
* `DG.CatModule.Cocycle.coboundaries M N n`: the coboundaries among the `n`-cocycles.
* `DG.CatModule.DGHomotopyEquiv M N`: homotopy equivalences; `DG.CatModule.IsContractible M`.
* `DG.CatModule.cohomologyMap φ X n : Hⁿ(M X) →+ Hⁿ(N X)`: the map induced on the cohomology
  of the values at `X`.

## Main results

* `DG.CatModule.quotientNullHomotopicAddEquiv`:
  `(M ⟶ N) ⧸ nullHomotopic M N ≃+ Cocycle M N 0 ⧸ Cocycle.coboundaries M N 0`, and
  `DG.CatModule.quotientNullHomotopicAddEquivCohomology`:
  `(M ⟶ N) ⧸ nullHomotopic M N ≃+ H⁰(HOM_C(M, N))`.
* `DG.CatModule.DGHomotopy.cohomologyMap_eq`: homotopic morphisms induce the same maps on
  cohomology at every object.
* `DG.CatModule.DGHomotopyEquiv.bijective_cohomologyMap_hom`: homotopy equivalences induce
  bijections on cohomology at every object.
* `DG.CatModule.IsContractible.subsingleton_cohomology`: contractible dg modules are acyclic
  at every object.
-/

open CategoryTheory DirectSum

universe w v u

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  {M N P Q : CatModule.{w} C}

open DG.CatModule.Cochain

/-- The differential of a `(-1)`-cochain: `δ h = d ∘ h + h ∘ d`. -/
theorem δ_neg_one_apply (z : Cochain M N (-1)) {X : C} (x : M.obj X) :
    (δ (-1) 0 z).app X x = d (z.app X x) + z.app X (d x) := by
  rw [δ_apply' (-1) 0 (neg_add_cancel 1), koszulSign, Int.negOnePow_zero, one_smul]

/-! ### Homotopies -/

/-- A homotopy from `f` to `g`, for morphisms of dg modules `f g : M ⟶ N`: a cochain `hom` of
degree `-1` of the Hom complex with `f = δ hom + g`, that is, `f - g = d ∘ hom + hom ∘ d`
(`DG.CatModule.DGHomotopy.comm`). -/
@[ext]
structure DGHomotopy (f g : M ⟶ N) where
  /-- The homotopy, a cochain of degree `-1`. -/
  hom : Cochain M N (-1)
  /-- The homotopy relation `f = δ hom + g` in the Hom complex. -/
  ofHom_eq : ofHom f = δ (-1) 0 hom + ofHom g

namespace DGHomotopy

variable {f g : M ⟶ N}

/-- The homotopy relation, pointwise: `f x = d (h x) + h (d x) + g x`. -/
theorem comm (h : DGHomotopy f g) {X : C} (x : M.obj X) :
    f.app X x = d (h.hom.app X x) + h.hom.app X (d x) + g.app X x := by
  have := congrArg (fun z : Cochain M N 0 => z.app X x) h.ofHom_eq
  simpa only [ofHom_apply, Cochain.add_apply, δ_neg_one_apply] using this

/-- Constructor for homotopies from the pointwise relation `f x = d (h x) + h (d x) + g x`. -/
@[simps]
def mk' (hom : Cochain M N (-1))
    (comm : ∀ {X : C} (x : M.obj X), f.app X x = d (hom.app X x) + hom.app X (d x) + g.app X x) :
    DGHomotopy f g where
  hom := hom
  ofHom_eq := by
    ext X x
    simp only [ofHom_apply, Cochain.add_apply, δ_neg_one_apply]
    exact comm x

/-- Equal morphisms are homotopic, by the zero homotopy. -/
@[simps]
def ofEq (h : f = g) : DGHomotopy f g where
  hom := 0
  ofHom_eq := by rw [δ_zero, zero_add, h]

/-- The zero homotopy from `f` to itself. -/
@[simps!]
def refl (f : M ⟶ N) : DGHomotopy f f := ofEq rfl

/-- The inverse of a homotopy. -/
@[simps]
def symm (h : DGHomotopy f g) : DGHomotopy g f where
  hom := -h.hom
  ofHom_eq := by rw [δ_neg, h.ofHom_eq]; abel

/-- The composition of two homotopies (the sum of the underlying cochains). -/
@[simps]
def trans {e : M ⟶ N} (h₁ : DGHomotopy e f) (h₂ : DGHomotopy f g) : DGHomotopy e g where
  hom := h₁.hom + h₂.hom
  ofHom_eq := by rw [δ_add, h₁.ofHom_eq, h₂.ofHom_eq, add_assoc]

/-- The sum of two homotopies is a homotopy between the sums. -/
@[simps]
def add {f₁ g₁ f₂ g₂ : M ⟶ N} (h₁ : DGHomotopy f₁ g₁) (h₂ : DGHomotopy f₂ g₂) :
    DGHomotopy (f₁ + f₂) (g₁ + g₂) where
  hom := h₁.hom + h₂.hom
  ofHom_eq := by rw [ofHom_add, ofHom_add, h₁.ofHom_eq, h₂.ofHom_eq, δ_add]; abel

/-- The negative of a homotopy is a homotopy between the negatives. -/
@[simps]
def neg (h : DGHomotopy f g) : DGHomotopy (-f) (-g) where
  hom := -h.hom
  ofHom_eq := by rw [ofHom_neg, ofHom_neg, h.ofHom_eq, δ_neg, neg_add]

/-- The difference of two homotopies is a homotopy between the differences. -/
@[simps]
def sub {f₁ g₁ f₂ g₂ : M ⟶ N} (h₁ : DGHomotopy f₁ g₁) (h₂ : DGHomotopy f₂ g₂) :
    DGHomotopy (f₁ - f₂) (g₁ - g₂) where
  hom := h₁.hom - h₂.hom
  ofHom_eq := by rw [ofHom_sub, ofHom_sub, h₁.ofHom_eq, h₂.ofHom_eq, δ_sub]; abel

/-- An integer multiple of a homotopy is a homotopy between the multiples. -/
@[simps]
def zsmul (k : ℤ) (h : DGHomotopy f g) : DGHomotopy (k • f) (k • g) where
  hom := k • h.hom
  ofHom_eq := by rw [ofHom_zsmul, ofHom_zsmul, h.ofHom_eq, δ_zsmul, _root_.smul_add]

/-- Postcomposition of a homotopy with a morphism: a homotopy from `e` to `f` gives one from
`e ≫ g` to `f ≫ g` (Mathlib's `Homotopy.compRight`). -/
@[simps]
def compRight {e : M ⟶ N} (h : DGHomotopy e f) (g : N ⟶ P) :
    DGHomotopy (e ≫ g) (f ≫ g) where
  hom := (ofHom g).comp h.hom (add_zero _)
  ofHom_eq := by
    rw [ofHom_comp, ofHom_comp, δ_comp_ofHom, h.ofHom_eq, Cochain.comp_add]

/-- Precomposition of a homotopy with a morphism: a homotopy from `f` to `g` gives one from
`e ≫ f` to `e ≫ g` (Mathlib's `Homotopy.compLeft`). -/
@[simps]
def compLeft {f g : N ⟶ P} (h : DGHomotopy f g) (e : M ⟶ N) :
    DGHomotopy (e ≫ f) (e ≫ g) where
  hom := h.hom.comp (ofHom e) (zero_add _)
  ofHom_eq := by
    rw [ofHom_comp, ofHom_comp, δ_ofHom_comp, h.ofHom_eq, Cochain.add_comp]

/-- The horizontal composition of homotopies: homotopies `f₁ ≃ g₁` and `f₂ ≃ g₂` give a
homotopy `f₁ ≫ f₂ ≃ g₁ ≫ g₂`. -/
@[simps!]
def comp {f₁ g₁ : M ⟶ N} {f₂ g₂ : N ⟶ P} (h₁ : DGHomotopy f₁ g₁)
    (h₂ : DGHomotopy f₂ g₂) : DGHomotopy (f₁ ≫ f₂) (g₁ ≫ g₂) :=
  (h₁.compRight f₂).trans (h₂.compLeft g₁)

/-- A homotopy `f ≃ 𝟙` gives a homotopy `f ≫ g ≃ g`. -/
@[simps!]
def compRightId {f : M ⟶ M} (h : DGHomotopy f (𝟙 M)) (g : M ⟶ N) : DGHomotopy (f ≫ g) g :=
  (h.compRight g).trans (ofEq (Category.id_comp g))

/-- A homotopy `f ≃ 𝟙` gives a homotopy `g ≫ f ≃ g`. -/
@[simps!]
def compLeftId {f : N ⟶ N} (h : DGHomotopy f (𝟙 N)) (g : M ⟶ N) : DGHomotopy (g ≫ f) g :=
  (h.compLeft g).trans (ofEq (Category.comp_id g))

/-- Homotopies from `f` to `g` are the same as homotopies from `f - g` to `0`. -/
@[simps]
def equivSubZero : DGHomotopy f g ≃ DGHomotopy (f - g) 0 where
  toFun h :=
    { hom := h.hom
      ofHom_eq := by rw [ofHom_sub, h.ofHom_eq, ofHom_zero]; abel }
  invFun h :=
    { hom := h.hom
      ofHom_eq := by
        have h' := h.ofHom_eq
        rw [ofHom_sub, ofHom_zero, add_zero] at h'
        rw [← h', sub_add_cancel] }
  left_inv _ := rfl
  right_inv _ := rfl

/-- The morphism of dg modules `δ h = d ∘ h + h ∘ d` attached to a cochain `h` of degree `-1`;
it is null-homotopic (`DG.CatModule.DGHomotopy.nullHomotopy`). -/
def nullHomotopicMap (h : Cochain M N (-1)) : M ⟶ N :=
  Cocycle.homOf (Cocycle.mk (δ (-1) 0 h) 1 (zero_add 1) (δ_δ _ _ _ h))

@[simp]
theorem nullHomotopicMap_app (h : Cochain M N (-1)) {X : C} (x : M.obj X) :
    (nullHomotopicMap h).app X x = d (h.app X x) + h.app X (d x) := δ_neg_one_apply h x

@[simp]
theorem ofHom_nullHomotopicMap (h : Cochain M N (-1)) :
    ofHom (nullHomotopicMap h) = δ (-1) 0 h := rfl

/-- The homotopy from `δ h` to `0` given by `h`. -/
@[simps]
def nullHomotopy (h : Cochain M N (-1)) : DGHomotopy (nullHomotopicMap h) 0 where
  hom := h
  ofHom_eq := by rw [ofHom_nullHomotopicMap, ofHom_zero, add_zero]

end DGHomotopy

/-! ### The homotopy relation -/

/-- Two morphisms of dg modules are homotopic if there is a homotopy between them. -/
def Homotopic (f g : M ⟶ N) : Prop := Nonempty (DGHomotopy f g)

namespace Homotopic

variable {e f g : M ⟶ N}

theorem _root_.DG.CatModule.DGHomotopy.homotopic (h : DGHomotopy f g) : Homotopic f g := ⟨h⟩

theorem of_eq (h : f = g) : Homotopic f g := ⟨DGHomotopy.ofEq h⟩

@[refl]
theorem refl (f : M ⟶ N) : Homotopic f f := ⟨DGHomotopy.refl f⟩

@[symm]
theorem symm (h : Homotopic f g) : Homotopic g f := ⟨h.some.symm⟩

@[trans]
theorem trans (h₁ : Homotopic e f) (h₂ : Homotopic f g) : Homotopic e g :=
  ⟨h₁.some.trans h₂.some⟩

theorem add {f₁ g₁ f₂ g₂ : M ⟶ N} (h₁ : Homotopic f₁ g₁) (h₂ : Homotopic f₂ g₂) :
    Homotopic (f₁ + f₂) (g₁ + g₂) :=
  ⟨h₁.some.add h₂.some⟩

theorem neg (h : Homotopic f g) : Homotopic (-f) (-g) := ⟨h.some.neg⟩

theorem sub {f₁ g₁ f₂ g₂ : M ⟶ N} (h₁ : Homotopic f₁ g₁) (h₂ : Homotopic f₂ g₂) :
    Homotopic (f₁ - f₂) (g₁ - g₂) :=
  ⟨h₁.some.sub h₂.some⟩

theorem zsmul (k : ℤ) (h : Homotopic f g) : Homotopic (k • f) (k • g) := ⟨h.some.zsmul k⟩

/-- Homotopy is compatible with postcomposition. -/
theorem comp_right (h : Homotopic e f) (g : N ⟶ P) : Homotopic (e ≫ g) (f ≫ g) :=
  ⟨h.some.compRight g⟩

/-- Homotopy is compatible with precomposition. -/
theorem comp_left {f g : N ⟶ P} (h : Homotopic f g) (e : M ⟶ N) :
    Homotopic (e ≫ f) (e ≫ g) :=
  ⟨h.some.compLeft e⟩

theorem comp {f₁ g₁ : M ⟶ N} {f₂ g₂ : N ⟶ P} (h₁ : Homotopic f₁ g₁)
    (h₂ : Homotopic f₂ g₂) : Homotopic (f₁ ≫ f₂) (g₁ ≫ g₂) :=
  ⟨h₁.some.comp h₂.some⟩

theorem iff_sub : Homotopic f g ↔ Homotopic (f - g) 0 :=
  ⟨fun ⟨h⟩ => ⟨DGHomotopy.equivSubZero h⟩, fun ⟨h⟩ => ⟨DGHomotopy.equivSubZero.symm h⟩⟩

end Homotopic

variable (M N) in
/-- Homotopy is an equivalence relation on `M ⟶ N`. -/
theorem homotopic_equivalence : Equivalence (Homotopic : (M ⟶ N) → (M ⟶ N) → Prop) :=
  ⟨Homotopic.refl, Homotopic.symm, Homotopic.trans⟩

variable (M N) in
/-- The setoid of morphisms of dg modules up to homotopy. -/
def homotopicSetoid : Setoid (M ⟶ N) := ⟨Homotopic, homotopic_equivalence M N⟩

/-! ### Null-homotopic morphisms -/

variable (M N) in
/-- The null-homotopic morphisms `M ⟶ N`, an additive subgroup. -/
def nullHomotopic : AddSubgroup (M ⟶ N) where
  carrier := {f | Homotopic f 0}
  zero_mem' := Homotopic.refl 0
  add_mem' hf hg := (Homotopic.add hf hg).trans (Homotopic.of_eq (add_zero 0))
  neg_mem' hf := (Homotopic.neg hf).trans (Homotopic.of_eq neg_zero)

theorem mem_nullHomotopic_iff {f : M ⟶ N} : f ∈ nullHomotopic M N ↔ Homotopic f 0 :=
  Iff.rfl

/-- A morphism is null-homotopic iff it is a coboundary in the Hom complex. -/
theorem mem_nullHomotopic_iff_exists {f : M ⟶ N} :
    f ∈ nullHomotopic M N ↔ ∃ h : Cochain M N (-1), ofHom f = δ (-1) 0 h := by
  refine ⟨fun ⟨h⟩ => ⟨h.hom, by rw [h.ofHom_eq, ofHom_zero, add_zero]⟩, fun ⟨h, hh⟩ =>
    ⟨⟨h, by rw [hh, ofHom_zero, add_zero]⟩⟩⟩

theorem homotopic_iff_sub_mem {f g : M ⟶ N} :
    Homotopic f g ↔ f - g ∈ nullHomotopic M N :=
  Homotopic.iff_sub

theorem nullHomotopicMap_mem (h : Cochain M N (-1)) :
    DGHomotopy.nullHomotopicMap h ∈ nullHomotopic M N :=
  ⟨DGHomotopy.nullHomotopy h⟩

/-- Null-homotopic morphisms form a left ideal: `f ≫ g` is null-homotopic if `f` is. -/
theorem comp_mem_nullHomotopic {f : M ⟶ N} (hf : f ∈ nullHomotopic M N)
    (g : N ⟶ P) : f ≫ g ∈ nullHomotopic M P :=
  (Homotopic.comp_right hf g).trans (Homotopic.of_eq Limits.zero_comp)

/-- Null-homotopic morphisms form a right ideal: `e ≫ f` is null-homotopic if `f` is. -/
theorem mem_nullHomotopic_comp {f : N ⟶ P} (hf : f ∈ nullHomotopic N P)
    (e : M ⟶ N) : e ≫ f ∈ nullHomotopic M P :=
  (Homotopic.comp_left hf e).trans (Homotopic.of_eq Limits.comp_zero)

/-! ### `H⁰` of the Hom complex -/

namespace Cocycle

variable (M N) in
/-- The coboundaries among the `n`-cocycles of the Hom complex: the image of `δ (n - 1) n`. -/
def coboundaries (n : ℤ) : AddSubgroup (Cocycle M N n) :=
  (δ_hom M N (n - 1) n).range.comap (cocycle M N n).subtype

theorem mem_coboundaries_iff {n : ℤ} (m : ℤ) (hmn : m + 1 = n) (z : Cocycle M N n) :
    z ∈ Cocycle.coboundaries M N n ↔ ∃ y : Cochain M N m, δ m n y = z := by
  obtain rfl : m = n - 1 := by omega
  rfl

end Cocycle

variable (M N) in
/-- Morphisms of dg modules modulo null-homotopic ones are the `0`-cocycles of the Hom complex
modulo coboundaries, at the level of cochains. -/
def quotientNullHomotopicAddEquiv :
    ((M ⟶ N) ⧸ nullHomotopic M N) ≃+ (Cocycle M N 0 ⧸ Cocycle.coboundaries M N 0) :=
  QuotientAddGroup.congr _ _ (Cocycle.equivHom M N) (by
    ext z
    rw [AddSubgroup.mem_map, Cocycle.mem_coboundaries_iff (-1) (neg_add_cancel 1)]
    constructor
    · rintro ⟨f, hf, rfl⟩
      obtain ⟨h, hh⟩ := mem_nullHomotopic_iff_exists.mp hf
      exact ⟨h, hh.symm⟩
    · rintro ⟨y, hy⟩
      refine ⟨Cocycle.homOf z, mem_nullHomotopic_iff_exists.mpr ⟨y, hy.symm⟩, ?_⟩
      exact Cocycle.ofHom_homOf_eq_self z)

@[simp]
theorem quotientNullHomotopicAddEquiv_mk (f : M ⟶ N) :
    quotientNullHomotopicAddEquiv M N (QuotientAddGroup.mk f) =
      QuotientAddGroup.mk (Cocycle.ofHom f) :=
  rfl

namespace HOM

variable (M N) in
/-- The inclusion of the `n`-cocycles `DG.CatModule.Cocycle M N n` into the `n`-cocycles of the
Hom complex `HOM_C(M, N)` (as a dg abelian group). -/
noncomputable def cocyclesAddMonoidHom (n : ℤ) : Cocycle M N n →+ cocycles (HOM M N) n where
  toFun z := ⟨DirectSum.of (fun n => Cochain M N n) n z,
    mem_cocycles.mpr ⟨of_mem_summand _ _, by rw [d_of, Cocycle.δ_eq_zero, map_zero]⟩⟩
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

variable (M N) in
/-- The `n`-cocycles of the Hom complex `HOM_C(M, N)` (as a dg abelian group) are the
`n`-cocycles `DG.CatModule.Cocycle M N n`. -/
noncomputable def cocyclesAddEquiv (n : ℤ) : Cocycle M N n ≃+ cocycles (HOM M N) n :=
  AddEquiv.ofBijective (cocyclesAddMonoidHom M N n) (by
    constructor
    · intro z₁ z₂ h
      exact Cocycle.ext (DirectSum.of_injective n (congrArg Subtype.val h))
    · rintro ⟨x, hx, hdx⟩
      obtain ⟨z, rfl⟩ := mem_summand.mp hx
      have hz : δ n (n + 1) z = 0 := by
        apply DirectSum.of_injective (β := fun n => Cochain M N n) (n + 1)
        rw [← d_of, map_zero]
        exact hdx
      exact ⟨Cocycle.mk z (n + 1) rfl hz, rfl⟩)

@[simp]
theorem coe_cocyclesAddEquiv_apply (n : ℤ) (z : Cocycle M N n) :
    (cocyclesAddEquiv M N n z : HOM M N) =
      DirectSum.of (fun n => Cochain M N n) n (z : Cochain M N n) :=
  rfl

theorem cocyclesAddEquiv_mem_coboundaries_iff (n : ℤ) (z : Cocycle M N n) :
    (cocyclesAddEquiv M N n z : HOM M N) ∈ coboundaries (HOM M N) n ↔
      z ∈ Cocycle.coboundaries M N n := by
  rw [Cocycle.mem_coboundaries_iff (n - 1) (sub_add_cancel n 1), mem_coboundaries,
    coe_cocyclesAddEquiv_apply]
  constructor
  · rintro ⟨x, hx, hdx⟩
    obtain ⟨y, rfl⟩ := mem_summand.mp hx
    refine ⟨y, DirectSum.of_injective (β := fun n => Cochain M N n) n ?_⟩
    rw [← hdx, d_of]
    exact (of_congr (sub_add_cancel n 1).symm fun X x => by
      rw [δ_apply _ _ (sub_add_cancel n 1), δ_apply _ _ rfl])
  · rintro ⟨y, hy⟩
    refine ⟨DirectSum.of (fun n => Cochain M N n) (n - 1) y, of_mem_summand _ _, ?_⟩
    rw [d_of, ← hy]
    exact of_congr (sub_add_cancel n 1) fun X x => by
      rw [δ_apply _ _ rfl, δ_apply _ _ (sub_add_cancel n 1)]

variable (M N) in
/-- The `n`-th cohomology of the Hom complex `HOM_C(M, N)` is the group of `n`-cocycles
`DG.CatModule.Cocycle M N n` modulo the coboundaries. -/
noncomputable def cohomologyAddEquiv (n : ℤ) :
    cohomology (HOM M N) n ≃+ (Cocycle M N n ⧸ Cocycle.coboundaries M N n) :=
  QuotientAddGroup.congr _ _ (cocyclesAddEquiv M N n).symm (by
    ext z
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, rfl⟩ := (cocyclesAddEquiv M N n).surjective x
      have hz : ((cocyclesAddEquiv M N n).symm : _ →+ _) (cocyclesAddEquiv M N n z) = z :=
        (cocyclesAddEquiv M N n).symm_apply_apply z
      rw [hz, ← cocyclesAddEquiv_mem_coboundaries_iff]
      exact AddSubgroup.mem_addSubgroupOf.mp hx
    · intro hz
      refine ⟨cocyclesAddEquiv M N n z, ?_, by simp⟩
      exact AddSubgroup.mem_addSubgroupOf.mpr
        ((cocyclesAddEquiv_mem_coboundaries_iff n z).mpr hz))

@[simp]
theorem cohomologyAddEquiv_mk (n : ℤ) (z : Cocycle M N n) :
    cohomologyAddEquiv M N n (cohomology.mk _ n (cocyclesAddEquiv M N n z)) =
      QuotientAddGroup.mk z := by
  show QuotientAddGroup.mk' _ ((cocyclesAddEquiv M N n).symm (cocyclesAddEquiv M N n z)) = _
  rw [AddEquiv.symm_apply_apply]
  rfl

end HOM

variable (M N) in
/-- `Hom_{H(C)}(M, N) ≅ H⁰(HOM_C(M, N))`: morphisms of dg modules modulo null-homotopic ones
are the `0`-th cohomology of the Hom complex. -/
noncomputable def quotientNullHomotopicAddEquivCohomology :
    ((M ⟶ N) ⧸ nullHomotopic M N) ≃+ cohomology (HOM M N) 0 :=
  (quotientNullHomotopicAddEquiv M N).trans (HOM.cohomologyAddEquiv M N 0).symm

@[simp]
theorem quotientNullHomotopicAddEquivCohomology_mk (f : M ⟶ N) :
    quotientNullHomotopicAddEquivCohomology M N (QuotientAddGroup.mk f) =
      cohomology.mk _ 0 (HOM.cocyclesAddEquiv M N 0 (Cocycle.ofHom f)) := by
  rw [quotientNullHomotopicAddEquivCohomology, AddEquiv.trans_apply,
    quotientNullHomotopicAddEquiv_mk, AddEquiv.symm_apply_eq, HOM.cohomologyAddEquiv_mk]

/-! ### Cohomology -/

/-- The map `Hⁿ(M X) →+ Hⁿ(N X)` induced on the cohomology of the values at `X` by a morphism
of dg modules. -/
def cohomologyMap (φ : M ⟶ N) (X : C) (n : ℤ) :
    cohomology (M.obj X) n →+ cohomology (N.obj X) n :=
  cohomology.mapAddMonoidHom (φ.app X) φ.map_mem φ.map_d n

@[simp]
theorem cohomologyMap_mk (φ : M ⟶ N) (X : C) (n : ℤ) (z : cocycles (M.obj X) n) :
    cohomologyMap φ X n (cohomology.mk _ n z) =
      cohomology.mk _ n (cocycles.mapAddMonoidHom (φ.app X) φ.map_mem φ.map_d n z) :=
  cohomology.mapAddMonoidHom_mk _ _ _ n z

theorem cohomologyMap_id (M : CatModule.{w} C) (X : C) (n : ℤ) :
    cohomologyMap (𝟙 M) X n = AddMonoidHom.id _ := by
  ext x
  rfl

theorem cohomologyMap_zero (X : C) (n : ℤ) : cohomologyMap (0 : M ⟶ N) X n = 0 := by
  ext z
  exact (congrArg (cohomology.mk _ n)
    (Subtype.ext rfl : (⟨0, zero_mem _⟩ : cocycles (N.obj X) n) = 0)).trans (map_zero _)

theorem cohomologyMap_comp_apply (φ : M ⟶ N) (ψ : N ⟶ P) (X : C) (n : ℤ)
    (x : cohomology (M.obj X) n) :
    cohomologyMap (φ ≫ ψ) X n x = cohomologyMap ψ X n (cohomologyMap φ X n x) := by
  induction x using QuotientAddGroup.induction_on with
  | H z => rfl

/-- Homotopic morphisms induce the same map on the cohomology at every object. -/
theorem DGHomotopy.cohomologyMap_eq {f g : M ⟶ N} (h : DGHomotopy f g) (X : C) (n : ℤ) :
    cohomologyMap f X n = cohomologyMap g X n := by
  ext z
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, cohomologyMap_mk]
  rw [cohomology.mk_eq_mk_iff]
  refine ⟨h.hom.app X z, ?_, ?_⟩
  · simpa [sub_eq_add_neg] using h.hom.map_mem (cocycles.mem_grading z)
  · simp [h.comm (z : M.obj X), cocycles.d_eq_zero z]

theorem Homotopic.cohomologyMap_eq {f g : M ⟶ N} (h : Homotopic f g) (X : C) (n : ℤ) :
    cohomologyMap f X n = cohomologyMap g X n :=
  h.some.cohomologyMap_eq X n

/-! ### Homotopy equivalences -/

variable (M N) in
/-- A homotopy equivalence between dg modules: morphisms both ways whose composites are
homotopic to the identities. -/
structure DGHomotopyEquiv where
  /-- The morphism `M ⟶ N`. -/
  hom : M ⟶ N
  /-- The morphism `N ⟶ M`. -/
  inv : N ⟶ M
  /-- A homotopy `hom ≫ inv ≃ 𝟙`. -/
  homotopyHomInvId : DGHomotopy (hom ≫ inv) (𝟙 M)
  /-- A homotopy `inv ≫ hom ≃ 𝟙`. -/
  homotopyInvHomId : DGHomotopy (inv ≫ hom) (𝟙 N)

namespace DGHomotopyEquiv

variable (M) in
/-- The identity homotopy equivalence. -/
@[simps]
def refl : DGHomotopyEquiv M M where
  hom := 𝟙 M
  inv := 𝟙 M
  homotopyHomInvId := DGHomotopy.ofEq (Category.id_comp _)
  homotopyInvHomId := DGHomotopy.ofEq (Category.id_comp _)

/-- The inverse of a homotopy equivalence. -/
@[simps]
def symm (e : DGHomotopyEquiv M N) : DGHomotopyEquiv N M where
  hom := e.inv
  inv := e.hom
  homotopyHomInvId := e.homotopyInvHomId
  homotopyInvHomId := e.homotopyHomInvId

/-- The composition of homotopy equivalences. -/
@[simps]
def trans (e : DGHomotopyEquiv M N) (e' : DGHomotopyEquiv N P) : DGHomotopyEquiv M P where
  hom := e.hom ≫ e'.hom
  inv := e'.inv ≫ e.inv
  homotopyHomInvId :=
    (DGHomotopy.ofEq (by simp only [Category.assoc])).trans
      (((e'.homotopyHomInvId.compRight e.inv).compLeft e.hom).trans
        ((DGHomotopy.ofEq (by rw [Category.id_comp])).trans e.homotopyHomInvId))
  homotopyInvHomId :=
    (DGHomotopy.ofEq (by simp only [Category.assoc])).trans
      (((e.homotopyInvHomId.compRight e'.hom).compLeft e'.inv).trans
        ((DGHomotopy.ofEq (by rw [Category.id_comp])).trans e'.homotopyInvHomId))

theorem cohomologyMap_inv_hom (e : DGHomotopyEquiv M N) (X : C) (n : ℤ)
    (x : cohomology (M.obj X) n) :
    cohomologyMap e.inv X n (cohomologyMap e.hom X n x) = x := by
  rw [← cohomologyMap_comp_apply, e.homotopyHomInvId.cohomologyMap_eq, cohomologyMap_id]
  rfl

theorem cohomologyMap_hom_inv (e : DGHomotopyEquiv M N) (X : C) (n : ℤ)
    (x : cohomology (N.obj X) n) :
    cohomologyMap e.hom X n (cohomologyMap e.inv X n x) = x :=
  e.symm.cohomologyMap_inv_hom X n x

/-- A homotopy equivalence induces bijections on the cohomology at every object (it is a
quasi-isomorphism). -/
theorem bijective_cohomologyMap_hom (e : DGHomotopyEquiv M N) (X : C) (n : ℤ) :
    Function.Bijective (cohomologyMap e.hom X n) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨cohomologyMap e.inv X n, e.cohomologyMap_inv_hom X n, e.cohomologyMap_hom_inv X n⟩

/-- The inverse of a homotopy equivalence induces bijections on cohomology. -/
theorem bijective_cohomologyMap_inv (e : DGHomotopyEquiv M N) (X : C) (n : ℤ) :
    Function.Bijective (cohomologyMap e.inv X n) :=
  e.symm.bijective_cohomologyMap_hom X n

end DGHomotopyEquiv

/-! ### Contractible dg modules -/

variable (M) in
/-- A dg module `M` is contractible if its identity is null-homotopic. -/
def IsContractible : Prop := Homotopic (𝟙 M) 0

namespace IsContractible

/-- Every morphism out of a contractible dg module is null-homotopic. -/
theorem homotopic_zero_of_left (hM : IsContractible M) (f : M ⟶ N) : Homotopic f 0 :=
  (Homotopic.of_eq (Category.id_comp f).symm).trans
    ((hM.comp_right f).trans (Homotopic.of_eq Limits.zero_comp))

/-- Every morphism into a contractible dg module is null-homotopic. -/
theorem homotopic_zero_of_right (hN : IsContractible N) (f : M ⟶ N) : Homotopic f 0 :=
  (Homotopic.of_eq (Category.comp_id f).symm).trans
    ((hN.comp_left f).trans (Homotopic.of_eq Limits.comp_zero))

/-- A contractible dg module is acyclic: all the cohomology groups of all its values
vanish. -/
theorem subsingleton_cohomology (hM : IsContractible M) (X : C) (n : ℤ) :
    Subsingleton (cohomology (M.obj X) n) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  have h := congrArg (fun φ => φ x) (hM.cohomologyMap_eq X n)
  simpa [cohomologyMap_id, cohomologyMap_zero] using h

theorem cohomology_eq_zero (hM : IsContractible M) {X : C} {n : ℤ}
    (x : cohomology (M.obj X) n) : x = 0 :=
  (hM.subsingleton_cohomology X n).elim x 0

end IsContractible

end CatModule

end DG
