import DG.Module.Cohomology
import DG.Module.Hom

/-!
# Homotopies between morphisms of dg modules

Let `A` be a dg ring and `M`, `N` dg `A`-modules. A homotopy between two morphisms
`f g : M →ᵈᵍ[A] N` is an `A`-linear map `h` of degree `-1` (a `(-1)`-cochain of the Hom complex,
`DG.Cochain A M N (-1)`) with `f - g = d ∘ h + h ∘ d`. In terms of the differential `δ` of the
Hom complex this reads `f = δ h + g`, which is the normal form used by Mathlib's
`CochainComplex.HomComplex.Cochain.equivHomotopy`, and the form we take as the definition.

## Main definitions

* `DG.DGHomotopy f g`: homotopies from `f` to `g`, with the API of Mathlib's `Homotopy`
  (`refl`, `symm`, `trans`, `add`, `neg`, `sub`, `zsmul`, `compLeft`, `compRight`, `comp`,
  `ofEq`, `equivSubZero`), and the null-homotopic morphism `DG.DGHomotopy.nullHomotopicMap h`
  attached to any `(-1)`-cochain `h`.
* `DG.Homotopic f g`: the relation "there is a homotopy from `f` to `g`". It is an equivalence
  relation (`DG.homotopic_equivalence`) compatible with composition on both sides and with
  addition: exactly the hypotheses of `CategoryTheory.Quotient` and
  `CategoryTheory.Quotient.preadditive` used to build the homotopy category.
* `DG.nullHomotopic A M N`: the null-homotopic morphisms, an additive subgroup of
  `M →ᵈᵍ[A] N`, closed under composition with arbitrary morphisms on both sides.
* `DG.Cocycle.coboundaries A M N n`: the coboundaries `δ (Cochain A M N (n - 1))` among the
  `n`-cocycles of the Hom complex.
* `DG.DGHomotopyEquiv A M N`: homotopy equivalences between dg modules.
* `DG.IsContractible A M`: the identity of `M` is null-homotopic.

## Main results

* `DG.quotientNullHomotopicAddEquiv`: morphisms modulo null-homotopic morphisms are the
  `0`-cocycles of the Hom complex modulo coboundaries,
  `(M →ᵈᵍ[A] N) ⧸ nullHomotopic A M N ≃+ Cocycle A M N 0 ⧸ Cocycle.coboundaries A M N 0`.
* `DG.DGModule.HOM.cohomologyAddEquiv`: `Hⁿ(HOM_A(M, N))` is `Cocycle A M N n` modulo
  coboundaries; hence `DG.quotientNullHomotopicAddEquivCohomology`:
  `(M →ᵈᵍ[A] N) ⧸ nullHomotopic A M N ≃+ H⁰(HOM_A(M, N))`.
* `DG.DGHomotopy.cohomology_map_eq`: homotopic morphisms induce the same map on cohomology.
* `DG.DGHomotopyEquiv.isQuasiIso_hom`: homotopy equivalences are quasi-isomorphisms.
* `DG.IsContractible.subsingleton_cohomology`: contractible dg modules are acyclic.

## Conventions

`δ (-1) 0 h = d ∘ h - (-1)^{-1} • h ∘ d = d ∘ h + h ∘ d` (`DG.δ_neg_one_apply`), so the
defining equation of a homotopy is `f x = d (h x) + h (d x) + g x` (`DG.DGHomotopy.comm`), as for
Mathlib's `Homotopy` of cochain complexes.
-/

open DirectSum

namespace DG

variable {A : Type*} {M N P Q : Type*} [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]
  [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]
  [AddCommGroup Q] [DGAddCommGroup Q] [Module A Q] [DGModule A Q]

open Cochain

/-- The differential of a `(-1)`-cochain: `δ h = d ∘ h + h ∘ d`. -/
theorem δ_neg_one_apply (z : Cochain A M N (-1)) (x : M) :
    δ (-1) 0 z x = d (z x) + z (d x) := by
  rw [δ_apply' (-1) 0 (neg_add_cancel 1), koszulSign, Int.negOnePow_zero, one_smul]

omit [DGModule A M] [DGModule A N] in
theorem Cochain.ofHom_zsmul (k : ℤ) (f : M →ᵈᵍ[A] N) : ofHom (k • f) = k • ofHom f := rfl

/-! ### Homotopies -/

/-- A homotopy from `f` to `g`, for morphisms of dg modules `f g : M →ᵈᵍ[A] N`: a cochain `hom`
of degree `-1` of the Hom complex with `f = δ hom + g`, that is, `f - g = d ∘ hom + hom ∘ d`
(`DG.DGHomotopy.comm`). -/
@[ext]
structure DGHomotopy (f g : M →ᵈᵍ[A] N) where
  /-- The homotopy, an `A`-linear map of degree `-1` (with the Koszul sign). -/
  hom : Cochain A M N (-1)
  /-- The homotopy relation `f = δ hom + g` in the Hom complex. -/
  ofHom_eq : ofHom f = δ (-1) 0 hom + ofHom g

namespace DGHomotopy

variable {f g : M →ᵈᵍ[A] N}

/-- The homotopy relation, pointwise: `f x = d (h x) + h (d x) + g x`. -/
theorem comm (h : DGHomotopy f g) (x : M) : f x = d (h.hom x) + h.hom (d x) + g x := by
  have := congrArg (fun z : Cochain A M N 0 => z x) h.ofHom_eq
  simpa only [ofHom_apply, Cochain.add_apply, δ_neg_one_apply] using this

/-- Constructor for homotopies from the pointwise relation `f x = d (h x) + h (d x) + g x`. -/
@[simps]
def mk' (hom : Cochain A M N (-1)) (comm : ∀ x, f x = d (hom x) + hom (d x) + g x) :
    DGHomotopy f g where
  hom := hom
  ofHom_eq := by
    ext x
    simp only [ofHom_apply, Cochain.add_apply, δ_neg_one_apply]
    exact comm x

/-- Equal morphisms are homotopic, by the zero homotopy. -/
@[simps]
def ofEq (h : f = g) : DGHomotopy f g where
  hom := 0
  ofHom_eq := by rw [δ_zero, zero_add, h]

/-- The zero homotopy from `f` to itself. -/
@[simps!]
def refl (f : M →ᵈᵍ[A] N) : DGHomotopy f f := ofEq rfl

/-- The inverse of a homotopy. -/
@[simps]
def symm (h : DGHomotopy f g) : DGHomotopy g f where
  hom := -h.hom
  ofHom_eq := by rw [δ_neg, h.ofHom_eq]; abel

/-- The composition of two homotopies (the sum of the underlying cochains). -/
@[simps]
def trans {e : M →ᵈᵍ[A] N} (h₁ : DGHomotopy e f) (h₂ : DGHomotopy f g) : DGHomotopy e g where
  hom := h₁.hom + h₂.hom
  ofHom_eq := by rw [δ_add, h₁.ofHom_eq, h₂.ofHom_eq, add_assoc]

/-- The sum of two homotopies is a homotopy between the sums. -/
@[simps]
def add {f₁ g₁ f₂ g₂ : M →ᵈᵍ[A] N} (h₁ : DGHomotopy f₁ g₁) (h₂ : DGHomotopy f₂ g₂) :
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
def sub {f₁ g₁ f₂ g₂ : M →ᵈᵍ[A] N} (h₁ : DGHomotopy f₁ g₁) (h₂ : DGHomotopy f₂ g₂) :
    DGHomotopy (f₁ - f₂) (g₁ - g₂) where
  hom := h₁.hom - h₂.hom
  ofHom_eq := by rw [ofHom_sub, ofHom_sub, h₁.ofHom_eq, h₂.ofHom_eq, δ_sub]; abel

/-- An integer multiple of a homotopy is a homotopy between the multiples. -/
@[simps]
def zsmul (k : ℤ) (h : DGHomotopy f g) : DGHomotopy (k • f) (k • g) where
  hom := k • h.hom
  ofHom_eq := by rw [ofHom_zsmul, ofHom_zsmul, h.ofHom_eq, δ_zsmul, smul_add]

/-- Postcomposition of a homotopy with a morphism: a homotopy from `e` to `f` gives one from
`g ∘ e` to `g ∘ f` (Mathlib's `Homotopy.compRight`, in diagrammatic order `e ≫ g`). -/
@[simps]
def compRight {e : M →ᵈᵍ[A] N} (h : DGHomotopy e f) (g : N →ᵈᵍ[A] P) :
    DGHomotopy (g.comp e) (g.comp f) where
  hom := (ofHom g).comp h.hom (add_zero _)
  ofHom_eq := by
    rw [ofHom_comp, ofHom_comp, δ_comp_ofHom, h.ofHom_eq, Cochain.comp_add]

/-- Precomposition of a homotopy with a morphism: a homotopy from `f` to `g` gives one from
`f ∘ e` to `g ∘ e` (Mathlib's `Homotopy.compLeft`, in diagrammatic order `e ≫ f`). -/
@[simps]
def compLeft {f g : N →ᵈᵍ[A] P} (h : DGHomotopy f g) (e : M →ᵈᵍ[A] N) :
    DGHomotopy (f.comp e) (g.comp e) where
  hom := h.hom.comp (ofHom e) (zero_add _)
  ofHom_eq := by
    rw [ofHom_comp, ofHom_comp, δ_ofHom_comp, h.ofHom_eq, Cochain.add_comp]

/-- The horizontal composition of homotopies: homotopies `f₁ ≃ g₁` and `f₂ ≃ g₂` give a
homotopy `f₂ ∘ f₁ ≃ g₂ ∘ g₁`. -/
@[simps!]
def comp {f₁ g₁ : M →ᵈᵍ[A] N} {f₂ g₂ : N →ᵈᵍ[A] P} (h₁ : DGHomotopy f₁ g₁)
    (h₂ : DGHomotopy f₂ g₂) : DGHomotopy (f₂.comp f₁) (g₂.comp g₁) :=
  (h₁.compRight f₂).trans (h₂.compLeft g₁)

/-- A homotopy `f ≃ id` gives a homotopy `g ∘ f ≃ g`. -/
@[simps!]
def compRightId {f : M →ᵈᵍ[A] M} (h : DGHomotopy f DGModuleHom.id) (g : M →ᵈᵍ[A] N) :
    DGHomotopy (g.comp f) g :=
  h.compRight g

/-- A homotopy `f ≃ id` gives a homotopy `f ∘ g ≃ g`. -/
@[simps!]
def compLeftId {f : N →ᵈᵍ[A] N} (h : DGHomotopy f DGModuleHom.id) (g : M →ᵈᵍ[A] N) :
    DGHomotopy (f.comp g) g :=
  h.compLeft g

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
it is null-homotopic (`DG.DGHomotopy.nullHomotopy`). -/
def nullHomotopicMap (h : Cochain A M N (-1)) : M →ᵈᵍ[A] N :=
  Cocycle.homOf (Cocycle.mk (δ (-1) 0 h) 1 (zero_add 1) (δ_δ _ _ _ h))

@[simp]
theorem nullHomotopicMap_apply (h : Cochain A M N (-1)) (x : M) :
    nullHomotopicMap h x = d (h x) + h (d x) := δ_neg_one_apply h x

@[simp]
theorem ofHom_nullHomotopicMap (h : Cochain A M N (-1)) :
    ofHom (nullHomotopicMap h) = δ (-1) 0 h := rfl

/-- The homotopy from `δ h` to `0` given by `h`. -/
@[simps]
def nullHomotopy (h : Cochain A M N (-1)) : DGHomotopy (nullHomotopicMap h) 0 where
  hom := h
  ofHom_eq := by rw [ofHom_nullHomotopicMap, ofHom_zero, add_zero]

end DGHomotopy

/-! ### The homotopy relation -/

/-- Two morphisms of dg modules are homotopic if there is a homotopy between them. -/
def Homotopic (f g : M →ᵈᵍ[A] N) : Prop := Nonempty (DGHomotopy f g)

namespace Homotopic

variable {e f g : M →ᵈᵍ[A] N}

theorem _root_.DG.DGHomotopy.homotopic (h : DGHomotopy f g) : Homotopic f g := ⟨h⟩

theorem of_eq (h : f = g) : Homotopic f g := ⟨DGHomotopy.ofEq h⟩

@[refl]
theorem refl (f : M →ᵈᵍ[A] N) : Homotopic f f := ⟨DGHomotopy.refl f⟩

@[symm]
theorem symm (h : Homotopic f g) : Homotopic g f := ⟨h.some.symm⟩

@[trans]
theorem trans (h₁ : Homotopic e f) (h₂ : Homotopic f g) : Homotopic e g :=
  ⟨h₁.some.trans h₂.some⟩

theorem add {f₁ g₁ f₂ g₂ : M →ᵈᵍ[A] N} (h₁ : Homotopic f₁ g₁) (h₂ : Homotopic f₂ g₂) :
    Homotopic (f₁ + f₂) (g₁ + g₂) :=
  ⟨h₁.some.add h₂.some⟩

theorem neg (h : Homotopic f g) : Homotopic (-f) (-g) := ⟨h.some.neg⟩

theorem sub {f₁ g₁ f₂ g₂ : M →ᵈᵍ[A] N} (h₁ : Homotopic f₁ g₁) (h₂ : Homotopic f₂ g₂) :
    Homotopic (f₁ - f₂) (g₁ - g₂) :=
  ⟨h₁.some.sub h₂.some⟩

theorem zsmul (k : ℤ) (h : Homotopic f g) : Homotopic (k • f) (k • g) := ⟨h.some.zsmul k⟩

/-- Homotopy is compatible with postcomposition. -/
theorem comp_right (h : Homotopic e f) (g : N →ᵈᵍ[A] P) : Homotopic (g.comp e) (g.comp f) :=
  ⟨h.some.compRight g⟩

/-- Homotopy is compatible with precomposition. -/
theorem comp_left {f g : N →ᵈᵍ[A] P} (h : Homotopic f g) (e : M →ᵈᵍ[A] N) :
    Homotopic (f.comp e) (g.comp e) :=
  ⟨h.some.compLeft e⟩

theorem comp {f₁ g₁ : M →ᵈᵍ[A] N} {f₂ g₂ : N →ᵈᵍ[A] P} (h₁ : Homotopic f₁ g₁)
    (h₂ : Homotopic f₂ g₂) : Homotopic (f₂.comp f₁) (g₂.comp g₁) :=
  ⟨h₁.some.comp h₂.some⟩

theorem iff_sub : Homotopic f g ↔ Homotopic (f - g) 0 :=
  ⟨fun ⟨h⟩ => ⟨DGHomotopy.equivSubZero h⟩, fun ⟨h⟩ => ⟨DGHomotopy.equivSubZero.symm h⟩⟩

end Homotopic

variable (A M N) in
/-- Homotopy is an equivalence relation on `M →ᵈᵍ[A] N`. -/
theorem homotopic_equivalence : Equivalence (Homotopic : (M →ᵈᵍ[A] N) → (M →ᵈᵍ[A] N) → Prop) :=
  ⟨Homotopic.refl, Homotopic.symm, Homotopic.trans⟩

variable (A M N) in
/-- The setoid of morphisms of dg modules up to homotopy. -/
def homotopicSetoid : Setoid (M →ᵈᵍ[A] N) := ⟨Homotopic, homotopic_equivalence A M N⟩

/-! ### Null-homotopic morphisms -/

variable (A M N) in
/-- The null-homotopic morphisms `M →ᵈᵍ[A] N`, an additive subgroup. -/
def nullHomotopic : AddSubgroup (M →ᵈᵍ[A] N) where
  carrier := {f | Homotopic f 0}
  zero_mem' := Homotopic.refl 0
  add_mem' hf hg := (Homotopic.add hf hg).trans (Homotopic.of_eq (add_zero 0))
  neg_mem' hf := (Homotopic.neg hf).trans (Homotopic.of_eq neg_zero)

theorem mem_nullHomotopic_iff {f : M →ᵈᵍ[A] N} : f ∈ nullHomotopic A M N ↔ Homotopic f 0 :=
  Iff.rfl

/-- A morphism is null-homotopic iff it is a coboundary in the Hom complex. -/
theorem mem_nullHomotopic_iff_exists {f : M →ᵈᵍ[A] N} :
    f ∈ nullHomotopic A M N ↔ ∃ h : Cochain A M N (-1), ofHom f = δ (-1) 0 h := by
  refine ⟨fun ⟨h⟩ => ⟨h.hom, by rw [h.ofHom_eq, ofHom_zero, add_zero]⟩, fun ⟨h, hh⟩ =>
    ⟨⟨h, by rw [hh, ofHom_zero, add_zero]⟩⟩⟩

theorem homotopic_iff_sub_mem {f g : M →ᵈᵍ[A] N} :
    Homotopic f g ↔ f - g ∈ nullHomotopic A M N :=
  Homotopic.iff_sub

theorem nullHomotopicMap_mem (h : Cochain A M N (-1)) :
    DGHomotopy.nullHomotopicMap h ∈ nullHomotopic A M N :=
  ⟨DGHomotopy.nullHomotopy h⟩

/-- Null-homotopic morphisms form a left ideal: `g ∘ f` is null-homotopic if `f` is. -/
theorem comp_mem_nullHomotopic {f : M →ᵈᵍ[A] N} (hf : f ∈ nullHomotopic A M N)
    (g : N →ᵈᵍ[A] P) : g.comp f ∈ nullHomotopic A M P :=
  (Homotopic.comp_right hf g).trans (Homotopic.of_eq (DGModuleHom.comp_zero g))

/-- Null-homotopic morphisms form a right ideal: `f ∘ e` is null-homotopic if `f` is. -/
theorem mem_nullHomotopic_comp {f : N →ᵈᵍ[A] P} (hf : f ∈ nullHomotopic A N P)
    (e : M →ᵈᵍ[A] N) : f.comp e ∈ nullHomotopic A M P :=
  (Homotopic.comp_left hf e).trans (Homotopic.of_eq (DGModuleHom.zero_comp e))

/-! ### `H⁰` of the Hom complex -/

namespace Cocycle

variable (A M N) in
/-- The coboundaries among the `n`-cocycles of the Hom complex: the image of `δ (n - 1) n`. -/
def coboundaries (n : ℤ) : AddSubgroup (Cocycle A M N n) :=
  (δ_hom A M N (n - 1) n).range.comap (cocycle A M N n).subtype

theorem mem_coboundaries_iff {n : ℤ} (m : ℤ) (hmn : m + 1 = n) (z : Cocycle A M N n) :
    z ∈ Cocycle.coboundaries A M N n ↔ ∃ y : Cochain A M N m, δ m n y = z := by
  obtain rfl : m = n - 1 := by omega
  rfl

end Cocycle

variable (A M N) in
/-- Morphisms of dg modules modulo null-homotopic ones are the `0`-cocycles of the Hom complex
modulo coboundaries: `Hom_{H(A)}(M, N) ≅ H⁰(HOM_A(M, N))`, at the level of cochains. -/
def quotientNullHomotopicAddEquiv :
    ((M →ᵈᵍ[A] N) ⧸ nullHomotopic A M N) ≃+
      (Cocycle A M N 0 ⧸ Cocycle.coboundaries A M N 0) :=
  QuotientAddGroup.congr _ _ (Cocycle.equivHom A M N) (by
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
theorem quotientNullHomotopicAddEquiv_mk (f : M →ᵈᵍ[A] N) :
    quotientNullHomotopicAddEquiv A M N (QuotientAddGroup.mk f) =
      QuotientAddGroup.mk (Cocycle.ofHom f) :=
  rfl

namespace DGModule.HOM

variable (A M N) in
/-- The inclusion of the `n`-cocycles `DG.Cocycle A M N n` into the `n`-cocycles of the Hom
complex `HOM_A(M, N)` (as a dg abelian group). -/
noncomputable def cocyclesAddMonoidHom (n : ℤ) : Cocycle A M N n →+ cocycles (HOM A M N) n where
  toFun z := ⟨DirectSum.of (fun n => Cochain A M N n) n z,
    mem_cocycles.mpr ⟨of_mem_summand _ _, by rw [d_of, Cocycle.δ_eq_zero, map_zero]⟩⟩
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

variable (A M N) in
/-- The `n`-cocycles of the Hom complex `HOM_A(M, N)` (as a dg abelian group) are the
`n`-cocycles `DG.Cocycle A M N n`. -/
noncomputable def cocyclesAddEquiv (n : ℤ) : Cocycle A M N n ≃+ cocycles (HOM A M N) n :=
  AddEquiv.ofBijective (cocyclesAddMonoidHom A M N n) (by
    constructor
    · intro z₁ z₂ h
      exact Cocycle.ext (DirectSum.of_injective n (congrArg Subtype.val h))
    · rintro ⟨x, hx, hdx⟩
      obtain ⟨z, rfl⟩ := mem_summand.mp hx
      have hz : δ n (n + 1) z = 0 := by
        apply DirectSum.of_injective (β := fun n => Cochain A M N n) (n + 1)
        rw [← d_of, map_zero]
        exact hdx
      exact ⟨Cocycle.mk z (n + 1) rfl hz, rfl⟩)

@[simp]
theorem coe_cocyclesAddEquiv_apply (n : ℤ) (z : Cocycle A M N n) :
    (cocyclesAddEquiv A M N n z : HOM A M N) =
      DirectSum.of (fun n => Cochain A M N n) n (z : Cochain A M N n) :=
  rfl

theorem cocyclesAddEquiv_mem_coboundaries_iff (n : ℤ) (z : Cocycle A M N n) :
    (cocyclesAddEquiv A M N n z : HOM A M N) ∈ coboundaries (HOM A M N) n ↔
      z ∈ Cocycle.coboundaries A M N n := by
  rw [Cocycle.mem_coboundaries_iff (n - 1) (sub_add_cancel n 1), mem_coboundaries,
    coe_cocyclesAddEquiv_apply]
  constructor
  · rintro ⟨x, hx, hdx⟩
    obtain ⟨y, rfl⟩ := mem_summand.mp hx
    refine ⟨y, DirectSum.of_injective (β := fun n => Cochain A M N n) n ?_⟩
    rw [← hdx, d_of]
    exact (of_congr (sub_add_cancel n 1).symm fun x => by
      rw [δ_apply _ _ (sub_add_cancel n 1), δ_apply _ _ rfl])
  · rintro ⟨y, hy⟩
    refine ⟨DirectSum.of (fun n => Cochain A M N n) (n - 1) y, of_mem_summand _ _, ?_⟩
    rw [d_of, ← hy]
    exact of_congr (sub_add_cancel n 1) fun x => by
      rw [δ_apply _ _ rfl, δ_apply _ _ (sub_add_cancel n 1)]

variable (A M N) in
/-- The `n`-th cohomology of the Hom complex `HOM_A(M, N)` is the group of `n`-cocycles
`DG.Cocycle A M N n` modulo the coboundaries. -/
noncomputable def cohomologyAddEquiv (n : ℤ) :
    cohomology (HOM A M N) n ≃+ (Cocycle A M N n ⧸ Cocycle.coboundaries A M N n) :=
  QuotientAddGroup.congr _ _ (cocyclesAddEquiv A M N n).symm (by
    ext z
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, rfl⟩ := (cocyclesAddEquiv A M N n).surjective x
      have hz : ((cocyclesAddEquiv A M N n).symm : _ →+ _) (cocyclesAddEquiv A M N n z) = z :=
        (cocyclesAddEquiv A M N n).symm_apply_apply z
      rw [hz, ← cocyclesAddEquiv_mem_coboundaries_iff]
      exact AddSubgroup.mem_addSubgroupOf.mp hx
    · intro hz
      refine ⟨cocyclesAddEquiv A M N n z, ?_, by simp⟩
      exact AddSubgroup.mem_addSubgroupOf.mpr
        ((cocyclesAddEquiv_mem_coboundaries_iff n z).mpr hz))

@[simp]
theorem cohomologyAddEquiv_mk (n : ℤ) (z : Cocycle A M N n) :
    cohomologyAddEquiv A M N n (cohomology.mk _ n (cocyclesAddEquiv A M N n z)) =
      QuotientAddGroup.mk z := by
  show QuotientAddGroup.mk' _ ((cocyclesAddEquiv A M N n).symm (cocyclesAddEquiv A M N n z)) = _
  rw [AddEquiv.symm_apply_apply]
  rfl

end DGModule.HOM

variable (A M N) in
/-- `Hom_{H(A)}(M, N) ≅ H⁰(HOM_A(M, N))`: morphisms of dg modules modulo null-homotopic ones
are the `0`-th cohomology of the Hom complex. -/
noncomputable def quotientNullHomotopicAddEquivCohomology :
    ((M →ᵈᵍ[A] N) ⧸ nullHomotopic A M N) ≃+ cohomology (DGModule.HOM A M N) 0 :=
  (quotientNullHomotopicAddEquiv A M N).trans (DGModule.HOM.cohomologyAddEquiv A M N 0).symm

@[simp]
theorem quotientNullHomotopicAddEquivCohomology_mk (f : M →ᵈᵍ[A] N) :
    quotientNullHomotopicAddEquivCohomology A M N (QuotientAddGroup.mk f) =
      cohomology.mk _ 0 (DGModule.HOM.cocyclesAddEquiv A M N 0 (Cocycle.ofHom f)) := by
  rw [quotientNullHomotopicAddEquivCohomology, AddEquiv.trans_apply,
    quotientNullHomotopicAddEquiv_mk, AddEquiv.symm_apply_eq,
    DGModule.HOM.cohomologyAddEquiv_mk]

/-! ### Cohomology -/

/-- Homotopic morphisms induce the same map on cohomology. -/
theorem DGHomotopy.cohomology_map_eq {f g : M →ᵈᵍ[A] N} (h : DGHomotopy f g) (n : ℤ) :
    cohomology.map f n = cohomology.map g n := by
  ext z
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, cohomology.map_mk]
  rw [cohomology.mk_eq_mk_iff]
  refine ⟨h.hom z, ?_, ?_⟩
  · simpa [sub_eq_add_neg] using h.hom.map_mem (cocycles.mem_grading z)
  · simp [h.comm z, cocycles.d_eq_zero z]

theorem Homotopic.cohomology_map_eq {f g : M →ᵈᵍ[A] N} (h : Homotopic f g) (n : ℤ) :
    cohomology.map f n = cohomology.map g n :=
  h.some.cohomology_map_eq n

/-! ### Homotopy equivalences -/

variable (A M N) in
/-- A homotopy equivalence between dg modules: morphisms both ways whose composites are
homotopic to the identities. -/
structure DGHomotopyEquiv where
  /-- The morphism `M → N`. -/
  hom : M →ᵈᵍ[A] N
  /-- The morphism `N → M`. -/
  inv : N →ᵈᵍ[A] M
  /-- A homotopy `inv ∘ hom ≃ id`. -/
  homotopyHomInvId : DGHomotopy (inv.comp hom) DGModuleHom.id
  /-- A homotopy `hom ∘ inv ≃ id`. -/
  homotopyInvHomId : DGHomotopy (hom.comp inv) DGModuleHom.id

namespace DGHomotopyEquiv

variable (A M) in
/-- The identity homotopy equivalence. -/
@[simps]
def refl : DGHomotopyEquiv A M M where
  hom := DGModuleHom.id
  inv := DGModuleHom.id
  homotopyHomInvId := DGHomotopy.refl _
  homotopyInvHomId := DGHomotopy.refl _

/-- The inverse of a homotopy equivalence. -/
@[simps]
def symm (e : DGHomotopyEquiv A M N) : DGHomotopyEquiv A N M where
  hom := e.inv
  inv := e.hom
  homotopyHomInvId := e.homotopyInvHomId
  homotopyInvHomId := e.homotopyHomInvId

/-- The composition of homotopy equivalences. -/
@[simps]
def trans (e : DGHomotopyEquiv A M N) (e' : DGHomotopyEquiv A N P) : DGHomotopyEquiv A M P where
  hom := e'.hom.comp e.hom
  inv := e.inv.comp e'.inv
  homotopyHomInvId :=
    ((e'.homotopyHomInvId.compLeft e.hom).compRight e.inv).trans e.homotopyHomInvId
  homotopyInvHomId :=
    ((e.homotopyInvHomId.compLeft e'.inv).compRight e'.hom).trans e'.homotopyInvHomId

theorem cohomology_map_inv_hom (e : DGHomotopyEquiv A M N) (n : ℤ) (x : cohomology M n) :
    cohomology.map e.inv n (cohomology.map e.hom n x) = x := by
  rw [← cohomology.map_comp_apply, e.homotopyHomInvId.cohomology_map_eq, cohomology.map_id]
  rfl

theorem cohomology_map_hom_inv (e : DGHomotopyEquiv A M N) (n : ℤ) (x : cohomology N n) :
    cohomology.map e.hom n (cohomology.map e.inv n x) = x :=
  e.symm.cohomology_map_inv_hom n x

/-- A homotopy equivalence is a quasi-isomorphism. -/
theorem isQuasiIso_hom (e : DGHomotopyEquiv A M N) : e.hom.IsQuasiIso := fun n =>
  Function.bijective_iff_has_inverse.mpr
    ⟨cohomology.map e.inv n, e.cohomology_map_inv_hom n, e.cohomology_map_hom_inv n⟩

/-- The inverse of a homotopy equivalence is a quasi-isomorphism. -/
theorem isQuasiIso_inv (e : DGHomotopyEquiv A M N) : e.inv.IsQuasiIso :=
  e.symm.isQuasiIso_hom

end DGHomotopyEquiv

/-! ### Contractible dg modules -/

variable (A M) in
/-- A dg module `M` is contractible if its identity is null-homotopic. -/
def IsContractible : Prop := Homotopic (DGModuleHom.id : M →ᵈᵍ[A] M) 0

namespace IsContractible

/-- Every morphism out of a contractible dg module is null-homotopic. -/
theorem homotopic_zero_of_left (hM : IsContractible A M) (f : M →ᵈᵍ[A] N) : Homotopic f 0 :=
  (hM.comp_right f).trans (Homotopic.of_eq (DGModuleHom.comp_zero f))

/-- Every morphism into a contractible dg module is null-homotopic. -/
theorem homotopic_zero_of_right (hN : IsContractible A N) (f : M →ᵈᵍ[A] N) : Homotopic f 0 :=
  (hN.comp_left f).trans (Homotopic.of_eq (DGModuleHom.zero_comp f))

/-- A contractible dg module is acyclic: all its cohomology groups vanish. -/
theorem subsingleton_cohomology (hM : IsContractible A M) (n : ℤ) :
    Subsingleton (cohomology M n) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  have h := congrArg (fun φ => φ x) (hM.cohomology_map_eq n)
  simpa using h

theorem cohomology_eq_zero (hM : IsContractible A M) {n : ℤ} (x : cohomology M n) : x = 0 :=
  (hM.subsingleton_cohomology n).elim x 0

end IsContractible

end DG
