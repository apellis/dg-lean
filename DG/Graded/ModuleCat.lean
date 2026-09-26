import DG.Graded.Basic
import Mathlib.Algebra.Module.GradedModule
import Mathlib.CategoryTheory.Iso

/-!
# The category of graded modules over a graded ring

For an additive monoid `ι` and a ring `A` with a family `𝒜 : ι → τ` of additive subgroups (in
practice a `GradedRing`), `DG.GradedModuleCat 𝒜` is the category whose objects are `A`-modules
`M` with an internal grading `M = ⨁ i, Mⁱ` (a `DirectSum.Decomposition`) compatible with the
action (`SetLike.GradedSMul 𝒜`, i.e. `𝒜 i • Mʲ ⊆ Mⁱ⁺ʲ`), and whose morphisms are the
`A`-linear maps of degree `0`. It is used for `ι = ℤ` and `ι = ZMod 2` in the regrading
equivalences (`DG.Graded.RegradingModuleCat`).

## Main definitions

* `DG.GradedModuleCat 𝒜`, `DG.GradedModuleCat.of`, and the morphisms `DG.GradedModuleCat.Hom`
  (fields `hom : M →ₗ[A] N` and degree preservation).
* `DG.GradedModuleCat.isoMk`: an isomorphism from a linear equivalence preserving degrees.
* `DG.GradedModuleCat.hom_ext_homogeneous`: morphisms agreeing on homogeneous elements are equal.
* `DG.GradedModuleCat.WithDifferential P`: graded modules with an additive endomorphism `d`
  satisfying a predicate `P`, and morphisms commuting with `d`; used for categories of dg modules
  over `ℤ`- and `ℤ/2`-graded dg rings.
* `DG.map_smul_of_homogeneous`: an additive map commutes with the action as soon as it commutes
  with the action of homogeneous elements on homogeneous elements.
-/

universe v u w

namespace DG

open CategoryTheory DirectSum

/-- Extensionality for the action on graded objects: an additive map commutes with the action of
`A` if it commutes with the action of homogeneous elements on homogeneous elements. -/
theorem map_smul_of_homogeneous {ι κ A M N τ σ : Type*} [DecidableEq ι] [DecidableEq κ]
    [Ring A] [SetLike τ A] [AddSubgroupClass τ A] (𝒜 : ι → τ) [Decomposition 𝒜]
    [AddCommGroup M] [Module A M] [SetLike σ M] [AddSubgroupClass σ M] (ℳ : κ → σ)
    [Decomposition ℳ] [AddCommGroup N] [Module A N] (f : M →+ N)
    (h : ∀ (i : ι) (j : κ) (a : A) (m : M), a ∈ 𝒜 i → m ∈ ℳ j → f (a • m) = a • f m)
    (a : A) (m : M) : f (a • m) = a • f m := by
  induction a using Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous a =>
    induction m using Decomposition.inductionOn ℳ with
    | zero => simp
    | homogeneous m => exact h _ _ _ _ a.2 m.2
    | add m m' hm hm' => rw [smul_add, map_add, hm, hm', map_add, smul_add]
  | add a a' ha ha' => rw [add_smul, map_add, ha, ha', add_smul]

variable {ι : Type w} [DecidableEq ι] [AddMonoid ι] {A : Type u} [Ring A] {τ : Type*}
  [SetLike τ A] (𝒜 : ι → τ)

/-- The category of `ι`-graded modules over the `ι`-graded ring `(A, 𝒜)`: an object is an
`A`-module `M` with an internal grading `M = ⨁ i, Mⁱ` (a `DirectSum.Decomposition`) such that
`𝒜 i • Mʲ ⊆ Mⁱ⁺ʲ`; morphisms are the `A`-linear maps of degree `0`
(`DG.GradedModuleCat.Hom`). -/
structure GradedModuleCat where
  /-- The underlying type. -/
  carrier : Type v
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module A carrier]
  /-- The grading. -/
  grading : ι → AddSubgroup carrier
  [decomposition : Decomposition grading]
  [gradedSMul : SetLike.GradedSMul 𝒜 grading]

attribute [instance] GradedModuleCat.isAddCommGroup GradedModuleCat.isModule
  GradedModuleCat.decomposition GradedModuleCat.gradedSMul

namespace GradedModuleCat

instance : CoeSort (GradedModuleCat.{v} 𝒜) (Type v) := ⟨GradedModuleCat.carrier⟩

attribute [coe] GradedModuleCat.carrier

/-- The object of `GradedModuleCat 𝒜` given by a graded module. -/
abbrev of (M : Type v) [AddCommGroup M] [Module A M] (ℳ : ι → AddSubgroup M)
    [Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ] : GradedModuleCat.{v} 𝒜 :=
  ⟨M, ℳ⟩

variable {𝒜}

/-- A morphism of graded modules: an `A`-linear map of degree `0`. -/
@[ext]
structure Hom (M N : GradedModuleCat.{v} 𝒜) where
  /-- The underlying linear map. -/
  hom : M →ₗ[A] N
  map_mem' : ∀ {i : ι} {m : M}, m ∈ M.grading i → hom m ∈ N.grading i

instance category : Category.{v} (GradedModuleCat.{v} 𝒜) where
  Hom M N := Hom M N
  id M := ⟨LinearMap.id, id⟩
  comp f g := ⟨g.hom.comp f.hom, fun h => g.map_mem' (f.map_mem' h)⟩

variable {M N P : GradedModuleCat.{v} 𝒜}

theorem Hom.map_mem (f : Hom M N) {i : ι} {m : M} (hm : m ∈ M.grading i) :
    f.hom m ∈ N.grading i :=
  f.map_mem' hm

@[ext]
theorem hom_ext {f g : M ⟶ N} (h : f.hom = g.hom) : f = g := Hom.ext h

@[simp]
theorem hom_id : (𝟙 M : M ⟶ M).hom = LinearMap.id := rfl

@[simp]
theorem hom_comp (f : M ⟶ N) (g : N ⟶ P) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/-- Two morphisms out of a graded module agreeing on homogeneous elements are equal. -/
theorem hom_ext_homogeneous {f g : M ⟶ N}
    (h : ∀ (i : ι) (m : M), m ∈ M.grading i → f.hom m = g.hom m) : f = g := by
  refine hom_ext (LinearMap.ext fun m => ?_)
  induction m using Decomposition.inductionOn M.grading with
  | zero => simp
  | homogeneous m => exact h _ _ m.2
  | add m m' hm hm' => rw [map_add, map_add, hm, hm']

/-- The restriction of a morphism to the degree-`i` pieces. -/
def Hom.restrict (f : Hom M N) (i : ι) : M.grading i →+ N.grading i :=
  (f.hom.toAddMonoidHom.comp (M.grading i).subtype).codRestrict _ fun m => f.map_mem m.2

@[simp]
theorem Hom.coe_restrict_apply (f : Hom M N) (i : ι) (m : M.grading i) :
    (f.restrict i m : N) = f.hom m := rfl

/-- An isomorphism of graded modules from a linear equivalence preserving the gradings. -/
def isoMk (e : M ≃ₗ[A] N) (he : ∀ (i : ι) (m : M), m ∈ M.grading i → e m ∈ N.grading i)
    (he' : ∀ (i : ι) (n : N), n ∈ N.grading i → e.symm n ∈ M.grading i) : M ≅ N where
  hom := ⟨e.toLinearMap, he _ _⟩
  inv := ⟨e.symm.toLinearMap, he' _ _⟩
  hom_inv_id := hom_ext (LinearMap.ext e.symm_apply_apply)
  inv_hom_id := hom_ext (LinearMap.ext e.apply_symm_apply)

@[simp]
theorem isoMk_hom_hom (e : M ≃ₗ[A] N) (he he') : (isoMk e he he').hom.hom = e.toLinearMap := rfl

@[simp]
theorem isoMk_inv_hom (e : M ≃ₗ[A] N) (he he') : (isoMk e he he').inv.hom = e.symm.toLinearMap :=
  rfl

/-! ### Graded modules with a differential -/

/-- The category of graded modules `M` equipped with an additive endomorphism `d` satisfying a
predicate `P M d` (for instance, being a differential satisfying a Leibniz rule); morphisms are
the morphisms of graded modules commuting with `d`. -/
structure WithDifferential (P : ∀ M : GradedModuleCat.{v} 𝒜, (M →+ M) → Prop) where
  /-- The underlying graded module. -/
  obj : GradedModuleCat.{v} 𝒜
  /-- The differential. -/
  d : obj →+ obj
  prop : P obj d

namespace WithDifferential

variable {P : ∀ M : GradedModuleCat.{v} 𝒜, (M →+ M) → Prop}

/-- A morphism in `WithDifferential P`: a morphism of graded modules commuting with `d`. -/
@[ext]
structure Hom (X Y : WithDifferential P) where
  /-- The underlying morphism of graded modules. -/
  hom : X.obj ⟶ Y.obj
  comm : ∀ x, hom.hom (X.d x) = Y.d (hom.hom x)

instance category : Category.{v} (WithDifferential P) where
  Hom X Y := Hom X Y
  id X := ⟨𝟙 X.obj, fun _ => rfl⟩
  comp f g := ⟨f.hom ≫ g.hom, fun x => by
    change g.hom.hom (f.hom.hom _) = _
    rw [f.comm, g.comm]; rfl⟩

variable {X Y : WithDifferential P}

@[ext]
theorem hom_ext {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g := Hom.ext h

@[simp]
theorem id_hom : (𝟙 X : X ⟶ X).hom = 𝟙 X.obj := rfl

@[simp]
theorem comp_hom {Z : WithDifferential P} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

theorem Hom.comm' (f : X ⟶ Y) (x : X.obj) : f.hom.hom (X.d x) = Y.d (f.hom.hom x) := f.comm x

/-- An isomorphism in `WithDifferential P` from an isomorphism of graded modules commuting with
the differentials. -/
def isoMk (e : X.obj ≅ Y.obj) (he : ∀ x, e.hom.hom (X.d x) = Y.d (e.hom.hom x)) : X ≅ Y where
  hom := ⟨e.hom, he⟩
  inv := ⟨e.inv, fun y => by
    have h : ∀ z : Y.obj, e.hom.hom (e.inv.hom z) = z := fun z => by
      rw [← LinearMap.comp_apply, ← hom_comp, e.inv_hom_id]; rfl
    have hinj : Function.Injective e.hom.hom := fun a b hab => by
      have : ∀ z : X.obj, e.inv.hom (e.hom.hom z) = z := fun z => by
        rw [← LinearMap.comp_apply, ← hom_comp, e.hom_inv_id]; rfl
      rw [← this a, hab, this b]
    apply hinj
    rw [h, he, h]⟩
  hom_inv_id := hom_ext e.hom_inv_id
  inv_hom_id := hom_ext e.inv_hom_id

@[simp]
theorem isoMk_hom_hom (e : X.obj ≅ Y.obj) (he) : (isoMk e he).hom.hom = e.hom := rfl

@[simp]
theorem isoMk_inv_hom (e : X.obj ≅ Y.obj) (he) : (isoMk e he).inv.hom = e.inv := rfl

end WithDifferential

end GradedModuleCat

end DG
