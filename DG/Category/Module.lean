import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import DG.Algebra.AddEquiv
import DG.Category.Functor
import DG.Module.PUnit
import DG.Module.Prod

/-!
# Dg modules over a dg category

Following `docs/CONVENTIONS.md`, a (left) dg module over a dg category `C` is a covariant dg
functor from `C` to dg abelian groups, described concretely: a family `M.obj X` of dg abelian
groups indexed by the objects of `C`, with actions `(X ⟶ Y) → M.obj X → M.obj Y`, written
`f • m`, which are biadditive, graded (`(X ⟶ Y)ⁱ • (M X)ʲ ⊆ (M Y)ⁱ⁺ʲ`), unital, associative in
the form `(f ≫ g) • m = g • (f • m)`, and satisfy the Leibniz rule
`d (f • m) = d f • m + (-1)^{|f|} • (f • d m)`.

For the one-object dg category `SingleObj A` of a dg ring these are exactly the left dg
`A`-modules (`DG.Category.Comparison`).

## Main definitions

* `DG.CatModule.{w} C`: dg modules over `C` with values in `Type w`, as a bundled structure. The
  action is `DG.CatModule.act`, with notation `f • m` (an `HSMul` instance).
* `DG.CatModule.Hom M N`: the morphisms, families of additive maps `M.obj X →+ N.obj X` of
  degree `0` commuting with the differentials and with the actions. `DG.CatModule.category`.
* `DG.CatModule.preadditive`, `DG.CatModule.hasZeroObject`, `DG.CatModule.hasFiniteBiproducts`:
  the category is preadditive with a zero object and finite biproducts (computed objectwise).
* `DG.CatModule.isIso_of_bijective`: a morphism which is objectwise bijective is an
  isomorphism.
* `DG.CatModule.precomp F : CatModule D ⥤ CatModule C`: restriction along a dg functor
  `F : C ⥤ D`, `(M ∘ F).obj X = M.obj (F.obj X)`.
-/

open CategoryTheory CategoryTheory.Limits

universe w w' v₁ v₂ u₁ u₂

namespace DG

/-- A left dg module over a category `C` with dg Hom groups (in the applications, a dg
category): dg abelian groups `obj X` for the objects `X` of `C`, with biadditive actions
`act f : obj X →+ obj Y` of the morphisms `f : X ⟶ Y`, which are graded, unital, associative
(`(f ≫ g) • m = g • (f • m)`), and satisfy the Leibniz rule
`d (f • m) = d f • m + (-1)^{|f|} • (f • d m)` for `f` homogeneous. -/
structure CatModule (C : Type u₁) [Category.{v₁} C] [Preadditive C]
    [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] where
  /-- The dg abelian group attached to an object. -/
  obj : C → Type w
  [isAddCommGroup : ∀ X, AddCommGroup (obj X)]
  [isDGAddCommGroup : ∀ X, DGAddCommGroup (obj X)]
  /-- The action of the morphisms of `C`, biadditive. -/
  act : ∀ {X Y : C}, (X ⟶ Y) →+ obj X →+ obj Y
  act_mem' : ∀ {X Y : C} {i j : ℤ} {f : X ⟶ Y} {m : obj X}, f ∈ grading i → m ∈ grading j →
    act f m ∈ grading (i + j)
  act_id' : ∀ (X : C) (m : obj X), act (𝟙 X) m = m
  act_comp' : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (m : obj X), act (f ≫ g) m = act g (act f m)
  d_act' : ∀ {X Y : C} {i : ℤ} {f : X ⟶ Y}, f ∈ grading i → ∀ m : obj X,
    d (act f m) = act (d f) m + koszulSign i • act f (d m)

attribute [instance] CatModule.isAddCommGroup CatModule.isDGAddCommGroup

namespace CatModule

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

section Action

variable (M : CatModule.{w} C)

/-- The action of the morphisms of `C` on a dg module, `f • m = M.act f m`. -/
instance instHSMul {X Y : C} : HSMul (X ⟶ Y) (M.obj X) (M.obj Y) :=
  ⟨fun f m => M.act f m⟩

variable {M}

theorem act_apply {X Y : C} (f : X ⟶ Y) (m : M.obj X) : M.act f m = f • m := rfl

theorem smul_mem_grading {X Y : C} {i j : ℤ} {f : X ⟶ Y} {m : M.obj X} (hf : f ∈ grading i)
    (hm : m ∈ grading j) : f • m ∈ grading (i + j) :=
  M.act_mem' hf hm

@[simp]
theorem id_smul {X : C} (m : M.obj X) : (𝟙 X) • m = m :=
  M.act_id' X m

theorem comp_smul {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (m : M.obj X) :
    (f ≫ g) • m = g • f • m :=
  M.act_comp' f g m

/-- The Leibniz rule for the action. -/
theorem d_smul {X Y : C} {i : ℤ} {f : X ⟶ Y} (hf : f ∈ grading i) (m : M.obj X) :
    d (f • m) = d f • m + koszulSign i • f • d m :=
  M.d_act' hf m

theorem d_smul_of_mem_zero {X Y : C} {f : X ⟶ Y} (hf : f ∈ grading 0) (m : M.obj X) :
    d (f • m) = d f • m + f • d m := by
  rw [d_smul hf, koszulSign_zero, one_smul]

/-- For a homogeneous cocycle `f` of degree `i`, `d (f • m) = (-1)^i • (f • d m)`. -/
theorem d_smul_of_d_eq_zero {X Y : C} {i : ℤ} {f : X ⟶ Y} (hf : f ∈ grading i) (hdf : d f = 0)
    (m : M.obj X) : d (f • m) = koszulSign i • f • d m := by
  rw [d_smul hf, hdf]
  change M.act 0 m + _ = _
  rw [map_zero, AddMonoidHom.zero_apply, zero_add]

@[simp]
theorem add_smul {X Y : C} (f g : X ⟶ Y) (m : M.obj X) : (f + g) • m = f • m + g • m := by
  change M.act (f + g) m = M.act f m + M.act g m
  rw [map_add, AddMonoidHom.add_apply]

@[simp]
theorem smul_add {X Y : C} (f : X ⟶ Y) (m m' : M.obj X) : f • (m + m') = f • m + f • m' :=
  map_add (M.act f) m m'

@[simp]
theorem zero_smul {X Y : C} (m : M.obj X) : (0 : X ⟶ Y) • m = (0 : M.obj Y) := by
  change M.act 0 m = 0
  rw [map_zero, AddMonoidHom.zero_apply]

@[simp]
theorem smul_zero {X Y : C} (f : X ⟶ Y) : f • (0 : M.obj X) = (0 : M.obj Y) :=
  map_zero (M.act f)

@[simp]
theorem neg_smul {X Y : C} (f : X ⟶ Y) (m : M.obj X) : (-f) • m = -(f • m) := by
  change M.act (-f) m = -M.act f m
  rw [map_neg, AddMonoidHom.neg_apply]

@[simp]
theorem smul_neg {X Y : C} (f : X ⟶ Y) (m : M.obj X) : f • (-m) = -(f • m) :=
  map_neg (M.act f) m

@[simp]
theorem sub_smul {X Y : C} (f g : X ⟶ Y) (m : M.obj X) : (f - g) • m = f • m - g • m := by
  rw [sub_eq_add_neg, add_smul, neg_smul, sub_eq_add_neg]

@[simp]
theorem smul_sub {X Y : C} (f : X ⟶ Y) (m m' : M.obj X) : f • (m - m') = f • m - f • m' :=
  map_sub (M.act f) m m'

@[simp]
theorem zsmul_smul {X Y : C} (n : ℤ) (f : X ⟶ Y) (m : M.obj X) : (n • f) • m = n • f • m := by
  change M.act (n • f) m = n • M.act f m
  rw [map_zsmul, AddMonoidHom.smul_apply]

@[simp]
theorem smul_zsmul {X Y : C} (f : X ⟶ Y) (n : ℤ) (m : M.obj X) : f • (n • m) = n • f • m :=
  map_zsmul (M.act f) n m

@[simp]
theorem units_smul_smul {X Y : C} (u : ℤˣ) (f : X ⟶ Y) (m : M.obj X) :
    (u • f) • m = u • f • m := by
  rw [Units.smul_def, Units.smul_def, zsmul_smul]

@[simp]
theorem smul_units_smul {X Y : C} (f : X ⟶ Y) (u : ℤˣ) (m : M.obj X) :
    f • (u • m) = u • f • m := by
  rw [Units.smul_def, Units.smul_def, smul_zsmul]

/-- If `m` is a cocycle then `d (f • m) = d f • m` for every `f`. -/
theorem d_smul_of_d_eq_zero_right {X Y : C} {m : M.obj X} (hm : d m = 0) (f : X ⟶ Y) :
    d (f • m) = d f • m := by
  induction f using induction_on with
  | h_zero =>
    change d (M.act 0 m) = M.act (d 0) m
    rw [d_zero, map_zero, AddMonoidHom.zero_apply, d_zero]
  | h_homogeneous f => rw [d_smul f.2, hm, smul_zero, _root_.smul_zero, add_zero]
  | h_add f f' hf hf' =>
    change d (M.act (f + f') m) = M.act (d (f + f')) m
    rw [d_add, map_add, map_add, AddMonoidHom.add_apply, AddMonoidHom.add_apply, d_add]
    exact congrArg₂ (· + ·) hf hf'

theorem sum_smul {X Y : C} {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) (m : M.obj X) :
    (∑ i ∈ s, f i) • m = ∑ i ∈ s, f i • m := by
  change M.act (∑ i ∈ s, f i) m = ∑ i ∈ s, M.act (f i) m
  rw [map_sum, AddMonoidHom.finset_sum_apply]

theorem smul_sum {X Y : C} {ι : Type*} (s : Finset ι) (f : X ⟶ Y) (m : ι → M.obj X) :
    f • (∑ i ∈ s, m i) = ∑ i ∈ s, f • m i :=
  map_sum (M.act f) m s

end Action

/-- A morphism of dg modules over `C`: a family of additive maps `M.obj X →+ N.obj X` of
degree `0` commuting with the differentials and with the actions. -/
structure Hom (M N : CatModule.{w} C) where
  /-- The component at an object. -/
  app : ∀ X : C, M.obj X →+ N.obj X
  map_mem' : ∀ {X : C} {n : ℤ} {m : M.obj X}, m ∈ grading n → app X m ∈ grading n
  map_d' : ∀ {X : C} (m : M.obj X), app X (d m) = d (app X m)
  map_smul' : ∀ {X Y : C} (f : X ⟶ Y) (m : M.obj X), app Y (f • m) = f • app X m

namespace Hom

variable {M N : CatModule.{w} C}

@[ext]
theorem ext {φ ψ : Hom M N} (h : ∀ X m, φ.app X m = ψ.app X m) : φ = ψ := by
  obtain ⟨φ, _, _, _⟩ := φ
  obtain ⟨ψ, _, _, _⟩ := ψ
  congr
  funext X
  exact AddMonoidHom.ext (h X)

variable (φ : Hom M N)

theorem map_mem {X : C} {n : ℤ} {m : M.obj X} (hm : m ∈ grading n) : φ.app X m ∈ grading n :=
  φ.map_mem' hm

@[simp]
theorem map_d {X : C} (m : M.obj X) : φ.app X (d m) = d (φ.app X m) :=
  φ.map_d' m

@[simp]
theorem map_smul {X Y : C} (f : X ⟶ Y) (m : M.obj X) : φ.app Y (f • m) = f • φ.app X m :=
  φ.map_smul' f m

/-- The identity morphism. -/
def id (M : CatModule.{w} C) : Hom M M where
  app _ := AddMonoidHom.id _
  map_mem' hm := hm
  map_d' _ := rfl
  map_smul' _ _ := rfl

/-- Composition of morphisms. -/
def comp {P : CatModule.{w} C} (φ : Hom M N) (ψ : Hom N P) : Hom M P where
  app X := (ψ.app X).comp (φ.app X)
  map_mem' hm := ψ.map_mem (φ.map_mem hm)
  map_d' m := by simp
  map_smul' f m := by simp

end Hom

instance category : Category.{max u₁ w} (CatModule.{w} C) where
  Hom M N := Hom M N
  id M := Hom.id M
  comp φ ψ := φ.comp ψ

section HomLemmas

variable {M N P : CatModule.{w} C}

@[ext]
theorem hom_ext {φ ψ : M ⟶ N} (h : ∀ X m, φ.app X m = ψ.app X m) : φ = ψ :=
  Hom.ext h

@[simp]
theorem id_app (M : CatModule.{w} C) (X : C) (m : M.obj X) : (𝟙 M : M ⟶ M).app X m = m := rfl

@[simp]
theorem comp_app (φ : M ⟶ N) (ψ : N ⟶ P) (X : C) (m : M.obj X) :
    (φ ≫ ψ).app X m = ψ.app X (φ.app X m) := rfl

theorem hom_injective : Function.Injective (Hom.app : (M ⟶ N) → ∀ X, M.obj X →+ N.obj X) :=
  fun _ _ h => hom_ext fun X m => congrArg (fun φ => φ X m) h

end HomLemmas

/-! ### Preadditive structure -/

section Preadditive

variable {M N : CatModule.{w} C}

instance : Zero (M ⟶ N) :=
  ⟨{ app := fun _ => 0
     map_mem' := fun _ => zero_mem _
     map_d' := fun _ => by simp
     map_smul' := fun _ _ => by simp }⟩

instance : Add (M ⟶ N) :=
  ⟨fun φ ψ =>
    { app := fun X => φ.app X + ψ.app X
      map_mem' := fun hm => add_mem (φ.map_mem hm) (ψ.map_mem hm)
      map_d' := fun _ => by simp [d_add]
      map_smul' := fun _ _ => by simp }⟩

instance : Neg (M ⟶ N) :=
  ⟨fun φ =>
    { app := fun X => -φ.app X
      map_mem' := fun hm => neg_mem (φ.map_mem hm)
      map_d' := fun _ => by simp [d_neg]
      map_smul' := fun _ _ => by simp }⟩

instance : Sub (M ⟶ N) :=
  ⟨fun φ ψ =>
    { app := fun X => φ.app X - ψ.app X
      map_mem' := fun hm => sub_mem (φ.map_mem hm) (ψ.map_mem hm)
      map_d' := fun _ => by simp [d_sub]
      map_smul' := fun _ _ => by simp }⟩

instance : SMul ℕ (M ⟶ N) :=
  ⟨fun n φ =>
    { app := fun X => n • φ.app X
      map_mem' := fun hm => nsmul_mem (φ.map_mem hm) n
      map_d' := fun _ => by simp [d_nsmul]
      map_smul' := fun _ _ => by simp [← natCast_zsmul] }⟩

instance : SMul ℤ (M ⟶ N) :=
  ⟨fun n φ =>
    { app := fun X => n • φ.app X
      map_mem' := fun hm => zsmul_mem (φ.map_mem hm) n
      map_d' := fun _ => by simp [d_zsmul]
      map_smul' := fun _ _ => by simp }⟩

@[simp] theorem zero_app (X : C) (m : M.obj X) : (0 : M ⟶ N).app X m = 0 := rfl
@[simp] theorem add_app (φ ψ : M ⟶ N) (X : C) (m : M.obj X) :
    (φ + ψ).app X m = φ.app X m + ψ.app X m := rfl
@[simp] theorem neg_app (φ : M ⟶ N) (X : C) (m : M.obj X) : (-φ).app X m = -φ.app X m := rfl
@[simp] theorem sub_app (φ ψ : M ⟶ N) (X : C) (m : M.obj X) :
    (φ - ψ).app X m = φ.app X m - ψ.app X m := rfl
@[simp] theorem nsmul_app (n : ℕ) (φ : M ⟶ N) (X : C) (m : M.obj X) :
    (n • φ).app X m = n • φ.app X m := rfl
@[simp] theorem zsmul_app (n : ℤ) (φ : M ⟶ N) (X : C) (m : M.obj X) :
    (n • φ).app X m = n • φ.app X m := rfl

instance : AddCommGroup (M ⟶ N) :=
  Function.Injective.addCommGroup Hom.app hom_injective rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance preadditive : Preadditive (CatModule.{w} C) where
  add_comp _ _ _ _ _ _ := hom_ext fun _ _ => by simp
  comp_add _ _ _ _ _ _ := hom_ext fun _ _ => by simp

end Preadditive

/-! ### Isomorphisms -/

section Iso

variable {M N : CatModule.{w} C}

/-- An isomorphism of dg modules from objectwise additive equivalences of degree `0` commuting
with the differentials and the actions. -/
@[simps]
def isoMk (e : ∀ X, M.obj X ≃+ N.obj X)
    (he : ∀ {X : C} {n : ℤ} {m : M.obj X}, e X m ∈ grading n ↔ m ∈ grading n)
    (hd : ∀ {X : C} (m : M.obj X), e X (d m) = d (e X m))
    (hs : ∀ {X Y : C} (f : X ⟶ Y) (m : M.obj X), e Y (f • m) = f • e X m) : M ≅ N where
  hom :=
    { app := fun X => (e X).toAddMonoidHom
      map_mem' := fun hm => he.mpr hm
      map_d' := hd
      map_smul' := hs }
  inv :=
    { app := fun X => (e X).symm.toAddMonoidHom
      map_mem' := fun {X n m} hm => by
        rw [← he]
        simpa using hm
      map_d' := fun {X} m => (e X).injective (by simp [hd])
      map_smul' := fun {X Y} f m => (e Y).injective (by simp [hs]) }
  hom_inv_id := hom_ext fun _ _ => by simp
  inv_hom_id := hom_ext fun _ _ => by simp

/-- A morphism which is bijective at every object is an isomorphism. -/
theorem isIso_of_bijective (φ : M ⟶ N) (hφ : ∀ X, Function.Bijective (φ.app X)) : IsIso φ := by
  let e : ∀ X, M.obj X ≃+ N.obj X := fun X => AddEquiv.ofBijective (φ.app X) (hφ X)
  have he : ∀ {X : C} {n : ℤ} {m : M.obj X}, e X m ∈ grading n ↔ m ∈ grading n :=
    fun {X n m} => ⟨fun h => mem_grading_of_injective (φ.app X) (fun h => φ.map_mem h)
      (hφ X).injective h, fun h => φ.map_mem h⟩
  exact (isoMk e he (fun m => φ.map_d m) (fun f m => φ.map_smul f m)).isIso_hom

/-- A morphism of dg modules is an isomorphism if and only if it is bijective at every
object. -/
theorem isIso_iff_bijective (φ : M ⟶ N) : IsIso φ ↔ ∀ X, Function.Bijective (φ.app X) := by
  refine ⟨fun _ X => ⟨fun a b h => ?_, fun b => ⟨(inv φ).app X b, ?_⟩⟩, isIso_of_bijective φ⟩
  · have := congrArg ((inv φ).app X) h
    rwa [← comp_app, ← comp_app, IsIso.hom_inv_id] at this
  · rw [← comp_app, IsIso.inv_hom_id, id_app]

end Iso

/-! ### The zero object -/

section Zero

/-- The zero dg module. -/
@[simps]
def zero : CatModule.{w} C where
  obj _ := PUnit
  act := 0
  act_mem' _ _ := trivial
  act_id' _ _ := rfl
  act_comp' _ _ _ := rfl
  d_act' _ _ := rfl

theorem isZero_of_subsingleton (M : CatModule.{w} C) [∀ X, Subsingleton (M.obj X)] :
    IsZero M where
  unique_to N := ⟨⟨⟨0⟩, fun φ => hom_ext fun X m => by
    rw [Subsingleton.elim m 0, map_zero, map_zero]⟩⟩
  unique_from N := ⟨⟨⟨0⟩, fun _ => hom_ext fun _ _ => Subsingleton.elim _ _⟩⟩

instance : ∀ X : C, Subsingleton ((zero.{w} (C := C)).obj X) :=
  fun _ => inferInstanceAs (Subsingleton PUnit)

theorem isZero_zero : IsZero (zero.{w} (C := C)) :=
  isZero_of_subsingleton _

instance hasZeroObject : HasZeroObject (CatModule.{w} C) :=
  ⟨⟨zero, isZero_zero⟩⟩

end Zero

/-! ### Finite biproducts -/

section Biproducts

variable (M N : CatModule.{w} C)

/-- The objectwise product of two dg modules. -/
def prod : CatModule.{w} C where
  obj X := M.obj X × N.obj X
  act := AddMonoidHom.mk' (fun f => AddMonoidHom.prodMap (M.act f) (N.act f)) fun f g => by
    ext <;> simp
  act_mem' hf hm := Prod.mem_grading.mpr
    ⟨smul_mem_grading hf (Prod.mem_grading.mp hm).1, smul_mem_grading hf (Prod.mem_grading.mp hm).2⟩
  act_id' _ _ := Prod.ext (id_smul _) (id_smul _)
  act_comp' _ _ _ := Prod.ext (comp_smul _ _ _) (comp_smul _ _ _)
  d_act' hf m := Prod.ext (d_smul (M := M) hf m.1) (d_smul (M := N) hf m.2)

@[simp]
theorem prod_smul_fst {X Y : C} (f : X ⟶ Y) (m : (prod M N).obj X) : (f • m).1 = f • m.1 := rfl

@[simp]
theorem prod_smul_snd {X Y : C} (f : X ⟶ Y) (m : (prod M N).obj X) : (f • m).2 = f • m.2 := rfl

/-- The first projection out of the product. -/
@[simps]
def fst : prod M N ⟶ M where
  app _ := AddMonoidHom.fst _ _
  map_mem' hm := hm.1
  map_d' _ := rfl
  map_smul' _ _ := rfl

/-- The second projection out of the product. -/
@[simps]
def snd : prod M N ⟶ N where
  app _ := AddMonoidHom.snd _ _
  map_mem' hm := hm.2
  map_d' _ := rfl
  map_smul' _ _ := rfl

variable {M N} in
/-- The morphism into the product given by two morphisms. -/
@[simps]
def lift {P : CatModule.{w} C} (φ : P ⟶ M) (ψ : P ⟶ N) : P ⟶ prod M N where
  app X := AddMonoidHom.prod (φ.app X) (ψ.app X)
  map_mem' hm := ⟨φ.map_mem hm, ψ.map_mem hm⟩
  map_d' m := Prod.ext (φ.map_d m) (ψ.map_d m)
  map_smul' f m := Prod.ext (φ.map_smul f m) (ψ.map_smul f m)

/-- The binary product of two dg modules, computed objectwise. -/
def binaryProductLimitCone : LimitCone (pair M N) where
  cone := BinaryFan.mk (fst M N) (snd M N)
  isLimit := BinaryFan.isLimitMk (fun s => lift s.fst s.snd) (fun _ => rfl) (fun _ => rfl)
    fun s _ h₁ h₂ => hom_ext fun X x =>
      Prod.ext (congrArg (fun φ : s.pt ⟶ M => φ.app X x) h₁)
        (congrArg (fun φ : s.pt ⟶ N => φ.app X x) h₂)

instance : HasLimit (pair M N) :=
  HasLimit.mk (binaryProductLimitCone M N)

instance hasBinaryProducts : HasBinaryProducts (CatModule.{w} C) :=
  hasBinaryProducts_of_hasLimit_pair _

instance hasFiniteProducts : HasFiniteProducts (CatModule.{w} C) :=
  hasFiniteProducts_of_has_binary_and_terminal

instance hasBinaryBiproducts : HasBinaryBiproducts (CatModule.{w} C) :=
  HasBinaryBiproducts.of_hasBinaryProducts

instance hasFiniteBiproducts : HasFiniteBiproducts (CatModule.{w} C) :=
  HasFiniteBiproducts.of_hasFiniteProducts

end Biproducts

/-! ### Restriction along dg functors -/

section Precomp

variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [∀ X Y : D, DGAddCommGroup (X ⟶ Y)]
  (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]

/-- The restriction of a dg module over `D` along a dg functor `F : C ⥤ D`:
`X ↦ M.obj (F.obj X)`, with `f • m = F.map f • m`. -/
@[simps]
def precompObj (M : CatModule.{w} D) : CatModule.{w} C where
  obj X := M.obj (F.obj X)
  act := M.act.comp F.mapAddHom
  act_mem' hf hm := smul_mem_grading (F.map_mem_grading hf) hm
  act_id' X m := by
    change F.map (𝟙 X) • m = m
    rw [F.map_id, id_smul]
  act_comp' f g m := by
    change F.map (f ≫ g) • m = F.map g • F.map f • m
    rw [F.map_comp, comp_smul]
  d_act' {X Y i f} hf m := by
    change d (F.map f • m) = F.map (d f) • m + koszulSign i • F.map f • d m
    rw [F.map_d, d_smul (F.map_mem_grading hf)]

theorem precompObj_smul (M : CatModule.{w} D) {X Y : C} (f : X ⟶ Y)
    (m : (precompObj F M).obj X) : f • m = M.act (F.map f) m :=
  rfl

/-- Restriction along a dg functor `F : C ⥤ D`, as a functor
`CatModule D ⥤ CatModule C`. -/
@[simps]
def precomp : CatModule.{w} D ⥤ CatModule.{w} C where
  obj M := precompObj F M
  map φ :=
    { app := fun X => φ.app (F.obj X)
      map_mem' := fun hm => φ.map_mem hm
      map_d' := fun m => φ.map_d m
      map_smul' := fun f m => φ.map_smul (F.map f) m }

instance : (precomp.{w} F).Additive where

end Precomp

end CatModule

end DG
