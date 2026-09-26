import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import DG.Algebra.Decompose
import DG.Module.PUnit
import DG.Module.Prod

/-!
# The category of dg modules

`DG.DGModuleCat.{v} A` is the category of bundled dg `A`-modules with carrier in `Type v`, for a
dg ring `A`. It is built in the style of Mathlib's `ModuleCat`: objects are structures carrying
a type with its instances, and morphisms are a one-field structure wrapping
`DG.DGModuleHom A M N` (`M →ᵈᵍ[A] N`), so that `DGModuleCat A` is a concrete category.

The category is preadditive (morphisms form abelian groups under pointwise addition), has a zero
object (the zero module), and has finite biproducts (`M × N` with its componentwise dg
structure, `DG.Prod.instDGAddCommGroup`).

For a dg `R`-algebra `A`, the category is `R`-linear: `R` acts on `M →ᵈᵍ[A] N` through the
structure map, `(r • f) m = algebraMap R A r • f m` (`DG.DGModuleHom.instModule`). This action
is `A`-linear because `algebraMap R A r` is central in `A`, and commutes with `d` because the
image of `R` is killed by `d` and sits in degree `0`.

## Implementation notes

The `R`-module structure on `M →ᵈᵍ[A] N` and the `Linear R` instance are declared with a low
priority: for `R = ℤ` they agree with the integer action of the abelian group structure only
propositionally, and Mathlib's `AddCommGroup.toIntModule` and `Linear.preadditiveIntLinear`
should be found first.
-/

open CategoryTheory CategoryTheory.Limits

universe v u

namespace DG

variable (A : Type u) [Ring A] [DGAddCommGroup A]

/-- The category of dg `A`-modules with carriers in `Type v`. -/
structure DGModuleCat where
  /-- The underlying type of a dg module. -/
  carrier : Type v
  [isAddCommGroup : AddCommGroup carrier]
  [isDGAddCommGroup : DGAddCommGroup carrier]
  [isModule : Module A carrier]
  [isDGModule : DGModule A carrier]

attribute [instance] DGModuleCat.isAddCommGroup DGModuleCat.isDGAddCommGroup
  DGModuleCat.isModule DGModuleCat.isDGModule

namespace DGModuleCat

instance : CoeSort (DGModuleCat.{v} A) (Type v) :=
  ⟨DGModuleCat.carrier⟩

attribute [coe] DGModuleCat.carrier

/-- The object of `DGModuleCat A` associated to a type with a dg `A`-module structure. -/
abbrev of (M : Type v) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M] :
    DGModuleCat.{v} A :=
  ⟨M⟩

theorem coe_of (M : Type v) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M] :
    (of A M : Type v) = M :=
  rfl

variable {A}

/-- The type of morphisms in `DGModuleCat A`. -/
@[ext]
structure Hom (M N : DGModuleCat.{v} A) where
  /-- The underlying morphism of dg modules. -/
  hom' : M →ᵈᵍ[A] N

instance category : Category.{v, max (v + 1) u} (DGModuleCat.{v} A) where
  Hom M N := Hom M N
  id _ := ⟨DGModuleHom.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance concreteCategory : ConcreteCategory (DGModuleCat.{v} A) (· →ᵈᵍ[A] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- The morphism of dg modules underlying a morphism in `DGModuleCat A`. -/
abbrev Hom.hom {M N : DGModuleCat.{v} A} (f : Hom M N) : M →ᵈᵍ[A] N :=
  ConcreteCategory.hom (C := DGModuleCat A) f

/-- A morphism of dg modules as a morphism in `DGModuleCat A`. -/
abbrev ofHom {M N : Type v} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
    [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N] (f : M →ᵈᵍ[A] N) :
    of A M ⟶ of A N :=
  ConcreteCategory.ofHom (C := DGModuleCat A) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (M N : DGModuleCat.{v} A) (f : Hom M N) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

@[simp]
theorem hom_id {M : DGModuleCat.{v} A} : (𝟙 M : M ⟶ M).hom = DGModuleHom.id := rfl

theorem id_apply (M : DGModuleCat.{v} A) (x : M) : (𝟙 M : M ⟶ M) x = x := rfl

@[simp]
theorem hom_comp {M N P : DGModuleCat.{v} A} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

theorem comp_apply {M N P : DGModuleCat.{v} A} (f : M ⟶ N) (g : N ⟶ P) (x : M) :
    (f ≫ g) x = g (f x) := rfl

@[ext]
theorem hom_ext {M N : DGModuleCat.{v} A} {f g : M ⟶ N} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

theorem hom_ext_apply {M N : DGModuleCat.{v} A} {f g : M ⟶ N} (h : ∀ x, f x = g x) : f = g :=
  hom_ext (DGModuleHom.ext h)

theorem hom_bijective {M N : DGModuleCat.{v} A} :
    Function.Bijective (Hom.hom : (M ⟶ N) → (M →ᵈᵍ[A] N)) where
  left f g h := by cases f; cases g; simpa using h
  right f := ⟨⟨f⟩, rfl⟩

theorem hom_injective {M N : DGModuleCat.{v} A} :
    Function.Injective (Hom.hom : (M ⟶ N) → (M →ᵈᵍ[A] N)) :=
  hom_bijective.injective

theorem hom_surjective {M N : DGModuleCat.{v} A} :
    Function.Surjective (Hom.hom : (M ⟶ N) → (M →ᵈᵍ[A] N)) :=
  hom_bijective.surjective

@[simp]
theorem hom_ofHom {M N : Type v} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
    [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N] (f : M →ᵈᵍ[A] N) :
    (ofHom f).hom = f := rfl

@[simp]
theorem ofHom_hom {M N : DGModuleCat.{v} A} (f : M ⟶ N) : ofHom f.hom = f := rfl

@[simp]
theorem ofHom_id {M : Type v} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M] :
    ofHom (DGModuleHom.id : M →ᵈᵍ[A] M) = 𝟙 (of A M) := rfl

@[simp]
theorem ofHom_comp {M N P : Type v} [AddCommGroup M] [DGAddCommGroup M] [Module A M]
    [DGModule A M] [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]
    [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]
    (f : M →ᵈᵍ[A] N) (g : N →ᵈᵍ[A] P) : ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

theorem ofHom_apply {M N : Type v} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
    [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N] (f : M →ᵈᵍ[A] N) (x : M) :
    ofHom f x = f x := rfl

/-- `DGModuleCat.Hom.hom` bundled as an equivalence. -/
def homEquiv {M N : DGModuleCat.{v} A} : (M ⟶ N) ≃ (M →ᵈᵍ[A] N) where
  toFun := Hom.hom
  invFun := ofHom
  left_inv _ := rfl
  right_inv _ := rfl

instance : Inhabited (DGModuleCat.{v} A) :=
  ⟨of A PUnit⟩

/-! ### Preadditive structure -/

section AddCommGroup

variable {M N : DGModuleCat.{v} A}

instance : Add (M ⟶ N) where
  add f g := ⟨f.hom + g.hom⟩

@[simp] theorem hom_add (f g : M ⟶ N) : (f + g).hom = f.hom + g.hom := rfl

instance : Zero (M ⟶ N) where
  zero := ⟨0⟩

@[simp] theorem hom_zero : (0 : M ⟶ N).hom = 0 := rfl

instance : SMul ℕ (M ⟶ N) where
  smul n f := ⟨n • f.hom⟩

@[simp] theorem hom_nsmul (n : ℕ) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl

instance : Neg (M ⟶ N) where
  neg f := ⟨-f.hom⟩

@[simp] theorem hom_neg (f : M ⟶ N) : (-f).hom = -f.hom := rfl

instance : Sub (M ⟶ N) where
  sub f g := ⟨f.hom - g.hom⟩

@[simp] theorem hom_sub (f g : M ⟶ N) : (f - g).hom = f.hom - g.hom := rfl

instance : SMul ℤ (M ⟶ N) where
  smul n f := ⟨n • f.hom⟩

@[simp] theorem hom_zsmul (n : ℤ) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl

instance : AddCommGroup (M ⟶ N) :=
  Function.Injective.addCommGroup (Hom.hom) hom_injective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

@[simp] theorem add_apply (f g : M ⟶ N) (x : M) : (f + g) x = f x + g x := rfl
@[simp] theorem zero_apply (x : M) : (0 : M ⟶ N) x = 0 := rfl
@[simp] theorem neg_apply (f : M ⟶ N) (x : M) : (-f) x = -f x := rfl
@[simp] theorem sub_apply (f g : M ⟶ N) (x : M) : (f - g) x = f x - g x := rfl

instance preadditive : Preadditive (DGModuleCat.{v} A) where
  add_comp _ _ _ _ _ _ := hom_ext_apply fun _ => by simp only [comp_apply, add_apply, map_add]
  comp_add _ _ _ _ _ _ := hom_ext_apply fun _ => by simp only [comp_apply, add_apply]

/-- `DGModuleCat.Hom.hom` bundled as an additive equivalence. -/
@[simps!]
def homAddEquiv : (M ⟶ N) ≃+ (M →ᵈᵍ[A] N) :=
  { homEquiv with map_add' := fun _ _ => rfl }

end AddCommGroup

/-! ### The zero object -/

theorem isZero_of_subsingleton (M : DGModuleCat.{v} A) [Subsingleton M] : IsZero M where
  unique_to N := ⟨⟨⟨0⟩, fun f => hom_ext_apply fun x => by
    rw [Subsingleton.elim x 0, map_zero, map_zero]⟩⟩
  unique_from N := ⟨⟨⟨0⟩, fun _ => hom_ext_apply fun _ => Subsingleton.elim _ _⟩⟩

instance hasZeroObject : HasZeroObject (DGModuleCat.{v} A) :=
  ⟨⟨of A PUnit, isZero_of_subsingleton _⟩⟩

/-! ### Finite biproducts -/

section Biproducts

variable (M N : DGModuleCat.{v} A)

/-- The binary product of two dg modules, computed on `M × N`. -/
def binaryProductLimitCone : LimitCone (pair M N) where
  cone := BinaryFan.mk (P := of A (M × N)) (ofHom (DGModuleHom.fst M N))
    (ofHom (DGModuleHom.snd M N))
  isLimit := BinaryFan.isLimitMk (fun s => ofHom (DGModuleHom.prod M N s.fst.hom s.snd.hom))
    (fun _ => rfl) (fun _ => rfl) fun s _ h₁ h₂ => hom_ext_apply fun x =>
      Prod.ext (congrArg (fun φ : s.pt ⟶ M => φ x) h₁) (congrArg (fun φ : s.pt ⟶ N => φ x) h₂)

instance : HasLimit (pair M N) :=
  HasLimit.mk (binaryProductLimitCone M N)

instance hasBinaryProducts : HasBinaryProducts (DGModuleCat.{v} A) :=
  hasBinaryProducts_of_hasLimit_pair _

instance hasFiniteProducts : HasFiniteProducts (DGModuleCat.{v} A) :=
  hasFiniteProducts_of_has_binary_and_terminal

instance hasBinaryBiproducts : HasBinaryBiproducts (DGModuleCat.{v} A) :=
  HasBinaryBiproducts.of_hasBinaryProducts

instance hasFiniteBiproducts : HasFiniteBiproducts (DGModuleCat.{v} A) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The biproduct in `DGModuleCat A` is the product `M × N` with its dg structure. -/
noncomputable def biprodIsoProd : (M ⊞ N : DGModuleCat.{v} A) ≅ of A (M × N) :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit M N) (binaryProductLimitCone M N).isLimit

@[simp]
theorem biprodIsoProd_inv_comp_fst :
    (biprodIsoProd M N).inv ≫ biprod.fst = ofHom (DGModuleHom.fst M N) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.left)

@[simp]
theorem biprodIsoProd_inv_comp_snd :
    (biprodIsoProd M N).inv ≫ biprod.snd = ofHom (DGModuleHom.snd M N) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.right)

end Biproducts

end DGModuleCat

/-! ### Isomorphisms -/

namespace DGModuleHom

variable {A} {M N : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N]

/-- The inverse of a bijective morphism of dg modules is a morphism of dg modules. -/
noncomputable def inverse (f : M →ᵈᵍ[A] N) (hf : Function.Bijective f) : N →ᵈᵍ[A] M where
  __ := (LinearEquiv.ofBijective f.toLinearMap hf).symm
  map_mem' := by
    intro n x hx
    refine mem_grading_of_injective f.toLinearMap.toAddMonoidHom (fun h => f.map_mem h)
      hf.injective ?_
    have h := (LinearEquiv.ofBijective f.toLinearMap hf).apply_symm_apply x
    rw [LinearEquiv.ofBijective_apply] at h
    change f ((LinearEquiv.ofBijective f.toLinearMap hf).symm x) ∈ _
    rwa [← toLinearMap_apply, h]
  map_d' x := by
    apply hf.injective
    have h := fun y => (LinearEquiv.ofBijective f.toLinearMap hf).apply_symm_apply y
    simp only [LinearEquiv.ofBijective_apply] at h
    change f ((LinearEquiv.ofBijective f.toLinearMap hf).symm (d x)) =
      f (d ((LinearEquiv.ofBijective f.toLinearMap hf).symm x))
    rw [map_d, ← toLinearMap_apply, ← toLinearMap_apply, h, h]

@[simp]
theorem apply_inverse_apply (f : M →ᵈᵍ[A] N) (hf : Function.Bijective f) (x : N) :
    f (f.inverse hf x) = x :=
  (LinearEquiv.ofBijective f.toLinearMap hf).apply_symm_apply x

@[simp]
theorem inverse_apply_apply (f : M →ᵈᵍ[A] N) (hf : Function.Bijective f) (x : M) :
    f.inverse hf (f x) = x :=
  hf.injective (apply_inverse_apply f hf (f x))

end DGModuleHom

namespace DGModuleCat

variable {A}

/-- A bijective morphism in `DGModuleCat A` is an isomorphism. -/
theorem isIso_of_bijective {M N : DGModuleCat.{v} A} (f : M ⟶ N) (hf : Function.Bijective f) :
    IsIso f :=
  ⟨⟨ofHom (f.hom.inverse hf), hom_ext_apply fun x => DGModuleHom.inverse_apply_apply f.hom hf x,
    hom_ext_apply fun x => DGModuleHom.apply_inverse_apply f.hom hf x⟩⟩

instance : (CategoryTheory.forget (DGModuleCat.{v} A)).ReflectsIsomorphisms where
  reflects f _ := isIso_of_bijective f
    ((isIso_iff_bijective ((CategoryTheory.forget (DGModuleCat.{v} A)).map f)).mp inferInstance)

end DGModuleCat

/-! ### `R`-linearity -/

namespace DGModuleHom

variable {A} {R : Type*} [CommRing R] [Algebra R A] [DGRing A] [DGAlgebra R A]
  {M N P : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]
  [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]

/-- The action of `R` on `M →ᵈᵍ[A] N` for a dg `R`-algebra `A`: `(r • f) m = algebraMap R A r • f m`.
See the implementation notes of `DG.Homotopy.ModuleCat` for the priority. -/
instance (priority := 100) instSMul : SMul R (M →ᵈᵍ[A] N) :=
  ⟨fun r f =>
    { toFun := fun m => algebraMap R A r • f m
      map_add' := fun m m' => by rw [map_add, smul_add]
      map_smul' := fun a m => by
        simp only [RingHom.id_apply, map_smul, smul_smul, Algebra.commutes]
      map_mem' := fun hm => by
        simpa using smul_mem_grading (algebraMap_mem_grading R (A := A) r) (f.map_mem hm)
      map_d' := fun m => by
        simp only [map_d, d_smul (algebraMap_mem_grading R (A := A) r), d_algebraMap, zero_smul,
          zero_add, koszulSign, Int.negOnePow_zero, one_smul] }⟩

@[simp]
theorem smul_apply (r : R) (f : M →ᵈᵍ[A] N) (m : M) : (r • f) m = algebraMap R A r • f m := rfl

/-- `M →ᵈᵍ[A] N` is an `R`-module for a dg `R`-algebra `A`. -/
instance (priority := 100) instModule : Module R (M →ᵈᵍ[A] N) where
  one_smul f := ext fun m => by simp
  mul_smul r s f := ext fun m => by simp [mul_smul]
  smul_zero r := ext fun m => by simp
  smul_add r f g := ext fun m => by simp
  add_smul r s f := ext fun m => by simp [add_smul]
  zero_smul f := ext fun m => by simp

omit [DGModule A N] in
theorem smul_comp (r : R) (g : N →ᵈᵍ[A] P) (f : M →ᵈᵍ[A] N) : (r • g).comp f = r • g.comp f :=
  rfl

theorem comp_smul (r : R) (g : N →ᵈᵍ[A] P) (f : M →ᵈᵍ[A] N) : g.comp (r • f) = r • g.comp f :=
  ext fun m => by simp

end DGModuleHom

namespace DGModuleCat

variable {A} {R : Type*} [CommRing R] [Algebra R A] [DGRing A] [DGAlgebra R A]

/-- The action of `R` on the morphisms of `DGModuleCat A` for a dg `R`-algebra `A`. -/
instance (priority := 100) instSMulHom {M N : DGModuleCat.{v} A} : SMul R (M ⟶ N) where
  smul r f := ⟨r • f.hom⟩

@[simp]
theorem hom_smul {M N : DGModuleCat.{v} A} (r : R) (f : M ⟶ N) : (r • f).hom = r • f.hom := rfl

@[simp]
theorem smul_apply {M N : DGModuleCat.{v} A} (r : R) (f : M ⟶ N) (x : M) :
    (r • f) x = algebraMap R A r • f x := rfl

/-- `DGModuleCat A` is an `R`-linear category for a dg `R`-algebra `A`. -/
instance (priority := 100) instLinear : Linear R (DGModuleCat.{v} A) where
  homModule M N := Function.Injective.module R
    { toFun := Hom.hom, map_zero' := hom_zero, map_add' := hom_add } hom_injective
    fun _ _ => rfl
  smul_comp _ _ _ _ _ _ := hom_ext_apply fun _ => by simp only [comp_apply, smul_apply, map_smul]
  comp_smul _ _ _ _ _ _ := hom_ext_apply fun _ => by simp only [comp_apply, smul_apply]

end DGModuleCat

end DG
