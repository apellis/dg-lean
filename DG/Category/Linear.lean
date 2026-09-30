import Mathlib.CategoryTheory.Linear.Basic
import DG.Category.SingleObj

/-!
# Dg categories over a commutative ring

Let `R` be a commutative ring. A dg category over `R` is a dg category `C` which is `R`-linear
(Mathlib's `CategoryTheory.Linear R C`) in such a way that the homogeneous components of the
Hom groups are `R`-submodules and the differentials are `R`-linear. This is the `Prop`-valued
mixin `DG.DGLinear R C`, on top of `[Linear R C]`, in the same way as `DG.DGAlgebra R A` sits on
top of `[Algebra R A]`.

## Main definitions and results

* `DG.DGLinear R C`, with `DG.DGLinear.smul_mem` and `DG.DGLinear.d_smul`.
* `DG.DGLinear.smul_id_mem`, `DG.DGLinear.d_smul_id`: the scalar endomorphisms `r • 𝟙 X` are
  degree-`0` cocycles; they are central (`DG.DGLinear.smul_id_comp`,
  `DG.DGLinear.comp_smul_id`).
* `DG.DGLinear.int`: every dg category is a dg category over `ℤ` (not an instance).
* `DG.SingleObj.linear`, `DG.SingleObj.dgLinear`: for a dg `R`-algebra `A`, the one-object
  category `SingleObj A` is an `R`-linear category and a dg category over `R`.

## Implementation notes

`DG.SingleObj.linear` has low priority: for `R = ℤ` it agrees with Mathlib's
`CategoryTheory.Linear.preadditiveIntLinear` only propositionally.
-/

open CategoryTheory

universe v u

namespace DG

/-- A dg category over a commutative ring `R`: the homogeneous components of the Hom groups of
the `R`-linear category `C` are `R`-submodules, and the differentials are `R`-linear. -/
class DGLinear (R : Type*) [CommRing R] (C : Type u) [Category.{v} C] [Preadditive C]
    [Linear R C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] : Prop where
  smul_mem' : ∀ {X Y : C} {n : ℤ} (r : R) {f : X ⟶ Y}, f ∈ grading n → r • f ∈ grading n
  d_smul' : ∀ {X Y : C} (r : R) (f : X ⟶ Y), d (r • f) = r • d f

namespace DGLinear

variable {R : Type*} [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGLinear R C]

theorem smul_mem {X Y : C} {n : ℤ} (r : R) {f : X ⟶ Y} (hf : f ∈ grading n) :
    r • f ∈ grading n :=
  DGLinear.smul_mem' r hf

/-- The differentials of a dg category over `R` are `R`-linear. -/
@[simp]
theorem d_smul {X Y : C} (r : R) (f : X ⟶ Y) : d (r • f) = r • d f :=
  DGLinear.d_smul' r f

variable (R) in
/-- The homogeneous component of degree `n` of a Hom group, as an `R`-submodule. -/
def gradingSubmodule (X Y : C) (n : ℤ) :
    Submodule R (X ⟶ Y) where
  __ := grading (M := X ⟶ Y) n
  smul_mem' r _ hf := smul_mem r hf

variable (R) in
/-- The differential of a Hom group, as an `R`-linear map. -/
def dLinear (X Y : C) :
    (X ⟶ Y) →ₗ[R] (X ⟶ Y) where
  toFun := d
  map_add' := d_add
  map_smul' := d_smul

@[simp]
theorem dLinear_apply (X Y : C) (f : X ⟶ Y) : dLinear R X Y f = d f := rfl

omit [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGLinear R C] in
theorem smul_id_comp {X Y : C} (r : R) (f : X ⟶ Y) : (r • 𝟙 X) ≫ f = r • f := by
  rw [Linear.smul_comp, Category.id_comp]

omit [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGLinear R C] in
theorem comp_smul_id {X Y : C} (r : R) (f : X ⟶ Y) : f ≫ (r • 𝟙 Y) = r • f := by
  rw [Linear.comp_smul, Category.comp_id]

omit [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGLinear R C] in
/-- The scalar endomorphisms `r • 𝟙 X` are central. -/
theorem smul_id_comp_eq_comp_smul_id {X Y : C} (r : R) (f : X ⟶ Y) :
    (r • 𝟙 X) ≫ f = f ≫ (r • 𝟙 Y) := by
  rw [smul_id_comp, comp_smul_id]

variable [DGCategory C]

/-- The scalar endomorphism `r • 𝟙 X` has degree `0`. -/
theorem smul_id_mem (r : R) (X : C) : r • 𝟙 X ∈ grading (M := X ⟶ X) 0 :=
  smul_mem r (id_mem_grading X)

/-- The scalar endomorphism `r • 𝟙 X` is a cocycle. -/
@[simp]
theorem d_smul_id (r : R) (X : C) : d (r • 𝟙 X) = 0 := by
  rw [d_smul, d_id, smul_zero]

end DGLinear

/-- Every category with dg Hom groups is a dg category over `ℤ`, for the `ℤ`-linear structure
`CategoryTheory.Linear.preadditiveIntLinear`. -/
theorem DGLinear.int (C : Type u) [Category.{v} C] [Preadditive C]
    [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] : DGLinear ℤ C where
  smul_mem' r _ hf := zsmul_mem hf r
  d_smul' r f := d_zsmul r f

namespace SingleObj

variable (R : Type*) (A : Type u) [CommRing R] [Ring A] [Algebra R A]

/-- For an `R`-algebra `A`, the one-object category `SingleObj A` (with `f ≫ g = g * f`) is
`R`-linear, with the action of `R` on `A`. See the implementation notes for the priority. -/
instance (priority := 100) linear : Linear R (SingleObj A) where
  homModule _ _ := inferInstanceAs (Module R A)
  smul_comp _ _ _ r f g := Algebra.mul_smul_comm (A := A) r g f
  comp_smul _ _ _ f r g := Algebra.smul_mul_assoc (A := A) r g f

theorem smul_def {X Y : SingleObj A} (r : R) (f : X ⟶ Y) : r • f = (r • (f : A) : A) := rfl

/-- The scalar endomorphism `r • 𝟙` of the unique object of `SingleObj A` is
`algebraMap R A r`. -/
theorem smul_id_eq_algebraMap (r : R) :
    (r • 𝟙 (SingleObj.star A) : SingleObj.star A ⟶ SingleObj.star A) = algebraMap R A r :=
  (Algebra.algebraMap_eq_smul_one r).symm

/-- For a dg `R`-algebra `A`, the one-object category `SingleObj A` is a dg category over
`R`. -/
instance dgLinear [DGAddCommGroup A] [DGRing A] [DGAlgebra R A] : DGLinear R (SingleObj A) where
  smul_mem' r _ hf := DGAlgebra.smul_mem (A := A) r hf
  d_smul' r f := d_smul_algebra (A := A) r f

end SingleObj

end DG
