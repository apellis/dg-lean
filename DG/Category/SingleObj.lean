import Mathlib.CategoryTheory.Preadditive.SingleObj
import DG.Category.Basic

/-!
# One-object dg categories and endomorphism dg rings

For a ring `A` with a dg structure, the Hom group of Mathlib's one-object category
`SingleObj A` (with composition `f ≫ g = g * f`) is `A` itself, and so carries the dg structure
of `A` (`DG.SingleObj.instDGAddCommGroupHom`). With this structure, `SingleObj A` is a dg
category if and only if `A` is a dg ring (`DG.SingleObj.dgCategory_iff`): the Leibniz rule of a
dg category, `d (f ≫ g) = f ≫ d g + (-1)^{|g|} (d f ≫ g)`, is
`d (g * f) = d g * f + (-1)^{|g|} g * d f`.

Conversely, for an object `X` of a dg category, the endomorphism ring `End X` (Mathlib's, with
product `f * g = g ≫ f`) is a dg ring (`DG.End.instDGRing`).
-/

open CategoryTheory

universe v u

namespace DG

namespace SingleObj

variable {A : Type u} [Ring A] [DGAddCommGroup A]

/-- The Hom group of `SingleObj A` is `A`, with its dg structure. -/
instance instDGAddCommGroupHom (X Y : SingleObj A) : DGAddCommGroup (X ⟶ Y) :=
  inferInstanceAs (DGAddCommGroup A)

theorem mem_grading_iff {X Y : SingleObj A} {n : ℤ} {f : X ⟶ Y} :
    f ∈ grading n ↔ (f : A) ∈ grading (M := A) n :=
  Iff.rfl

theorem d_def {X Y : SingleObj A} (f : X ⟶ Y) : d f = (d (f : A) : A) :=
  rfl

/-- The one-object category of a dg ring is a dg category. -/
instance instDGCategory [DGRing A] : DGCategory (SingleObj A) where
  comp_mem' {_ _ _ i j f g} hf hg := by
    rw [add_comm]
    exact mul_mem_grading (A := A) hg hf
  id_mem' _ := one_mem_grading (A := A)
  d_comp' f _ hg := d_mul (A := A) hg f

/-- If `SingleObj A` is a dg category then `A` is a dg ring. -/
theorem dgRing_of_dgCategory [DGCategory (SingleObj A)] : DGRing A where
  one_mem := id_mem_grading (SingleObj.star A)
  mul_mem i j a b ha hb := by
    rw [add_comm]
    exact comp_mem_grading (X := SingleObj.star A) (Y := SingleObj.star A)
      (Z := SingleObj.star A) hb ha
  d_mul' {_ a} ha b := d_comp (X := SingleObj.star A) (Y := SingleObj.star A)
    (Z := SingleObj.star A) b ha

/-- `SingleObj A` is a dg category if and only if `A` is a dg ring. -/
theorem dgCategory_iff : DGCategory (SingleObj A) ↔ DGRing A :=
  ⟨fun _ => dgRing_of_dgCategory, fun _ => inferInstance⟩

end SingleObj

namespace End

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

/-- The endomorphism ring of an object of a category with dg Hom groups is a dg abelian
group. -/
instance instDGAddCommGroup (X : C) : DGAddCommGroup (End X) :=
  inferInstanceAs (DGAddCommGroup (X ⟶ X))

variable [DGCategory C]

/-- The endomorphism ring `End X` of an object of a dg category, with product `f * g = g ≫ f`,
is a dg ring. -/
instance instDGRing (X : C) : DGRing (End X) where
  one_mem := id_mem_grading X
  mul_mem i j f g hf hg := by
    rw [add_comm]
    exact comp_mem_grading (X := X) (Y := X) (Z := X) hg hf
  d_mul' {_ f} hf g := d_comp (X := X) (Y := X) (Z := X) g hf

end End

end DG
