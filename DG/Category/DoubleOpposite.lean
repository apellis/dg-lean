import DG.Category.Opposite
import DG.Category.Functor

/-!
# The double opposite dg category

On homogeneous compositions the two Koszul signs cancel. The canonical
double-unop functor is therefore a dg functor with the original
differential and grading on each hom group.
-/

namespace DG.DGOpposite

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]

/-- The two opposite hom-group identifications. -/
def doubleUnop {X Y : DGOpposite (DGOpposite C)} (f : X ⟶ Y) :
    X.unop.unop ⟶ Y.unop.unop :=
  homUnop (homUnop f)

@[simp] theorem doubleUnop_add {X Y : DGOpposite (DGOpposite C)} (f g : X ⟶ Y) :
    doubleUnop (f + g) = doubleUnop f + doubleUnop g := rfl

@[simp] theorem doubleUnop_zero {X Y : DGOpposite (DGOpposite C)} :
    doubleUnop (0 : X ⟶ Y) = 0 := rfl

private theorem doubleUnop_comp_homogeneous {X Y Z : DGOpposite (DGOpposite C)}
    {i j : ℤ} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : f ∈ grading i) (hg : g ∈ grading j) :
    doubleUnop (f ≫ g) = doubleUnop f ≫ doubleUnop g := by
  have h := homUnop_comp_of_mem hf hg
  have hg' : homUnop g ∈ grading j := hg
  have hf' : homUnop f ∈ grading i := hf
  have h' := homUnop_comp_of_mem hg' hf'
  change homUnop (homUnop (f ≫ g)) = _
  rw [h]
  change koszulSign (i * j) • homUnop (homUnop g ≫ homUnop f) =
    homUnop (homUnop f) ≫ homUnop (homUnop g)
  rw [h', mul_comm j i, smul_smul, Int.units_mul_self, one_smul]

/-- The two Koszul signs cancel in the composition of the double opposite. -/
theorem doubleUnop_comp {X Y Z : DGOpposite (DGOpposite C)}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    doubleUnop (f ≫ g) = doubleUnop f ≫ doubleUnop g := by
  induction f using DG.induction_on with
  | h_zero => simp
  | h_add f f' hf hf' => simp only [Preadditive.add_comp, doubleUnop_add, hf, hf']
  | @h_homogeneous i f =>
    induction g using DG.induction_on with
    | h_zero => simp
    | h_add g g' hg hg' => simp only [Preadditive.comp_add, doubleUnop_add, hg, hg']
    | h_homogeneous g => exact doubleUnop_comp_homogeneous f.property g.property

/-- The dg double opposite identifies with the original category. -/
def doubleUnopFunctor (C : Type u) [Category.{v} C] [Preadditive C]
    [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C] :
    DGOpposite (DGOpposite C) ⥤ C where
  obj X := X.unop.unop
  map := doubleUnop
  map_id _ := rfl
  map_comp f g := doubleUnop_comp f g

instance doubleUnopFunctor_additive : (doubleUnopFunctor C).Additive where
  map_add := fun {_ _} f g => doubleUnop_add f g

instance doubleUnopFunctor_isDGFunctor : (doubleUnopFunctor C).IsDGFunctor where
  map_mem' hf := hf
  map_d' _ := rfl

end DG.DGOpposite
