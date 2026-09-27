import DG.Category.Abelian
import DG.Category.Homotopy.Comparison
import DG.Category.Homotopy.Precomp
import DG.Homotopy.ForgetTriangulated

/-!
# Evaluation at an object on the homotopy category of dg modules over a dg category

Let `C` be a dg category and `X` an object of `C`. The value `M.obj X` of a dg module over `C`
has an underlying cochain complex of abelian groups (`DG.CatModule.evalComplex X`). This file
shows that evaluation at `X` induces a triangulated functor from the homotopy category of dg
modules over `C` to Mathlib's homotopy category of cochain complexes of abelian groups, and
deduces that the cohomology at `X` is a homological functor.

The functor is the composite of three triangulated functors: restriction along the inclusion
`DG.CatModule.endInclusion X : SingleObj (End X) ⥤ C` of the endomorphism dg ring of `X`
(`DG.CatModule.HomotopyCategory.precomp`), the comparison
`DG.CatModule.HomotopyCategory.toDGHomotopyCategory (End X)` with the homotopy category of dg
`End X`-modules, and the forgetful functor of `DG.Homotopy.ForgetTriangulated` (for `R = ℤ`)
followed by the forgetful functor from `ℤ`-modules to abelian groups.

## Main definitions and results

* `DG.HomotopyCategory.forgetToAddCommGrp A : DG.HomotopyCategory A ⥤
  HomotopyCategory AddCommGrp (ComplexShape.up ℤ)` for a dg ring `A`, a triangulated functor
  (`DG.HomotopyCategory.forgetToAddCommGrp_isTriangulated`).
* `DG.CatModule.HomotopyCategory.eval X : HomotopyCategory C ⥤
  HomotopyCategory AddCommGrp (ComplexShape.up ℤ)`, a triangulated functor
  (`DG.CatModule.HomotopyCategory.eval_isTriangulated`), induced by the underlying complexes
  of the values at `X` (`DG.CatModule.HomotopyCategory.evalFactors`).
* `DG.CatModule.HomotopyCategory.cohomologyFunctor X n`: the `n`-th cohomology of the value at
  `X`, a homological functor (`DG.CatModule.HomotopyCategory.cohomologyFunctor_isHomological`).

The forgetful functor for a dg ring `A` is stated for a general dg ring (so that its `ℤ`-algebra
structure is the canonical one) and then applied to `End X`, whose `ℤ`-algebra structure is
otherwise found through the `ℤ`-linear structure of `C`.
-/

open CategoryTheory Category Limits Pretriangulated

universe w v u

namespace DG

namespace HomotopyCategory

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The underlying complexes of abelian groups of dg `A`-modules, on homotopy categories. -/
noncomputable def forgetToAddCommGrp :
    HomotopyCategory.{w} A ⥤ _root_.HomotopyCategory AddCommGrp.{w} (ComplexShape.up ℤ) :=
  forget ℤ A ⋙ (forget₂ (ModuleCat.{w} ℤ) AddCommGrp.{w}).mapHomotopyCategory _

noncomputable instance forgetToAddCommGrpCommShift :
    (forgetToAddCommGrp.{w} A).CommShift ℤ :=
  inferInstanceAs ((forget ℤ A ⋙
    (forget₂ (ModuleCat.{w} ℤ) AddCommGrp.{w}).mapHomotopyCategory _).CommShift ℤ)

/-- The underlying complexes of abelian groups define a triangulated functor on the homotopy
category of dg `A`-modules. -/
instance forgetToAddCommGrp_isTriangulated : (forgetToAddCommGrp.{w} A).IsTriangulated :=
  inferInstanceAs (forget ℤ A ⋙
    (forget₂ (ModuleCat.{w} ℤ) AddCommGrp.{w}).mapHomotopyCategory _).IsTriangulated

/-- The functor `forgetToAddCommGrp A` is induced by the underlying complexes of abelian groups
`DG.DGModuleCat.forgetToAddCommGrp A` of dg `A`-modules. -/
noncomputable def forgetToAddCommGrpFactors :
    quotient A ⋙ forgetToAddCommGrp.{w} A ≅
      DGModuleCat.forgetToAddCommGrp A ⋙ _root_.HomotopyCategory.quotient _ _ :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by
    rw [Iso.refl_hom, Iso.refl_hom, comp_id, id_comp]
    rfl

end HomotopyCategory

namespace CatModule

namespace HomotopyCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C]

/-- Evaluation at an object `X`, on homotopy categories: the underlying complex of abelian
groups of the value at `X`, as a functor to Mathlib's homotopy category. -/
noncomputable def eval (X : C) :
    HomotopyCategory.{w} C ⥤ _root_.HomotopyCategory AddCommGrp.{w} (ComplexShape.up ℤ) :=
  precomp (endInclusion X) ⋙ toDGHomotopyCategory (End X) ⋙
    DG.HomotopyCategory.forgetToAddCommGrp (End X)

noncomputable instance evalCommShift (X : C) : (eval.{w} X).CommShift ℤ :=
  inferInstanceAs ((precomp (endInclusion X) ⋙ toDGHomotopyCategory (End X) ⋙
    DG.HomotopyCategory.forgetToAddCommGrp (End X)).CommShift ℤ)

/-- Evaluation at an object is a triangulated functor on homotopy categories. -/
instance eval_isTriangulated (X : C) : (eval.{w} X).IsTriangulated :=
  inferInstanceAs (precomp (endInclusion X) ⋙ toDGHomotopyCategory (End X) ⋙
    DG.HomotopyCategory.forgetToAddCommGrp (End X)).IsTriangulated

/-- Evaluation at `X` on homotopy categories is induced by the underlying complexes of the
values at `X`, `DG.CatModule.evalComplex X`. -/
noncomputable def evalFactors (X : C) :
    quotient C ⋙ eval.{w} X ≅ evalComplex X ⋙ _root_.HomotopyCategory.quotient _ _ :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by
    rw [Iso.refl_hom, Iso.refl_hom, comp_id, id_comp]
    rfl

/-- The `n`-th cohomology of the value at `X`, as a functor on the homotopy category. -/
noncomputable def cohomologyFunctor (X : C) (n : ℤ) : HomotopyCategory.{w} C ⥤ AddCommGrp.{w} :=
  eval X ⋙ _root_.HomotopyCategory.homologyFunctor AddCommGrp.{w} (ComplexShape.up ℤ) n

/-- The cohomology at an object is a homological functor on the homotopy category. -/
instance cohomologyFunctor_isHomological (X : C) (n : ℤ) :
    (cohomologyFunctor.{w} X n).IsHomological := by
  dsimp only [cohomologyFunctor]
  infer_instance

end HomotopyCategory

end CatModule

end DG
