import DG.Category.Derived.Keller
import DG.K0.Compact

/-!
# The perfect derived category of a dg category

Let `C` be a dg category. Its *perfect derived category* `D^c(C)`
(`DG.CatModule.PerfectDerivedCategory C`) is the full triangulated subcategory of compact objects
of the derived category `D(C)`; the compactness refers to coproducts indexed by types in the
universe `w` of the dg modules (`[HasDerivedCategory.{w', w} C]`). When `D(C)` has morphisms in
the universe `max u v w` of the dg modules, its objects are exactly the thick closure of the
representable modules (`DG.CatModule.DerivedCategory.thickClosure_representable_eq_isCompact`).

## Main definitions and results

* `DG.CatModule.DerivedCategory.isCompact_Q_representable`: the (lifted) representable modules
  `C(X, -)` are compact, and `DG.CatModule.PerfectDerivedCategory.representable X` is the
  corresponding object of `D^c(C)`.
* `DG.CatModule.DerivedCategory.isCompact_induction_obj`: for a dg functor `F : C ⥤ D`, derived
  induction `LF_! : D(C) ⥤ D(D)` preserves compact objects (it is left adjoint to restriction,
  which preserves coproducts), so it restricts to a triangulated functor
  `DG.CatModule.DerivedCategory.perfectInduction F : D^c(C) ⥤ D^c(D)`.
* `DG.CatModule.DerivedCategory.inductionRepresentableIso`: `LF_! C(X, -) ≅ D(F X, -)`.

## Universes

For `C : Type u₁` with `[Category.{v₁} C]` and `D : Type u₂` with `[Category.{v₂} D]`, derived
induction is defined for dg modules in `Type (max u₁ v₁ v₂ w)` on both sides, with `D(C)` having
morphisms in the same universe (as in `DG.CatModule.DerivedCategory.kellerEquivalence`); the
representable modules are lifted to that universe with `DG.CatModule.ulift`.
-/

open CategoryTheory Limits Pretriangulated

universe w' w₁ w₂ w v v₁ v₂ u u₁ u₂

set_option backward.isDefEq.respectTransparency false

namespace DG

namespace CatModule

section Perfect

variable (C : Type u) [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C]

/-- The perfect derived category `D^c(C)` of a dg category `C`: the full subcategory of compact
objects of `D(C)`, compactness being taken with respect to coproducts indexed by types in the
universe `w` of the dg modules. It is pretriangulated (triangulated), closed under direct
summands in `D(C)`. -/
abbrev PerfectDerivedCategory [HasDerivedCategory.{w', w} C] :=
  (compactSubcategory.{w} (DerivedCategory.{w', w} C)).FullSubcategory

variable {C}

namespace DerivedCategory

/-- The representable module `C(X, -)`, lifted to dg modules with values in `Type (max v w)`, is
compact in `D(C)`. -/
theorem isCompact_Q_representable [HasDerivedCategory.{w', max v w} C] (X : C) :
    IsCompact.{max v w} (Q.obj (ulift.{w} (representable X)) :
      DerivedCategory.{w', max v w} C) :=
  isCompact_Q_obj (isCornerGenerator_representable X).ulift

end DerivedCategory

namespace PerfectDerivedCategory

/-- The representable module `C(X, -)` as an object of the perfect derived category. -/
noncomputable def representable [HasDerivedCategory.{w', max v w} C] (X : C) :
    PerfectDerivedCategory.{w', max v w} C :=
  ⟨DerivedCategory.Q.obj (ulift.{w} (CatModule.representable X)),
    DerivedCategory.isCompact_Q_representable X⟩

end PerfectDerivedCategory

end Perfect

section Induction

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] [DGCategory D] (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]

namespace DerivedCategory

variable [HasDerivedCategory.{max u₁ v₁ v₂ w, max u₁ v₁ v₂ w} C]
  [HasDerivedCategory.{w₂, max u₁ v₁ v₂ w} D]

/-- Derived induction `LF_! : D(C) ⥤ D(D)` along a dg functor preserves compact objects: it is
left adjoint to restriction, which preserves coproducts. -/
theorem isCompact_induction_obj {X : DerivedCategory.{max u₁ v₁ v₂ w, max u₁ v₁ v₂ w} C}
    (hX : IsCompact.{max u₁ v₁ v₂ w} X) :
    IsCompact.{max u₁ v₁ v₂ w} ((induction.{max u₁ v₁ v₂ w, w₂, w} F).obj X) :=
  hX.map_of_adjunction (inductionAdjunction F)

/-- Derived induction of a lifted representable module is a lifted representable module:
`LF_! C(X, -) ≅ D(F X, -)`. -/
noncomputable def inductionRepresentableIso (X : C) :
    (induction.{max u₁ v₁ v₂ w, w₂, w} F).obj
        (Q.obj (ulift.{max u₁ v₂ w} (representable X))) ≅
      Q.obj (ulift.{max u₁ v₁ v₂ w} (representable (F.obj X))) :=
  (inductionObjIso F (isCornerGenerator_representable X).ulift.isKProjective).symm ≪≫
    Q.mapIso (inductionULiftRepresentableIso.{max u₁ v₂ w} F X)

/-- Derived induction restricted to the perfect derived categories,
`LF_! : D^c(C) ⥤ D^c(D)`; it commutes with the shifts and is triangulated. -/
noncomputable abbrev perfectInduction :
    PerfectDerivedCategory.{max u₁ v₁ v₂ w, max u₁ v₁ v₂ w} C ⥤
      PerfectDerivedCategory.{w₂, max u₁ v₁ v₂ w} D :=
  compactRestriction (induction.{max u₁ v₁ v₂ w, w₂, w} F) fun _ h => isCompact_induction_obj F h

end DerivedCategory

end Induction

end CatModule

end DG
