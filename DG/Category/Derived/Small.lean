import DG.Category.Derived.Compact
import Mathlib.CategoryTheory.Localization.LocallySmall

/-!
# The derived category of a dg category has small Hom sets

Let `C` be a dg category with `C : Type u` and `[Category.{v} C]`, and consider dg modules with
values in `Type (max u v w)`. Every object of `D(C)` is the image of a K-projective module `P`,
and morphisms `Q P ⟶ Q N` in `D(C)` are images of morphisms of dg modules `P ⟶ N`
(`DG.CatModule.DerivedCategory.exists_Q_map_eq`). Hence the morphisms of `D(C)` are
`(max u v w)`-small (`DG.CatModule.DerivedCategory.locallySmall`), and the derived category can
be chosen with morphisms in `Type (max u v w)`
(`DG.CatModule.HasDerivedCategory.small`).
-/

open CategoryTheory

universe w' w v u

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C]

namespace DerivedCategory

/-- The derived category of a dg category is locally small: its morphisms are
`(max u v w)`-small, for dg modules with values in `Type (max u v w)`. -/
theorem locallySmall [HasDerivedCategory.{w', max u v w} C] :
    LocallySmall.{max u v w} (DerivedCategory.{w', max u v w} C) where
  hom_small X Y := by
    obtain ⟨P, hP, ⟨eX⟩⟩ := exists_isKProjective_iso.{w', w} X
    obtain ⟨N, ⟨eY⟩⟩ := exists_iso_Q_obj Y
    have : Small.{max u v w} (Q.obj P ⟶ Q.obj N) :=
      small_of_surjective (f := fun f : P ⟶ N => Q.map f) fun φ => exists_Q_map_eq hP φ
    exact small_map (Iso.homCongr eX eY)

end DerivedCategory

variable (C) in
/-- A choice of the derived category of a dg category with morphisms in `Type (max u v w)`, for
dg modules with values in `Type (max u v w)`, obtained by shrinking the morphisms of the
constructed localization. -/
@[instance_reducible]
noncomputable def HasDerivedCategory.small : HasDerivedCategory.{max u v w, max u v w} C :=
  letI : HasDerivedCategory.{_, max u v w} C := HasDerivedCategory.standard C
  have := DerivedCategory.locallySmall.{_, w} (C := C)
  { toHasLocalization := MorphismProperty.hasLocalizationOfLocallySmall _ (DerivedCategory.Qh) }

end CatModule

end DG
