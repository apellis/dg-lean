import DG.Category.Derived.Induction
import DG.Category.Derived.RestrictionIso
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Functoriality of restriction and derived induction

For dg functors `F : C ⥤ D` and `G : D ⥤ E`, restriction on derived categories is compatible
with composition and identities (`DG.CatModule.DerivedCategory.restrictCompIso`,
`DG.CatModule.DerivedCategory.restrictIdIso`, in `DG/Category/Derived/RestrictionIso.lean`). By
uniqueness of left adjoints, derived induction is too:
`DG.CatModule.DerivedCategory.inductionCompIso : LF⋙G_! ≅ LF_! ⋙ LG_!` and
`DG.CatModule.DerivedCategory.inductionIdIso : L𝟭_! ≅ 𝟭`. Also: the isomorphism
`Q (F_! P) ≅ LF_! (Q P)` for K-projective `P` is natural in `P`
(`DG.CatModule.DerivedCategory.inductionObjIso_hom_naturality`).

## Universes

For `C : Type u₁`, `D : Type u₂`, `E : Type u₃` with morphisms in `v₁`, `v₂`, `v₃`, the
composition statement uses dg modules in `Type (max u₁ u₂ v₁ v₂ v₃ w)` on all three categories,
which is the module universe of derived induction along each of `F`, `G` and `F ⋙ G`.
-/

open CategoryTheory

universe w w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

set_option backward.isDefEq.respectTransparency false

namespace DG

namespace CatModule

section

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [∀ X Y : D, DGAddCommGroup (X ⟶ Y)]
  {E : Type u₃} [Category.{v₃} E] [Preadditive E] [∀ X Y : E, DGAddCommGroup (X ⟶ Y)]
  (F : C ⥤ D) [F.Additive] [F.IsDGFunctor] (G : D ⥤ E) [G.Additive] [G.IsDGFunctor]

variable [DGCategory C] [DGCategory D] [DGCategory E]

namespace DerivedCategory

section Induction

variable [HasDerivedCategory.{w₁, max u₁ u₂ v₁ v₂ v₃ w} C]
  [HasDerivedCategory.{w₂, max u₁ u₂ v₁ v₂ v₃ w} D]
  [HasDerivedCategory.{w₃, max u₁ u₂ v₁ v₂ v₃ w} E]

/-- Derived induction along a composite is the composite of the derived inductions: both are
left adjoint to restriction along the composite. -/
noncomputable def inductionCompIso :
    induction.{w₁, w₃, max u₂ v₂ w} (F ⋙ G) ≅
      induction.{w₁, w₂, max u₂ v₃ w} F ⋙ induction.{w₂, w₃, max u₁ v₁ w} G :=
  (inductionAdjunction (F ⋙ G)).leftAdjointUniq
    (((inductionAdjunction F).comp (inductionAdjunction G)).ofNatIsoRight
      (restrictCompIso F G).symm)

end Induction

section InductionId

variable (C) [HasDerivedCategory.{w₁, max u₁ v₁ w} C]

/-- Derived induction along the identity is the identity. -/
noncomputable def inductionIdIso :
    induction.{w₁, w₁, w} (𝟭 C) ≅ 𝟭 (DerivedCategory.{w₁, max u₁ v₁ w} C) :=
  (inductionAdjunction (𝟭 C)).leftAdjointUniq
    (Adjunction.id.ofNatIsoRight (restrictIdIso C).symm)

end InductionId

end DerivedCategory

end

end CatModule

end DG

namespace DG.CatModule.DerivedCategory

section Naturality

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] [DGCategory D] (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]
  [HasDerivedCategory.{w₁, max u₁ v₁ v₂ w} C] [HasDerivedCategory.{w₂, max u₁ v₁ v₂ w} D]

/-- Naturality of the universal arrows `unitMap`. -/
theorem unitMap_naturality {P P' : CatModule.{max u₁ v₁ v₂ w} C} (g : P ⟶ P') :
    unitMap F P ≫ (restrict F).map (Q.map ((CatModule.induction.{max v₁ w} F).map g)) =
      Q.map g ≫ unitMap F P' := by
  rw [unitMap_comp_restrict_map, unitMap, ← Category.assoc, ← Q.map_comp]
  congr 2
  rw [Adjunction.homEquiv_unit]
  exact ((CatModule.inductionAdjunction.{max v₁ w} F).unit.naturality g).symm

/-- Naturality of `Q (F_! P) ≅ LF_! (Q P)` in the K-projective module `P`. -/
theorem inductionObjIso_hom_naturality {P P' : CatModule.{max u₁ v₁ v₂ w} C}
    (hP : IsKProjective P) (hP' : IsKProjective P') (g : P ⟶ P') :
    Q.map ((CatModule.induction.{max v₁ w} F).map g) ≫ (inductionObjIso F hP').hom =
      (inductionObjIso F hP).hom ≫ (induction.{w₁, w₂, w} F).map (Q.map g) := by
  apply (unitMapEquiv F hP _).injective
  simp only [unitMapEquiv, Equiv.ofBijective_apply, Functor.map_comp, inductionObjIso_hom]
  rw [← Category.assoc, unitMap_naturality, Category.assoc, unitMap_comp_inductionObjIsoHom,
    ← Category.assoc, unitMap_comp_inductionObjIsoHom]
  exact (inductionAdjunction F).unit.naturality (Q.map g)

end Naturality

end DG.CatModule.DerivedCategory
