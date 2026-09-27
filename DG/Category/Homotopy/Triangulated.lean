import Mathlib.CategoryTheory.Triangulated.Triangulated
import DG.Category.Homotopy.ConeComp
import DG.Category.Homotopy.Pretriangulated

/-!
# The homotopy category of dg modules over a dg category is triangulated

This file shows that the pretriangulated category `DG.CatModule.HomotopyCategory C` satisfies
the octahedron axiom. It is a port of `DG.Homotopy.Triangulated` (the case of a dg ring, itself
a port of Mathlib's `Mathlib/Algebra/Homology/HomotopyCategory/Triangulated.lean`): for
composable morphisms `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃`, the triangle
`cone f ⟶ cone (f ≫ g) ⟶ cone g ⟶ (cone f)⟦1⟧` is distinguished in the homotopy category,
because `cone g` is homotopy equivalent to the cone of `cone f ⟶ cone (f ≫ g)`
(`DG.CatModule.cone.mappingConeCompHomotopyEquiv`).

## Main results

* `DG.CatModule.cone.mappingConeCompTriangle f g` and its image
  `DG.CatModule.cone.mappingConeCompTriangleh f g` in the homotopy category;
* `DG.CatModule.HomotopyCategory.mappingConeCompTriangleh_distinguished`;
* the instance `DG.CatModule.HomotopyCategory.isTriangulated`.
-/

open CategoryTheory Category Limits Pretriangulated

universe w v u

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C]

namespace cone

open HomotopyCategory

variable {X₁ X₂ X₃ : CatModule.{w} C} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)

/-- For composable morphisms `f` and `g` of dg modules, the triangle
`cone f ⟶ cone (f ≫ g) ⟶ cone g ⟶ (cone f)⟦1⟧` in `CatModule C` (Mathlib's
`mappingConeCompTriangle`). -/
@[simps! mor₁ mor₂ mor₃ obj₁ obj₂ obj₃]
def mappingConeCompTriangle : Triangle (CatModule.{w} C) :=
  Triangle.mk (compMor₁ f g) (compMor₂ f g) ((triangle g).mor₃ ≫ (inr f)⟦(1 : ℤ)⟧')

/-- The triangle `mappingConeCompTriangle f g` in the homotopy category (Mathlib's
`mappingConeCompTriangleh`); it is distinguished
(`DG.CatModule.HomotopyCategory.mappingConeCompTriangleh_distinguished`). -/
noncomputable def mappingConeCompTriangleh : Triangle (HomotopyCategory.{w} C) :=
  (quotient C).mapTriangle.obj (mappingConeCompTriangle f g)

@[reassoc (attr := simp)]
theorem mappingConeCompTriangleh_comm₁ :
    (mappingConeCompTriangleh f g).mor₂ ≫
      (quotient C).map (mappingConeCompHomotopyEquiv f g).hom =
    (quotient C).map (inr (compMor₁ f g)) := by
  rw [← cancel_mono (isoOfHomotopyEquiv (mappingConeCompHomotopyEquiv f g)).inv, assoc]
  dsimp [mappingConeCompTriangleh]
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    mappingConeCompHomotopyEquiv_hom_comp_inv, comp_id]
  congr 1
  exact (mappingConeCompHomotopyEquiv_comm₁ f g).symm

end cone

namespace HomotopyCategory

open cone

theorem mappingConeCompTriangleh_distinguished {X₁ X₂ X₃ : CatModule.{w} C} (f : X₁ ⟶ X₂)
    (g : X₂ ⟶ X₃) : mappingConeCompTriangleh f g ∈ distTriang (HomotopyCategory.{w} C) := by
  refine ⟨_, _, (mappingConeCompTriangle f g).mor₁, ⟨?_⟩⟩
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (isoOfHomotopyEquiv (mappingConeCompHomotopyEquiv f g)) (by aesop_cat) (by simp) ?_
  dsimp [mappingConeCompTriangleh]
  rw [CategoryTheory.Functor.map_id, comp_id, ← Functor.map_comp_assoc]
  congr 2
  exact (mappingConeCompHomotopyEquiv_comm₂ f g).symm

variable (C) in
/-- The homotopy category of dg modules over a dg category is triangulated. -/
noncomputable instance isTriangulated : IsTriangulated (HomotopyCategory.{w} C) :=
  IsTriangulated.mk' (by
    rintro ⟨X₁ : CatModule.{w} C⟩ ⟨X₂ : CatModule.{w} C⟩ ⟨X₃ : CatModule.{w} C⟩ u₁₂' u₂₃'
    obtain ⟨u₁₂, rfl⟩ := (quotient C).map_surjective u₁₂'
    obtain ⟨u₂₃, rfl⟩ := (quotient C).map_surjective u₂₃'
    refine ⟨_, _, _, _, _, _, _, _, Iso.refl _, Iso.refl _, Iso.refl _, by simp, by simp,
        _, _, triangleh_distinguished u₁₂,
        _, _, triangleh_distinguished u₂₃,
        _, _, triangleh_distinguished (u₁₂ ≫ u₂₃), ⟨?_⟩⟩
    let α := triangleMap u₁₂ (u₁₂ ≫ u₂₃) (𝟙 X₁) u₂₃ (by rw [id_comp])
    let β := triangleMap (u₁₂ ≫ u₂₃) u₂₃ u₁₂ (𝟙 X₃) (by rw [comp_id])
    refine Triangulated.Octahedron.mk ((quotient C).map α.hom₃)
      ((quotient C).map β.hom₃) ?_ ?_ ?_ ?_ ?_
    · exact ((quotient C).mapTriangle.map α).comm₂
    · exact ((quotient C).mapTriangle.map α).comm₃.symm.trans (by dsimp [α]; simp)
    · exact ((quotient C).mapTriangle.map β).comm₂.trans (by dsimp [β]; simp)
    · exact ((quotient C).mapTriangle.map β).comm₃
    · refine isomorphic_distinguished _ (mappingConeCompTriangleh_distinguished u₁₂ u₂₃) _ ?_
      exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by dsimp [α, mappingConeCompTriangleh]; simp; rfl)
        (by dsimp [β, mappingConeCompTriangleh]; simp; rfl)
        (by dsimp [mappingConeCompTriangleh]; simp))

end HomotopyCategory

end CatModule

end DG
