import Mathlib.CategoryTheory.Triangulated.Triangulated
import DG.Homotopy.ConeComp
import DG.Homotopy.Pretriangulated

/-!
# The homotopy category of dg modules is triangulated

This file shows that the pretriangulated category `DG.HomotopyCategory A` is triangulated,
i.e. satisfies the octahedron axiom. It is a port of Mathlib's
`Mathlib/Algebra/Homology/HomotopyCategory/Triangulated.lean`: for composable morphisms
`f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` of dg modules, the triangle
`Cone f ⟶ Cone (f ≫ g) ⟶ Cone g ⟶ (Cone f)⟦1⟧` (`DG.Cone.mappingConeCompTriangle`) is
distinguished in the homotopy category
(`DG.HomotopyCategory.mappingConeCompTriangleh_distinguished`), because `Cone g` is homotopy
equivalent to the cone of `Cone f ⟶ Cone (f ≫ g)` (`DG.Cone.mappingConeCompHomotopyEquiv`, in
`DG.Homotopy.ConeComp`).

## Main results

* `DG.Cone.mappingConeCompTriangle f g` and its image `DG.Cone.mappingConeCompTriangleh f g`
  in the homotopy category (Mathlib's names);
* `DG.HomotopyCategory.mappingConeCompTriangleh_distinguished`;
* the instance `IsTriangulated (DG.HomotopyCategory A)`.
-/

open CategoryTheory Category Limits Pretriangulated

universe v u

set_option backward.isDefEq.respectTransparency false

namespace DG

namespace Cone

open DGModuleCat DG.HomotopyCategory

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]
  {X₁ X₂ X₃ : DGModuleCat.{v} A} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)

/-- For composable morphisms `f` and `g` of dg modules, the triangle
`Cone f ⟶ Cone (f ≫ g) ⟶ Cone g ⟶ (Cone f)⟦1⟧` in `DGModuleCat A` (Mathlib's
`mappingConeCompTriangle`). -/
@[simps! mor₁ mor₂ mor₃ obj₁ obj₂ obj₃]
def mappingConeCompTriangle : Triangle (DGModuleCat.{v} A) :=
  Triangle.mk (DGModuleCat.ofHom (compMor₁ f.hom g.hom))
    (DGModuleCat.ofHom (compMor₂ f.hom g.hom))
    ((triangle g).mor₃ ≫ (DGModuleCat.ofHom (inr f.hom))⟦(1 : ℤ)⟧')

/-- The triangle `mappingConeCompTriangle f g` in the homotopy category (Mathlib's
`mappingConeCompTriangleh`); it is distinguished
(`DG.HomotopyCategory.mappingConeCompTriangleh_distinguished`). -/
noncomputable def mappingConeCompTriangleh : Triangle (HomotopyCategory.{v} A) :=
  (quotient A).mapTriangle.obj (mappingConeCompTriangle f g)

@[reassoc (attr := simp)]
theorem mappingConeCompHomotopyEquiv_hom_inv_id :
    DGModuleCat.ofHom (mappingConeCompHomotopyEquiv f.hom g.hom).hom ≫
      DGModuleCat.ofHom (mappingConeCompHomotopyEquiv f.hom g.hom).inv = 𝟙 _ :=
  hom_ext (mappingConeCompHomotopyEquiv_inv_comp_hom f.hom g.hom)

@[reassoc (attr := simp)]
theorem mappingConeCompTriangleh_comm₁ :
    (mappingConeCompTriangleh f g).mor₂ ≫
      (quotient A).map (DGModuleCat.ofHom (mappingConeCompHomotopyEquiv f.hom g.hom).hom) =
    (quotient A).map (DGModuleCat.ofHom (inr (compMor₁ f.hom g.hom))) := by
  rw [← cancel_mono (isoOfHomotopyEquiv (M := DGModuleCat.of A (Cone g.hom))
    (N := DGModuleCat.of A (Cone (compMor₁ f.hom g.hom)))
    (mappingConeCompHomotopyEquiv f.hom g.hom)).inv, assoc]
  dsimp [mappingConeCompTriangleh, mappingConeCompTriangle, isoOfHomotopyEquiv, triangle]
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    mappingConeCompHomotopyEquiv_hom_inv_id, comp_id]
  congr 1
  exact (hom_ext (mappingConeCompHomotopyEquiv_comm₁ f.hom g.hom)).symm

end Cone

namespace HomotopyCategory

open Cone

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]

theorem mappingConeCompTriangleh_distinguished {X₁ X₂ X₃ : DGModuleCat.{v} A} (f : X₁ ⟶ X₂)
    (g : X₂ ⟶ X₃) : mappingConeCompTriangleh f g ∈ distTriang (HomotopyCategory.{v} A) := by
  refine ⟨_, _, (mappingConeCompTriangle f g).mor₁, ⟨?_⟩⟩
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (isoOfHomotopyEquiv (M := DGModuleCat.of A (Cone g.hom))
      (N := DGModuleCat.of A (Cone (compMor₁ f.hom g.hom)))
      (mappingConeCompHomotopyEquiv f.hom g.hom)) (by aesop_cat) (by simp; rfl) ?_
  dsimp [mappingConeCompTriangleh, mappingConeCompTriangle, isoOfHomotopyEquiv, triangle]
  rw [CategoryTheory.Functor.map_id, comp_id, ← Functor.map_comp_assoc]
  congr 2
  exact (DGModuleCat.hom_ext (mappingConeCompHomotopyEquiv_comm₂ f.hom g.hom)).symm

variable (A) in
/-- The homotopy category of dg modules is triangulated. -/
noncomputable instance isTriangulated : IsTriangulated (HomotopyCategory.{v} A) :=
  IsTriangulated.mk' (by
    rintro ⟨X₁ : DGModuleCat.{v} A⟩ ⟨X₂ : DGModuleCat.{v} A⟩ ⟨X₃ : DGModuleCat.{v} A⟩ u₁₂' u₂₃'
    obtain ⟨u₁₂, rfl⟩ := (quotient A).map_surjective u₁₂'
    obtain ⟨u₂₃, rfl⟩ := (quotient A).map_surjective u₂₃'
    refine ⟨_, _, _, _, _, _, _, _, Iso.refl _, Iso.refl _, Iso.refl _, by simp, by simp,
        _, _, triangleh_distinguished u₁₂,
        _, _, triangleh_distinguished u₂₃,
        _, _, triangleh_distinguished (u₁₂ ≫ u₂₃), ⟨?_⟩⟩
    let α := triangleMap u₁₂ (u₁₂ ≫ u₂₃) (𝟙 X₁) u₂₃ (by rw [id_comp])
    let β := triangleMap (u₁₂ ≫ u₂₃) u₂₃ u₁₂ (𝟙 X₃) (by rw [comp_id])
    refine Triangulated.Octahedron.mk ((quotient A).map α.hom₃)
      ((quotient A).map β.hom₃) ?_ ?_ ?_ ?_ ?_
    · exact ((quotient A).mapTriangle.map α).comm₂
    · exact ((quotient A).mapTriangle.map α).comm₃.symm.trans (by dsimp [α]; simp)
    · exact ((quotient A).mapTriangle.map β).comm₂.trans (by dsimp [β]; simp)
    · exact ((quotient A).mapTriangle.map β).comm₃
    · refine isomorphic_distinguished _ (mappingConeCompTriangleh_distinguished u₁₂ u₂₃) _ ?_
      exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by dsimp [α, mappingConeCompTriangleh]; simp; rfl)
        (by dsimp [β, mappingConeCompTriangleh]; simp; rfl)
        (by dsimp [mappingConeCompTriangleh, mappingConeCompTriangle, isoOfHomotopyEquiv, triangle]; simp))

end HomotopyCategory

end DG
