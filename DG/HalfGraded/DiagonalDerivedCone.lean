import DG.HalfGraded.DiagonalConeNaturality
import DG.HalfGraded.DiagonalDerivedTriangulated

/-!
# Descent of the original diagonal cone comparison to derived categories

For actual dg module maps, the existing localization comparison transports the original
`diagonalConeIso` and `diagonalConeTriangleIso`. The cone comparison is natural for
commuting squares of actual module maps. The triangle comparison uses the published
coherent signed shifts; its third component is exactly the transported original cone map.
No cone functor on arbitrary derived arrows, or forward homotopy functor, is constructed.
-/

open CategoryTheory Pretriangulated
universe w' w v u
namespace DG.Diagonal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]
  [HasDerivedCategory.{w, v} A]
  [CatModule.HasDerivedCategory.{w', v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]
variable {M N M' N' : DGModuleCat.{v} A}

/-- The original cone comparison, transported by the existing localization comparison.
The endpoints are the actual source cone under `toDerived` and the localized target cone. -/
def diagonalDerivedConeIso (f : M ⟶ N) :
    (toDerived A).obj (DerivedCategory.Q.obj (DGModuleCat.of A (Cone f.hom))) ≅
      CatModule.DerivedCategory.Q.obj (CatModule.cone ((toCatModule A).map f)) :=
  toDerivedObjIso A (DGModuleCat.of A (Cone f.hom)) ≪≫
    CatModule.DerivedCategory.Q.mapIso (diagonalConeIso A f)

/-- Identification with the original cone map, not an isomorphism chosen from
triangulatedness. -/
theorem diagonalDerivedConeIso_hom (f : M ⟶ N) :
    (diagonalDerivedConeIso A f).hom =
      (toDerivedObjIso A (DGModuleCat.of A (Cone f.hom))).hom ≫
        CatModule.DerivedCategory.Q.map (diagonalConeIso A f).hom := rfl

/-- Naturality after localization for arbitrary commuting squares of actual dg module
maps, using both original cone maps. This does not posit a cone functor on derived arrows. -/
@[reassoc]
theorem diagonalDerivedConeIso_naturality {f : M ⟶ N} {f' : M' ⟶ N'}
    (a : M ⟶ M') (b : N ⟶ N') (h : f ≫ b = a ≫ f') :
    (toDerived A).map (DerivedCategory.Q.map (DGModuleCat.Hom.mk
      (M := DGModuleCat.of A (Cone f.hom)) (N := DGModuleCat.of A (Cone f'.hom))
      (Cone.map a.hom b.hom (congrArg DGModuleCat.Hom.hom h)))) ≫
        (diagonalDerivedConeIso A f').hom =
      (diagonalDerivedConeIso A f).hom ≫
        CatModule.DerivedCategory.Q.map
          (CatModule.cone.map ((toCatModule A).map a) ((toCatModule A).map b)
            (by simpa only [← Functor.map_comp] using congrArg (toCatModule A).map h)) := by
  simp only [diagonalDerivedConeIso_hom, ← Category.assoc]
  rw [toDerived_map_Q]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [diagonalConeIso_naturality A a b h]

/-- Transport of the original standard-triangle comparison through the actual
shift-compatible localization comparison. All three structure maps, including the
negative connecting map, are retained by `mapTriangle`. -/
def diagonalDerivedConeTriangleIso (f : M ⟶ N) :
    (toDerived A).mapTriangle.obj (DerivedCategory.Q.mapTriangle.obj (Cone.triangle f)) ≅
      CatModule.DerivedCategory.Q.mapTriangle.obj
        (CatModule.cone.triangle ((toCatModule A).map f)) :=
  ((Functor.mapTriangleCompIso DerivedCategory.Q (toDerived A)).app _).symm ≪≫
    (Functor.mapTriangleIso (QCompToDerivedIso A)).app _ ≪≫
    (Functor.mapTriangleCompIso (toCatModule A) CatModule.DerivedCategory.Q).app _ ≪≫
    CatModule.DerivedCategory.Q.mapTriangle.mapIso (diagonalConeTriangleIso A f)

/-- The first triangle component is the existing localization comparison. -/
@[simp]
theorem diagonalDerivedConeTriangleIso_hom₁ (f : M ⟶ N) :
    (diagonalDerivedConeTriangleIso A f).hom.hom₁ = (toDerivedObjIso A M).hom := by
  change 𝟙 _ ≫ (toDerivedObjIso A M).hom ≫ 𝟙 _ ≫
    CatModule.DerivedCategory.Q.map (𝟙 _) = _
  simp only [Category.id_comp]
  rw [CatModule.DerivedCategory.Q.map_id, Category.comp_id]

/-- The second triangle component is the existing localization comparison. -/
@[simp]
theorem diagonalDerivedConeTriangleIso_hom₂ (f : M ⟶ N) :
    (diagonalDerivedConeTriangleIso A f).hom.hom₂ = (toDerivedObjIso A N).hom := by
  change 𝟙 _ ≫ (toDerivedObjIso A N).hom ≫ 𝟙 _ ≫
    CatModule.DerivedCategory.Q.map (𝟙 _) = _
  simp only [Category.id_comp]
  rw [CatModule.DerivedCategory.Q.map_id, Category.comp_id]

/-- The third triangle component is exactly the localization transport of the original
all-weight cone comparison, rather than another cone isomorphism. -/
@[simp]
theorem diagonalDerivedConeTriangleIso_hom₃ (f : M ⟶ N) :
    (diagonalDerivedConeTriangleIso A f).hom.hom₃ = (diagonalDerivedConeIso A f).hom := by
  change 𝟙 _ ≫ (toDerivedObjIso A (DGModuleCat.of A (Cone f.hom))).hom ≫ 𝟙 _ ≫
    CatModule.DerivedCategory.Q.map (diagonalConeIso A f).hom = _
  simp only [Category.id_comp, diagonalDerivedConeIso_hom]

end
end DG.Diagonal
