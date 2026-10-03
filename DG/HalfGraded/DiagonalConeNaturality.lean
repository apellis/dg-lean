import DG.HalfGraded.DiagonalCone

/-!
# Naturality and standard triangles for the original diagonal cone comparison

The existing `diagonalConeIso` is natural under arbitrary commuting squares, using
`Cone.map` and `CatModule.cone.map` on the original cones. Its previously proved
structure-map equations bundle to an isomorphism of the actual standard triangles,
using the existing coherent signed-shift structure. No homotopy or derived descent
of this comparison is asserted here.
-/

open CategoryTheory Pretriangulated
universe v u
namespace DG.Diagonal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The explicit homogeneous-decomposition lift is natural for the original maps. -/
theorem weightZeroLift_naturality {M N : DGModuleCat.{v} A} (f : M ⟶ N) (x : M) :
    weightZeroLift A N (f.hom x) =
      ((toCatModule A).map f).app ⟨0⟩ (weightZeroLift A M x) := by
  apply (recoveryMap_bijective A N).injective
  change valueEvaluation A N 0 _ = valueEvaluation A N 0 _
  rw [valueEvaluation_weightZeroLift]
  exact ((evaluation_regradedMap f (weightZeroLift A M x).1).trans
    (congrArg f.hom (valueEvaluation_weightZeroLift A M x))).symm

variable {M N M' N' : DGModuleCat.{v} A}
  {f : M ⟶ N} {f' : M' ⟶ N'} (a : M ⟶ M') (b : N ⟶ N')
  (h : f ≫ b = a ≫ f')

/-- The explicit cone lift intertwines the actual maps induced by a commuting square. -/
theorem diagonalConeLift_naturality (p : Cone f.hom) :
    diagonalConeLift A f' (Cone.map a.hom b.hom (congrArg DGModuleCat.Hom.hom h) p) =
      (CatModule.cone.map ((toCatModule A).map a) ((toCatModule A).map b)
        (by simpa only [← Functor.map_comp] using congrArg (toCatModule A).map h)).app ⟨0⟩
        (diagonalConeLift A f p) := by
  apply Prod.ext
  · exact congrArg (CatModule.shift.mk 1)
      (weightZeroLift_naturality A a (Shift.unmk 1 p.1))
  · exact weightZeroLift_naturality A b p.2

/-- Naturality of the original all-weight cone isomorphism for any commuting square.
Both sides use the existing cone maps; no replacement comparison is chosen. -/
theorem diagonalConeIso_naturality :
    (toCatModule A).map (DGModuleCat.Hom.mk
      (M := DGModuleCat.of A (Cone f.hom)) (N := DGModuleCat.of A (Cone f'.hom))
      (Cone.map a.hom b.hom (congrArg DGModuleCat.Hom.hom h))) ≫
        (diagonalConeIso A f').hom =
      (diagonalConeIso A f).hom ≫
        CatModule.cone.map ((toCatModule A).map a) ((toCatModule A).map b)
          (by simpa only [← Functor.map_comp] using congrArg (toCatModule A).map h) := by
  apply diagonalSource_hom_ext A
  intro x
  change (diagonalConeIso A f').hom.app ⟨0⟩
    (((toCatModule A).map (DGModuleCat.Hom.mk
      (M := DGModuleCat.of A (Cone f.hom)) (N := DGModuleCat.of A (Cone f'.hom))
      (Cone.map a.hom b.hom (congrArg DGModuleCat.Hom.hom h)))).app ⟨0⟩ x) = _
  rw [diagonalConeIso_hom_zero]
  have he := evaluation_regradedMap (DGModuleCat.Hom.mk
    (M := DGModuleCat.of A (Cone f.hom)) (N := DGModuleCat.of A (Cone f'.hom))
    (Cone.map a.hom b.hom (congrArg DGModuleCat.Hom.hom h))) x.1
  change diagonalConeLift A f' (evaluation (regradedMap (DGModuleCat.Hom.mk
    (M := DGModuleCat.of A (Cone f.hom)) (N := DGModuleCat.of A (Cone f'.hom))
    (Cone.map a.hom b.hom (congrArg DGModuleCat.Hom.hom h))) x.1)) = _
  rw [he]
  change _ = (CatModule.cone.map ((toCatModule A).map a) ((toCatModule A).map b)
    (by simpa only [← Functor.map_comp] using congrArg (toCatModule A).map h)).app ⟨0⟩
      ((diagonalConeIso A f).hom.app ⟨0⟩ x)
  rw [diagonalConeIso_hom_zero]
  exact diagonalConeLift_naturality A a b h _

/-- The image of the original standard triangle is isomorphic to the original target
standard triangle, with the original cone comparison as its third component. The
triangle image uses the existing coherent `CommShift` instance. -/
def diagonalConeTriangleIso (f : M ⟶ N) :
    (toCatModule A).mapTriangle.obj (Cone.triangle f) ≅
      CatModule.cone.triangle ((toCatModule A).map f) := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (diagonalConeIso A f) ?_ ?_ ?_
  · simp
  · change (toCatModule A).map (DGModuleCat.Hom.mk
      (N := DGModuleCat.of A (Cone f.hom)) (Cone.inr f.hom)) ≫
        (diagonalConeIso A f).hom = 𝟙 _ ≫ CatModule.cone.inr ((toCatModule A).map f)
    rw [Category.id_comp]
    exact diagonalConeIso_inr A f
  · change ((toCatModule A).map (Cone.triangle f).mor₃ ≫
      ((toCatModule A).commShiftIso (1 : ℤ)).hom.app M) ≫
        (shiftFunctor _ (1 : ℤ)).map (𝟙 _) = _
    simp only [CategoryTheory.Functor.map_id]
    rw [toCatModule_commShiftIso]
    exact (diagonalConeIso_triangle_mor₃ A f).symm

end
end DG.Diagonal
