import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Shift.CommShift

/-!
# Products of triangulated functors

For a family `Φ : J → C ⥤ D` of functors between categories with shifts, where `D` has products
indexed by `J`, the functor `X ↦ ∏ⱼ Φⱼ X` (`DG.piFunctor Φ`) commutes with the shifts when every
`Φⱼ` does (`DG.piFunctor_commShift`), the comparison being the product of the comparisons of the
`Φⱼ` followed by the inverse of the canonical map `(∏ⱼ Yⱼ)⟦n⟧ → ∏ⱼ Yⱼ⟦n⟧`. If `C` and `D` are
pretriangulated and every `Φⱼ` is triangulated, then so is `piFunctor Φ`
(`DG.piFunctor_isTriangulated`): the image of a distinguished triangle is the product of the images
(`DG.piFunctorMapTriangleIso`), which is distinguished
(`CategoryTheory.Pretriangulated.productTriangle_distinguished`).
-/

open CategoryTheory Limits Category

universe v₁ v₂ u₁ u₂ w

noncomputable section

namespace DG

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : Type w} (Φ : J → C ⥤ D) [HasProductsOfShape J D]

/-- The product `X ↦ ∏ⱼ Φⱼ X` of a family of functors. -/
abbrev piFunctor : C ⥤ D where
  obj X := ∏ᶜ fun j => (Φ j).obj X
  map f := Limits.Pi.map fun j => (Φ j).map f
  map_id X := by
    ext j
    simp
  map_comp f g := by
    ext j
    simp

@[reassoc (attr := simp)]
theorem piFunctor_map_π {X Y : C} (f : X ⟶ Y) (j : J) :
    (piFunctor Φ).map f ≫ Pi.π _ j = Pi.π _ j ≫ (Φ j).map f :=
  Limits.Pi.map_π (fun j => (Φ j).map f) j

section Shift

variable [HasShift C ℤ] [HasShift D ℤ] [∀ j, (Φ j).CommShift ℤ]

instance (n : ℤ) (f : J → D) : IsIso (piComparison (shiftFunctor D n) f) := inferInstance

/-- The comparison `∏ⱼ Φⱼ (X⟦n⟧) ≅ (∏ⱼ Φⱼ X)⟦n⟧`. -/
def piFunctorCommShiftIsoApp (n : ℤ) (X : C) :
    (piFunctor Φ).obj (X⟦n⟧) ≅ ((piFunctor Φ).obj X)⟦n⟧ :=
  Limits.Pi.mapIso (fun j => ((Φ j).commShiftIso n).app X) ≪≫
    (asIso (piComparison (shiftFunctor D n) fun j => (Φ j).obj X)).symm

@[reassoc (attr := simp)]
theorem piFunctorCommShiftIsoApp_hom_π (n : ℤ) (X : C) (j : J) :
    (piFunctorCommShiftIsoApp Φ n X).hom ≫ (Pi.π _ j)⟦n⟧' =
      Pi.π _ j ≫ ((Φ j).commShiftIso n).hom.app X := by
  rw [← piComparison_comp_π]
  simp [piFunctorCommShiftIsoApp]

/-- Morphisms into a shifted product are determined by their components. -/
theorem shift_pi_hom_ext (n : ℤ) {f : J → D} {Y : D} {g g' : Y ⟶ (∏ᶜ f)⟦n⟧}
    (h : ∀ j, g ≫ (Pi.π f j)⟦n⟧' = g' ≫ (Pi.π f j)⟦n⟧') : g = g' := by
  rw [← cancel_mono (piComparison (shiftFunctor D n) f)]
  ext j
  simpa only [assoc, piComparison_comp_π] using h j

/-- The shift comparison of `piFunctor Φ`. -/
def piFunctorCommShiftIso (n : ℤ) :
    shiftFunctor C n ⋙ piFunctor Φ ≅ piFunctor Φ ⋙ shiftFunctor D n :=
  NatIso.ofComponents (piFunctorCommShiftIsoApp Φ n) fun {X Y} f => by
    apply shift_pi_hom_ext
    intro j
    have h1 := piFunctorCommShiftIsoApp_hom_π Φ n Y j
    have h2 := piFunctorCommShiftIsoApp_hom_π Φ n X j
    have h3 := piFunctor_map_π Φ ((shiftFunctor C n).map f) j
    have h4 := piFunctor_map_π Φ f j
    calc ((piFunctor Φ).map ((shiftFunctor C n).map f) ≫ (piFunctorCommShiftIsoApp Φ n Y).hom) ≫
          (Pi.π _ j)⟦n⟧' = Pi.π _ j ≫ (Φ j).map ((shiftFunctor C n).map f) ≫
            ((Φ j).commShiftIso n).hom.app Y := by
          rw [assoc, h1, reassoc_of% h3]
      _ = Pi.π _ j ≫ ((Φ j).commShiftIso n).hom.app X ≫ ((Φ j).map f)⟦n⟧' :=
          congrArg (Pi.π _ j ≫ ·) (((Φ j).commShiftIso n).hom.naturality f)
      _ = ((piFunctorCommShiftIsoApp Φ n X).hom ≫ ((piFunctor Φ).map f)⟦n⟧') ≫
          (Pi.π _ j)⟦n⟧' := by
          rw [assoc, ← Functor.map_comp, h4, Functor.map_comp, reassoc_of% h2]

/-- **The product of functors commuting with the shifts commutes with the shifts.** -/
instance piFunctor_commShift : (piFunctor Φ).CommShift ℤ where
  commShiftIso := piFunctorCommShiftIso Φ
  commShiftIso_zero := by
    ext X
    apply shift_pi_hom_ext
    intro j
    simp only [piFunctorCommShiftIso, NatIso.ofComponents_hom_app, piFunctorCommShiftIsoApp_hom_π,
      Functor.commShiftIso_zero, Functor.CommShift.isoZero_hom_app, Functor.comp_obj, assoc]
    rw [← NatTrans.naturality, Functor.id_map, Limits.Pi.map_π_assoc]
  commShiftIso_add a b := by
    ext X
    apply shift_pi_hom_ext
    intro j
    simp only [piFunctorCommShiftIso, NatIso.ofComponents_hom_app, piFunctorCommShiftIsoApp_hom_π,
      Functor.commShiftIso_add, Functor.CommShift.isoAdd_hom_app, Functor.comp_obj, assoc]
    rw [← NatTrans.naturality, Functor.comp_map, ← Functor.map_comp_assoc,
      piFunctorCommShiftIsoApp_hom_π, Functor.map_comp_assoc, piFunctorCommShiftIsoApp_hom_π_assoc,
      Limits.Pi.map_π_assoc]

end Shift

section Triangulated

open Pretriangulated

variable [HasShift C ℤ] [HasShift D ℤ] [∀ j, (Φ j).CommShift ℤ]
  [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [Preadditive D] [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The image of a triangle under `piFunctor Φ` is the product of its images under the `Φⱼ`. -/
def piFunctorMapTriangleIso (T : Triangle C) :
    (piFunctor Φ).mapTriangle.obj T ≅ productTriangle fun j => (Φ j).mapTriangle.obj T :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((comp_id _).trans (id_comp _).symm) ((comp_id _).trans (id_comp _).symm) (by
    dsimp [Functor.mapTriangle, productTriangle]
    rw [CategoryTheory.Functor.map_id, comp_id, id_comp]
    change Limits.Pi.map (fun j => (Φ j).map T.mor₃) ≫
        (Limits.Pi.map (fun j => ((Φ j).commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
          inv (piComparison (shiftFunctor D (1 : ℤ)) fun j => (Φ j).obj T.obj₁)) = _
    rw [← assoc]
    congr 1
    ext j
    simp only [assoc, Limits.Pi.map_π, Limits.Pi.map_π_assoc]
    exact (Limits.Pi.map_π (fun j => (Φ j).map T.mor₃ ≫
      ((Φ j).commShiftIso (1 : ℤ)).hom.app T.obj₁) j).symm)

/-- **A product of triangulated functors is triangulated.** -/
instance piFunctor_isTriangulated [∀ j, (Φ j).IsTriangulated] :
    (piFunctor Φ).IsTriangulated where
  map_distinguished T hT := isomorphic_distinguished _
    (productTriangle_distinguished _ fun j => (Φ j).map_distinguished T hT) _
    (piFunctorMapTriangleIso Φ T)

end Triangulated

end DG

end
