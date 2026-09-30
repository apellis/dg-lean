import DG.Category.Derived.FiniteCell
import DG.Category.Derived.InductionComp
import DG.Category.Derived.Perfect

/-!
# Derived induction of cells

Let `F : C ⥤ D` be a dg functor. A degree-`0` idempotent cocycle `e` of an object `X` of `C` has
image `F e` (`DG.DGCategory.Idempotent.map`), a degree-`0` idempotent cocycle of `F X`. Derived
induction `LF_! : D(C) ⥤ D(D)` takes the cell `Q (e · C(X, -))` to the cell
`Q (F e · D(F X, -))` (`DG.CatModule.DerivedCategory.inductionCellIso`).

The proof: `e · C(X, -)` is a retract of `C(X, -)` with idempotent `h ↦ e ≫ h`, and derived
induction takes `C(X, -)` to `D(F X, -)` (`DG.CatModule.DerivedCategory.inductionRepresentableIso`)
and this idempotent to `h ↦ F e ≫ h`, whose image is `F e · D(F X, -)`; two retracts of an
object with the same idempotent are isomorphic (`CategoryTheory.isoOfRetractOfEq`).
-/

open CategoryTheory

universe w w₂ v₁ v₂ u₁ u₂

set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

variable {𝒞 : Type*} [Category 𝒞] {X X' Y : 𝒞}

/-- Two retracts `X`, `X'` of an object `Y` which split the same idempotent of `Y` are
isomorphic. -/
@[simps]
def isoOfRetractOfEq (i : X ⟶ Y) (r : Y ⟶ X) (i' : X' ⟶ Y) (r' : Y ⟶ X') (h : i ≫ r = 𝟙 X)
    (h' : i' ≫ r' = 𝟙 X') (hp : r ≫ i = r' ≫ i') : X ≅ X' where
  hom := i ≫ r'
  inv := i' ≫ r
  hom_inv_id := by
    simp only [Category.assoc]
    rw [← Category.assoc r' i' r, ← hp, Category.assoc, reassoc_of% h, h]
  inv_hom_id := by
    simp only [Category.assoc]
    rw [← Category.assoc r i r', hp, Category.assoc, reassoc_of% h', h']

end CategoryTheory

namespace DG

namespace DGCategory.Idempotent

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [∀ X Y : D, DGAddCommGroup (X ⟶ Y)]
  (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]

/-- The image `F e` of a degree-`0` idempotent cocycle `e` of `X` under a dg functor, a
degree-`0` idempotent cocycle of `F X`. -/
@[simps]
def map {X : C} (e : Idempotent X) : Idempotent (F.obj X) where
  val := F.map e.val
  mem_cocycles := F.map_mem_cocycles e.mem_cocycles
  comp_self := by rw [← F.map_comp, e.comp_self]

end DGCategory.Idempotent

namespace CatModule

open DGCategory

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C]

section Idempotent

variable {X : C} (e : Idempotent X)

/-- The idempotent `h ↦ e ≫ h` of the representable module `C(X, -)` whose image is the corner
`e · C(X, -)`. -/
noncomputable def cornerIdem : representable X ⟶ representable X :=
  (cornerRetract e).r ≫ (cornerRetract e).i

theorem cornerIdem_app {Y : C} (h : (representable X).obj Y) :
    (cornerIdem e).app Y h = e.val ≫ (h : X ⟶ Y) :=
  rfl

end Idempotent

variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [∀ X Y : D, DGAddCommGroup (X ⟶ Y)]
  [DGCategory D] (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]

/-- Induction takes the idempotent `h ↦ e ≫ h` of `C(X, -)` to the idempotent `h ↦ F e ≫ h` of
`D(F X, -)`, under `F_! C(X, -) ≅ D(F X, -)`. -/
theorem induction_map_uliftMap_cornerIdem {X : C} (e : Idempotent X) :
    (induction.{max v₁ w} F).map (uliftMap.{max u₁ v₂ w} (cornerIdem e)) ≫
        (inductionULiftRepresentableIso.{max u₁ v₂ w} F X).hom =
      (inductionULiftRepresentableIso.{max u₁ v₂ w} F X).hom ≫
        uliftMap.{max u₁ v₁ v₂ w} (cornerIdem (e.map F)) := by
  apply ((inductionAdjunction.{max v₁ w} F).homEquiv _ _).injective
  refine ((isCornerGenerator_representable X).ulift.{max u₁ v₂ w}).ext_hom ?_
  rw [inductionAdjunction_homEquiv_apply_app, inductionAdjunction_homEquiv_apply_app, comp_app,
    comp_app, induction_map_app_tmul]
  refine ULift.ext _ _ ?_
  have h1 := inductionULiftRepresentableIso_hom_app_tmul.{max u₁ v₂ w} F X X (𝟙 (F.obj X))
    (ULift.up (e.val ≫ 𝟙 X))
  have h2 := inductionULiftRepresentableIso_hom_app_tmul.{max u₁ v₂ w} F X X (𝟙 (F.obj X))
    (ULift.up (𝟙 X))
  refine h1.trans (Eq.trans ?_ (congrArg (F.map e.val ≫ ·) h2).symm)
  simp

namespace DerivedCategory

section Retract

universe t w'

variable {E : Type u₁} [Category.{v₁} E] [Preadditive E] [∀ X Y : E, DGAddCommGroup (X ⟶ Y)]
  [DGCategory E] [HasDerivedCategory.{w', max v₁ t} E] {X : E} (e : Idempotent X)

/-- The inclusion `Q (e · C(X, -)) ⟶ Q C(X, -)` of a cell of shift `0`. -/
noncomputable def cellι : cell.{w', t} e 0 ⟶ Q.obj (ulift.{t} (representable X)) :=
  Q.map ((shiftZeroIso _).hom ≫ uliftMap (cornerRetract e).i)

/-- The retraction `Q C(X, -) ⟶ Q (e · C(X, -))` onto a cell of shift `0`. -/
noncomputable def cellπ : Q.obj (ulift.{t} (representable X)) ⟶ cell.{w', t} e 0 :=
  Q.map (uliftMap (cornerRetract e).r ≫ (shiftZeroIso _).inv)

@[reassoc (attr := simp)]
theorem cellι_cellπ : (cellι e ≫ cellπ e : cell.{w', t} e 0 ⟶ cell.{w', t} e 0) = 𝟙 _ := by
  rw [cellι, cellπ, ← Q.map_comp, Category.assoc, ← Category.assoc (uliftMap _),
    ← uliftMap_comp, (cornerRetract e).retract, uliftMap_id, Category.id_comp,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id]

theorem cellπ_cellι :
    (cellπ e ≫ cellι e : (Q.obj (ulift.{t} (representable X)) : DerivedCategory.{w', max v₁ t} E) ⟶
      Q.obj (ulift.{t} (representable X))) = Q.map (uliftMap (cornerIdem e)) := by
  rw [cellι, cellπ, ← Q.map_comp, Category.assoc, Iso.inv_hom_id_assoc, ← uliftMap_comp]
  rfl

end Retract

variable [HasDerivedCategory.{max u₁ v₁ v₂ w, max u₁ v₁ v₂ w} C]
  [HasDerivedCategory.{w₂, max u₁ v₁ v₂ w} D]

/-- Under `LF_! C(X, -) ≅ D(F X, -)`, derived induction takes the idempotent `h ↦ e ≫ h` to
`h ↦ F e ≫ h`. -/
theorem induction_map_Q_map_cornerIdem {X : C} (e : Idempotent X) :
    (induction.{max u₁ v₁ v₂ w, w₂, w} F).map (Q.map (uliftMap.{max u₁ v₂ w} (cornerIdem e))) ≫
        (inductionRepresentableIso.{w₂, w} F X).hom =
      (inductionRepresentableIso.{w₂, w} F X).hom ≫
        Q.map (uliftMap.{max u₁ v₁ v₂ w} (cornerIdem (e.map F))) := by
  have hP := (isCornerGenerator_representable X).ulift.{max u₁ v₂ w}.isKProjective
  have hn := inductionObjIso_hom_naturality.{w} F hP hP (uliftMap (cornerIdem e))
  have hn' : (induction.{max u₁ v₁ v₂ w, w₂, w} F).map
      (Q.map (uliftMap.{max u₁ v₂ w} (cornerIdem e))) ≫ (inductionObjIso F hP).inv =
      (inductionObjIso F hP).inv ≫ Q.map ((CatModule.induction.{max v₁ w} F).map
        (uliftMap.{max u₁ v₂ w} (cornerIdem e))) := by
    rw [Iso.comp_inv_eq, Category.assoc, hn, Iso.inv_hom_id_assoc]
  simp only [inductionRepresentableIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [reassoc_of% hn', ← Q.map_comp, induction_map_uliftMap_cornerIdem, Q.map_comp,
    Category.assoc]

/-- **Derived induction of a cell**: `LF_! Q (e · C(X, -)) ≅ Q (F e · D(F X, -))`. -/
noncomputable def inductionCellIso {X : C} (e : Idempotent X) :
    (induction.{max u₁ v₁ v₂ w, w₂, w} F).obj (cell.{max u₁ v₁ v₂ w, max u₁ v₂ w} e 0) ≅
      cell.{w₂, max u₁ v₁ v₂ w} (e.map F) 0 :=
  isoOfRetractOfEq
    ((induction.{max u₁ v₁ v₂ w, w₂, w} F).map (cellι e) ≫
      (inductionRepresentableIso.{w₂, w} F X).hom)
    ((inductionRepresentableIso.{w₂, w} F X).inv ≫
      (induction.{max u₁ v₁ v₂ w, w₂, w} F).map (cellπ e))
    (cellι (e.map F)) (cellπ (e.map F))
    (by
      rw [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, cellι_cellπ,
        CategoryTheory.Functor.map_id])
    (cellι_cellπ _)
    (by
      rw [cellπ_cellι, Category.assoc, ← Functor.map_comp_assoc, cellπ_cellι,
        induction_map_Q_map_cornerIdem, Iso.inv_hom_id_assoc])

end DerivedCategory

end CatModule

end DG
