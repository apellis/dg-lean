import DG.Category.Basic

/-!
# Dg functors

A dg functor between categories with dg Hom groups is an additive functor `F : C ⥤ D` which
preserves the grading of the Hom groups and commutes with the differentials. This is the
`Prop`-valued mixin `CategoryTheory.Functor.IsDGFunctor F`, on top of `[F.Additive]` (as for
Mathlib's `CategoryTheory.Functor.Linear`).

## Main definitions

* `CategoryTheory.Functor.IsDGFunctor F`, with instances for the identity functor and for
  composites.
* `CategoryTheory.Functor.mapZ0 F : Z⁰(C) ⥤ Z⁰(D)` and
  `CategoryTheory.Functor.mapH0 F : H⁰(C) ⥤ H⁰(D)`: the functors induced by a dg functor on the
  categories of degree-`0` cocycles and on the homotopy categories.
-/

open CategoryTheory DG DG.DGCategory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [∀ X Y : D, DGAddCommGroup (X ⟶ Y)]
  {E : Type u₃} [Category.{v₃} E] [Preadditive E] [∀ X Y : E, DGAddCommGroup (X ⟶ Y)]

/-- A dg functor: an additive functor which preserves the degrees of morphisms and commutes with
the differentials of the Hom groups. -/
class IsDGFunctor (F : C ⥤ D) [F.Additive] : Prop where
  map_mem' : ∀ {X Y : C} {n : ℤ} {f : X ⟶ Y}, f ∈ grading n → F.map f ∈ grading n
  map_d' : ∀ {X Y : C} (f : X ⟶ Y), F.map (d f) = d (F.map f)

section IsDGFunctor

variable (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]

theorem map_mem_grading {X Y : C} {n : ℤ} {f : X ⟶ Y} (hf : f ∈ grading n) :
    F.map f ∈ grading n :=
  IsDGFunctor.map_mem' hf

@[simp]
theorem map_d {X Y : C} (f : X ⟶ Y) : F.map (d f) = d (F.map f) :=
  IsDGFunctor.map_d' f

theorem map_mem_cocycles {X Y : C} {n : ℤ} {f : X ⟶ Y} (hf : f ∈ cocycles (X ⟶ Y) n) :
    F.map f ∈ cocycles (F.obj X ⟶ F.obj Y) n :=
  ⟨F.map_mem_grading hf.1, show d (F.map f) = 0 by rw [← F.map_d, hf.2, F.map_zero]⟩

theorem map_mem_coboundaries {X Y : C} {n : ℤ} {f : X ⟶ Y}
    (hf : f ∈ coboundaries (X ⟶ Y) n) : F.map f ∈ coboundaries (F.obj X ⟶ F.obj Y) n := by
  obtain ⟨g, hg, rfl⟩ := hf
  exact ⟨F.map g, F.map_mem_grading hg, (F.map_d g).symm⟩

/-- The action of a dg functor on the homogeneous components of a morphism. -/
theorem map_decompose {X Y : C} (f : X ⟶ Y) (n : ℤ) :
    F.map (DirectSum.decompose (grading (M := X ⟶ Y)) f n : X ⟶ Y) =
      (DirectSum.decompose (grading (M := F.obj X ⟶ F.obj Y)) (F.map f) n : F.obj X ⟶ F.obj Y) :=
  (decompose_map (k := 0) (F.mapAddHom (X := X) (Y := Y))
    (fun hf => by rw [add_zero]; exact F.map_mem_grading hf) f n).symm.trans
    (by rw [add_zero]; rfl)

end IsDGFunctor

instance isDGFunctor_id : (𝟭 C).IsDGFunctor where
  map_mem' hf := hf
  map_d' _ := rfl

instance isDGFunctor_comp (F : C ⥤ D) [F.Additive] [F.IsDGFunctor] (G : D ⥤ E) [G.Additive]
    [G.IsDGFunctor] : (F ⋙ G).IsDGFunctor where
  map_mem' hf := G.map_mem_grading (F.map_mem_grading hf)
  map_d' f := (congrArg G.map (F.map_d f)).trans (G.map_d (F.map f))

/-! ### The induced functors on `Z⁰` and `H⁰` -/

variable [DGCategory C] [DGCategory D] (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]

/-- The functor `Z⁰(C) ⥤ Z⁰(D)` induced by a dg functor. -/
@[simps]
def mapZ0 : Z0 C ⥤ Z0 D where
  obj X := ⟨F.obj X.as⟩
  map f := ⟨F.map f.hom, F.map_mem_cocycles f.mem_cocycles⟩
  map_id X := Z0.hom_ext (F.map_id X.as)
  map_comp f g := Z0.hom_ext (F.map_comp f.hom g.hom)

instance : F.mapZ0.Additive where
  map_add := Z0.hom_ext (F.map_add)

/-- The functor `Z⁰(C) ⥤ Z⁰(D)` induced by a dg functor is compatible with the forgetful
functors. -/
def mapZ0CompForgetIso : F.mapZ0 ⋙ Z0.forget D ≅ Z0.forget C ⋙ F :=
  Iso.refl _

theorem mapZ0_homotopic {X Y : Z0 C} {f g : X ⟶ Y} (h : Z0.homotopic C f g) :
    Z0.homotopic D (F.mapZ0.map f) (F.mapZ0.map g) := by
  rw [Z0.homotopic_iff] at h ⊢
  change F.map f.hom - F.map g.hom ∈ _
  rw [← F.map_sub]
  exact F.map_mem_coboundaries h

/-- The functor `H⁰(C) ⥤ H⁰(D)` induced by a dg functor. -/
def mapH0 : H0 C ⥤ H0 D :=
  CategoryTheory.Quotient.lift _ (F.mapZ0 ⋙ H0.quotient D) fun _ _ _ _ h =>
    (H0.quotient_map_eq_iff _ _).mpr (F.mapZ0_homotopic h)

/-- The functor induced on `H⁰` is compatible with the quotient functors. -/
def quotientCompMapH0Iso : H0.quotient C ⋙ F.mapH0 ≅ F.mapZ0 ⋙ H0.quotient D :=
  CategoryTheory.Quotient.lift.isLift _ _ _

theorem mapH0_map_quotient_map {X Y : Z0 C} (f : X ⟶ Y) :
    F.mapH0.map ((H0.quotient C).map f) = (H0.quotient D).map (F.mapZ0.map f) :=
  CategoryTheory.Quotient.lift_map_functor_map _ _ _ f

end CategoryTheory.Functor
