import DG.Category.Module
import DG.Module.DirectSum

/-!
# Coproducts of dg modules over a dg category

The category `DG.CatModule C` has arbitrary coproducts, computed objectwise as direct sums: the
coproduct of a family `F j` is `X ↦ ⨁ j, (F j).obj X`, with the componentwise grading,
differential and action.

## Main definitions

* `DG.CatModule.directSum F`, the objectwise direct sum, with the inclusions
  `DG.CatModule.directSumι F j` and the morphism out of it `DG.CatModule.directSumDesc`.
* `DG.CatModule.coproductCocone F`, `DG.CatModule.coproductCoconeIsColimit F`.
* `DG.CatModule.hasCoproducts : HasCoproducts.{w'} (CatModule.{max w w'} C)`.

## Universes

As for `DG.DGModuleCat` (`DG/Homotopy/Products.lean`), coproducts indexed by `J : Type w'` are
constructed in `CatModule.{max w w'} C`.
-/

open CategoryTheory CategoryTheory.Limits DirectSum

universe w w' v u

noncomputable section

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  {J : Type w'} [DecidableEq J] (F : J → CatModule.{max w w'} C)

/-- The objectwise direct sum of a family of dg modules. -/
def directSum : CatModule.{max w w'} C where
  obj X := ⨁ j, (F j).obj X
  act := AddMonoidHom.mk' (fun f => DirectSum.map fun j => (F j).act f) fun f g => by
    refine DirectSum.addHom_ext fun j m => ?_
    simp only [DirectSum.map_of, map_add, AddMonoidHom.add_apply]
  act_mem' {X Y i n f x} hf hx j := by
    change DirectSum.map (fun j => (F j).act f) x j ∈ _
    rw [DirectSum.map_apply]
    exact smul_mem_grading hf (hx j)
  act_id' X x := by
    ext j
    change DirectSum.map (fun j => (F j).act (𝟙 X)) x j = x j
    rw [DirectSum.map_apply]
    exact id_smul (x j)
  act_comp' f g x := by
    ext j
    change DirectSum.map (fun j => (F j).act (f ≫ g)) x j =
      DirectSum.map (fun j => (F j).act g) (DirectSum.map (fun j => (F j).act f) x) j
    rw [DirectSum.map_apply, DirectSum.map_apply, DirectSum.map_apply]
    exact comp_smul f g (x j)
  d_act' {X Y i f} hf x := by
    ext j
    have e : ∀ (n : ℤ) (y : ⨁ j, (F j).obj Y), (n • y) j = n • y j := fun n y =>
      map_zsmul (DFinsupp.evalAddMonoidHom (β := fun j => (F j).obj Y) j) n y
    change d (DirectSum.map (fun j => (F j).act f) x) j =
      (DirectSum.map (fun j => (F j).act (d f)) x +
        (koszulSign i : ℤ) • DirectSum.map (fun j => (F j).act f) (d x)) j
    rw [DirectSum.add_apply, e, DG.DirectSum.coe_d_apply, DirectSum.map_apply,
      DirectSum.map_apply, DirectSum.map_apply, DG.DirectSum.coe_d_apply]
    exact (d_smul hf (x j)).trans (by rw [Units.smul_def]; rfl)

theorem directSum_smul_apply {X Y : C} (f : X ⟶ Y) (x : ⨁ j, (F j).obj X) (j : J) :
    (show ⨁ j, (F j).obj Y from (f • (show (directSum F).obj X from x))) j = f • x j :=
  DirectSum.map_apply _ _ _

/-- The inclusion of a summand into the direct sum. -/
def directSumι (j : J) : F j ⟶ directSum F where
  app X := DirectSum.of (fun j => (F j).obj X) j
  map_mem' hm := DG.DirectSum.of_mem_grading _ j hm
  map_d' {X} m := (DG.DirectSum.d_of (fun j => (F j).obj X) j m).symm
  map_smul' f m := (DirectSum.map_of (fun j => (F j).act f) j m).symm

theorem directSumι_app (j : J) (X : C) (m : (F j).obj X) :
    (directSumι F j).app X m = DirectSum.of (fun j => (F j).obj X) j m := rfl

variable {F} in
/-- The morphism out of the direct sum determined by its restrictions to the summands. -/
def directSumDesc {N : CatModule.{max w w'} C} (φ : ∀ j, F j ⟶ N) : directSum F ⟶ N where
  app X := DirectSum.toAddMonoid fun j => (φ j).app X
  map_mem' {X n x} hx := by
    classical
    change DirectSum.toAddMonoid (fun j => (φ j).app X) x ∈ _
    rw [← DirectSum.sum_support_of x, map_sum]
    refine sum_mem fun j _ => ?_
    rw [DirectSum.toAddMonoid_of]
    exact (φ j).map_mem (hx j)
  map_d' {X} x := by
    have h : (DirectSum.toAddMonoid fun j => (φ j).app X).comp (DG.DirectSum.d _) =
        (d : N.obj X →+ N.obj X).comp (DirectSum.toAddMonoid fun j => (φ j).app X) :=
      DirectSum.addHom_ext fun j m => by
        simp only [AddMonoidHom.comp_apply, DG.DirectSum.d, DirectSum.map_of,
          DirectSum.toAddMonoid_of]
        exact (φ j).map_d m
    exact congrArg (fun χ : (⨁ j, (F j).obj X) →+ N.obj X => χ x) h
  map_smul' {X Y} f x := by
    have h : (DirectSum.toAddMonoid fun j => (φ j).app Y).comp
        (DirectSum.map fun j => (F j).act f) =
        (N.act f).comp (DirectSum.toAddMonoid fun j => (φ j).app X) :=
      DirectSum.addHom_ext fun j m => by
        simp only [AddMonoidHom.comp_apply, DirectSum.map_of, DirectSum.toAddMonoid_of]
        exact (φ j).map_smul f m
    exact congrArg (fun χ : (⨁ j, (F j).obj X) →+ N.obj Y => χ x) h

@[simp]
theorem directSumι_desc {N : CatModule.{max w w'} C} (φ : ∀ j, F j ⟶ N) (j : J) :
    directSumι F j ≫ directSumDesc φ = φ j :=
  hom_ext fun X m => DirectSum.toAddMonoid_of (fun j => (φ j).app X) j m

/-- Two morphisms out of the direct sum agreeing on the summands are equal. -/
theorem directSum_hom_ext {N : CatModule.{max w w'} C} {φ ψ : directSum F ⟶ N}
    (h : ∀ j, directSumι F j ≫ φ = directSumι F j ≫ ψ) : φ = ψ :=
  hom_injective (funext fun X => DirectSum.addHom_ext fun j m => by
    have := congrArg (fun χ : F j ⟶ N => χ.app X m) (h j)
    exact this)

/-- The direct sum, as a cofan. -/
def coproductCocone : Cofan F :=
  Cofan.mk (directSum F) (directSumι F)

@[simp]
theorem coproductCocone_pt : (coproductCocone F).pt = directSum F := rfl

@[simp]
theorem coproductCocone_inj (j : J) : (coproductCocone F).inj j = directSumι F j := rfl

/-- The objectwise direct sum is the coproduct in `CatModule C`. -/
def coproductCoconeIsColimit : IsColimit (coproductCocone F) :=
  mkCofanColimit _ (fun t => directSumDesc t.inj) (fun t j => directSumι_desc F t.inj j)
    fun t m hm => directSum_hom_ext F fun j => by rw [directSumι_desc]; exact hm j

instance hasCoproduct : HasCoproduct F :=
  HasColimit.mk ⟨_, coproductCoconeIsColimit F⟩

omit [DecidableEq J] F

instance hasCoproducts : HasCoproducts.{w'} (CatModule.{max w w'} C) := fun J =>
  { has_colimit := fun K => by
      letI := Classical.decEq J
      exact HasColimit.mk
        ⟨(Cocones.precompose Discrete.natIsoFunctor.hom).obj
          (coproductCocone (K.obj ∘ Discrete.mk)),
          (IsColimit.precomposeHomEquiv _ _).symm (coproductCoconeIsColimit _)⟩ }

instance hasCoproducts' : HasCoproducts.{w} (CatModule.{w} C) :=
  hasCoproducts.{w, w}

end CatModule

end DG
