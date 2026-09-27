import Mathlib.CategoryTheory.Preadditive.Opposite
import DG.Category.Module

/-!
# Representable dg modules and the dg Yoneda lemma

For an object `X` of a dg category `C`, the representable dg module `C(X, -)`
(`DG.CatModule.representable X`) is `Y ↦ (X ⟶ Y)`, with the action of `C` by postcomposition,
`f • h = h ≫ f`. The Leibniz rule of the action is the Leibniz rule of `C`.

## Main results

* `DG.CatModule.yonedaEquiv : (C(X, -) ⟶ M) ≃+ Z⁰(M X)`, the dg Yoneda lemma: a morphism of dg
  modules out of `C(X, -)` is determined by the image of `𝟙 X`, which is a degree-`0` cocycle of
  `M.obj X`, and every such cocycle arises. It is natural in `M`
  (`DG.CatModule.yonedaEquiv_comp`).
* `DG.CatModule.yoneda : Z⁰(C)ᵒᵖ ⥤ CatModule C`, the contravariant dg Yoneda embedding
  `X ↦ C(X, -)`, sending a degree-`0` cocycle `f : X' ⟶ X` to precomposition with `f`. It is
  fully faithful (`DG.CatModule.yonedaFullyFaithful`) and additive.
-/

open CategoryTheory Opposite

universe v u

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C]

/-- The representable dg module `C(X, -)`: `Y ↦ (X ⟶ Y)`, with `f • h = h ≫ f`. -/
def representable (X : C) : CatModule.{v} C where
  obj Y := X ⟶ Y
  act := AddMonoidHom.mk' (fun f => Preadditive.rightComp X f) fun f g => by
    ext h
    exact Preadditive.comp_add _ _ _ h f g
  act_mem' {_ _ i j f h} hf hh := by
    rw [add_comm]
    exact comp_mem_grading hh hf
  act_id' _ h := Category.comp_id h
  act_comp' f g h := (Category.assoc h f g).symm
  d_act' hf h := d_comp h hf

@[simp]
theorem representable_obj (X Y : C) : (representable X).obj Y = (X ⟶ Y) := rfl

@[simp]
theorem representable_smul {X Y Z : C} (f : Y ⟶ Z) (h : (representable X).obj Y) :
    f • h = (h : X ⟶ Y) ≫ f := rfl

variable {X : C} {M : CatModule.{v} C}

/-- The morphism `C(X, -) ⟶ M` attached to a degree-`0` cocycle `m` of `M.obj X`:
`h ↦ h • m`. -/
@[simps]
def yonedaHom (m : cocycles (M.obj X) 0) : representable X ⟶ M where
  app Y := (M.act (X := X) (Y := Y)).flip (m : M.obj X)
  map_mem' {Y n h} hh := by
    simpa using smul_mem_grading (M := M) hh m.2.1
  map_d' h := (d_smul_of_d_eq_zero_right (M := M) m.2.2 h).symm
  map_smul' f h := comp_smul (M := M) h f m

/-- The dg Yoneda lemma: morphisms of dg modules `C(X, -) ⟶ M` correspond to the degree-`0`
cocycles of `M.obj X`, by evaluation at `𝟙 X`. -/
def yonedaEquiv : (representable X ⟶ M) ≃+ cocycles (M.obj X) 0 where
  toFun φ := ⟨φ.app X (𝟙 X), φ.map_mem (id_mem_grading X),
    show d (φ.app X (𝟙 X)) = 0 by
      rw [← φ.map_d]
      exact (congrArg (φ.app X) (d_id X)).trans (map_zero _)⟩
  invFun m := yonedaHom m
  left_inv φ := hom_ext fun Y h =>
    (φ.map_smul h (𝟙 X)).symm.trans (congrArg (φ.app Y) (Category.id_comp h))
  right_inv m := Subtype.ext (id_smul (M := M) (m : M.obj X))
  map_add' _ _ := rfl

@[simp]
theorem coe_yonedaEquiv_apply (φ : representable X ⟶ M) :
    (yonedaEquiv φ : M.obj X) = φ.app X (𝟙 X) := rfl

@[simp]
theorem yonedaEquiv_symm_app_apply (m : cocycles (M.obj X) 0) {Y : C} (h : X ⟶ Y) :
    (yonedaEquiv.symm m).app Y h = h • (m : M.obj X) := rfl

/-- The dg Yoneda isomorphism is natural in the module. -/
theorem yonedaEquiv_comp {N : CatModule.{v} C} (φ : representable X ⟶ M) (ψ : M ⟶ N) :
    (yonedaEquiv (φ ≫ ψ) : N.obj X) = ψ.app X (yonedaEquiv φ) := rfl

/-- The dg Yoneda isomorphism is natural in the module: the inverse direction. -/
theorem yonedaEquiv_symm_comp {N : CatModule.{v} C} (m : cocycles (M.obj X) 0) (ψ : M ⟶ N) :
    yonedaEquiv.symm m ≫ ψ =
      yonedaEquiv.symm ⟨ψ.app X m, ψ.map_mem m.2.1,
        show d (ψ.app X m) = 0 by rw [← ψ.map_d, m.2.2, map_zero]⟩ :=
  hom_ext fun _ h => ψ.map_smul h (m : M.obj X)

variable (C) in
/-- The contravariant dg Yoneda embedding `Z⁰(C)ᵒᵖ ⥤ CatModule C`, `X ↦ C(X, -)`; a
degree-`0` cocycle `f : X' ⟶ X` is sent to the morphism `C(X, -) ⟶ C(X', -)`, `h ↦ f ≫ h`. -/
@[simps obj]
def yoneda : (DGCategory.Z0 C)ᵒᵖ ⥤ CatModule.{v} C where
  obj X := representable X.unop.as
  map f := yonedaEquiv.symm ⟨f.unop.hom, f.unop.mem_cocycles⟩
  map_id _ := hom_ext fun _ h => Category.id_comp h
  map_comp _ _ := hom_ext fun _ h => Category.assoc _ _ h

@[simp]
theorem yoneda_map_app {X X' : (DGCategory.Z0 C)ᵒᵖ} (f : X ⟶ X') {Y : C}
    (h : (representable X.unop.as).obj Y) :
    ((yoneda C).map f).app Y h = f.unop.hom ≫ (h : X.unop.as ⟶ Y) := rfl

variable (C) in
/-- The dg Yoneda embedding is fully faithful. -/
def yonedaFullyFaithful : (yoneda C).FullyFaithful where
  preimage {X Y} φ :=
    (DGCategory.Z0.homMk (X := Y.unop) (Y := X.unop) (yonedaEquiv φ).1 (yonedaEquiv φ).2).op
  map_preimage _ := yonedaEquiv.injective (yonedaEquiv.apply_symm_apply _)
  preimage_map f :=
    Quiver.Hom.unop_inj (DGCategory.Z0.hom_ext (Category.comp_id f.unop.hom))

instance : (yoneda C).Full := (yonedaFullyFaithful C).full

instance : (yoneda C).Faithful := (yonedaFullyFaithful C).faithful

instance : (yoneda C).Additive where
  map_add := hom_ext fun _ h => Preadditive.add_comp _ _ _ _ _ h

end CatModule

end DG
