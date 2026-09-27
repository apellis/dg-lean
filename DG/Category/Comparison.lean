import DG.Category.Module
import DG.Category.SingleObj
import DG.Homotopy.ModuleCat

/-!
# Dg modules over a one-object dg category

For a ring `A` with a dg structure, a dg module over the one-object dg category `SingleObj A`
(`DG.Category.SingleObj`) is the same as a left dg `A`-module: the action of the morphisms
`f : star ⟶ star`, i.e. of the elements of `A`, on the value at the unique object is an
`A`-module structure, because `(a * b) • m = (b ≫ a) • m = a • (b • m)`, and the axioms of a dg
module over `SingleObj A` are those of `DG.DGModule`.

## Main definitions

* `DG.CatModule.singleObjModule M`: the `A`-module structure on `M.obj star` (not an instance),
  and `DG.CatModule.singleObjDGModule M`, the dg module axioms.
* `DG.CatModule.toDGModuleCat : CatModule (SingleObj A) ⥤ DGModuleCat A` and
  `DG.DGModuleCat.toCatModule : DGModuleCat A ⥤ CatModule (SingleObj A)`.
* `DG.CatModule.singleObjEquivalence : CatModule (SingleObj A) ≌ DGModuleCat A`, an equivalence
  of categories whose unit and counit are the identity on elements.
-/

open CategoryTheory

universe w u

namespace DG

variable {A : Type u} [Ring A] [DGAddCommGroup A]

namespace CatModule

variable (M : CatModule.{w} (SingleObj A))

/-- The `A`-module structure on the value at the unique object of a dg module over
`SingleObj A`: `a • m` is the action of `a : star ⟶ star`. -/
@[reducible]
def singleObjModule : Module A (M.obj (SingleObj.star A)) where
  smul a m := M.act (X := SingleObj.star A) (Y := SingleObj.star A) a m
  one_smul m := M.act_id' _ m
  mul_smul a b m := M.act_comp' (X := SingleObj.star A) (Y := SingleObj.star A)
    (Z := SingleObj.star A) b a m
  smul_zero a := map_zero _
  smul_add a := map_add _
  add_smul a b m := by
    change M.act (a + b) m = M.act a m + M.act b m
    rw [map_add, AddMonoidHom.add_apply]
  zero_smul m := by
    change M.act 0 m = 0
    rw [map_zero, AddMonoidHom.zero_apply]

theorem singleObjModule_smul (a : A) (m : M.obj (SingleObj.star A)) :
    letI := singleObjModule M
    a • m = M.act (X := SingleObj.star A) (Y := SingleObj.star A) a m :=
  rfl

/-- The value at the unique object of a dg module over `SingleObj A` is a dg `A`-module. -/
theorem singleObjDGModule :
    letI := singleObjModule M
    DGModule A (M.obj (SingleObj.star A)) :=
  letI := singleObjModule M
  { smul_mem := fun _ _ _ _ ha hm =>
      M.act_mem' (X := SingleObj.star A) (Y := SingleObj.star A) ha hm
    d_smul' := fun ha m => M.d_act' (X := SingleObj.star A) (Y := SingleObj.star A) ha m }

/-- The dg `A`-module underlying a dg module over `SingleObj A`. -/
def toDGModuleCatObj : DGModuleCat.{w} A :=
  letI := singleObjModule M
  haveI := singleObjDGModule M
  DGModuleCat.of A (M.obj (SingleObj.star A))

@[simp]
theorem toDGModuleCatObj_carrier : (toDGModuleCatObj M : Type w) = M.obj (SingleObj.star A) :=
  rfl

variable (A) in
/-- The functor from dg modules over `SingleObj A` to dg `A`-modules: evaluation at the unique
object. -/
@[simps obj]
def toDGModuleCat : CatModule.{w} (SingleObj A) ⥤ DGModuleCat.{w} A where
  obj M := toDGModuleCatObj M
  map {M N} φ := DGModuleCat.Hom.mk
    { toFun := φ.app (SingleObj.star A)
      map_add' := map_add _
      map_smul' := fun a m => φ.map_smul (X := SingleObj.star A) (Y := SingleObj.star A) a m
      map_mem' := fun hm => φ.map_mem hm
      map_d' := fun m => φ.map_d m }

@[simp]
theorem toDGModuleCat_map_apply {M N : CatModule.{w} (SingleObj A)} (φ : M ⟶ N)
    (m : M.obj (SingleObj.star A)) :
    ((toDGModuleCat A).map φ).hom m = φ.app (SingleObj.star A) m :=
  rfl

end CatModule

namespace DGModuleCat

/-- A dg `A`-module as a dg module over `SingleObj A`. -/
@[simps obj]
def toCatModuleObj (M : DGModuleCat.{w} A) : CatModule.{w} (SingleObj A) where
  obj _ := M
  act := smulAddHom A M
  act_mem' hf hm := smul_mem_grading (A := A) hf hm
  act_id' _ m := one_smul A m
  act_comp' f g m := mul_smul (g : A) (f : A) m
  d_act' hf m := d_smul (A := A) hf m

theorem toCatModuleObj_smul (M : DGModuleCat.{w} A) {X Y : SingleObj A} (a : X ⟶ Y) (m : M) :
    (a • m : (toCatModuleObj M).obj Y) = (a : A) • (m : M) :=
  rfl

variable (A) in
/-- The functor from dg `A`-modules to dg modules over `SingleObj A`. -/
@[simps obj]
def toCatModule : DGModuleCat.{w} A ⥤ CatModule.{w} (SingleObj A) where
  obj M := toCatModuleObj M
  map {M N} φ :=
    { app := fun _ => φ.hom.toLinearMap.toAddMonoidHom
      map_mem' := fun hm => φ.hom.map_mem hm
      map_d' := fun m => φ.hom.map_d m
      map_smul' := fun a m => φ.hom.map_smul (a : A) m }

@[simp]
theorem toCatModule_map_app {M N : DGModuleCat.{w} A} (φ : M ⟶ N) (X : SingleObj A) (m : M) :
    ((toCatModule A).map φ).app X m = φ.hom m :=
  rfl

end DGModuleCat

namespace CatModule

variable (A) in
/-- Dg modules over the one-object dg category `SingleObj A` are the same as left dg
`A`-modules: the equivalence of categories `CatModule (SingleObj A) ≌ DGModuleCat A`, given by
evaluation at the unique object. Its unit and counit are the identity on elements. -/
@[simps functor inverse]
def singleObjEquivalence : CatModule.{w} (SingleObj A) ≌ DGModuleCat.{w} A where
  functor := toDGModuleCat A
  inverse := DGModuleCat.toCatModule A
  unitIso := NatIso.ofComponents
    (fun _ => isoMk (fun _ => AddEquiv.refl _) Iff.rfl (fun _ => rfl) (fun _ _ => rfl))
    fun _ => rfl
  counitIso := NatIso.ofComponents
    (fun _ =>
      { hom := DGModuleCat.Hom.mk
          { toFun := fun m => m
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl
            map_mem' := fun hm => hm
            map_d' := fun _ => rfl }
        inv := DGModuleCat.Hom.mk
          { toFun := fun m => m
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl
            map_mem' := fun hm => hm
            map_d' := fun _ => rfl }
        hom_inv_id := rfl
        inv_hom_id := rfl })
    fun _ => rfl
  functor_unitIso_comp _ := rfl

end CatModule

end DG
