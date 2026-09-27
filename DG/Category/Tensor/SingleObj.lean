import DG.Category.Tensor.Basic
import DG.Category.Comparison
import DG.Module.TensorProductOver

/-!
# The tensor product over a one-object dg category

For a dg ring `A`, a right dg `A`-module `N` (`DG.DGRightModule`, the right action being
`Module Aᵐᵒᵖ N`) is a right dg module over the one-object dg category `SingleObj A`
(`DG.CatModule.ofDGRightModule`), whose right action (`DG.CatModule.ract`) is the given one,
`n • a = op a • n`; the corresponding left action of `DGOpposite (SingleObj A)` is the Koszul
twist `a • n = (-1)^{|a||n|} • (op a • n)`, as for the opposite dg ring
(`DG.Module.Opposite`).

With the left dg module over `SingleObj A` attached to a left dg `A`-module `M`
(`DG.DGModuleCat.toCatModuleObj`), the tensor product over the dg category `SingleObj A` is the
tensor product over the dg ring `A` (`DG.Module.TensorProductOver`):

* `DG.CatTensorProduct.singleObjEquiv N M : N ⊗_{SingleObj A} M ≅ N ⊗_A M`, an isomorphism of
  dg abelian groups, `n ⊗ m ↦ n ⊗ m`.

This checks that the (sign-free) balancing relations `(n • f) ⊗ m = n ⊗ (f • m)` of
`DG.CatTensorProduct`, written with the right action, are those of `DG.TensorProductOver`.
-/

open CategoryTheory MulOpposite

universe w w' u

noncomputable section

namespace DG

open scoped CatModule

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]

namespace CatModule

variable (N : Type w) [AddCommGroup N] [DGAddCommGroup N] [Module Aᵐᵒᵖ N] [DGRightModule A N]

/-- The right action of a right dg `A`-module, `(a, n) ↦ n • a = op a • n`, as a family of
bi-additive maps indexed by pairs of objects of `SingleObj A`. -/
def singleObjRightAct {X Y : SingleObj A} : (X ⟶ Y) →+ N →+ N :=
  (smulAddHom Aᵐᵒᵖ N).comp (opAddEquiv : A ≃+ Aᵐᵒᵖ).toAddMonoidHom

omit [DGAddCommGroup A] [DGRing A] [DGAddCommGroup N] [DGRightModule A N] in
theorem singleObjRightAct_apply {X Y : SingleObj A} (a : X ⟶ Y) (n : N) :
    singleObjRightAct N a n = op (a : A) • n :=
  rfl

/-- A right dg `A`-module as a right dg module over the one-object dg category `SingleObj A`,
with right action `n • a = op a • n`. -/
@[reducible]
def ofDGRightModule : CatModule.{w} (DGOpposite (SingleObj A)) :=
  ofRightAction (fun _ => N) (singleObjRightAct N)
    (fun hf hn => op_smul_mem_grading hf hn)
    (fun _ n => by
      rw [singleObjRightAct_apply, SingleObj.id_as_one, op_one, one_smul])
    (fun f g n => by
      rw [singleObjRightAct_apply, singleObjRightAct_apply, singleObjRightAct_apply,
        SingleObj.comp_as_mul, op_mul, mul_smul])
    (fun hn f => d_op_smul hn f)

@[simp]
theorem ofDGRightModule_obj (X : DGOpposite (SingleObj A)) : (ofDGRightModule N).obj X = N :=
  rfl

/-- The right action of `ofDGRightModule N` is the given right action. -/
@[simp]
theorem ofDGRightModule_ract {X Y : SingleObj A} (a : X ⟶ Y) (n : N) :
    (ofDGRightModule N).ract a n = op (a : A) • n :=
  DFunLike.congr_fun (DFunLike.congr_fun
    (koszulTwist_koszulTwist (singleObjRightAct N (X := X) (Y := Y))) a) n

end CatModule

namespace CatTensorProduct

variable (N : Type w) [AddCommGroup N] [DGAddCommGroup N] [Module Aᵐᵒᵖ N] [DGRightModule A N]
  (M : DGModuleCat.{w'} A)

theorem balanced_singleObj :
    Balanced (N := CatModule.ofDGRightModule N) (M := DGModuleCat.toCatModuleObj M)
      fun _ => TensorProductOver.tmulAddHom A N M := fun f n m => by
  change TensorProductOver.tmul (M := N) (N := M) A ((CatModule.ofDGRightModule N).ract f n) m =
    TensorProductOver.tmul (M := N) (N := M) A n ((f : A) • m)
  rw [CatModule.ofDGRightModule_ract, TensorProductOver.op_smul_tmul]

theorem balanced_singleObj_symm (X : SingleObj A) (a : A) (n : N) (m : M) :
    tmulAddHom (CatModule.ofDGRightModule N) (DGModuleCat.toCatModuleObj M) X (op a • n) m =
      tmulAddHom (CatModule.ofDGRightModule N) (DGModuleCat.toCatModuleObj M) X n (a • m) := by
  rw [tmulAddHom_apply, tmulAddHom_apply, ← CatModule.ofDGRightModule_ract N
    (X := X) (Y := X) a n]
  exact ract_tmul (N := CatModule.ofDGRightModule N) (M := DGModuleCat.toCatModuleObj M)
    (X := X) (Y := X) a n m

/-- The tensor product over the one-object dg category `SingleObj A` of a right dg `A`-module
`N` and a left dg `A`-module `M` is the tensor product `N ⊗_A M` over the dg ring `A`:
the isomorphism of dg abelian groups `n ⊗ m ↦ n ⊗ m`. -/
def singleObjEquiv :
    DGAddEquiv (CatTensorProduct (CatModule.ofDGRightModule N) (DGModuleCat.toCatModuleObj M))
      (TensorProductOver A N M) :=
  DGAddEquiv.ofAddMonoidHom (lift _ (balanced_singleObj N M))
    (TensorProductOver.lift (M := N) (N := M)
      (tmulAddHom (CatModule.ofDGRightModule N) (DGModuleCat.toCatModuleObj M)
        (SingleObj.star A))
      (balanced_singleObj_symm N M (SingleObj.star A)))
    (fun x => by
      induction x using induction_on with
      | zero => simp
      | tmul X n m =>
        rw [lift_tmul]
        rfl
      | add x y hx hy => rw [map_add, map_add, hx, hy])
    (fun y => by
      induction y using TensorProductOver.induction_on with
      | zero => simp
      | tmul n m =>
        rw [TensorProductOver.lift_tmul]
        exact lift_tmul _ (balanced_singleObj N M) (SingleObj.star A) n m
      | add x y hx hy => rw [map_add, map_add, hx, hy])
    (fun hy => lift_mem _ (balanced_singleObj N M) (fun _ _ _ _ _ hn hm =>
      TensorProductOver.tmul_mem_grading (A := A) (M := N) (N := M) hn hm) hy)
    (lift_d _ (balanced_singleObj N M) fun _ _ _ hn m =>
      TensorProductOver.d_tmul_of_mem (A := A) (M := N) (N := M) hn m)

@[simp]
theorem singleObjEquiv_tmul (X : SingleObj A) (n : N) (m : M) :
    singleObjEquiv N M (tmul X (N := CatModule.ofDGRightModule N) n m) =
      TensorProductOver.tmul A n m :=
  lift_tmul _ (balanced_singleObj N M) X n m

@[simp]
theorem singleObjEquiv_symm_tmul (n : N) (m : M) :
    (singleObjEquiv N M).symm (TensorProductOver.tmul A n m) =
      tmul (SingleObj.star A) (N := CatModule.ofDGRightModule N)
        (M := DGModuleCat.toCatModuleObj M) n m :=
  rfl

end CatTensorProduct

end DG
