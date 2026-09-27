import DG.Category.Tensor.Basic

/-!
# Dg bimodules over dg categories

For dg categories `C` and `D`, a dg `(C, D)`-bimodule (`DG.CatBimodule C D`) is a family of dg
abelian groups `B(X, Y)`, `X ∈ C`, `Y ∈ D`, with a left action of `C` (covariant in `X`) and a
right action of `D` (contravariant in `Y`),

  `f • x ∈ B(X', Y)` for `f : X ⟶ X'`,   `x • g ∈ B(X, Y)` for `g : Y ⟶ Y'`, `x ∈ B(X, Y')`,

each satisfying the axioms of a left, respectively right, dg module (for the right action:
`x • (g ≫ g') = (x • g) • g'` and `d (x • g) = d x • g + (-1)^{|x|} x • d g`), and commuting
without sign, `f • (x • g) = (f • x) • g`. This is the Mathlib convention for bimodules over
rings (a left module and a right module, i.e. a module over `Dᵐᵒᵖ`, with commuting actions,
`SMulCommClass`); it is the direct generalization of `DG.DGBimodule`.

Design: the bimodule is recorded as a single structure with both actions, rather than as a left
module over a tensor product `C ⊗ Dᵒᵖ` of dg categories (which is not constructed in the library).
Every bimodule gives, for each `Y ∈ D`, a left dg module `B(-, Y)` over `C`
(`DG.CatBimodule.left`), and for each `X ∈ C`, a right dg module `B(X, -)` over `D`, i.e. a left
dg module over `DGOpposite D` (`DG.CatBimodule.right`, via `DG.CatModule.ofRightAction`), whose
right action is the given one (`DG.CatBimodule.right_ract`).

## Main definitions and results

* `DG.CatBimodule.{w} C D`, with `DG.CatBimodule.left`, `DG.CatBimodule.right`.
* `DG.CatBimodule.tensorObj B M`: for a dg `(C, D)`-bimodule `B` and a left dg module `M` over
  `D`, the left dg module `B ⊗_D M` over `C`, `X ↦ B(X, -) ⊗_D M`, with
  `f • (x ⊗ m) = (f • x) ⊗ m` (`DG.CatBimodule.tensorObj_act_tmul`). No sign appears: `f` acts
  on the left factor.
* `DG.CatBimodule.tensorFunctor B : CatModule D ⥤ CatModule C`, `M ↦ B ⊗_D M`.
-/

open CategoryTheory

universe w w' v₁ v₂ u₁ u₂

noncomputable section

namespace DG

open DGOpposite
open scoped CatModule

/-- A dg `(C, D)`-bimodule: dg abelian groups `obj X Y` for `X ∈ C`, `Y ∈ D`, with a left dg
action of `C` (`lact f : obj X Y →+ obj X' Y` for `f : X ⟶ X'`) and a right dg action of `D`
(`ract g : obj X Y' →+ obj X Y` for `g : Y ⟶ Y'`, the right action `x • g`), which commute:
`f • (x • g) = (f • x) • g`. The left action satisfies the axioms of `DG.CatModule`; the right
action is graded, unital, associative in the form `x • (g ≫ g') = (x • g) • g'` and satisfies the
right Leibniz rule `d (x • g) = d x • g + (-1)^{|x|} • (x • d g)`. -/
structure CatBimodule (C : Type u₁) [Category.{v₁} C] [Preadditive C]
    [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] (D : Type u₂) [Category.{v₂} D] [Preadditive D]
    [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] where
  /-- The dg abelian group attached to a pair of objects. -/
  obj : C → D → Type w
  [isAddCommGroup : ∀ X Y, AddCommGroup (obj X Y)]
  [isDGAddCommGroup : ∀ X Y, DGAddCommGroup (obj X Y)]
  /-- The left action of `C`. -/
  lact : ∀ {X X' : C} {Y : D}, (X ⟶ X') →+ obj X Y →+ obj X' Y
  /-- The right action of `D`: `ract g x` is `x • g`. -/
  ract : ∀ {X : C} {Y Y' : D}, (Y ⟶ Y') →+ obj X Y' →+ obj X Y
  lact_mem' : ∀ {X X' : C} {Y : D} {i j : ℤ} {f : X ⟶ X'} {x : obj X Y}, f ∈ grading i →
    x ∈ grading j → lact f x ∈ grading (i + j)
  lact_id' : ∀ (X : C) (Y : D) (x : obj X Y), lact (𝟙 X) x = x
  lact_comp' : ∀ {X X' X'' : C} {Y : D} (f : X ⟶ X') (f' : X' ⟶ X'') (x : obj X Y),
    lact (f ≫ f') x = lact f' (lact f x)
  d_lact' : ∀ {X X' : C} {Y : D} {i : ℤ} {f : X ⟶ X'}, f ∈ grading i → ∀ x : obj X Y,
    d (lact f x) = lact (d f) x + koszulSign i • lact f (d x)
  ract_mem' : ∀ {X : C} {Y Y' : D} {i j : ℤ} {g : Y ⟶ Y'} {x : obj X Y'}, g ∈ grading i →
    x ∈ grading j → ract g x ∈ grading (j + i)
  ract_id' : ∀ (X : C) (Y : D) (x : obj X Y), ract (𝟙 Y) x = x
  ract_comp' : ∀ {X : C} {Y Y' Y'' : D} (g : Y ⟶ Y') (g' : Y' ⟶ Y'') (x : obj X Y''),
    ract (g ≫ g') x = ract g (ract g' x)
  d_ract' : ∀ {X : C} {Y Y' : D} {j : ℤ} {x : obj X Y'}, x ∈ grading j → ∀ g : Y ⟶ Y',
    d (ract g x) = ract g (d x) + koszulSign j • ract (d g) x
  lact_ract' : ∀ {X X' : C} {Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') (x : obj X Y'),
    lact f (ract g x) = ract g (lact f x)

attribute [instance] CatBimodule.isAddCommGroup CatBimodule.isDGAddCommGroup

namespace CatBimodule

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [∀ X Y : D, DGAddCommGroup (X ⟶ Y)]
  (B : CatBimodule.{w} C D)

/-- The left dg module `B(-, Y)` over `C`. -/
@[simps]
def left (Y : D) : CatModule.{w} C where
  obj X := B.obj X Y
  act := B.lact
  act_mem' := B.lact_mem'
  act_id' X := B.lact_id' X Y
  act_comp' := B.lact_comp'
  d_act' := B.d_lact'

variable [DGCategory D]

/-- The right dg module `B(X, -)` over `D`, as a left dg module over `DGOpposite D`. -/
@[reducible]
def right (X : C) : CatModule.{w} (DGOpposite D) :=
  CatModule.ofRightAction (B.obj X) B.ract B.ract_mem' (B.ract_id' X) B.ract_comp' B.d_ract'

/-- The right action of `B(X, -)` is the right action of `B`. -/
@[simp]
theorem right_ract (X : C) {Y Y' : D} (g : Y ⟶ Y') (x : B.obj X Y') :
    (B.right X).ract g x = B.ract g x :=
  DFunLike.congr_fun (DFunLike.congr_fun
    (koszulTwist_koszulTwist (B.ract (X := X) (Y := Y) (Y' := Y'))) g) x

/-! ### Tensor product with a left module -/

section Tensor

variable (M : CatModule.{w'} D)

theorem balanced_lact {X X' : C} (f : X ⟶ X') :
    CatTensorProduct.Balanced (N := B.right X) (M := M)
      fun Y => (CatTensorProduct.tmulAddHom (B.right X') M Y).comp
        (B.lact (X := X) (X' := X') (Y := Y) f) :=
  fun {Y Y'} g x m => by
    change CatTensorProduct.tmul (N := B.right X') Y (B.lact f ((B.right X).ract g x)) m =
      CatTensorProduct.tmul (N := B.right X') Y' (B.lact f x) (g • m)
    rw [right_ract, B.lact_ract', ← right_ract, CatTensorProduct.ract_tmul]

/-- The action of `f : X ⟶ X'` on `B(X, -) ⊗_D M`, `x ⊗ m ↦ (f • x) ⊗ m`. -/
def tensorAct {X X' : C} (f : X ⟶ X') :
    CatTensorProduct (B.right X) M →+ CatTensorProduct (B.right X') M :=
  CatTensorProduct.lift _ (B.balanced_lact M f)

@[simp]
theorem tensorAct_tmul {X X' : C} (f : X ⟶ X') (Y : D) (x : B.obj X Y) (m : M.obj Y) :
    B.tensorAct M f (CatTensorProduct.tmul Y x m) = CatTensorProduct.tmul Y (B.lact f x) m :=
  CatTensorProduct.lift_tmul _ (B.balanced_lact M f) Y x m

theorem tensorAct_add {X X' : C} (f f' : X ⟶ X') :
    B.tensorAct M (f + f') = B.tensorAct M f + B.tensorAct M f' :=
  CatTensorProduct.addHom_ext fun Y x m => by
    rw [AddMonoidHom.add_apply, tensorAct_tmul, tensorAct_tmul, tensorAct_tmul, map_add,
      AddMonoidHom.add_apply, CatTensorProduct.add_tmul]

theorem tensorAct_mem {X X' : C} {i : ℤ} {f : X ⟶ X'} (hf : f ∈ grading i) {k : ℤ}
    {y : CatTensorProduct (B.right X) M} (hy : y ∈ grading k) :
    B.tensorAct M f y ∈ grading (i + k) := by
  rw [add_comm]
  refine CatTensorProduct.lift_mem_add _ (B.balanced_lact M f) i (fun Y _ _ _ _ hx hm => ?_) hy
  rw [add_right_comm, add_comm _ i]
  exact CatTensorProduct.tmul_mem_grading (B.lact_mem' hf hx) hm

theorem tensorAct_id (X : C) (y : CatTensorProduct (B.right X) M) :
    B.tensorAct M (𝟙 X) y = y := by
  induction y using CatTensorProduct.induction_on with
  | zero => simp
  | tmul Y x m => rw [tensorAct_tmul, B.lact_id']
  | add x y hx hy => rw [map_add, hx, hy]

theorem tensorAct_comp {X X' X'' : C} (f : X ⟶ X') (f' : X' ⟶ X'')
    (y : CatTensorProduct (B.right X) M) :
    B.tensorAct M (f ≫ f') y = B.tensorAct M f' (B.tensorAct M f y) := by
  induction y using CatTensorProduct.induction_on with
  | zero => simp
  | tmul Y x m => rw [tensorAct_tmul, tensorAct_tmul, tensorAct_tmul, B.lact_comp']
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]

theorem d_tensorAct {X X' : C} {i : ℤ} {f : X ⟶ X'} (hf : f ∈ grading i)
    (y : CatTensorProduct (B.right X) M) :
    d (B.tensorAct M f y) = B.tensorAct M (d f) y + koszulSign i • B.tensorAct M f (d y) := by
  induction y using CatTensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, d_add, hx, hy, d_add, map_add, map_add, smul_add]
    abel
  | tmul Y x m =>
    induction x using DG.induction_on with
    | h_zero =>
      simp only [CatTensorProduct.zero_tmul, map_zero, d_zero, _root_.smul_zero, add_zero]
    | h_add x x' hx hx' =>
      rw [CatTensorProduct.add_tmul]
      simp only [map_add, d_add, hx, hx', _root_.smul_add]
      abel
    | h_homogeneous x =>
      rename_i j
      rw [tensorAct_tmul, CatTensorProduct.d_tmul_of_mem Y (B.lact_mem' hf x.2), B.d_lact' hf,
        CatTensorProduct.d_tmul_of_mem Y x.2, map_add, map_units_zsmul, tensorAct_tmul,
        tensorAct_tmul, tensorAct_tmul, CatTensorProduct.add_tmul,
        CatTensorProduct.units_smul_tmul, smul_add, smul_smul, ← koszulSign_add]
      abel

/-- The tensor product `B ⊗_D M` of a dg `(C, D)`-bimodule `B` and a left dg module `M` over
`D`: the left dg module `X ↦ B(X, -) ⊗_D M` over `C`, with `f • (x ⊗ m) = (f • x) ⊗ m`. -/
def tensorObj : CatModule.{max u₂ w w'} C where
  obj X := CatTensorProduct (B.right X) M
  act := AddMonoidHom.mk' (fun f => B.tensorAct M f) fun f f' => B.tensorAct_add M f f'
  act_mem' hf hy := B.tensorAct_mem M hf hy
  act_id' X y := B.tensorAct_id M X y
  act_comp' f f' y := B.tensorAct_comp M f f' y
  d_act' hf y := B.d_tensorAct M hf y

@[simp]
theorem tensorObj_obj (X : C) : (B.tensorObj M).obj X = CatTensorProduct (B.right X) M := rfl

theorem tensorObj_smul {X X' : C} (f : X ⟶ X') (y : (B.tensorObj M).obj X) :
    f • y = B.tensorAct M f y := rfl

/-- The action on `B ⊗_D M`: `f • (x ⊗ m) = (f • x) ⊗ m`. -/
@[simp]
theorem tensorObj_act_tmul {X X' : C} (f : X ⟶ X') (Y : D) (x : B.obj X Y) (m : M.obj Y) :
    (B.tensorObj M).act f (CatTensorProduct.tmul Y x m) =
      CatTensorProduct.tmul Y (B.lact f x) m :=
  B.tensorAct_tmul M f Y x m

variable {M} in
/-- The morphism `B ⊗_D M ⟶ B ⊗_D M'` induced by a morphism `ψ : M ⟶ M'`. -/
@[simps]
def tensorMap {M' : CatModule.{w'} D} (ψ : M ⟶ M') : B.tensorObj M ⟶ B.tensorObj M' where
  app X := CatTensorProduct.map (𝟙 (B.right X)) ψ
  map_mem' hy := CatTensorProduct.map_mem _ _ hy
  map_d' y := CatTensorProduct.map_d _ _ y
  map_smul' {X X'} f y := by
    change CatTensorProduct.map _ ψ (B.tensorAct M f y) =
      B.tensorAct M' f (CatTensorProduct.map _ ψ y)
    induction y using CatTensorProduct.induction_on with
    | zero => simp
    | tmul Y x m =>
      rw [tensorAct_tmul, CatTensorProduct.map_tmul, CatTensorProduct.map_tmul, tensorAct_tmul]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

variable {M} in
@[simp]
theorem tensorMap_tmul {M' : CatModule.{w'} D} (ψ : M ⟶ M') (X : C) (Y : D) (x : B.obj X Y)
    (m : M.obj Y) :
    (B.tensorMap ψ).app X (CatTensorProduct.tmul (N := B.right X) Y x m) =
      CatTensorProduct.tmul (N := B.right X) Y x (ψ.app Y m) := by
  show CatTensorProduct.map (𝟙 (B.right X)) ψ (CatTensorProduct.tmul Y x m) = _
  rw [CatTensorProduct.map_tmul]
  rfl

/-- The functor `M ↦ B ⊗_D M` from left dg modules over `D` to left dg modules over `C`. -/
@[simps]
def tensorFunctor : CatModule.{max u₂ w w'} D ⥤ CatModule.{max u₂ w w'} C where
  obj M := B.tensorObj M
  map ψ := B.tensorMap ψ
  map_id M := CatModule.hom_ext fun X y => by
    induction y using CatTensorProduct.induction_on with
    | zero => simp
    | tmul Y x m => rw [tensorMap_tmul, CatModule.id_app, CatModule.id_app]
    | add x y hx hy => rw [map_add, hx, hy, map_add]
  map_comp ψ ψ' := CatModule.hom_ext fun X y => by
    induction y using CatTensorProduct.induction_on with
    | zero => simp
    | tmul Y x m =>
      rw [CatModule.comp_app, tensorMap_tmul, tensorMap_tmul, tensorMap_tmul, CatModule.comp_app]
    | add x y hx hy => rw [map_add, hx, hy, map_add]

end Tensor

end CatBimodule

end DG
