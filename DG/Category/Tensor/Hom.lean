import DG.Category.Tensor.Bimodule
import DG.Category.Homotopy.HomComp

set_option backward.isDefEq.respectTransparency false

/-!
# The Hom functor of a dg bimodule and the tensor–Hom adjunction

Let `C` and `D` be dg categories and `B` a dg `(D, C)`-bimodule (`DG.CatBimodule D C`): dg
abelian groups `B(X, Y)` for `X ∈ D`, `Y ∈ C`, with a left action of `D` and a right action of
`C`. Tensoring with `B` is a functor `B ⊗_C - : CatModule C ⥤ CatModule D`
(`DG.CatBimodule.tensorFunctor`). This file constructs its right adjoint

  `HOM_D(B, -) : CatModule D ⥤ CatModule C`,   `HOM_D(B, N)(Y) = HOM_D(B(-, Y), N)`

(`DG.CatBimodule.homObj`, `DG.CatBimodule.homFunctor`), where `B(-, Y)` is the left dg module
`DG.CatBimodule.left B Y` over `D`, and the tensor–Hom adjunction
`DG.CatBimodule.tensorHomAdjunction B : B ⊗_C - ⊣ HOM_D(B, -)`.

## Conventions

A morphism `f : Y ⟶ Y'` of `C` acts on `HOM_D(B, N)` by precomposition with the right action
of `f` on `B`, with the Koszul signs of `docs/CONVENTIONS.md`: for homogeneous `f`, `w` and `x`,

  `(f • w)(x) = (-1)^{|f| |w|} w (f • x) = (-1)^{|f| (|w| + |x|)} w (x • f)`,

where `f • x = (-1)^{|f||x|} x • f` is the left action of the opposite dg category on the right
dg module `B(X, -)` (`DG.CatModule.ofRightAction`); the map `x ↦ f • x` is a cochain
`B(-, Y') ⟶ B(-, Y)` of degree `|f|` (`DG.CatBimodule.ractCochain`). The adjunction bijection
sends `Φ : B ⊗_C M ⟶ N` to `m ↦ (x ↦ (-1)^{|x||m|} Φ (x ⊗ m))`, the sign being that of the
exchange of `x` and `m` (`DG.CatBimodule.homOfTensor`), with inverse
`x ⊗ m ↦ (-1)^{|x||m|} ψ(m)(x)` (`DG.CatBimodule.tensorOfHom`).

## Universes

`HOM_D(B(-, Y), N)` is defined for `B(-, Y)` and `N` with values in the same universe `w`, and
lives in `Type (max u₂ w)`, `u₂` the universe of the objects of `D`; `B ⊗_C M` lives in the
universe of `M` provided it contains the objects of `C`. The adjunction is therefore stated for
bimodules and modules with values in `Type (max u₁ u₂ w)`.
-/

open CategoryTheory

universe w v₁ v₂ u₁ u₂

noncomputable section

namespace DG

open DGOpposite
open scoped CatModule
open CatModule (HOM)

namespace CatBimodule

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [∀ X Y : D, DGAddCommGroup (X ⟶ Y)]

private theorem ks_eq {m n : ℤ} (k : ℤ) (h : m - n = 2 * k) : koszulSign m = koszulSign n :=
  (Int.negOnePow_eq_iff m n).mpr ⟨k, by omega⟩

private theorem map_units {A A' : Type*} [AddCommGroup A] [AddCommGroup A'] (f : A →+ A')
    (u : ℤˣ) (x : A) : f (u • x) = u • f x := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

section RightActCochain

variable (B : CatBimodule.{w} D C)

/-- The action of `f : Y ⟶ Y'` on `B(X, -)` as a left dg module over `DGOpposite C`:
`f • x = (-1)^{|f||x|} x • f`. -/
theorem homOp_smul_of_mem (X : D) {Y Y' : C} {i j : ℤ} {f : Y ⟶ Y'} (hf : f ∈ grading i)
    {x : B.obj X Y'} (hx : x ∈ grading j) :
    (B.right X).act (homOp f) x = koszulSign (i * j) • B.ract f x :=
  koszulTwist_apply_of_mem _ hf hx

/-- The right action of a homogeneous morphism `f : Y ⟶ Y'` of `C` of degree `i`, with the
Koszul sign, as a cochain `B(-, Y') ⟶ B(-, Y)` of degree `i` of left dg modules over `D`:
`x ↦ f • x = (-1)^{|f||x|} x • f`. -/
def ractCochain {Y Y' : C} {i : ℤ} (f : Y ⟶ Y') (hf : f ∈ grading i) :
    CatModule.Cochain (B.left Y') (B.left Y) i where
  app X := (B.right X).act (homOp f)
  map_mem' {X j x} hx := by
    rw [add_comm]
    exact CatModule.smul_mem_grading (M := B.right X) (f := homOp f) hf hx
  map_smul' {X X' k g} hg x := by
    change (B.right X').act (homOp f) (B.lact g x) =
      koszulSign (i * k) • B.lact g ((B.right X).act (homOp f) x)
    induction x using DG.induction_on with
    | h_zero => simp
    | h_add x x' hx hx' =>
      rw [map_add, map_add, hx, hx', map_add, map_add, _root_.smul_add]
    | h_homogeneous x =>
      rename_i j
      rw [homOp_smul_of_mem B X' hf (B.lact_mem' hg x.2), homOp_smul_of_mem B X hf x.2,
        map_units, smul_smul, ← koszulSign_add, B.lact_ract']
      congr 1
      exact congrArg koszulSign (by ring)

variable {B}

theorem ractCochain_app_of_mem {Y Y' : C} {i j : ℤ} {f : Y ⟶ Y'} (hf : f ∈ grading i) {X : D}
    {x : B.obj X Y'} (hx : x ∈ grading j) :
    (B.ractCochain f hf).app X x = koszulSign (i * j) • B.ract f x :=
  homOp_smul_of_mem B X hf hx

theorem ractCochain_add {Y Y' : C} {i : ℤ} {f f' : Y ⟶ Y'} (hf : f ∈ grading i)
    (hf' : f' ∈ grading i) :
    B.ractCochain (f + f') (add_mem hf hf') = B.ractCochain f hf + B.ractCochain f' hf' :=
  CatModule.Cochain.ext fun X x => by
    change (B.right X).act (homOp (f + f')) x = (B.right X).act (homOp f) x +
      (B.right X).act (homOp f') x
    rw [show homOp (f + f') = homOp f + homOp f' from rfl, map_add, AddMonoidHom.add_apply]

theorem ractCochain_zero {Y Y' : C} (i : ℤ) :
    B.ractCochain (0 : Y ⟶ Y') (zero_mem (grading i)) = 0 :=
  CatModule.Cochain.ext fun X x => by
    change (B.right X).act (homOp (0 : Y ⟶ Y')) x = 0
    rw [show homOp (0 : Y ⟶ Y') = 0 from rfl, map_zero, AddMonoidHom.zero_apply]

theorem ractCochain_id (Y : C) :
    B.ractCochain (𝟙 Y) (id_mem_grading Y) = CatModule.Cochain.id (B.left Y) :=
  CatModule.Cochain.ext fun X x => CatModule.id_smul (M := B.right X) (X := op Y) x

theorem ractCochain_comp {Y Y' Y'' : C} {i i' : ℤ} {f : Y ⟶ Y'} (hf : f ∈ grading i)
    {f' : Y' ⟶ Y''} (hf' : f' ∈ grading i') (X : D) (x : B.obj X Y'') :
    (B.ractCochain (f ≫ f') (comp_mem_grading hf hf')).app X x =
      koszulSign (i * i') • (B.ractCochain f hf).app X ((B.ractCochain f' hf').app X x) := by
  induction x using DG.induction_on with
  | h_zero => simp
  | h_add x x' hx hx' => rw [map_add, hx, hx', map_add, map_add, _root_.smul_add]
  | h_homogeneous x =>
    rename_i j
    rw [ractCochain_app_of_mem _ x.2, ractCochain_app_of_mem _ x.2, map_units,
      ractCochain_app_of_mem _ (B.ract_mem' hf' x.2), smul_smul, smul_smul,
      ← koszulSign_add, ← koszulSign_add, B.ract_comp']
    congr 1
    exact ks_eq (-(i * i')) (by ring)

theorem δ_ractCochain {Y Y' : C} {i : ℤ} {f : Y ⟶ Y'} (hf : f ∈ grading i) :
    CatModule.δ i (i + 1) (B.ractCochain f hf) = B.ractCochain (d f) (d_mem hf) :=
  CatModule.Cochain.ext fun X x => by
    rw [CatModule.δ_apply _ _ rfl]
    have h := CatModule.d_smul (M := B.right X) (f := homOp f) hf x
    change d ((B.right X).act (homOp f) x) = (B.right X).act (homOp (d f)) x +
      koszulSign i • (B.right X).act (homOp f) (d x) at h
    change d ((B.right X).act (homOp f) x) - koszulSign i • (B.right X).act (homOp f) (d x) =
      (B.right X).act (homOp (d f)) x
    rw [h]
    exact add_sub_cancel_right _ _

end RightActCochain

/-! ### The Hom module -/

section HomObj

variable (B : CatBimodule.{w} D C) (N : CatModule.{w} D)

/-- The action of `f : Y ⟶ Y'` on `HOM_D(B(-, Y), N)`: on homogeneous `f`, precomposition with
the cochain `x ↦ f • x` with the Koszul sign, `(f • w)(x) = (-1)^{|f||w|} w (f • x)`. -/
def homAct {Y Y' : C} : (Y ⟶ Y') →+ HOM (B.left Y) N →+ HOM (B.left Y') N :=
  liftHomogeneous (grading (M := Y ⟶ Y')) fun i =>
    { toFun := fun f => HOM.precompCochain (B.ractCochain f.1 f.2)
      map_zero' := AddMonoidHom.ext fun w => by
        have e : B.ractCochain ((0 : grading (M := Y ⟶ Y') i) : Y ⟶ Y')
            (0 : grading (M := Y ⟶ Y') i).2 = 0 := ractCochain_zero (B := B) i
        rw [AddMonoidHom.zero_apply, e, HOM.precompCochain_zero]
      map_add' := fun f f' => AddMonoidHom.ext fun w => by
        rw [AddMonoidHom.add_apply, ← HOM.precompCochain_add, ← ractCochain_add (B := B) f.2 f'.2]
        rfl }

variable {B N}

theorem homAct_of_mem {Y Y' : C} {i : ℤ} {f : Y ⟶ Y'} (hf : f ∈ grading i)
    (w : HOM (B.left Y) N) : B.homAct N f w = HOM.precompCochain (B.ractCochain f hf) w := by
  rw [homAct, liftHomogeneous_of_mem _ _ hf]
  rfl

theorem homAct_mem {Y Y' : C} {i j : ℤ} {f : Y ⟶ Y'} (hf : f ∈ grading i)
    {w : HOM (B.left Y) N} (hw : w ∈ grading j) : B.homAct N f w ∈ grading (i + j) := by
  rw [homAct_of_mem hf]
  exact HOM.precompCochain_mem _ hw

theorem homAct_id (Y : C) (w : HOM (B.left Y) N) : B.homAct N (𝟙 Y) w = w := by
  rw [homAct_of_mem (id_mem_grading Y), ractCochain_id, HOM.precompCochain_id]

theorem homAct_comp {Y Y' Y'' : C} (f : Y ⟶ Y') (f' : Y' ⟶ Y'') (w : HOM (B.left Y) N) :
    B.homAct N (f ≫ f') w = B.homAct N f' (B.homAct N f w) := by
  induction f using DG.induction_on with
  | h_zero => simp
  | h_add f g hf hg =>
    rw [Preadditive.add_comp, map_add, AddMonoidHom.add_apply, hf, hg, map_add,
      AddMonoidHom.add_apply, map_add]
  | h_homogeneous f =>
    rename_i i
    induction f' using DG.induction_on with
    | h_zero => simp
    | h_add f' g' hf' hg' =>
      rw [Preadditive.comp_add, map_add, AddMonoidHom.add_apply, hf', hg', map_add,
        AddMonoidHom.add_apply]
    | h_homogeneous f' =>
      rename_i i'
      rw [homAct_of_mem (comp_mem_grading f.2 f'.2), homAct_of_mem f.2, homAct_of_mem f'.2,
        HOM.precompCochain_precompCochain]
      induction w using DirectSum.induction_on with
      | zero => simp
      | add w w' hw hw' => rw [map_add, hw, hw', map_add, _root_.smul_add]
      | of j w =>
        rw [HOM.precompCochain_of, HOM.precompCochain_of]
        simp only [← HOM.of_units_smul, smul_smul]
        refine HOM.of_congr (by ring) fun X x => ?_
        rw [CatModule.Cochain.units_smul_apply, CatModule.Cochain.units_smul_apply,
          CatModule.Cochain.comp_apply, CatModule.Cochain.comp_apply, CatModule.Cochain.comp_apply,
          ractCochain_comp f.2 f'.2, map_units _,
          smul_smul, ← koszulSign_add, ← koszulSign_add]
        congr 1
        exact congrArg koszulSign (by ring)

theorem d_homAct {Y Y' : C} {i : ℤ} {f : Y ⟶ Y'} (hf : f ∈ grading i) (w : HOM (B.left Y) N) :
    d (B.homAct N f w) = B.homAct N (d f) w + koszulSign i • B.homAct N f (d w) := by
  rw [homAct_of_mem hf, homAct_of_mem (d_mem hf), homAct_of_mem hf, HOM.d_precompCochain,
    δ_ractCochain]

variable (B N) in
/-- The dg module `HOM_D(B, N)` over `C` attached to a dg `(D, C)`-bimodule `B` and a dg module
`N` over `D`: `Y ↦ HOM_D(B(-, Y), N)`, with `(f • w)(x) = (-1)^{|f||w|} w (f • x)`. It is
reducible, so that its values are syntactically Hom complexes. -/
@[reducible]
def homObj : CatModule.{max u₂ w} C where
  obj Y := HOM (B.left Y) N
  act := B.homAct N
  act_mem' hf hw := homAct_mem hf hw
  act_id' Y w := homAct_id Y w
  act_comp' f f' w := homAct_comp f f' w
  d_act' hf w := d_homAct hf w

theorem homObj_obj (Y : C) : (B.homObj N).obj Y = HOM (B.left Y) N := rfl

theorem homObj_act {Y Y' : C} (f : Y ⟶ Y') (w : (B.homObj N).obj Y) :
    (B.homObj N).act f w = B.homAct N f w := rfl

variable {N' N'' : CatModule.{w} D}

variable (B) in
/-- The morphism `HOM_D(B, N) ⟶ HOM_D(B, N')` induced by `φ : N ⟶ N'`, by postcomposition. -/
@[simps]
def homMap (φ : N ⟶ N') : B.homObj N ⟶ B.homObj N' where
  app Y := HOM.postcompCochain (CatModule.Cochain.ofHom φ)
  map_mem' hw := by
    have := HOM.postcompCochain_mem (CatModule.Cochain.ofHom φ) hw
    rwa [add_zero] at this
  map_d' {Y} w := by
    have h := HOM.d_postcompCochain (P := B.left Y) (CatModule.Cochain.ofHom φ) w
    rw [CatModule.δ_ofHom, HOM.postcompCochain_zero, zero_add, koszulSign_zero, one_smul] at h
    exact h.symm
  map_smul' {Y Y'} f w := by
    change HOM.postcompCochain (CatModule.Cochain.ofHom φ) (B.homAct N f w) =
      B.homAct N' f (HOM.postcompCochain (CatModule.Cochain.ofHom φ) w)
    induction f using DG.induction_on with
    | h_zero => simp
    | h_add f g hf hg => rw [map_add, AddMonoidHom.add_apply, map_add, hf, hg, map_add]; rfl
    | h_homogeneous f =>
      rw [homAct_of_mem f.2, homAct_of_mem f.2, HOM.postcompCochain_precompCochain, mul_zero,
        koszulSign_zero,
        one_smul]

variable (B) in
/-- The functor `HOM_D(B, -) : CatModule D ⥤ CatModule C` of a dg `(D, C)`-bimodule `B`. -/
@[simps]
def homFunctor : CatModule.{w} D ⥤ CatModule.{max u₂ w} C where
  obj N := B.homObj N
  map φ := B.homMap φ
  map_id N := CatModule.hom_ext fun Y w => by
    change HOM.postcompCochain (CatModule.Cochain.ofHom (𝟙 N)) w = w
    rw [CatModule.Cochain.ofHom_id, HOM.postcompCochain_id]
  map_comp φ ψ := CatModule.hom_ext fun Y w => by
    change HOM.postcompCochain (CatModule.Cochain.ofHom (φ ≫ ψ)) w =
      HOM.postcompCochain (CatModule.Cochain.ofHom ψ)
        (HOM.postcompCochain (CatModule.Cochain.ofHom φ) w)
    rw [HOM.postcompCochain_postcompCochain, CatModule.Cochain.ofHom_comp]

/-- The Hom functor of a dg bimodule is additive. -/
instance homFunctor_additive : (B.homFunctor : CatModule.{w} D ⥤ CatModule.{max u₂ w} C).Additive
    where
  map_add {_ _ f g} := CatModule.hom_ext fun Y w => by
    change HOM.postcompCochain (CatModule.Cochain.ofHom (f + g)) w =
      HOM.postcompCochain (CatModule.Cochain.ofHom f) w +
        HOM.postcompCochain (CatModule.Cochain.ofHom g) w
    rw [CatModule.Cochain.ofHom_add, HOM.postcompCochain_add]

end HomObj

/-! ### The tensor–Hom adjunction -/

section Adjunction

variable (B : CatBimodule.{max u₁ u₂ w} D C) {M : CatModule.{max u₁ u₂ w} C}
  {N : CatModule.{max u₁ u₂ w} D}

/-- The biadditive map `(x, m) ↦ (-1)^{|x||m|} Φ (x ⊗ m)` attached to `Φ : B ⊗_C M ⟶ N`. -/
def tensorPairing (Φ : B.tensorObj M ⟶ N) (X : D) (Y : C) : B.obj X Y →+ M.obj Y →+ N.obj X :=
  koszulTwist ((CatTensorProduct.tmulAddHom (B.right X) M Y).compr₂ (Φ.app X))

variable {B}

theorem tensorPairing_of_mem (Φ : B.tensorObj M ⟶ N) {X : D} {Y : C} {i j : ℤ} {x : B.obj X Y}
    (hx : x ∈ grading i) {m : M.obj Y} (hm : m ∈ grading j) :
    B.tensorPairing Φ X Y x m =
      koszulSign (i * j) • Φ.app X (CatTensorProduct.tmul (N := B.right X) Y x m) :=
  koszulTwist_apply_of_mem ((CatTensorProduct.tmulAddHom (B.right X) M Y).compr₂ (Φ.app X)) hx hm

variable (B) in
/-- The cochain `x ↦ (-1)^{|x||m|} Φ (x ⊗ m)` of degree `j` attached to `Φ : B ⊗_C M ⟶ N` and
`m ∈ M(Y)ʲ`. -/
def homOfTensorCochain (Φ : B.tensorObj M ⟶ N) (Y : C) {j : ℤ} (m : M.obj Y)
    (hm : m ∈ grading j) : CatModule.Cochain (B.left Y) N j where
  app X := (B.tensorPairing Φ X Y).flip m
  map_mem' {X i x} hx := by
    change B.tensorPairing Φ X Y x m ∈ _
    rw [tensorPairing_of_mem Φ hx hm]
    exact units_smul_mem_grading _ (Φ.map_mem (CatTensorProduct.tmul_mem_grading hx hm))
  map_smul' {X X' k g} hg x := by
    change B.tensorPairing Φ X' Y (B.lact g x) m =
      koszulSign (j * k) • N.act g (B.tensorPairing Φ X Y x m)
    induction x using DG.induction_on with
    | h_zero => simp
    | h_add x x' hx hx' =>
      rw [map_add, map_add, AddMonoidHom.add_apply, hx, hx', map_add, AddMonoidHom.add_apply,
        map_add, _root_.smul_add]
    | h_homogeneous x =>
      rename_i i
      rw [tensorPairing_of_mem Φ (B.lact_mem' hg x.2) hm, tensorPairing_of_mem Φ x.2 hm,
        ← tensorObj_act_tmul, CatModule.act_apply, CatModule.act_apply, Φ.map_smul,
        CatModule.smul_units_smul, smul_smul, ← koszulSign_add]
      congr 1
      exact congrArg koszulSign (by ring)

theorem homOfTensorCochain_app (Φ : B.tensorObj M ⟶ N) {Y : C} {j : ℤ} {m : M.obj Y}
    (hm : m ∈ grading j) (X : D) (x : B.obj X Y) :
    (B.homOfTensorCochain Φ Y m hm).app X x = B.tensorPairing Φ X Y x m :=
  rfl

theorem homOfTensorCochain_add (Φ : B.tensorObj M ⟶ N) {Y : C} {j : ℤ} {m m' : M.obj Y}
    (hm : m ∈ grading j) (hm' : m' ∈ grading j) :
    B.homOfTensorCochain Φ Y (m + m') (add_mem hm hm') =
      B.homOfTensorCochain Φ Y m hm + B.homOfTensorCochain Φ Y m' hm' :=
  CatModule.Cochain.ext fun X x => by
    rw [CatModule.Cochain.add_apply, homOfTensorCochain_app, homOfTensorCochain_app,
      homOfTensorCochain_app, map_add]

theorem homOfTensorCochain_zero (Φ : B.tensorObj M ⟶ N) (Y : C) (j : ℤ) :
    B.homOfTensorCochain Φ Y (0 : M.obj Y) (zero_mem (grading j)) = 0 :=
  CatModule.Cochain.ext fun X x => by
    rw [CatModule.Cochain.zero_apply, homOfTensorCochain_app, map_zero]

variable (B) in
/-- The additive map `M(Y) →+ HOM_D(B(-, Y), N)` attached to `Φ : B ⊗_C M ⟶ N`. -/
def homOfTensorApp (Φ : B.tensorObj M ⟶ N) (Y : C) : M.obj Y →+ HOM (B.left Y) N :=
  liftHomogeneous (grading (M := M.obj Y)) fun j =>
    { toFun := fun m => DirectSum.of (fun n => CatModule.Cochain (B.left Y) N n) j
        (B.homOfTensorCochain Φ Y m.1 m.2)
      map_zero' := by
        rw [← map_zero (DirectSum.of (fun n => CatModule.Cochain (B.left Y) N n) j)]
        congr 1
        exact homOfTensorCochain_zero Φ Y j
      map_add' := fun m m' => by
        rw [← map_add]
        congr 1
        exact homOfTensorCochain_add Φ m.2 m'.2 }

theorem homOfTensorApp_of_mem (Φ : B.tensorObj M ⟶ N) {Y : C} {j : ℤ} {m : M.obj Y}
    (hm : m ∈ grading j) :
    B.homOfTensorApp Φ Y m =
      DirectSum.of (fun n => CatModule.Cochain (B.left Y) N n) j
        (B.homOfTensorCochain Φ Y m hm) := by
  rw [homOfTensorApp, liftHomogeneous_of_mem _ _ hm]
  rfl

theorem tensorPairing_d (Φ : B.tensorObj M ⟶ N) {X : D} {Y : C} {j : ℤ} {m : M.obj Y}
    (hm : m ∈ grading j) (x : B.obj X Y) :
    B.tensorPairing Φ X Y x (d m) =
      d (B.tensorPairing Φ X Y x m) - koszulSign j • B.tensorPairing Φ X Y (d x) m := by
  induction x using DG.induction_on with
  | h_zero => simp
  | h_add x x' hx hx' =>
    rw [map_add, AddMonoidHom.add_apply, hx, hx', map_add, AddMonoidHom.add_apply, d_add,
      map_add, AddMonoidHom.add_apply, _root_.smul_add]
    abel
  | h_homogeneous x =>
    rename_i i
    rw [tensorPairing_of_mem Φ x.2 (d_mem hm), tensorPairing_of_mem Φ x.2 hm,
      tensorPairing_of_mem Φ (d_mem x.2) hm, d_units_smul, ← Φ.map_d]
    erw [CatTensorProduct.d_tmul_of_mem (N := B.right X) Y x.2]
    rw [map_add, map_units,
      _root_.smul_add, smul_smul, smul_smul, ← koszulSign_add, ← koszulSign_add,
      show koszulSign (j + (i + 1) * j) = koszulSign (i * j) from ks_eq j (by ring),
      add_sub_cancel_left]
    congr 1
    exact congrArg koszulSign (by ring)

theorem homOfTensorCochain_d (Φ : B.tensorObj M ⟶ N) {Y : C} {j : ℤ} {m : M.obj Y}
    (hm : m ∈ grading j) :
    B.homOfTensorCochain Φ Y (d m) (d_mem hm) =
      CatModule.δ j (j + 1) (B.homOfTensorCochain Φ Y m hm) := by
  refine CatModule.Cochain.ext fun X x => ?_
  rw [CatModule.δ_apply _ _ rfl]
  exact tensorPairing_d Φ hm x

theorem homOfTensorCochain_smul (Φ : B.tensorObj M ⟶ N) {Y Y' : C} {i j : ℤ} {f : Y ⟶ Y'}
    (hf : f ∈ grading i) {m : M.obj Y} (hm : m ∈ grading j) (X : D) (x : B.obj X Y') :
    (B.homOfTensorCochain Φ Y' (f • m) (CatModule.smul_mem_grading hf hm)).app X x =
      koszulSign (i * j) •
        (B.homOfTensorCochain Φ Y m hm).app X ((B.ractCochain f hf).app X x) := by
  rw [homOfTensorCochain_app, homOfTensorCochain_app]
  induction x using DG.induction_on with
  | h_zero => simp
  | h_add x x' hx hx' =>
    rw [map_add, AddMonoidHom.add_apply, hx, hx', map_add, map_add, AddMonoidHom.add_apply,
      _root_.smul_add]
  | h_homogeneous x =>
    rename_i a
    rw [tensorPairing_of_mem Φ x.2 (CatModule.smul_mem_grading hf hm),
      ractCochain_app_of_mem hf x.2, map_units, AddMonoidHom.smul_apply,
      tensorPairing_of_mem Φ (B.ract_mem' hf x.2) hm, smul_smul, smul_smul,
      ← koszulSign_add, ← koszulSign_add, ← right_ract, CatTensorProduct.ract_tmul]
    congr 1
    exact ks_eq (-(i * j)) (by ring)

variable (B) in
/-- The morphism `M ⟶ HOM_D(B, N)` attached to `Φ : B ⊗_C M ⟶ N`:
`m ↦ (x ↦ (-1)^{|x||m|} Φ (x ⊗ m))`. -/
def homOfTensor (Φ : B.tensorObj M ⟶ N) : M ⟶ B.homObj N where
  app := B.homOfTensorApp Φ
  map_mem' {Y j m} hm := ⟨_, (homOfTensorApp_of_mem Φ hm).symm⟩
  map_d' {Y} m := by
    show B.homOfTensorApp Φ Y (d m) = d (M := HOM (B.left Y) N) (B.homOfTensorApp Φ Y m)
    induction m using DG.induction_on with
    | h_zero => simp
    | h_add m m' hm hm' => rw [d_add, map_add, hm, hm', map_add, d_add]
    | h_homogeneous m =>
      rw [homOfTensorApp_of_mem Φ (d_mem m.2), homOfTensorApp_of_mem Φ m.2, HOM.d_of,
        homOfTensorCochain_d]
  map_smul' {Y Y'} f m := by
    show B.homOfTensorApp Φ Y' (f • m) = B.homAct N f (B.homOfTensorApp Φ Y m)
    induction f using DG.induction_on with
    | h_zero => simp [CatModule.zero_smul]
    | h_add f g hf hg =>
      rw [CatModule.add_smul, map_add, hf, hg, map_add, AddMonoidHom.add_apply]
    | h_homogeneous f =>
      rename_i i
      induction m using DG.induction_on with
      | h_zero => simp [CatModule.smul_zero]
      | h_add m m' hm hm' => rw [CatModule.smul_add, map_add, hm, hm', map_add, map_add]
      | h_homogeneous m =>
        rename_i j
        rw [homOfTensorApp_of_mem Φ (CatModule.smul_mem_grading f.2 m.2),
          homOfTensorApp_of_mem Φ m.2, homAct_of_mem f.2, HOM.precompCochain_of,
          ← HOM.of_units_smul]
        congr 1
        exact CatModule.Cochain.ext fun X x => homOfTensorCochain_smul Φ f.2 m.2 X x

theorem homOfTensor_app_of_mem (Φ : B.tensorObj M ⟶ N) {Y : C} {j : ℤ} {m : M.obj Y}
    (hm : m ∈ grading j) :
    (B.homOfTensor Φ).app Y m =
      DirectSum.of (fun n => CatModule.Cochain (B.left Y) N n) j
        (B.homOfTensorCochain Φ Y m hm) :=
  homOfTensorApp_of_mem Φ hm

variable (B) in
/-- The biadditive map `(x, m) ↦ (-1)^{|x||m|} ψ(m)(x)` attached to `ψ : M ⟶ HOM_D(B, N)`. -/
def homPairing (ψ : M ⟶ B.homObj N) (X : D) (Y : C) : B.obj X Y →+ M.obj Y →+ N.obj X :=
  koszulTwist ((HOM.eval (B.left Y) N X).comp (ψ.app Y)).flip

theorem homPairing_of_mem (ψ : M ⟶ B.homObj N) {X : D} {Y : C} {a j : ℤ} {x : B.obj X Y}
    (hx : x ∈ grading a) {m : M.obj Y} (hm : m ∈ grading j) :
    B.homPairing ψ X Y x m = koszulSign (a * j) • HOM.eval (B.left Y) N X (ψ.app Y m) x :=
  koszulTwist_apply_of_mem ((HOM.eval (B.left Y) N X).comp (ψ.app Y)).flip hx hm

/-- The value of `ψ : M ⟶ HOM_D(B, N)` at a homogeneous element of degree `j` is a cochain of
degree `j`. -/
theorem exists_app_eq_of (ψ : M ⟶ B.homObj N) {Y : C} {j : ℤ} {m : M.obj Y}
    (hm : m ∈ grading j) : ∃ w : CatModule.Cochain (B.left Y) N j,
      ψ.app Y m = DirectSum.of (fun n => CatModule.Cochain (B.left Y) N n) j w := by
  obtain ⟨w, hw⟩ := ψ.map_mem hm
  exact ⟨w, hw.symm⟩

theorem homPairing_balanced (ψ : M ⟶ B.homObj N) (X : D) :
    CatTensorProduct.Balanced (N := B.right X) (M := M) fun Y => B.homPairing ψ X Y := by
  intro Y Y' f x m
  rw [right_ract]
  induction f using DG.induction_on with
  | h_zero => simp [CatModule.zero_smul]
  | h_add f g hf hg =>
    rw [map_add, AddMonoidHom.add_apply, map_add, AddMonoidHom.add_apply, hf, hg,
      CatModule.add_smul, map_add]
  | h_homogeneous f =>
    rename_i i
    induction x using DG.induction_on with
    | h_zero => simp
    | h_add x x' hx hx' => rw [map_add, map_add, AddMonoidHom.add_apply, hx, hx', map_add,
        AddMonoidHom.add_apply]
    | h_homogeneous x =>
      rename_i a
      induction m using DG.induction_on with
      | h_zero => simp [CatModule.smul_zero]
      | h_add m m' hm hm' => rw [map_add, hm, hm', CatModule.smul_add, map_add]
      | h_homogeneous m =>
        rename_i j
        obtain ⟨w, hw⟩ := exists_app_eq_of ψ m.2
        have hfm := ψ.map_smul (f : Y ⟶ Y') (m : M.obj Y)
        change ψ.app Y' ((f : Y ⟶ Y') • (m : M.obj Y)) = B.homAct N f (ψ.app Y m) at hfm
        rw [homPairing_of_mem ψ (B.ract_mem' f.2 x.2) m.2,
          homPairing_of_mem ψ x.2 (CatModule.smul_mem_grading f.2 m.2), hfm, hw,
          homAct_of_mem f.2, HOM.precompCochain_of, map_units, AddMonoidHom.smul_apply, HOM.eval_of,
          HOM.eval_of, CatModule.Cochain.comp_apply, ractCochain_app_of_mem f.2 x.2,
          CatModule.Cochain.map_units_smul, smul_smul, smul_smul, ← koszulSign_add,
          ← koszulSign_add]
        congr 1
        exact ks_eq (-(a * i)) (by ring)

theorem homPairing_mem (ψ : M ⟶ B.homObj N) (X : D) (Y : C) {a j : ℤ} {x : B.obj X Y}
    (hx : x ∈ grading a) {m : M.obj Y} (hm : m ∈ grading j) :
    B.homPairing ψ X Y x m ∈ grading (a + j) := by
  obtain ⟨w, hw⟩ := exists_app_eq_of ψ hm
  rw [homPairing_of_mem ψ hx hm, hw, HOM.eval_of]
  exact units_smul_mem_grading _ (w.map_mem hx)

theorem homPairing_d (ψ : M ⟶ B.homObj N) (X : D) (Y : C) {a : ℤ} {x : B.obj X Y}
    (hx : x ∈ grading a) (m : M.obj Y) :
    d (B.homPairing ψ X Y x m) =
      B.homPairing ψ X Y (d x) m + koszulSign a • B.homPairing ψ X Y x (d m) := by
  induction m using DG.induction_on with
  | h_zero => simp
  | h_add m m' hm hm' =>
    rw [map_add, d_add, hm, hm', map_add, d_add, map_add, _root_.smul_add]
    abel
  | h_homogeneous m =>
    rename_i j
    obtain ⟨w, hw⟩ := exists_app_eq_of ψ m.2
    have hdm : ψ.app Y (d (m : M.obj Y)) =
        DirectSum.of (fun n => CatModule.Cochain (B.left Y) N n) (j + 1)
          (CatModule.δ j (j + 1) w) := by
      rw [ψ.map_d, hw]
      exact HOM.d_of j w
    rw [homPairing_of_mem ψ hx m.2, homPairing_of_mem ψ (d_mem hx) m.2,
      homPairing_of_mem ψ hx (d_mem m.2), hdm, hw, HOM.eval_of, HOM.eval_of, HOM.eval_of,
      CatModule.δ_apply _ _ rfl, d_units_smul]
    simp only [smul_sub, smul_smul, ← koszulSign_add]
    rw [ks_eq (m := a + a * (j + 1)) (n := a * j) a (by ring),
      ks_eq (m := a + (a * (j + 1) + j)) (n := (a + 1) * j) a (by ring)]
    exact (add_sub_cancel _ _).symm

theorem homPairing_lact (ψ : M ⟶ B.homObj N) {X X' : D} (g : X ⟶ X') (Y : C) (x : B.obj X Y)
    (m : M.obj Y) : B.homPairing ψ X' Y (B.lact g x) m = g • B.homPairing ψ X Y x m := by
  induction g using DG.induction_on with
  | h_zero => simp [CatModule.zero_smul]
  | h_add g g' hg hg' =>
    rw [map_add, AddMonoidHom.add_apply, map_add, AddMonoidHom.add_apply, hg, hg',
      CatModule.add_smul]
  | h_homogeneous g =>
    rename_i k
    induction x using DG.induction_on with
    | h_zero => simp [CatModule.smul_zero]
    | h_add x x' hx hx' =>
      rw [map_add, map_add, AddMonoidHom.add_apply, hx, hx', map_add, AddMonoidHom.add_apply,
        CatModule.smul_add]
    | h_homogeneous x =>
      rename_i a
      induction m using DG.induction_on with
      | h_zero => simp [CatModule.smul_zero]
      | h_add m m' hm hm' => rw [map_add, hm, hm', map_add, CatModule.smul_add]
      | h_homogeneous m =>
        rename_i j
        obtain ⟨w, hw⟩ := exists_app_eq_of ψ m.2
        rw [homPairing_of_mem ψ (B.lact_mem' g.2 x.2) m.2, homPairing_of_mem ψ x.2 m.2, hw,
          HOM.eval_of, HOM.eval_of, CatModule.smul_units_smul]
        have := w.map_smul (X := X) (Y := X') g.2 (x : B.obj X Y)
        change w.app X' (B.lact g (x : B.obj X Y)) = _ at this
        rw [this, smul_smul, ← koszulSign_add]
        congr 1
        exact ks_eq (k * j) (by ring)

variable (B) in
/-- The morphism `B ⊗_C M ⟶ N` attached to `ψ : M ⟶ HOM_D(B, N)`:
`x ⊗ m ↦ (-1)^{|x||m|} ψ(m)(x)`. -/
def tensorOfHom (ψ : M ⟶ B.homObj N) : B.tensorObj M ⟶ N where
  app X := CatTensorProduct.lift _ (homPairing_balanced ψ X)
  map_mem' {X _ _} hy := CatTensorProduct.lift_mem _ (homPairing_balanced ψ X)
    (fun Y _ _ _ _ hx hm => homPairing_mem ψ X Y hx hm) hy
  map_d' {X} y := CatTensorProduct.lift_d _ (homPairing_balanced ψ X)
    (fun Y _ _ hx m => homPairing_d ψ X Y hx m) y
  map_smul' {X X'} g y := by
    change CatTensorProduct.lift _ (homPairing_balanced ψ X') (B.tensorAct M g y) =
      g • CatTensorProduct.lift _ (homPairing_balanced ψ X) y
    induction y using CatTensorProduct.induction_on with
    | zero => simp [CatModule.smul_zero]
    | tmul Y x m =>
      rw [tensorAct_tmul, CatTensorProduct.lift_tmul, CatTensorProduct.lift_tmul]
      exact homPairing_lact ψ g Y x m
    | add y y' hy hy' => rw [map_add, map_add, hy, hy', map_add, CatModule.smul_add]

@[simp]
theorem tensorOfHom_app_tmul (ψ : M ⟶ B.homObj N) (X : D) (Y : C) (x : B.obj X Y)
    (m : M.obj Y) :
    (B.tensorOfHom ψ).app X (CatTensorProduct.tmul (N := B.right X) Y x m) =
      B.homPairing ψ X Y x m :=
  CatTensorProduct.lift_tmul _ (homPairing_balanced ψ X) Y x m

theorem tensorPairing_homPairing (ψ : M ⟶ B.homObj N) (X : D) (Y : C) (x : B.obj X Y)
    (m : M.obj Y) : B.tensorPairing (B.tensorOfHom ψ) X Y x m =
      HOM.eval (B.left Y) N X (ψ.app Y m) x := by
  induction x using DG.induction_on with
  | h_zero => simp
  | h_add x x' hx hx' => rw [map_add, AddMonoidHom.add_apply, hx, hx', map_add]
  | h_homogeneous x =>
    rename_i a
    induction m using DG.induction_on with
    | h_zero => simp
    | h_add m m' hm hm' =>
      rw [map_add, hm, hm', map_add]
      erw [map_add]
      rfl
    | h_homogeneous m =>
      rw [tensorPairing_of_mem _ x.2 m.2, tensorOfHom_app_tmul, homPairing_of_mem ψ x.2 m.2,
        smul_smul, Int.units_mul_self, one_smul]

theorem homPairing_homOfTensor (Φ : B.tensorObj M ⟶ N) (X : D) (Y : C) (x : B.obj X Y)
    (m : M.obj Y) :
    B.homPairing (B.homOfTensor Φ) X Y x m =
      Φ.app X (CatTensorProduct.tmul (N := B.right X) Y x m) := by
  induction x using DG.induction_on with
  | h_zero => simp
  | h_add x x' hx hx' =>
    rw [map_add, AddMonoidHom.add_apply, hx, hx', CatTensorProduct.add_tmul, map_add]
  | h_homogeneous x =>
    rename_i a
    induction m using DG.induction_on with
    | h_zero => simp
    | h_add m m' hm hm' => rw [map_add, hm, hm', CatTensorProduct.tmul_add, map_add]
    | h_homogeneous m =>
      rw [homPairing_of_mem _ x.2 m.2, homOfTensor_app_of_mem Φ m.2, HOM.eval_of,
        homOfTensorCochain_app, tensorPairing_of_mem Φ x.2 m.2, smul_smul, Int.units_mul_self,
        one_smul]

variable (B M N) in
/-- The tensor–Hom adjunction bijection `(B ⊗_C M ⟶ N) ≃ (M ⟶ HOM_D(B, N))`. -/
def tensorHomEquiv : (B.tensorObj M ⟶ N) ≃ (M ⟶ B.homObj N) where
  toFun := B.homOfTensor
  invFun := B.tensorOfHom
  left_inv Φ := CatModule.hom_ext fun X y => by
    induction y using CatTensorProduct.induction_on with
    | zero => simp
    | tmul Y x m => rw [tensorOfHom_app_tmul, homPairing_homOfTensor]
    | add y y' hy hy' => rw [map_add, hy, hy', map_add]
  right_inv ψ := CatModule.hom_ext fun Y m => by
    induction m using DG.induction_on with
    | h_zero => simp
    | h_add m m' hm hm' => rw [map_add, hm, hm', map_add]
    | h_homogeneous m =>
      obtain ⟨w, hw⟩ := exists_app_eq_of ψ m.2
      rw [homOfTensor_app_of_mem _ m.2, hw]
      congr 1
      refine CatModule.Cochain.ext fun X x => ?_
      rw [homOfTensorCochain_app, tensorPairing_homPairing, hw, HOM.eval_of]

theorem tensorOfHom_comp {M' : CatModule.{max u₁ u₂ w} C} (f : M' ⟶ M) (ψ : M ⟶ B.homObj N) :
    B.tensorOfHom (f ≫ ψ) = B.tensorMap f ≫ B.tensorOfHom ψ :=
  CatModule.hom_ext fun X y => by
    rw [CatModule.comp_app]
    show CatTensorProduct.lift _ (homPairing_balanced (f ≫ ψ) X) y =
      CatTensorProduct.lift _ (homPairing_balanced ψ X) (CatTensorProduct.map (𝟙 (B.right X)) f y)
    induction y using CatTensorProduct.induction_on with
    | zero => simp
    | tmul Y x m =>
      rw [CatTensorProduct.map_tmul, CatTensorProduct.lift_tmul, CatTensorProduct.lift_tmul,
        CatModule.id_app]
      induction x using DG.induction_on with
      | h_zero => simp
      | h_add x x' hx hx' => rw [map_add, AddMonoidHom.add_apply, hx, hx', map_add,
          AddMonoidHom.add_apply]
      | h_homogeneous x =>
        induction m using DG.induction_on with
        | h_zero => simp
        | h_add m m' hm hm' => rw [map_add, hm, hm', map_add, map_add]
        | h_homogeneous m =>
          rw [homPairing_of_mem _ x.2 m.2, homPairing_of_mem _ x.2 (f.map_mem m.2)]
          rfl
    | add y y' hy hy' => rw [map_add, hy, hy', map_add, map_add]

theorem homOfTensor_comp {N' : CatModule.{max u₁ u₂ w} D} (Φ : B.tensorObj M ⟶ N)
    (h : N ⟶ N') : B.homOfTensor (Φ ≫ h) = B.homOfTensor Φ ≫ B.homMap h :=
  CatModule.hom_ext fun Y m => by
    rw [CatModule.comp_app, homMap_app]
    show B.homOfTensorApp (Φ ≫ h) Y m =
      HOM.postcompCochain (CatModule.Cochain.ofHom h) (B.homOfTensorApp Φ Y m)
    induction m using DG.induction_on with
    | h_zero => simp
    | h_add m m' hm hm' => rw [map_add, hm, hm', map_add, map_add]
    | h_homogeneous m =>
      rw [homOfTensorApp_of_mem _ m.2, homOfTensorApp_of_mem _ m.2, HOM.postcompCochain_of]
      refine HOM.of_congr (add_zero _).symm fun X x => ?_
      rw [homOfTensorCochain_app, CatModule.Cochain.comp_apply, CatModule.Cochain.ofHom_apply,
        homOfTensorCochain_app]
      induction x using DG.induction_on with
      | h_zero => simp
      | h_add x x' hx hx' => rw [map_add, AddMonoidHom.add_apply, hx, hx', map_add,
          AddMonoidHom.add_apply, map_add]
      | h_homogeneous x =>
        rw [tensorPairing_of_mem _ x.2 m.2, tensorPairing_of_mem _ x.2 m.2, map_units]
        rfl

variable (B) in
/-- The tensor–Hom adjunction `B ⊗_C - ⊣ HOM_D(B, -)` for a dg `(D, C)`-bimodule `B`. -/
def tensorHomAdjunction :
    (B.tensorFunctor : CatModule.{max u₁ u₂ w} C ⥤ CatModule.{max u₁ u₂ w} D) ⊣ B.homFunctor :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N => B.tensorHomEquiv M N
      homEquiv_naturality_left_symm := fun f g => tensorOfHom_comp f g
      homEquiv_naturality_right := fun Φ h => homOfTensor_comp Φ h }

end Adjunction

end CatBimodule

end DG
