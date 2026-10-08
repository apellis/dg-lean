import DG.Homotopy.ChangeOfRings
import DG.Homotopy.HomotopyCategory

/-!
# The tensor product with a dg bimodule on dg modules and homotopy categories

Let `A`, `B` be dg rings and `M` a dg `(A, B)`-bimodule.

* `DG.gradeInvolution_smul_of_mem`, `DG.gradeInvolution_op_smul_of_mem`: the grade involution
  `m ↦ (-1)^{|m|} m` commutes with the actions up to the Koszul sign of the scalar.
* `DG.TensorProductOver.lTensorCochain M h`: for a cochain `h` of degree `-1` between left dg
  `B`-modules, the cochain `1 ⊗ h` of degree `-1`, `(1 ⊗ h)(m ⊗ n) = (-1)^{|m|} m ⊗ h n`;
  `DG.DGHomotopy.lTensor`: it is a homotopy from `1 ⊗ f` to `1 ⊗ g` when `h` is one from `f` to `g`.
* `DG.DGModuleCat.tensorFunctor A M : DGModuleCat B ⥤ DGModuleCat A`, `N ↦ M ⊗_B N`
  (generalizing `DG.DGModuleCat.extendScalars`), and its descent to homotopy categories
  `DG.HomotopyCategory.tensorFunctor A M` (`DG.HomotopyCategory.tensorFunctorQuotientIso`).
* Natural isomorphisms: `DG.DGModuleCat.tensorFunctorRegularIso : B ⊗_B - ≅ 𝟭`,
  `DG.DGModuleCat.tensorFunctorCompIso : M' ⊗_A (M ⊗_B -) ≅ (M' ⊗_A M) ⊗_B -`, and
  `DG.DGModuleCat.tensorFunctorIsoOfEquiv : M ⊗_B - ≅ M' ⊗_B -` for an isomorphism of dg
  bimodules `M ≅ M'`.
* **Morita equivalence from invertible bimodules**: if `P` is a dg `(A, B)`-bimodule and `Q` a dg
  `(B, A)`-bimodule with `Q ⊗_A P ≅ B` and `P ⊗_B Q ≅ A` as dg bimodules, then
  `Q ⊗_A - : DGModuleCat A ⥤ DGModuleCat B` is an equivalence with inverse `P ⊗_B -`
  (`DG.DGModuleCat.moritaEquivalence`), and likewise on homotopy categories
  (`DG.HomotopyCategory.moritaEquivalence`).

All rings and modules live in one universe `v`.
-/

open CategoryTheory MulOpposite

universe v

noncomputable section

namespace DG

/-! ### The grade involution and the actions -/

section GradeInvolution

theorem koszulSign_neg_one_mul (i : ℤ) : koszulSign (-1 * i) = koszulSign i := by
  rw [neg_one_mul, koszulSign, Int.negOnePow_neg]

variable {A M : Type*} [Ring A] [DGAddCommGroup A] [AddCommGroup M] [DGAddCommGroup M]

theorem gradeInvolution_smul_of_mem [Module A M] [DGModule A M] {i : ℤ} {a : A}
    (ha : a ∈ grading i) (m : M) :
    gradeInvolution M (a • m) = koszulSign i • (a • gradeInvolution M m) := by
  induction m using DG.induction_on with
  | h_zero => simp
  | @h_homogeneous j m =>
    rw [gradeInvolution_of_mem (smul_mem_grading ha m.2), gradeInvolution_of_mem m.2,
      smul_comm a (koszulSign j) (m : M), smul_smul, koszulSign_add, mul_comm]
  | h_add m m' hm hm' => rw [smul_add, map_add, hm, hm', map_add, smul_add, smul_add]

theorem gradeInvolution_op_smul_of_mem [Module Aᵐᵒᵖ M] [DGRightModule A M] {i : ℤ} {a : A}
    (ha : a ∈ grading i) (m : M) :
    gradeInvolution M (op a • m) = koszulSign i • (op a • gradeInvolution M m) := by
  induction m using DG.induction_on with
  | h_zero => simp
  | @h_homogeneous j m =>
    rw [gradeInvolution_of_mem (op_smul_mem_grading ha m.2), gradeInvolution_of_mem m.2,
      smul_comm (op a) (koszulSign j) (m : M), smul_smul, koszulSign_add, mul_comm]
  | h_add m m' hm hm' => rw [smul_add, map_add, hm, hm', map_add, smul_add, smul_add]

end GradeInvolution

/-! ### Tensoring cochains of degree `-1` and homotopies -/

namespace TensorProductOver

section Aux

variable {B : Type*} [Ring B] [DGAddCommGroup B]
  (M : Type*) [AddCommGroup M] [DGAddCommGroup M] [Module Bᵐᵒᵖ M] [DGRightModule B M]
  {N N' : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module B N]
  [AddCommGroup N'] [DGAddCommGroup N'] [Module B N']

/-- The balanced bi-additive map `(m, n) ↦ (-1)^{|m|} m ⊗ h n`. -/
def lTensorCochainAux (h : Cochain B N N' (-1)) : M →+ N →+ TensorProductOver B M N' :=
  ((tmulAddHom B M N').compl₂ (h : N →+ N')).comp (gradeInvolution M)

omit [DGRightModule B M] in
theorem lTensorCochainAux_apply (h : Cochain B N N' (-1)) (m : M) (n : N) :
    lTensorCochainAux M h m n = tmul B (gradeInvolution M m) (h n) := rfl

theorem lTensorCochainAux_balanced (h : Cochain B N N' (-1)) (b : B) (m : M) (n : N) :
    lTensorCochainAux M h (op b • m) n = lTensorCochainAux M h m (b • n) := by
  induction b using DG.induction_on with
  | h_zero => simp [lTensorCochainAux_apply]
  | @h_homogeneous i b =>
    rw [lTensorCochainAux_apply, lTensorCochainAux_apply,
      gradeInvolution_op_smul_of_mem b.2, h.map_smul b.2, koszulSign_neg_one_mul,
      units_smul_tmul, tmul_units_smul, op_smul_tmul]
  | h_add b b' hb hb' =>
    rw [MulOpposite.op_add, add_smul, map_add, AddMonoidHom.add_apply, hb, hb', add_smul, map_add]

end Aux

variable {A B : Type*} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]
  (M : Type*) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [DGBimodule A B M]
  {N N' : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module B N] [DGModule B N]
  [AddCommGroup N'] [DGAddCommGroup N'] [Module B N'] [DGModule B N']

/-- For a cochain `h` of degree `-1` between left dg `B`-modules, the cochain `1 ⊗ h` of degree
`-1` between the left dg `A`-modules `M ⊗_B N` and `M ⊗_B N'`,
`(1 ⊗ h)(m ⊗ n) = (-1)^{|m|} m ⊗ h n`. -/
def lTensorCochain (h : Cochain B N N' (-1)) :
    Cochain A (TensorProductOver B M N) (TensorProductOver B M N') (-1) where
  toAddMonoidHom := lift (lTensorCochainAux M h) (lTensorCochainAux_balanced M h)
  map_mem' k x hx := by
    refine induction_on_mem_grading
      (P := fun x => lift (lTensorCochainAux M h) (lTensorCochainAux_balanced M h) x ∈
        grading (k + -1)) ?_ ?_ ?_ ?_ hx
    · rw [map_zero]; exact zero_mem _
    · intro p q m n hm hn hpq
      rw [lift_tmul, lTensorCochainAux_apply, ← hpq, add_assoc]
      exact tmul_mem_grading (gradeInvolution_mem hm) (h.map_mem hn)
    · intro x y hx hy; rw [map_add]; exact add_mem hx hy
    · intro x hx; rw [map_neg]; exact neg_mem hx
  map_smul' {i} {a} ha x := by
    change lift (lTensorCochainAux M h) (lTensorCochainAux_balanced M h) (a • x) =
      koszulSign (-1 * i) • (a • lift (lTensorCochainAux M h) (lTensorCochainAux_balanced M h) x)
    induction x using TensorProductOver.induction_on with
    | zero => simp
    | tmul m n =>
      rw [smul_tmul, lift_tmul, lift_tmul, lTensorCochainAux_apply, lTensorCochainAux_apply,
        gradeInvolution_smul_of_mem ha, koszulSign_neg_one_mul, units_smul_tmul, smul_tmul]
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add, smul_add]

@[simp]
theorem lTensorCochain_tmul (h : Cochain B N N' (-1)) (m : M) (n : N) :
    lTensorCochain (A := A) M h (tmul B m n) = tmul B (gradeInvolution M m) (h n) := rfl

end TensorProductOver

section Homotopy

variable (A : Type*) {B : Type*} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]
  (M : Type*) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [DGBimodule A B M]
  {N N' : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module B N] [DGModule B N]
  [AddCommGroup N'] [DGAddCommGroup N'] [Module B N'] [DGModule B N']

set_option linter.unusedSimpArgs false in
open TensorProductOver in
/-- A homotopy `h` from `f` to `g` gives the homotopy `1 ⊗ h` from `1 ⊗ f` to `1 ⊗ g`. -/
def DGHomotopy.lTensor {f g : N →ᵈᵍ[B] N'} (h : DGHomotopy f g) :
    DGHomotopy (DGModuleHom.lTensor A M f) (DGModuleHom.lTensor A M g) :=
  DGHomotopy.mk' (lTensorCochain (A := A) M h.hom) fun x => by
    induction x using TensorProductOver.induction_on with
    | zero => simp
    | tmul m n =>
      induction m using DG.induction_on with
      | h_zero => simp
      | @h_homogeneous j m =>
        have hdm : d (m : M) ∈ grading (j + 1) := d_mem m.2
        rw [DGModuleHom.lTensor_tmul, DGModuleHom.lTensor_tmul, h.comm n,
          TensorProductOver.d_tmul_of_mem m.2, map_add, Units.smul_def, map_zsmul,
          lTensorCochain_tmul (A := A), lTensorCochain_tmul (A := A),
          lTensorCochain_tmul (A := A), gradeInvolution_of_mem m.2, gradeInvolution_of_mem hdm,
          units_smul_tmul, d_units_smul, TensorProductOver.d_tmul_of_mem m.2, units_smul_tmul,
          koszulSign_add, tmul_add, tmul_add]
        rcases Int.units_eq_one_or (koszulSign j) with hε | hε <;>
          simp only [hε, koszulSign, Int.negOnePow_one, one_mul, neg_mul, neg_neg, one_smul,
            neg_smul, Units.val_one, Units.val_neg, smul_add, Units.neg_smul,
            TensorProductOver.units_smul_tmul, neg_one_zsmul, TensorProductOver.neg_tmul] <;>
          abel
      | h_add m m' hm hm' =>
        simp only [add_tmul, map_add, hm, hm']
        abel
    | add x y hx hy =>
      rw [map_add, hx, hy, map_add, d_add, map_add, map_add, map_add]
      abel

theorem Homotopic.lTensor {f g : N →ᵈᵍ[B] N'} (h : Homotopic f g) :
    Homotopic (DGModuleHom.lTensor A M f) (DGModuleHom.lTensor A M g) :=
  ⟨DGHomotopy.lTensor A M h.some⟩

end Homotopy

/-! ### The functor `M ⊗_B -` -/

namespace DGModuleCat

open TensorProductOver

section Functor

variable (A : Type v) {B : Type v} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]
  (M : Type v) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [DGBimodule A B M]

/-- The functor `M ⊗_B - : DGModuleCat B ⥤ DGModuleCat A` for a dg `(A, B)`-bimodule `M`. -/
def tensorFunctor : DGModuleCat.{v} B ⥤ DGModuleCat.{v} A where
  obj N := of A (TensorProductOver B M N)
  map g := ofHom (DGModuleHom.lTensor A M g.hom)
  map_id N := hom_ext (DGModuleHom.lTensor_id A M N)
  map_comp f g := hom_ext (DGModuleHom.lTensor_comp g.hom f.hom)

@[simp]
theorem tensorFunctor_map_tmul {N N' : DGModuleCat.{v} B} (g : N ⟶ N') (m : M) (n : N) :
    (tensorFunctor A M).map g (tmul B m n) = tmul B m (g n) := rfl

variable {A M} in
/-- Morphisms out of `M ⊗_B N` agree if they agree on the elements `m ⊗ n`. -/
theorem tensor_hom_ext {N : DGModuleCat.{v} B} {X : DGModuleCat.{v} A}
    {f g : (tensorFunctor A M).obj N ⟶ X} (h : ∀ (m : M) (n : N), f (tmul B m n) = g (tmul B m n)) :
    f = g := by
  have hfg : AddMonoidHomClass.toAddMonoidHom f.hom = AddMonoidHomClass.toAddMonoidHom g.hom :=
    TensorProductOver.addHom_ext h
  exact hom_ext_apply fun x => DFunLike.congr_fun hfg x

end Functor

/-- An isomorphism of dg modules as an isomorphism in `DGModuleCat`. -/
@[simps]
def isoOfDGModuleEquiv {A : Type v} [Ring A] [DGAddCommGroup A] {M N : DGModuleCat.{v} A}
    (e : M ≃ᵈᵍ[A] N) : M ≅ N where
  hom := ⟨e.toDGModuleHom⟩
  inv := ⟨e.symm.toDGModuleHom⟩
  hom_inv_id := hom_ext_apply fun x => e.symm_apply_apply x
  inv_hom_id := hom_ext_apply fun x => e.apply_symm_apply x

/-! ### The unit isomorphism -/

section Regular

variable (B : Type v) [Ring B] [DGAddCommGroup B] [DGRing B]

/-- `B ⊗_B - ≅ 𝟭`, `b ⊗ n ↦ b • n`. -/
def tensorFunctorRegularIso : tensorFunctor B B ≅ 𝟭 (DGModuleCat.{v} B) :=
  NatIso.ofComponents (fun N => isoOfDGModuleEquiv (lidDGModuleEquiv B N)) fun {N N'} g =>
    tensor_hom_ext fun b n => by
      change lidDGModuleEquiv B N' (tmul B b (g n)) = g (lidDGModuleEquiv B N (tmul B b n))
      rw [lidDGModuleEquiv_tmul, lidDGModuleEquiv_tmul, map_smul]

@[simp]
theorem tensorFunctorRegularIso_hom_app_tmul (N : DGModuleCat.{v} B) (b : B) (n : N) :
    (tensorFunctorRegularIso B).hom.app N (tmul B b n) = b • n := rfl

end Regular

/-! ### Isomorphisms of bimodules -/

section OfEquiv

variable {A B : Type v} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]
  {M M' : Type v} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [DGBimodule A B M] [AddCommGroup M'] [DGAddCommGroup M'] [Module A M'] [Module Bᵐᵒᵖ M']
  [DGBimodule A B M']

/-- A right `B`-linear isomorphism of left dg `A`-modules `e : M ≅ M'` as a right linear map. -/
def rightLinearOfEquiv (e : M ≃ᵈᵍ[A] M') (he : ∀ (b : B) (m : M), e (op b • m) = op b • e m) :
    M →ₗ[Bᵐᵒᵖ] M' where
  toFun := e
  map_add' := map_add e
  map_smul' b m := by rw [RingHom.id_apply]; exact he b.unop m

/-- The isomorphism `M ⊗_B N ≅ M' ⊗_B N` induced by an isomorphism of dg bimodules. -/
def tensorEquivOfEquiv (e : M ≃ᵈᵍ[A] M') (he : ∀ (b : B) (m : M), e (op b • m) = op b • e m)
    (N : Type v) [AddCommGroup N] [DGAddCommGroup N] [Module B N] [DGModule B N] :
    TensorProductOver B M N ≃ᵈᵍ[A] TensorProductOver B M' N where
  toFun := map (rightLinearOfEquiv e he) LinearMap.id
  invFun := map (rightLinearOfEquiv e.symm fun b m' => by
      apply e.injective
      rw [he, e.apply_symm_apply, e.apply_symm_apply]) LinearMap.id
  left_inv x := by
    induction x using TensorProductOver.induction_on with
    | zero => simp
    | tmul m n =>
      change tmul B (e.symm (e m)) n = tmul B m n
      rw [e.symm_apply_apply]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  right_inv x := by
    induction x using TensorProductOver.induction_on with
    | zero => simp
    | tmul m n =>
      change tmul B (e (e.symm m)) n = tmul B m n
      rw [e.apply_symm_apply]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  map_add' := map_add _
  map_smul' a x := by
    induction x using TensorProductOver.induction_on with
    | zero => simp
    | tmul m n =>
      change tmul B (e (a • m)) n = a • tmul B (e m) n
      rw [map_smul, smul_tmul]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy, RingHom.id_apply] at *
  map_mem' hx := map_mem _ _ (fun hm => e.map_mem hm) (fun hn => hn) hx
  map_d' x := by
    induction x using TensorProductOver.induction_on with
    | zero => simp
    | tmul m n =>
      induction m using DG.induction_on with
      | h_zero => simp
      | @h_homogeneous j m =>
        change map (rightLinearOfEquiv e he) LinearMap.id (d (tmul B (m : M) n)) =
          d (tmul B (e m) n)
        rw [TensorProductOver.d_tmul_of_mem m.2, TensorProductOver.d_tmul_of_mem (e.map_mem m.2),
          map_add, map_units_zsmul]
        change tmul B (e (d (m : M))) n + koszulSign j • tmul B (e m) (d n) = _
        rw [e.map_d]
      | h_add m m' hm hm' =>
        rw [add_tmul, d_add, map_add, map_add, d_add, hm, hm']
    | add x y hx hy => rw [d_add, map_add, map_add, hx, hy, d_add]

@[simp]
theorem tensorEquivOfEquiv_tmul (e : M ≃ᵈᵍ[A] M')
    (he : ∀ (b : B) (m : M), e (op b • m) = op b • e m)
    (N : Type v) [AddCommGroup N] [DGAddCommGroup N] [Module B N] [DGModule B N] (m : M) (n : N) :
    tensorEquivOfEquiv e he N (tmul B m n) = tmul B (e m) n := rfl

/-- `M ⊗_B - ≅ M' ⊗_B -` for an isomorphism of dg bimodules `e : M ≅ M'`. -/
def tensorFunctorIsoOfEquiv (e : M ≃ᵈᵍ[A] M')
    (he : ∀ (b : B) (m : M), e (op b • m) = op b • e m) :
    tensorFunctor (B := B) A M ≅ tensorFunctor (B := B) A M' :=
  NatIso.ofComponents (fun N => isoOfDGModuleEquiv (tensorEquivOfEquiv e he N)) fun _ =>
    tensor_hom_ext (M := M) fun _ _ => rfl

end OfEquiv

/-! ### Composition -/

section Comp

open TensorProductOver.RightAction

variable {A B C : Type v} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]
  [Ring C] [DGAddCommGroup C]
  (M : Type v) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [DGBimodule A B M]
  (M' : Type v) [AddCommGroup M'] [DGAddCommGroup M'] [Module C M'] [Module Aᵐᵒᵖ M']
  [DGBimodule C A M']

instance : SMulCommClass C Bᵐᵒᵖ (TensorProductOver A M' M) where
  smul_comm c b x := by
    induction x using TensorProductOver.induction_on with
    | zero => simp
    | tmul m n => rfl
    | add x y hx hy => rw [smul_add, smul_add, hx, hy, smul_add, smul_add]

/-- `M' ⊗_A M` as a dg `(C, B)`-bimodule (left action through `M'`, right action through `M`). -/
instance instDGBimoduleTensor : DGBimodule C B (TensorProductOver A M' M) := DGBimodule.mk'

/-- Associativity, `(M' ⊗_A M) ⊗_B N ≅ M' ⊗_A (M ⊗_B N)`, as an isomorphism of dg `C`-modules. -/
def assocDGModuleEquiv (N : Type v) [AddCommGroup N] [DGAddCommGroup N] [Module B N]
    [DGModule B N] :
    TensorProductOver B (TensorProductOver A M' M) N ≃ᵈᵍ[C]
      TensorProductOver A M' (TensorProductOver B M N) where
  __ := (assocEquiv A B M' M N).toAddEquiv
  map_smul' c x := by
    change assocEquiv A B M' M N (c • x) = c • assocEquiv A B M' M N x
    induction x using TensorProductOver.induction_on with
    | zero => simp
    | tmul y n =>
      induction y using TensorProductOver.induction_on with
      | zero => simp
      | tmul m' m => rfl
      | add y y' hy hy' =>
        rw [add_tmul, smul_add, map_add, hy, hy', map_add, smul_add]
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
  map_mem' hx := (assocEquiv A B M' M N).map_mem hx
  map_d' x := (assocEquiv A B M' M N).map_d x

omit [DGBimodule C A M'] in
/-- Morphisms out of `M' ⊗_A (M ⊗_B N)` agree if they agree on the elements `m' ⊗ (m ⊗ n)`. -/
theorem tensor_hom_ext₂ [DGBimodule C A M'] {N : DGModuleCat.{v} B} {X : DGModuleCat.{v} C}
    {f g : (tensorFunctor C M').obj ((tensorFunctor A M).obj N) ⟶ X}
    (h : ∀ (m' : M') (m : M) (n : N), f (tmul A m' (tmul B m n)) = g (tmul A m' (tmul B m n))) :
    f = g := by
  refine tensor_hom_ext (M := M') fun m' y => ?_
  have hfg : (AddMonoidHomClass.toAddMonoidHom f.hom).comp
      (TensorProductOver.tmulAddHom A M' (TensorProductOver B M N) m') =
      (AddMonoidHomClass.toAddMonoidHom g.hom).comp
      (TensorProductOver.tmulAddHom A M' (TensorProductOver B M N) m') :=
    TensorProductOver.addHom_ext fun m n => h m' m n
  exact DFunLike.congr_fun hfg y

/-- `M' ⊗_A (M ⊗_B -) ≅ (M' ⊗_A M) ⊗_B -`. -/
def tensorFunctorCompIso :
    tensorFunctor (B := B) A M ⋙ tensorFunctor (B := A) C M' ≅
      tensorFunctor (B := B) C (TensorProductOver A M' M) :=
  NatIso.ofComponents (fun N => (isoOfDGModuleEquiv (assocDGModuleEquiv M M' N)).symm)
    fun _ => tensor_hom_ext₂ M M' fun _ _ _ => rfl

end Comp

/-! ### Morita equivalence -/

section Morita

open TensorProductOver.RightAction

variable {A B : Type v} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B]
  (P : Type v) [AddCommGroup P] [DGAddCommGroup P] [Module A P] [Module Bᵐᵒᵖ P]
  [DGBimodule A B P]
  (Q : Type v) [AddCommGroup Q] [DGAddCommGroup Q] [Module B Q] [Module Aᵐᵒᵖ Q]
  [DGBimodule B A Q]

/-- The unit of the Morita equivalence, `𝟭 ≅ P ⊗_B (Q ⊗_A -)`. -/
def moritaUnitIso (e₂ : TensorProductOver B P Q ≃ᵈᵍ[A] A)
    (he₂ : ∀ (a : A) x, e₂ (op a • x) = op a • e₂ x) :
    𝟭 (DGModuleCat.{v} A) ≅ tensorFunctor B Q ⋙ tensorFunctor A P :=
  (tensorFunctorRegularIso A).symm ≪≫ (tensorFunctorIsoOfEquiv e₂ he₂).symm ≪≫
    (tensorFunctorCompIso Q P).symm

/-- The counit of the Morita equivalence, `Q ⊗_A (P ⊗_B -) ≅ 𝟭`. -/
def moritaCounitIso (e₁ : TensorProductOver A Q P ≃ᵈᵍ[B] B)
    (he₁ : ∀ (b : B) x, e₁ (op b • x) = op b • e₁ x) :
    tensorFunctor A P ⋙ tensorFunctor B Q ≅ 𝟭 (DGModuleCat.{v} B) :=
  tensorFunctorCompIso P Q ≪≫ tensorFunctorIsoOfEquiv e₁ he₁ ≪≫ tensorFunctorRegularIso B

/-- **Morita equivalence from invertible dg bimodules**: for a dg `(A, B)`-bimodule `P` and a dg
`(B, A)`-bimodule `Q` with isomorphisms of dg bimodules `Q ⊗_A P ≅ B` and `P ⊗_B Q ≅ A`, the
functor `Q ⊗_A -` is an equivalence `DGModuleCat A ≌ DGModuleCat B` with inverse `P ⊗_B -`. -/
def moritaEquivalence (e₁ : TensorProductOver A Q P ≃ᵈᵍ[B] B)
    (he₁ : ∀ (b : B) x, e₁ (op b • x) = op b • e₁ x)
    (e₂ : TensorProductOver B P Q ≃ᵈᵍ[A] A)
    (he₂ : ∀ (a : A) x, e₂ (op a • x) = op a • e₂ x) :
    DGModuleCat.{v} A ≌ DGModuleCat.{v} B :=
  CategoryTheory.Equivalence.mk (tensorFunctor B Q) (tensorFunctor A P)
    (moritaUnitIso P Q e₂ he₂) (moritaCounitIso P Q e₁ he₁)

theorem moritaEquivalence_functor (e₁ : TensorProductOver A Q P ≃ᵈᵍ[B] B)
    (he₁ : ∀ (b : B) x, e₁ (op b • x) = op b • e₁ x)
    (e₂ : TensorProductOver B P Q ≃ᵈᵍ[A] A)
    (he₂ : ∀ (a : A) x, e₂ (op a • x) = op a • e₂ x) :
    (moritaEquivalence P Q e₁ he₁ e₂ he₂).functor = tensorFunctor B Q := rfl

theorem moritaEquivalence_inverse (e₁ : TensorProductOver A Q P ≃ᵈᵍ[B] B)
    (he₁ : ∀ (b : B) x, e₁ (op b • x) = op b • e₁ x)
    (e₂ : TensorProductOver B P Q ≃ᵈᵍ[A] A)
    (he₂ : ∀ (a : A) x, e₂ (op a • x) = op a • e₂ x) :
    (moritaEquivalence P Q e₁ he₁ e₂ he₂).inverse = tensorFunctor A P := rfl

end Morita

end DGModuleCat

/-! ### Homotopy categories -/

namespace HomotopyCategory

open DGModuleCat

section Lift

variable {A B : Type v} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]

/-- A functor of dg modules preserving homotopies descends to the homotopy categories. -/
def liftFunctor (F : DGModuleCat.{v} B ⥤ DGModuleCat.{v} A)
    (hF : ∀ {N N' : DGModuleCat.{v} B} (f g : N ⟶ N'), Homotopic f.hom g.hom →
      Homotopic (F.map f).hom (F.map g).hom) :
    HomotopyCategory.{v} B ⥤ HomotopyCategory.{v} A :=
  CategoryTheory.Quotient.lift _ (F ⋙ quotient A) fun _ _ f g h =>
    (quotient_map_eq_iff _ _).mpr (hF f g h)

/-- The descended functor commutes with the quotient functors. -/
def liftFunctorQuotientIso (F : DGModuleCat.{v} B ⥤ DGModuleCat.{v} A)
    (hF : ∀ {N N' : DGModuleCat.{v} B} (f g : N ⟶ N'), Homotopic f.hom g.hom →
      Homotopic (F.map f).hom (F.map g).hom) :
    quotient B ⋙ liftFunctor F hF ≅ F ⋙ quotient A :=
  CategoryTheory.Quotient.lift.isLift _ _ _

/-- A natural isomorphism of functors of dg modules descends to the homotopy categories. -/
def liftNatIso {F G : DGModuleCat.{v} B ⥤ DGModuleCat.{v} A}
    (hF : ∀ {N N' : DGModuleCat.{v} B} (f g : N ⟶ N'), Homotopic f.hom g.hom →
      Homotopic (F.map f).hom (F.map g).hom)
    (hG : ∀ {N N' : DGModuleCat.{v} B} (f g : N ⟶ N'), Homotopic f.hom g.hom →
      Homotopic (G.map f).hom (G.map g).hom) (α : F ≅ G) :
    liftFunctor F hF ≅ liftFunctor G hG :=
  CategoryTheory.Quotient.natIsoLift _
    (liftFunctorQuotientIso F hF ≪≫ Functor.isoWhiskerRight α (quotient A) ≪≫
      (liftFunctorQuotientIso G hG).symm)

end Lift

section Tensor

variable (A : Type v) {B : Type v} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]
  (M : Type v) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [DGBimodule A B M]

theorem tensorFunctor_homotopic {N N' : DGModuleCat.{v} B} (f g : N ⟶ N')
    (h : Homotopic f.hom g.hom) :
    Homotopic ((DGModuleCat.tensorFunctor A M).map f).hom
      ((DGModuleCat.tensorFunctor A M).map g).hom :=
  h.lTensor A M

/-- `M ⊗_B -` on homotopy categories. -/
def tensorFunctor : HomotopyCategory.{v} B ⥤ HomotopyCategory.{v} A :=
  liftFunctor (DGModuleCat.tensorFunctor A M) (tensorFunctor_homotopic A M)

/-- `M ⊗_B -` on homotopy categories commutes with the quotient functors. -/
def tensorFunctorQuotientIso :
    quotient B ⋙ tensorFunctor A M ≅ DGModuleCat.tensorFunctor A M ⋙ quotient A :=
  liftFunctorQuotientIso _ _

end Tensor

section Morita

open TensorProductOver.RightAction

variable {A B : Type v} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B]
  (P : Type v) [AddCommGroup P] [DGAddCommGroup P] [Module A P] [Module Bᵐᵒᵖ P]
  [DGBimodule A B P]
  (Q : Type v) [AddCommGroup Q] [DGAddCommGroup Q] [Module B Q] [Module Aᵐᵒᵖ Q]
  [DGBimodule B A Q]

/-- A composite of two descended functors is the descent of the composite. -/
def liftFunctorCompIso {C : Type v} [Ring C] [DGAddCommGroup C]
    (F : DGModuleCat.{v} A ⥤ DGModuleCat.{v} B) (G : DGModuleCat.{v} B ⥤ DGModuleCat.{v} C)
    (hF : ∀ {N N' : DGModuleCat.{v} A} (f g : N ⟶ N'), Homotopic f.hom g.hom →
      Homotopic (F.map f).hom (F.map g).hom)
    (hG : ∀ {N N' : DGModuleCat.{v} B} (f g : N ⟶ N'), Homotopic f.hom g.hom →
      Homotopic (G.map f).hom (G.map g).hom) :
    liftFunctor F hF ⋙ liftFunctor G hG ≅
      liftFunctor (F ⋙ G) (fun f g h => hG _ _ (hF f g h)) :=
  CategoryTheory.Quotient.natIsoLift _
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (liftFunctorQuotientIso F hF) _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F (liftFunctorQuotientIso G hG) ≪≫
      (Functor.associator _ _ _).symm ≪≫ (liftFunctorQuotientIso (F ⋙ G) _).symm)

/-- The identity functor descends to the identity. -/
def liftFunctorIdIso :
    liftFunctor (𝟭 (DGModuleCat.{v} A)) (fun _ _ h => h) ≅ 𝟭 (HomotopyCategory.{v} A) :=
  CategoryTheory.Quotient.natIsoLift _
    (liftFunctorQuotientIso _ _ ≪≫ Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm)

/-- **Morita equivalence on homotopy categories**: with `P`, `Q` as in
`DG.DGModuleCat.moritaEquivalence`, `Q ⊗_A -` is an equivalence `H(A) ≌ H(B)` with inverse
`P ⊗_B -`. -/
def moritaEquivalence (e₁ : TensorProductOver A Q P ≃ᵈᵍ[B] B)
    (he₁ : ∀ (b : B) x, e₁ (op b • x) = op b • e₁ x)
    (e₂ : TensorProductOver B P Q ≃ᵈᵍ[A] A)
    (he₂ : ∀ (a : A) x, e₂ (op a • x) = op a • e₂ x) :
    HomotopyCategory.{v} A ≌ HomotopyCategory.{v} B :=
  CategoryTheory.Equivalence.mk (tensorFunctor B Q) (tensorFunctor A P)
    (liftFunctorIdIso.symm ≪≫ liftNatIso _ _ (DGModuleCat.moritaUnitIso P Q e₂ he₂) ≪≫
      (liftFunctorCompIso _ _ (tensorFunctor_homotopic B Q) (tensorFunctor_homotopic A P)).symm)
    (liftFunctorCompIso _ _ (tensorFunctor_homotopic A P) (tensorFunctor_homotopic B Q) ≪≫
      liftNatIso _ _ (DGModuleCat.moritaCounitIso P Q e₁ he₁) ≪≫ liftFunctorIdIso)

theorem moritaEquivalence_functor (e₁ : TensorProductOver A Q P ≃ᵈᵍ[B] B)
    (he₁ : ∀ (b : B) x, e₁ (op b • x) = op b • e₁ x)
    (e₂ : TensorProductOver B P Q ≃ᵈᵍ[A] A)
    (he₂ : ∀ (a : A) x, e₂ (op a • x) = op a • e₂ x) :
    (moritaEquivalence P Q e₁ he₁ e₂ he₂).functor = tensorFunctor B Q := rfl

end Morita

end HomotopyCategory

end DG
