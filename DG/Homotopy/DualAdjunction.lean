import DG.Derived.RightBasisMorita
import DG.Homotopy.BimoduleTensor

/-!
# `M^∨ ⊗_E (-) ⊣ M ⊗_A (-)` for a module with a finite right basis

Let `E`, `A` be dg rings and `M` a dg `(E, A)`-bimodule with a finite homogeneous right
basis `R : RightBasis A M ι` (dual basis `δ_i`), so that `M^∨ = HOM_A(M, A)` (`RightDual A M`) is a
dg `(A, E)`-bimodule. Then:

* `RightBasis.canon R = Σ_i b_i ⊗ δ_i ∈ M ⊗_A M^∨` is a cycle of degree `0` commuting with `E`
  (`canon_mem`, `d_canon`, `smul_canon`);
* `RightBasis.dualAdjunction R : M^∨ ⊗_E (-) ⊣ M ⊗_A (-)` as functors between `DGModuleCat E` and
  `DGModuleCat A`, with unit `x ↦ Σ_i b_i ⊗ (δ_i ⊗ x)` and counit `f ⊗ (m ⊗ y) ↦ f(m) y`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open CategoryTheory MulOpposite DG.TensorProductOver DG.TensorProductOver.RightAction

namespace DG

universe v

variable {A : Type v} [Ring A] [DGAddCommGroup A] [DGRing A]
  {M : Type v} [AddCommGroup M] [DGAddCommGroup M] [Module Aᵐᵒᵖ M]
  {ι : Type} [Fintype ι] [DecidableEq ι] (R : RightBasis A M ι)

namespace RightBasis

section NoE

variable [DGRightModule A M]

/-- The canonical element `Σ_i b_i ⊗ δ_i ∈ M ⊗_A M^∨`. -/
def canon : TensorProductOver A M (RightDual A M) := ∑ i, tmul A (R.b i) (R.δ i)

theorem coeffTensor_tmul (i : ι) (z : M) (f : RightDual A M) :
    coeffTensor R i (tmul A z f) = op (RightDual.toHom f (R.b i)) • z := rfl

theorem ext_coeffTensor {t t' : TensorProductOver A M (RightDual A M)}
    (h : ∀ i, coeffTensor R i t = coeffTensor R i t') : t = t' := by
  rw [eq_sum_coeffTensor R t, eq_sum_coeffTensor R t']
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

theorem coeffTensor_canon (i : ι) : coeffTensor R i R.canon = R.b i := by
  rw [canon, map_sum]
  simp only [coeffTensor_tmul, toHom_δ]
  conv_rhs => rw [← R.sum_coeff (R.b i)]

theorem canon_mem : R.canon ∈ grading (0 : ℤ) :=
  sum_mem fun i _ => by
    have := TensorProductOver.tmul_mem_grading (A := A) (R.b_mem i) (R.δ_mem i)
    rwa [add_neg_cancel] at this

end NoE

section WithE

variable {E : Type v} [Ring E] [DGAddCommGroup E] [DGRing E] [Module E M] [DGBimodule E A M]

theorem coeffTensor_smul (e : E) (i : ι) (t : TensorProductOver A M (RightDual A M)) :
    coeffTensor R i (e • t) = e • coeffTensor R i t := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul z f =>
    rw [smul_tmul, coeffTensor_tmul, coeffTensor_tmul]
    exact (DGBimodule.smul_op_smul e _ z).symm
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- `e (Σ b_i ⊗ δ_i) = (Σ b_i ⊗ δ_i) e`. -/
theorem smul_canon (e : E) : e • R.canon = op e • R.canon := by
  refine ext_coeffTensor R fun i => ?_
  rw [coeffTensor_smul, coeffTensor_canon, canon, Finset.smul_sum, map_sum]
  simp only [op_smul_tmul_right, coeffTensor_tmul, RightDual.toHom_op_smul, toHom_δ]
  conv_lhs => rw [← R.sum_coeff (e • R.b i)]

end WithE

section NoE2

variable [DGRightModule A M]

/-- `d (Σ b_i ⊗ δ_i) = 0`. -/
theorem d_canon : d R.canon = 0 := by
  refine ext_coeffTensor R fun i => ?_
  rw [canon, map_sum, map_sum, map_zero]
  simp only [TensorProductOver.d_tmul_of_mem (R.b_mem _), map_add, map_units_zsmul, coeffTensor_tmul, toHom_δ]
  have h2 : ∀ j, RightDual.toHom (d (R.δ j)) (R.b i) =
      -((koszulSign (R.deg j) : ℤ) • R.coeff (d (R.b i)) j) := fun j => by
    rw [← Units.smul_def]; exact R.dualBasis_coeff_d j i
  have h3 : ∀ j, koszulSign (R.deg j) • op (RightDual.toHom (d (R.δ j)) (R.b i)) • R.b j =
      -(op (R.coeff (d (R.b i)) j) • R.b j) := fun j => by
    rw [h2, MulOpposite.op_neg, neg_smul, smul_neg, MulOpposite.op_smul, smul_assoc, Units.smul_def, smul_smul,
      ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]
  simp only [h3, R.coeff_basis, Finset.sum_add_distrib, Finset.sum_neg_distrib, R.sum_coeff]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, MulOpposite.op_zero, zero_smul])
    (by simp), Pi.single_eq_same, MulOpposite.op_one, one_smul, add_neg_cancel]

end NoE2

end RightBasis

/-! ### Tensoring a right linear map of dg bimodules -/

section RTensor

variable {B C : Type v} [Ring B] [DGAddCommGroup B] [Ring C] [DGAddCommGroup C]
  {P P' : Type v} [AddCommGroup P] [DGAddCommGroup P] [Module C P] [Module Bᵐᵒᵖ P] [DGBimodule C B P]
  [AddCommGroup P'] [DGAddCommGroup P'] [Module C P'] [Module Bᵐᵒᵖ P'] [DGBimodule C B P']

/-- `f ⊗ 1 : P ⊗_B N → P' ⊗_B N` for a right `B`-linear morphism `f` of left dg `C`-modules. -/
def rTensorHom (f : P →ᵈᵍ[C] P') (hf : ∀ (b : B) (p : P), f (op b • p) = op b • f p)
    (N : Type v) [AddCommGroup N] [DGAddCommGroup N] [Module B N] [DGModule B N] :
    TensorProductOver B P N →ᵈᵍ[C] TensorProductOver B P' N where
  toFun := map ⟨⟨f, map_add f⟩, fun b p => by rw [RingHom.id_apply]; exact hf b.unop p⟩ LinearMap.id
  map_add' := map_add _
  map_smul' c x := by
    induction x using TensorProductOver.induction_on with
    | zero => simp
    | tmul p n =>
      change tmul B (f (c • p)) n = c • tmul B (f p) n
      rw [map_smul, smul_tmul]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy, RingHom.id_apply] at *
  map_mem' hx := map_mem _ _ (fun hm => f.map_mem hm) (fun hn => hn) hx
  map_d' x := by
    induction x using TensorProductOver.induction_on with
    | zero => simp
    | tmul p n =>
      induction p using DG.induction_on with
      | h_zero => simp
      | @h_homogeneous j p =>
        change map _ LinearMap.id (d (tmul B (p : P) n)) = d (tmul B (f p) n)
        rw [TensorProductOver.d_tmul_of_mem p.2, TensorProductOver.d_tmul_of_mem (f.map_mem p.2),
          map_add, map_units_zsmul]
        change tmul B (f (d (p : P))) n + koszulSign j • tmul B (f p) (d n) = _
        rw [f.map_d]
      | h_add p p' hp hp' =>
        rw [add_tmul, d_add, map_add, map_add, d_add, hp, hp']
    | add x y hx hy => rw [d_add, map_add, map_add, hx, hy, d_add]

@[simp]
theorem rTensorHom_tmul (f : P →ᵈᵍ[C] P') (hf : ∀ (b : B) (p : P), f (op b • p) = op b • f p)
    (N : Type v) [AddCommGroup N] [DGAddCommGroup N] [Module B N] [DGModule B N] (p : P) (n : N) :
    rTensorHom f hf N (tmul B p n) = tmul B (f p) n := rfl

end RTensor

namespace RightBasis

section Adjunction

variable {E : Type v} [Ring E] [DGAddCommGroup E] [DGRing E] [Module E M] [DGBimodule E A M]

/-- The evaluation `M^∨ ⊗_E M → A`, `f ⊗ m ↦ f(m)`, as a morphism of dg `A`-modules. -/
def evDG : TensorProductOver E (RightDual A M) M →ᵈᵍ[A] A where
  toFun := FullAction.evHom
  map_add' := map_add _
  map_smul' a t := by rw [FullAction.evHom_smul, smul_eq_mul, RingHom.id_apply]
  map_mem' ht := FullAction.evHom_mem ht
  map_d' t := FullAction.evHom_d t

theorem evDG_op_smul (a : A) (t : TensorProductOver E (RightDual A M) M) :
    evDG (op a • t) = op a • evDG t := by
  change FullAction.evHom (op a • t) = op a • FullAction.evHom t
  rw [FullAction.evHom_op_smul, MulOpposite.smul_eq_mul_unop, unop_op]

variable (E) in
/-- `x ↦ (Σ_i b_i ⊗ δ_i) ⊗ x`. -/
def canonTensor (X : Type v) [AddCommGroup X] [DGAddCommGroup X] [Module E X] [DGModule E X] :
    X →ᵈᵍ[E] TensorProductOver E (TensorProductOver A M (RightDual A M)) X where
  toFun x := tmul E R.canon x
  map_add' x y := tmul_add _ _ _
  map_smul' e x := by
    rw [RingHom.id_apply, smul_tmul, ← op_smul_tmul]
    exact congrArg (fun t => tmul E t x) (R.smul_canon e).symm
  map_mem' {k x} hx := by
    have := TensorProductOver.tmul_mem_grading (A := E) R.canon_mem hx
    rwa [zero_add] at this
  map_d' x := by
    rw [TensorProductOver.d_tmul_of_mem R.canon_mem, R.d_canon, zero_tmul, zero_add, koszulSign_zero,
      one_smul]

variable (E) in
/-- The unit `x ↦ Σ_i b_i ⊗ (δ_i ⊗ x)`. -/
def unitHom (X : Type v) [AddCommGroup X] [DGAddCommGroup X] [Module E X] [DGModule E X] :
    X →ᵈᵍ[E] TensorProductOver A M (TensorProductOver E (RightDual A M) X) :=
  (DGModuleCat.assocDGModuleEquiv (RightDual A M) M X).toDGModuleHom.comp (R.canonTensor E X)

theorem unitHom_apply (X : Type v) [AddCommGroup X] [DGAddCommGroup X] [Module E X] [DGModule E X]
    (x : X) : R.unitHom E X x = ∑ i, tmul A (R.b i) (tmul E (R.δ i) x) := by
  change assocEquiv A E M (RightDual A M) X (tmul E R.canon x) = _
  rw [canon, show tmul E (∑ i, tmul A (R.b i) (R.δ i)) x = ∑ i, tmul E (tmul A (R.b i) (R.δ i)) x from
    map_sum ((TensorProductOver.tmulAddHom E (TensorProductOver A M (RightDual A M)) X).flip x) _ _,
    map_sum]
  rfl

variable (E) in
/-- The counit `f ⊗ (m ⊗ y) ↦ f(m) y`. -/
def counitHom (Y : Type v) [AddCommGroup Y] [DGAddCommGroup Y] [Module A Y] [DGModule A Y] :
    TensorProductOver E (RightDual A M) (TensorProductOver A M Y) →ᵈᵍ[A] Y :=
  (lidDGModuleEquiv A Y).toDGModuleHom.comp ((rTensorHom (evDG (E := E)) evDG_op_smul Y).comp
    (DGModuleCat.assocDGModuleEquiv M (RightDual A M) Y).symm.toDGModuleHom)

theorem counitHom_tmul (Y : Type v) [AddCommGroup Y] [DGAddCommGroup Y] [Module A Y] [DGModule A Y]
    (f : RightDual A M) (m : M) (y : Y) :
    counitHom (M := M) E Y (tmul E f (tmul A m y)) = RightDual.toHom f m • y := rfl

set_option backward.isDefEq.respectTransparency false in
open DGModuleCat in
/-- **`M^∨ ⊗_E (-) ⊣ M ⊗_A (-)`** for a dg `(E, A)`-bimodule `M` with a finite homogeneous right
basis over `A`: unit `x ↦ Σ_i b_i ⊗ (δ_i ⊗ x)`, counit `f ⊗ (m ⊗ y) ↦ f(m) y`. -/
def dualAdjunction :
    tensorFunctor (B := E) A (RightDual A M) ⊣ tensorFunctor (B := A) E M where
  unit :=
    { app X := ofHom (R.unitHom E X)
      naturality {X X'} f := hom_ext_apply fun x => by
        change R.unitHom E X' (f x) = (tensorFunctor E M).map ((tensorFunctor A (RightDual A M)).map f)
          (R.unitHom E X x)
        rw [unitHom_apply, unitHom_apply, map_sum]
        rfl }
  counit :=
    { app Y := ofHom (counitHom (M := M) E Y)
      naturality {Y Y'} g := tensor_hom_ext fun f t => by
        induction t using TensorProductOver.induction_on with
        | zero => simp
        | tmul m y =>
          change counitHom (M := M) E Y' (tmul E f (tmul A m (g y))) = g (counitHom (M := M) E Y (tmul E f (tmul A m y)))
          rw [counitHom_tmul, counitHom_tmul, map_smul]
        | add t t' ht ht' =>
          rw [tmul_add, map_add, map_add, ht, ht'] }
  left_triangle_components X := tensor_hom_ext fun f x => by
    change counitHom (M := M) E _ (tmul E f (R.unitHom E X x)) = tmul E f x
    rw [unitHom_apply, ← TensorProductOver.tmulAddHom_apply, map_sum, map_sum]
    simp only [TensorProductOver.tmulAddHom_apply, counitHom_tmul, smul_tmul]
    conv_rhs => rw [← R.dualBasis.sum_coeff f]
    exact (map_sum ((TensorProductOver.tmulAddHom E (RightDual A M) X).flip x) _ Finset.univ).symm
  right_triangle_components Y := tensor_hom_ext fun m y => by
    change (tensorFunctor E M).map (ofHom (counitHom (M := M) E Y)) (R.unitHom E _ (tmul A m y)) =
      tmul A m y
    rw [unitHom_apply, map_sum]
    change ∑ i, tmul A (R.b i) (counitHom (M := M) E Y (tmul E (R.δ i) (tmul A m y))) = _
    simp only [counitHom_tmul, toHom_δ, ← op_smul_tmul]
    conv_rhs => rw [← R.sum_coeff m]
    exact (map_sum ((TensorProductOver.tmulAddHom A M Y).flip y) _ Finset.univ).symm

end Adjunction

end RightBasis

end DG
