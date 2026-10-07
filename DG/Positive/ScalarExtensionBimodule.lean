import DG.Positive.ScalarExtensionModule
import DG.Module.Right

/-!
# Base change of dg bimodules along `ℤ → K`

Let `K` be a commutative ring and `X` a dg `(A, B)`-bimodule. Then `K ⊗_ℤ X` (`K` in degree `0`)
is a dg `(K ⊗ A, K ⊗ B)`-bimodule (`DG.ExtendScalars.instDGBimodule`): the left action is that of
the base-changed left module (`DG.ExtendScalars.baseChange`, the external tensor product), and
the right action is `(x ⊗ m) • (k ⊗ b) = x k ⊗ m b` (`DG.ExtendScalars.op_tmul_smul_tmul`).
There are no signs since `K` sits in degree `0`.
-/

open MulOpposite
open scoped TensorProduct

universe u

noncomputable section

namespace DG

namespace ExtendScalars

variable {K : Type u} [CommRing K] {B : Type u} [Ring B] [DGAddCommGroup B] [DGRing B]
  {X : Type u} [AddCommGroup X] [DGAddCommGroup X] [Module Bᵐᵒᵖ X]

local notation "𝒦" => DGAlgebra.gradingSubmodule ℤ (DegreeZeroRing K)
local notation "ℬ" => DGAlgebra.gradingSubmodule ℤ B

variable (K X) in
/-- The right action of `k ⊗ b` on `K ⊗_ℤ X`, `x ⊗ m ↦ x k ⊗ m b`. -/
def ract (k : DegreeZeroRing K) (b : B) : DegreeZeroRing K ⊗[ℤ] X →+ DegreeZeroRing K ⊗[ℤ] X :=
  (TensorProduct.map (AddMonoidHom.mulRight k).toIntLinearMap
    (smulAddHom Bᵐᵒᵖ X (op b)).toIntLinearMap).toAddMonoidHom

omit [DGAddCommGroup B] [DGRing B] [DGAddCommGroup X] in
theorem ract_tmul (k : DegreeZeroRing K) (b : B) (x : DegreeZeroRing K) (m : X) :
    ract K X k b (x ⊗ₜ m) = (x * k) ⊗ₜ (op b • m) := rfl

omit [DGAddCommGroup B] [DGRing B] [DGAddCommGroup X] [Module Bᵐᵒᵖ X] in
theorem addHom_ext {f g : DegreeZeroRing K ⊗[ℤ] X →+ DegreeZeroRing K ⊗[ℤ] X}
    (h : ∀ x m, f (x ⊗ₜ m) = g (x ⊗ₜ m)) : f = g :=
  AddMonoidHom.ext fun z => by
    induction z using TensorProduct.inductionOn with
    | tmul x m => exact h x m
    | add a b ha hb => rw [map_add, map_add, ha, hb]

variable (K X) in
/-- The right action as a bi-additive map. -/
def ractBilin : DegreeZeroRing K →+ B →+ AddMonoid.End (DegreeZeroRing K ⊗[ℤ] X) :=
  AddMonoidHom.mk' (fun k => AddMonoidHom.mk' (fun b => ract K X k b) fun b b' => by
      refine addHom_ext fun x m => ?_
      change ract K X k (b + b') (x ⊗ₜ m) = ract K X k b (x ⊗ₜ m) + ract K X k b' (x ⊗ₜ m)
      rw [ract_tmul, ract_tmul, ract_tmul, op_add, add_smul, TensorProduct.tmul_add])
    fun k k' => by
      ext b : 1
      refine addHom_ext fun x m => ?_
      change ract K X (k + k') b (x ⊗ₜ m) = ract K X k b (x ⊗ₜ m) + ract K X k' b (x ⊗ₜ m)
      rw [ract_tmul, ract_tmul, ract_tmul, mul_add, TensorProduct.add_tmul]

variable (K X) in
/-- The right action of `K ⊗ B` on `K ⊗_ℤ X`, as an additive map to the endomorphisms. -/
def ractAdd : ExtendScalars K B →+ AddMonoid.End (DegreeZeroRing K ⊗[ℤ] X) :=
  (TensorProduct.liftAddHom (ractBilin K X) fun r k b => by
      rw [map_zsmul, AddMonoidHom.zsmul_apply, map_zsmul]).comp
    (_root_.GradedTensorProduct.of ℤ 𝒦 ℬ).symm.toLinearMap.toAddMonoidHom

omit [DGAddCommGroup X] in
theorem ractAdd_tmul (k : DegreeZeroRing K) (b : B) :
    ractAdd K X (k ᵍ⊗ₜ[ℤ] b) = ract K X k b := rfl

omit [DGAddCommGroup X] in
theorem ractAdd_mul (y y' : ExtendScalars K B) :
    ractAdd K X (y' * y) = ractAdd K X y * ractAdd K X y' := by
  induction y using GradedTensorProduct.induction_on_tmul (R := ℤ) with
  | zero => simp
  | add y z hy hz => rw [mul_add, map_add, hy, hz, map_add, add_mul]
  | @tmul i j k hk b hb =>
    induction y' using GradedTensorProduct.induction_on_tmul (R := ℤ) with
    | zero => simp
    | add y z hy hz => rw [add_mul, map_add, hy, hz, map_add, mul_add]
    | @tmul i' j' k' hk' b' hb' =>
      by_cases hi : i = 0
      · subst hi
        rw [GradedTensorProduct.tmul_mul_tmul 𝒦 ℬ (j := j') (i' := 0) k' hb' hk b, mul_zero,
          koszulSign_zero, one_smul, ractAdd_tmul, ractAdd_tmul, ractAdd_tmul]
        refine addHom_ext fun x m => ?_
        change ract K X (k' * k) (b' * b) (x ⊗ₜ m) = ract K X k b (ract K X k' b' (x ⊗ₜ m))
        rw [ract_tmul, ract_tmul, ract_tmul, op_mul, mul_smul, mul_assoc]
      · rw [DegreeZeroRing.eq_zero_of_mem_grading K hi hk, GradedTensorProduct.zero_tmul,
          mul_zero, map_zero, zero_mul]

variable (K X) in
/-- The right action of `K ⊗ B` on `K ⊗_ℤ X`, a ring homomorphism out of `(K ⊗ B)ᵐᵒᵖ`. -/
def ractionHom : (ExtendScalars K B)ᵐᵒᵖ →+* AddMonoid.End (DegreeZeroRing K ⊗[ℤ] X) where
  toFun z := ractAdd K X (unop z)
  map_zero' := map_zero _
  map_add' z z' := map_add _ _ _
  map_one' := by
    change ractAdd K X ((1 : DegreeZeroRing K) ᵍ⊗ₜ[ℤ] (1 : B)) = 1
    rw [ractAdd_tmul]
    refine addHom_ext fun x m => ?_
    change ract K X 1 1 (x ⊗ₜ m) = x ⊗ₜ m
    rw [ract_tmul, mul_one, op_one, one_smul]
  map_mul' z z' := by
    change ractAdd K X (unop z' * unop z) = _
    exact ractAdd_mul _ _

instance instModuleOp : Module (ExtendScalars K B)ᵐᵒᵖ (DegreeZeroRing K ⊗[ℤ] X) :=
  Module.compHom _ (ractionHom K X)

omit [DGAddCommGroup X] in
theorem op_smul_def (y : ExtendScalars K B) (z : DegreeZeroRing K ⊗[ℤ] X) :
    op y • z = ractAdd K X y z := rfl

omit [DGAddCommGroup X] in
/-- `(x ⊗ m) • (k ⊗ b) = x k ⊗ m b`. -/
theorem op_tmul_smul_tmul (k : DegreeZeroRing K) (b : B) (x : DegreeZeroRing K) (m : X) :
    op (k ᵍ⊗ₜ[ℤ] b : ExtendScalars K B) • (x ⊗ₜ[ℤ] m : DegreeZeroRing K ⊗[ℤ] X) =
      (x * k) ⊗ₜ (op b • m) := rfl

section DGRight

variable [DGRightModule B X]

omit [DGRing B] in
theorem ract_mem {i₁ j₁ : ℤ} {k : DegreeZeroRing K} (hk : k ∈ grading i₁) {b : B}
    (hb : b ∈ grading j₁) {q : ℤ} {z : DegreeZeroRing K ⊗[ℤ] X} (hz : z ∈ grading q) :
    ract K X k b z ∈ grading (q + (i₁ + j₁)) := by
  by_cases hi : i₁ = 0
  · subst hi
    refine map_mem_grading_of_tmul (ract K X k b) (0 + j₁) (fun {i j x m} hx hm => ?_) hz
    rw [ract_tmul]
    have h := tmul_mem_grading (mul_mem_grading hx hk) (op_smul_mem_grading hb hm)
    convert h using 2
    ring
  · rw [DegreeZeroRing.eq_zero_of_mem_grading K hi hk]
    have : ract K X 0 b = 0 := addHom_ext fun x m => by
      change (x * 0) ⊗ₜ (op b • m) = (0 : DegreeZeroRing K ⊗[ℤ] X)
      rw [mul_zero, TensorProduct.zero_tmul]
    rw [this]
    exact zero_mem _

omit [DGRing B] in
theorem gradeInvolution_degreeZero (x : DegreeZeroRing K) :
    gradeInvolution (DegreeZeroRing K) x = x := by
  rw [gradeInvolution_of_mem (DegreeZeroRing.mem_grading_zero K x), koszulSign_zero, one_smul]

omit [DGRing B] in
/-- The Leibniz rule for the right action: `d (z (k ⊗ b)) = (d z) (k ⊗ b) + ε(z) (k ⊗ d b)`, with
`ε` the grade involution. -/
theorem d_ract (k : DegreeZeroRing K) (b : B) (z : DegreeZeroRing K ⊗[ℤ] X) :
    d (ract K X k b z) =
      ract K X k b (d z) + ract K X k (d b) (gradeInvolution _ z) := by
  induction z using tensor_induction_on with
  | zero => simp
  | add z z' hz hz' =>
    rw [map_add, d_add, hz, hz', d_add, map_add, map_add, map_add]
    abel
  | @tmul i' j' x m =>
    rw [ract_tmul, d_tmul_of_mem (DegreeZeroRing.mem_grading_zero K _),
      DegreeZeroRing.d_eq_zero, TensorProduct.zero_tmul, zero_add, koszulSign_zero, one_smul,
      d_op_smul m.2, d_tmul_of_mem (DegreeZeroRing.mem_grading_zero K _),
      DegreeZeroRing.d_eq_zero, TensorProduct.zero_tmul, zero_add, koszulSign_zero, one_smul,
      gradeInvolution_tmul, gradeInvolution_degreeZero, gradeInvolution_of_mem m.2, ract_tmul,
      ract_tmul, TensorProduct.tmul_add, Units.smul_def, Units.smul_def, smul_comm]

instance instDGRightModule : DGRightModule (ExtendScalars K B) (DegreeZeroRing K ⊗[ℤ] X) where
  op_smul_mem' {i j y z} hy hz := by
    rw [op_smul_def]
    refine GradedTensorProduct.grading_induction 𝒦 ℬ hy
      (motive := fun y => ractAdd K X y z ∈ grading (j + i)) (by simp) ?_ ?_
    · intro i₁ j₁ k b hij
      rw [ractAdd_tmul, ← hij]
      exact ract_mem k.2 b.2 hz
    · intro y y' hy hy'
      rw [map_add]
      exact add_mem hy hy'
  d_op_smul' {j z} hz y := by
    simp only [op_smul_def]
    induction y using GradedTensorProduct.induction_on_tmul (R := ℤ) with
    | zero => simp
    | add y y' hy hy' =>
      rw [map_add]
      change d (ractAdd K X y z + ractAdd K X y' z) =
        ractAdd K X y (d z) + ractAdd K X y' (d z) + koszulSign j • ractAdd K X (d (y + y')) z
      rw [d_add, hy, hy', d_add, map_add]
      change _ = _ + _ + koszulSign j • (ractAdd K X (d y) z + ractAdd K X (d y') z)
      rw [smul_add]
      abel
    | @tmul i j₂ k hk b hb =>
      by_cases hi : i = 0
      · subst hi
        rw [GradedTensorProduct.d_tmul hk, DegreeZeroRing.d_eq_zero, GradedTensorProduct.zero_tmul,
          zero_add, koszulSign_zero, one_smul, ractAdd_tmul, ractAdd_tmul]
        have h := d_ract (K := K) (X := X) k b z
        rw [gradeInvolution_of_mem hz, Units.smul_def, map_zsmul] at h
        rw [Units.smul_def]
        exact h
      · rw [DegreeZeroRing.eq_zero_of_mem_grading K hi hk, GradedTensorProduct.zero_tmul, d_zero,
          map_zero]
        change d (0 : DegreeZeroRing K ⊗[ℤ] X) = 0 + koszulSign j • (0 : DegreeZeroRing K ⊗[ℤ] X)
        simp

end DGRight

section Bimodule

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [Module A X]

omit [DGAddCommGroup X] in
theorem op_add_smul (y y' : ExtendScalars K B) (z : DegreeZeroRing K ⊗[ℤ] X) :
    op (y + y') • z = op y • z + op y' • z := by
  rw [op_smul_def, map_add]; rfl

omit [DGAddCommGroup X] in
theorem op_zero_smul (z : DegreeZeroRing K ⊗[ℤ] X) : op (0 : ExtendScalars K B) • z = 0 := by
  rw [op_smul_def, map_zero]; rfl

omit [DGAddCommGroup X] in
theorem op_smul_add (y : ExtendScalars K B) (z z' : DegreeZeroRing K ⊗[ℤ] X) :
    op y • (z + z') = op y • z + op y • z' := by
  rw [op_smul_def, op_smul_def, op_smul_def, map_add]

omit [DGAddCommGroup X] in
theorem op_smul_zero (y : ExtendScalars K B) : op y • (0 : DegreeZeroRing K ⊗[ℤ] X) = 0 := by
  rw [op_smul_def, map_zero]

theorem smul_comm_tmul [SMulCommClass A Bᵐᵒᵖ X] (s : ExtendScalars K A) (y : ExtendScalars K B)
    (z : DegreeZeroRing K ⊗[ℤ] X) : s • (op y • z) = op y • (s • z) := by
  induction s using GradedTensorProduct.induction_on_tmul (R := ℤ) with
  | zero => rw [ExternalTensor.zero_smul', ExternalTensor.zero_smul', op_smul_zero]
  | add s s' hs hs' =>
    rw [ExternalTensor.add_smul', ExternalTensor.add_smul', hs, hs', op_smul_add]
  | @tmul i j k₁ hk₁ a ha =>
    induction y using GradedTensorProduct.induction_on_tmul (R := ℤ) with
    | zero => rw [op_zero_smul, op_zero_smul, ExternalTensor.smul_zero']
    | add y y' hy hy' =>
      rw [op_add_smul, op_add_smul, ExternalTensor.smul_add', hy, hy']
    | @tmul i' j' k hk b hb =>
      induction z using TensorProduct.inductionOn with
      | tmul x m =>
        rw [op_tmul_smul_tmul, tmul_smul_tmul, tmul_smul_tmul, op_tmul_smul_tmul, mul_assoc,
          smul_comm a (op b) m]
      | add z z' hz hz' =>
        rw [op_smul_add, ExternalTensor.smul_add', hz, hz', ExternalTensor.smul_add', op_smul_add]

instance instSMulCommClass [SMulCommClass A Bᵐᵒᵖ X] :
    SMulCommClass (ExtendScalars K A) (ExtendScalars K B)ᵐᵒᵖ (DegreeZeroRing K ⊗[ℤ] X) where
  smul_comm s t z := by
    rw [← op_unop t]
    exact smul_comm_tmul s (unop t) z

/-- **Base change of dg bimodules**: for a dg `(A, B)`-bimodule `X`, `K ⊗_ℤ X` is a dg
`(K ⊗ A, K ⊗ B)`-bimodule; its left module is the base change of the left module of `X`. -/
instance instDGBimodule [DGBimodule A B X] :
    DGBimodule (ExtendScalars K A) (ExtendScalars K B) (DegreeZeroRing K ⊗[ℤ] X) :=
  DGBimodule.mk'

end Bimodule

end ExtendScalars

end DG

end
