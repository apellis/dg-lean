import DG.Module.ExternalTensor
import DG.Module.Right
import DG.Module.Equiv

/-!
# The external tensor product of dg bimodules

For dg rings `A`, `A'`, `B`, `B'`, a dg `(A, A')`-bimodule `M` and a dg `(B, B')`-bimodule `N`, the
tensor product `M ⊗[ℤ] N` of dg abelian groups is a left dg module over `A ⊗ B`
(`DG.ExternalTensor.instDGModule`, `(a ⊗ b) • (m ⊗ n) = (-1)^{|b| |m|} (a • m) ⊗ (b • n)`). This file
adds the right action of `A' ⊗ B'` with the Koszul sign rule

`(m ⊗ n) • (a' ⊗ b') = (-1)^{|n| |a'|} (m • a') ⊗ (n • b')`

(`DG.ExternalTensor.tmul_op_smul_tmul`), making `M ⊗ N` a right dg `A' ⊗ B'`-module
(`DG.ExternalTensor.instDGRightModule`) and a dg `(A ⊗ B, A' ⊗ B')`-bimodule
(`DG.ExternalTensor.instDGBimodule`). Here `A' ⊗ B'` is the graded tensor product
`A' ᵍ⊗[ℤ] B'` and right modules are modules over the multiplicative opposite.
-/

open scoped TensorProduct
open DirectSum MulOpposite

noncomputable section

set_option linter.unusedSectionVars false

namespace DG

namespace ExternalTensor

private theorem ks_eq' {m n : ℤ} (h : Even (m - n)) : koszulSign m = koszulSign n :=
  (Int.negOnePow_eq_iff m n).mpr h

private theorem ks_val' (n : ℤ) : (koszulSign n : ℤ) = if Even n then 1 else -1 := by
  split_ifs with h
  · rw [koszulSign, Int.negOnePow_even n h]; rfl
  · rw [koszulSign, Int.negOnePow_odd n (Int.not_even_iff_odd.mp h)]; rfl

section Right

variable {A' B' : Type*} [Ring A'] [DGAddCommGroup A'] [DGRing A'] [Ring B'] [DGAddCommGroup B']
  [DGRing B']
  {M : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A'ᵐᵒᵖ M] [DGRightModule A' M]
  {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module B'ᵐᵒᵖ N] [DGRightModule B' N]

local notation "𝒜'" => DGAlgebra.gradingSubmodule ℤ A'
local notation "ℬ'" => DGAlgebra.gradingSubmodule ℤ B'

variable (M N) in
/-- The right action of `a' ⊗ b'` on `M ⊗ N`, `m ⊗ n ↦ (-1)^{|n| |a'|} (m • a') ⊗ (n • b')`. -/
def ract (a' : A') (b' : B') : M ⊗[ℤ] N →+ M ⊗[ℤ] N :=
  tensorLiftHomogeneous fun _ j =>
    AddMonoidHom.mk' (fun m => AddMonoidHom.mk'
      (fun n => (op (twist A' j a') • (m : M)) ⊗ₜ (op b' • (n : N)))
      fun n n' => by simp [smul_add, TensorProduct.tmul_add])
      fun m m' => by ext n; simp [smul_add, TensorProduct.add_tmul]

omit [DGRing A'] [DGRing B'] [DGRightModule A' M] [DGRightModule B' N] in
theorem ract_tmul (a' : A') (b' : B') {i j : ℤ} {m : M} (hm : m ∈ grading i) {n : N}
    (hn : n ∈ grading j) : ract M N a' b' (m ⊗ₜ n) = (op (twist A' j a') • m) ⊗ₜ (op b' • n) :=
  tensorLiftHomogeneous_tmul _ hm hn

omit [DGRing A'] [DGRing B'] [DGRightModule A' M] [DGRightModule B' N] in
theorem ract_tmul_of_mem {k : ℤ} {a' : A'} (ha : a' ∈ grading k) (b' : B') (m : M) {j : ℤ}
    {n : N} (hn : n ∈ grading j) :
    ract M N a' b' (m ⊗ₜ n) = koszulSign (k * j) • ((op a' • m) ⊗ₜ (op b' • n)) := by
  induction m using DG.induction_on with
  | h_zero => simp
  | h_homogeneous m =>
    rw [ract_tmul a' b' m.2 hn, twist_of_mem j ha, Units.smul_def, Units.smul_def, op_smul,
      smul_assoc, TensorProduct.smul_tmul']
  | h_add m m' hm hm' => rw [TensorProduct.add_tmul, map_add, hm, hm', smul_add,
      TensorProduct.add_tmul, smul_add]

variable (M N) in
/-- The right action as a bi-additive map. -/
def ractBilin : A' →+ B' →+ AddMonoid.End (M ⊗[ℤ] N) :=
  AddMonoidHom.mk' (fun a' => AddMonoidHom.mk' (fun b' => ract M N a' b') fun b b' =>
      tensor_addHom_ext fun m n => by
        change ract M N a' (b + b') _ = ract M N a' b _ + ract M N a' b' _
        rw [ract_tmul a' _ m.2 n.2, ract_tmul a' _ m.2 n.2, ract_tmul a' _ m.2 n.2, op_add,
          add_smul, TensorProduct.tmul_add])
    fun a a' => by
      ext b : 1
      refine tensor_addHom_ext fun m n => ?_
      change ract M N (a + a') b _ = ract M N a b _ + ract M N a' b _
      rw [ract_tmul _ b m.2 n.2, ract_tmul _ b m.2 n.2, ract_tmul _ b m.2 n.2, map_add, op_add,
        add_smul, TensorProduct.add_tmul]

variable (M N) in
/-- The right action of `A' ⊗ B'` on `M ⊗ N`, as an additive map to the endomorphisms. -/
def ractAdd : (𝒜' ᵍ⊗[ℤ] ℬ') →+ AddMonoid.End (M ⊗[ℤ] N) :=
  (TensorProduct.liftAddHom (ractBilin M N) fun r a b => by
      rw [map_zsmul, AddMonoidHom.zsmul_apply, map_zsmul]).comp
    (_root_.GradedTensorProduct.of ℤ 𝒜' ℬ').symm.toLinearMap.toAddMonoidHom

omit [DGRightModule A' M] [DGRightModule B' N] in
theorem ractAdd_tmul (a : A') (b : B') :
    ractAdd M N (a ᵍ⊗ₜ[ℤ] b) = ract M N a b := rfl

theorem ract_ract {i j i' : ℤ} {a : A'} (ha : a ∈ grading i) {b : B'} (hb : b ∈ grading j)
    {a' : A'} (ha' : a' ∈ grading i') (b' : B') (x : M ⊗[ℤ] N) :
    ractAdd M N ((a ᵍ⊗ₜ[ℤ] b : 𝒜' ᵍ⊗[ℤ] ℬ') * (a' ᵍ⊗ₜ[ℤ] b')) x =
      ract M N a' b' (ract M N a b x) := by
  rw [GradedTensorProduct.tmul_mul_tmul 𝒜' ℬ' a hb ha' b', Units.smul_def, map_zsmul,
    ractAdd_tmul]
  induction x using tensor_induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, ← hx, ← hy]
  | @tmul p q m n =>
    change ((koszulSign (j * i') : ℤ) • ract M N (a * a') (b * b')) ((m : M) ⊗ₜ (n : N)) = _
    rw [AddMonoidHom.zsmul_apply, ract_tmul_of_mem (mul_mem_grading ha ha') _ _ n.2,
      ract_tmul_of_mem ha _ _ n.2, map_units_zsmul,
      ract_tmul_of_mem ha' _ _ (op_smul_mem_grading hb n.2), op_mul, op_mul, ← Units.smul_def,
      mul_smul (op a') (op a) (m : M), mul_smul (op b') (op b) (n : N)]
    simp only [smul_smul, ← koszulSign_add]
    congr 1
    exact ks_eq' ⟨0, by ring⟩

omit [DGRightModule A' M] [DGRightModule B' N] in
theorem ractAdd_one : ractAdd M N (1 : 𝒜' ᵍ⊗[ℤ] ℬ') = 1 := by
  refine AddMonoidHom.ext fun x => ?_
  show ract M N 1 1 x = x
  induction x using tensor_induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy]
  | tmul m n =>
    rw [ract_tmul_of_mem (one_mem_grading (A := A')) _ _ n.2, zero_mul, koszulSign_zero, one_smul]
    simp only [op_one, one_smul]

theorem ractAdd_mul (x y : 𝒜' ᵍ⊗[ℤ] ℬ') :
    ractAdd M N (x * y) = ractAdd M N y * ractAdd M N x := by
  induction x using GradedTensorProduct.induction_on_tmul (R := ℤ) with
  | zero => simp only [zero_mul, map_zero, mul_zero]
  | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, mul_add]
  | @tmul i j a ha b hb =>
    induction y using GradedTensorProduct.induction_on_tmul (R := ℤ) with
    | zero => simp only [mul_zero, map_zero, zero_mul]
    | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, add_mul]
    | @tmul i' j' a' ha' b' hb' =>
      ext x
      exact ract_ract ha hb ha' b' x

variable (M N) in
/-- The right action of `A' ⊗ B'` on `M ⊗ N`, a ring homomorphism out of the opposite ring. -/
def ractHom : (𝒜' ᵍ⊗[ℤ] ℬ')ᵐᵒᵖ →+* AddMonoid.End (M ⊗[ℤ] N) where
  toFun x := ractAdd M N x.unop
  map_one' := ractAdd_one
  map_mul' x y := by rw [unop_mul, ractAdd_mul]
  map_zero' := by rw [unop_zero, map_zero]
  map_add' x y := by rw [unop_add, map_add]

/-- The right action of `A' ⊗ B'` on `M ⊗ N`. -/
instance instModuleOp : Module (𝒜' ᵍ⊗[ℤ] ℬ')ᵐᵒᵖ (M ⊗[ℤ] N) :=
  Module.compHom (M ⊗[ℤ] N) (ractHom M N)

theorem op_smul_def (x : 𝒜' ᵍ⊗[ℤ] ℬ') (y : M ⊗[ℤ] N) : op x • y = ractAdd M N x y := rfl

theorem zero_op_smul' (y : M ⊗[ℤ] N) : op (0 : 𝒜' ᵍ⊗[ℤ] ℬ') • y = 0 := by
  rw [op_smul_def, map_zero]; rfl

theorem add_op_smul' (x x' : 𝒜' ᵍ⊗[ℤ] ℬ') (y : M ⊗[ℤ] N) :
    op (x + x') • y = op x • y + op x' • y := by
  rw [op_smul_def, op_smul_def, op_smul_def, map_add]; rfl

theorem op_smul_zero' (x : 𝒜' ᵍ⊗[ℤ] ℬ') : op x • (0 : M ⊗[ℤ] N) = 0 := by
  rw [op_smul_def, map_zero]

theorem op_smul_add' (x : 𝒜' ᵍ⊗[ℤ] ℬ') (y y' : M ⊗[ℤ] N) :
    op x • (y + y') = op x • y + op x • y' := by
  rw [op_smul_def, op_smul_def, op_smul_def, map_add]

theorem op_smul_neg' (x : 𝒜' ᵍ⊗[ℤ] ℬ') (y : M ⊗[ℤ] N) : op x • (-y) = -(op x • y) := by
  rw [op_smul_def, op_smul_def, map_neg]

/-- **The Koszul sign rule** `(m ⊗ n) • (a' ⊗ b') = (-1)^{|n| |a'|} (m • a') ⊗ (n • b')`. -/
theorem tmul_op_smul_tmul {k : ℤ} {a' : A'} (ha : a' ∈ grading k) (b' : B') (m : M) {j : ℤ}
    {n : N} (hn : n ∈ grading j) :
    op (a' ᵍ⊗ₜ[ℤ] b' : 𝒜' ᵍ⊗[ℤ] ℬ') • (m ⊗ₜ[ℤ] n) =
      koszulSign (k * j) • ((op a' • m) ⊗ₜ (op b' • n)) :=
  ract_tmul_of_mem ha b' m hn

theorem op_smul_units_smul (x : 𝒜' ᵍ⊗[ℤ] ℬ') (u : ℤˣ) (y : M ⊗[ℤ] N) :
    op x • (u • y) = u • (op x • y) := by
  rw [op_smul_def, op_smul_def]
  exact map_units_zsmul (ractAdd M N x : M ⊗[ℤ] N →+ M ⊗[ℤ] N) u y

theorem units_op_smul (u : ℤˣ) (x : 𝒜' ᵍ⊗[ℤ] ℬ') (y : M ⊗[ℤ] N) :
    op (u • x) • y = u • (op x • y) := by
  rw [op_smul_def, op_smul_def, Units.smul_def, map_zsmul, Units.smul_def]
  rfl

theorem ract_mem {i j : ℤ} {a : A'} (ha : a ∈ grading i) {b : B'} (hb : b ∈ grading j) {q : ℤ}
    {y : M ⊗[ℤ] N} (hy : y ∈ grading q) : ract M N a b y ∈ grading (q + (i + j)) := by
  refine map_mem_grading_of_tmul (ract M N a b) (i + j) (fun {i' j' m n} hm hn => ?_) hy
  rw [ract_tmul_of_mem ha b m hn, Units.smul_def]
  refine zsmul_mem ?_ _
  have := tmul_mem_grading (op_smul_mem_grading ha hm) (op_smul_mem_grading hb hn)
  rwa [show i' + i + (j' + j) = i' + j' + (i + j) by ring] at this

theorem op_smul_mem_grading' {p q : ℤ} {x : 𝒜' ᵍ⊗[ℤ] ℬ'} (hx : x ∈ grading p)
    {y : M ⊗[ℤ] N} (hy : y ∈ grading q) : op x • y ∈ grading (q + p) := by
  refine GradedTensorProduct.grading_induction 𝒜' ℬ' hx
    (motive := fun x => op x • y ∈ grading (q + p)) ?_ ?_ ?_
  · rw [op_zero, zero_smul]; exact zero_mem _
  · intro i j a b hij
    have := ract_mem a.2 b.2 hy
    rwa [hij] at this
  · intro x x' hx hx'
    rw [op_add, add_smul]
    exact add_mem hx hx'

theorem d_op_smul_tmul_tmul {i : ℤ} {a : A'} (ha : a ∈ grading i) (b : B') {k l : ℤ} {m : M} (hm : m ∈ grading k) {n : N} (hn : n ∈ grading l) :
    d (op (a ᵍ⊗ₜ[ℤ] b : 𝒜' ᵍ⊗[ℤ] ℬ') • (m ⊗ₜ[ℤ] n)) =
      op (a ᵍ⊗ₜ[ℤ] b : 𝒜' ᵍ⊗[ℤ] ℬ') • d (m ⊗ₜ[ℤ] n) +
        koszulSign (k + l) • (op (d (a ᵍ⊗ₜ[ℤ] b : 𝒜' ᵍ⊗[ℤ] ℬ')) • (m ⊗ₜ[ℤ] n)) := by
  have h1 := tmul_op_smul_tmul (M := M) ha b (d m) hn
  have h2 := tmul_op_smul_tmul ha b m (d_mem hn)
  have h3 := tmul_op_smul_tmul (d_mem ha) b m hn
  have h4 := tmul_op_smul_tmul ha (d b) m hn
  rw [tmul_op_smul_tmul ha b m hn, d_units_smul, d_tmul_of_mem (op_smul_mem_grading ha hm),
    d_op_smul hm a, d_op_smul hn b, GradedTensorProduct.d_tmul ha b, d_tmul_of_mem hm n]
  simp only [add_op_smul', op_smul_add', op_smul_units_smul, units_op_smul, h1, h2, h3, h4]
  simp only [Units.smul_def, TensorProduct.add_tmul, TensorProduct.tmul_add,
    TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add, smul_smul, ks_val']
  by_cases hi : Even i <;> by_cases hk : Even k <;> by_cases hl : Even l <;>
    simp [Int.even_add, Int.even_mul, ← Int.not_even_iff_odd, hi, hk, hl] <;> abel

theorem d_op_smul_of_mem {q : ℤ} {y : M ⊗[ℤ] N} (hy : y ∈ grading q) (x : 𝒜' ᵍ⊗[ℤ] ℬ') :
    d (op x • y) = op x • d y + koszulSign q • (op (d x) • y) := by
  induction x using GradedTensorProduct.induction_on_tmul (R := ℤ) with
  | zero =>
    rw [zero_op_smul', d_zero, d_zero, zero_op_smul', zero_op_smul', smul_zero, add_zero]
  | add x x' hx hx' =>
    rw [add_op_smul', d_add, hx, hx', d_add, add_op_smul', add_op_smul', smul_add]
    abel
  | @tmul i j a ha b hb =>
    change y ∈ tensorGrading M N q at hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy' =>
      obtain ⟨k, l, rfl, m, hm, n, hn, rfl⟩ := hy'
      exact d_op_smul_tmul_tmul ha b hm hn
    | zero => rw [op_smul_zero', d_zero, op_smul_zero', op_smul_zero', smul_zero, add_zero]
    | add y y' _ _ h h' =>
      rw [op_smul_add', d_add, h, h', d_add, op_smul_add', op_smul_add', smul_add]
      abel
    | neg y _ h => rw [op_smul_neg', d_neg, h, d_neg, op_smul_neg', op_smul_neg', smul_neg, neg_add]

/-- **`M ⊗ N` is a right dg module over `A' ⊗ B'`.** -/
instance instDGRightModule : DGRightModule (𝒜' ᵍ⊗[ℤ] ℬ') (M ⊗[ℤ] N) where
  op_smul_mem' hx hy := op_smul_mem_grading' hx hy
  d_op_smul' hy x := d_op_smul_of_mem hy x

end Right

section Bimodule

variable {A B A' B' : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B] [Ring A'] [DGAddCommGroup A'] [DGRing A'] [Ring B'] [DGAddCommGroup B'] [DGRing B']
  {M : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M] [Module A'ᵐᵒᵖ M]
  [DGRightModule A' M] [SMulCommClass A A'ᵐᵒᵖ M]
  {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module B N] [DGModule B N] [Module B'ᵐᵒᵖ N]
  [DGRightModule B' N] [SMulCommClass B B'ᵐᵒᵖ N]

local notation "𝒜" => DGAlgebra.gradingSubmodule ℤ A
local notation "ℬ" => DGAlgebra.gradingSubmodule ℤ B
local notation "𝒜'" => DGAlgebra.gradingSubmodule ℤ A'
local notation "ℬ'" => DGAlgebra.gradingSubmodule ℤ B'

theorem smul_op_smul_tmul_tmul {i j : ℤ} (a : A) {b : B} (hb : b ∈ grading j) {a' : A'}
    (ha' : a' ∈ grading i) (b' : B') {k l : ℤ} {m : M} (hm : m ∈ grading k) {n : N}
    (hn : n ∈ grading l) :
    (a ᵍ⊗ₜ[ℤ] b : 𝒜 ᵍ⊗[ℤ] ℬ) • (op (a' ᵍ⊗ₜ[ℤ] b' : 𝒜' ᵍ⊗[ℤ] ℬ') • (m ⊗ₜ[ℤ] n)) =
      op (a' ᵍ⊗ₜ[ℤ] b' : 𝒜' ᵍ⊗[ℤ] ℬ') • ((a ᵍ⊗ₜ[ℤ] b : 𝒜 ᵍ⊗[ℤ] ℬ) • (m ⊗ₜ[ℤ] n)) := by
  rw [tmul_op_smul_tmul ha' b' m hn, smul_units_smul, tmul_smul_tmul a hb (op_smul_mem_grading ha' hm),
    tmul_smul_tmul a hb hm n, op_smul_units_smul,
    tmul_op_smul_tmul ha' b' (a • m) (smul_mem_grading hb hn), smul_smul, smul_smul,
    ← koszulSign_add, ← koszulSign_add, smul_comm a (op a') m, smul_comm b (op b') n]
  congr 1
  exact ks_eq' ⟨0, by ring⟩

instance instSMulCommClass : SMulCommClass (𝒜 ᵍ⊗[ℤ] ℬ) (𝒜' ᵍ⊗[ℤ] ℬ')ᵐᵒᵖ (M ⊗[ℤ] N) where
  smul_comm x x' y := by
    induction x' using MulOpposite.rec' with
    | _ x' =>
    induction x using GradedTensorProduct.induction_on_tmul (R := ℤ) with
    | zero => rw [zero_smul', zero_smul', smul_zero]
    | add x₁ x₂ h₁ h₂ => rw [add_smul', h₁, h₂, add_smul', smul_add]
    | @tmul j' j a ha b hb =>
      induction x' using GradedTensorProduct.induction_on_tmul (R := ℤ) with
      | zero => rw [zero_op_smul', zero_op_smul', smul_zero']
      | add x₁ x₂ h₁ h₂ => rw [add_op_smul', add_op_smul', smul_add', h₁, h₂]
      | @tmul i i' a' ha' b' hb' =>
        induction y using tensor_induction_on with
        | zero => rw [op_smul_zero', smul_zero', op_smul_zero']
        | add y y' hy hy' => rw [op_smul_add', smul_add', hy, hy', smul_add', op_smul_add']
        | tmul m n => exact smul_op_smul_tmul_tmul a hb ha' b' m.2 n.2

/-- **`M ⊗ N` is a dg `(A ⊗ B, A' ⊗ B')`-bimodule.** -/
instance instDGBimodule : DGBimodule (𝒜 ᵍ⊗[ℤ] ℬ) (𝒜' ᵍ⊗[ℤ] ℬ') (M ⊗[ℤ] N) := DGBimodule.mk'

end Bimodule


section Regular

variable {A B : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B]

local notation "𝒜" => DGAlgebra.gradingSubmodule ℤ A
local notation "ℬ" => DGAlgebra.gradingSubmodule ℤ B

variable (A B) in
/-- **The external tensor product of the regular bimodules is the regular bimodule** of
`A ⊗ B`: `a ⊗ b ↦ a ⊗ b` is an isomorphism of dg `A ⊗ B`-modules `A ⊗ B ≅ A ⊗ B`, and it is
right `A ⊗ B`-linear (`regularEquiv_op_smul`). -/
def regularEquiv : (A ⊗[ℤ] B) ≃ᵈᵍ[𝒜 ᵍ⊗[ℤ] ℬ] (𝒜 ᵍ⊗[ℤ] ℬ) where
  toFun := _root_.GradedTensorProduct.of ℤ 𝒜 ℬ
  invFun := (_root_.GradedTensorProduct.of ℤ 𝒜 ℬ).symm
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' := map_add _
  map_smul' x y := by
    change _ = x * _
    induction x using GradedTensorProduct.induction_on_tmul (R := ℤ) with
    | zero => rw [ExternalTensor.zero_smul', map_zero, zero_mul]
    | add x x' hx hx' => rw [ExternalTensor.add_smul', map_add, hx, hx', add_mul]
    | @tmul i j a ha b hb =>
      induction y using DG.tensor_induction_on with
      | zero => rw [ExternalTensor.smul_zero', map_zero, mul_zero]
      | add y y' hy hy' => rw [ExternalTensor.smul_add', map_add, hy, hy', map_add, mul_add]
      | @tmul p q a' b' =>
        rw [ExternalTensor.tmul_smul_tmul a hb a'.2 (b' : B), smul_eq_mul, smul_eq_mul,
          Units.smul_def, map_zsmul]
        change _ = (a ᵍ⊗ₜ[ℤ] b : 𝒜 ᵍ⊗[ℤ] ℬ) * ((a' : A) ᵍ⊗ₜ[ℤ] (b' : B))
        rw [GradedTensorProduct.tmul_mul_tmul 𝒜 ℬ a hb a'.2 (b' : B), Units.smul_def]
  map_mem' {n x} hx := by
    simpa using map_mem_grading_of_tmul (M := A) (N := B)
      (_root_.GradedTensorProduct.of ℤ 𝒜 ℬ).toLinearMap.toAddMonoidHom 0
      (fun {i j a b} ha hb => by
        simpa using GradedTensorProduct.tmul_mem_grading (R := ℤ) ha hb) hx
  map_d' x := by
    induction x using DG.tensor_induction_on with
    | zero => simp
    | add x y hx hy => rw [d_add, map_add, hx, hy, map_add, d_add]
    | @tmul i j a b =>
      rw [d_tmul_of_mem a.2]
      change _ = d ((a : A) ᵍ⊗ₜ[ℤ] (b : B) : 𝒜 ᵍ⊗[ℤ] ℬ)
      rw [GradedTensorProduct.d_tmul a.2 (b : B), map_add, Units.smul_def, map_zsmul,
        Units.smul_def]

theorem regularEquiv_tmul (a : A) (b : B) :
    regularEquiv A B (a ⊗ₜ[ℤ] b) = (a ᵍ⊗ₜ[ℤ] b : 𝒜 ᵍ⊗[ℤ] ℬ) := rfl

theorem regularEquiv_op_smul (x : 𝒜 ᵍ⊗[ℤ] ℬ) (y : A ⊗[ℤ] B) :
    regularEquiv A B (op x • y) = op x • regularEquiv A B y := by
  rw [MulOpposite.smul_eq_mul_unop, unop_op]
  induction x using GradedTensorProduct.induction_on_tmul (R := ℤ) with
  | zero => rw [zero_op_smul', map_zero, mul_zero]
  | add x x' hx hx' => rw [add_op_smul', map_add, hx, hx', mul_add]
  | @tmul i j a ha b hb =>
    induction y using DG.tensor_induction_on with
    | zero => rw [op_smul_zero', map_zero, zero_mul]
    | add y y' hy hy' => rw [op_smul_add', map_add, hy, hy', map_add, add_mul]
    | @tmul p q a' b' =>
      rw [tmul_op_smul_tmul ha b (a' : A) b'.2, Units.smul_def, map_zsmul, regularEquiv_tmul,
        regularEquiv_tmul, GradedTensorProduct.tmul_mul_tmul 𝒜 ℬ (a' : A) b'.2 ha b,
        op_smul_eq_mul, op_smul_eq_mul, mul_comm i q, Units.smul_def]

end Regular

section TensorEquiv

variable {A B : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B]
  {M M' : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  [AddCommGroup M'] [DGAddCommGroup M'] [Module A M'] [DGModule A M']
  {N N' : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module B N] [DGModule B N]
  [AddCommGroup N'] [DGAddCommGroup N'] [Module B N'] [DGModule B N']

local notation "𝒜" => DGAlgebra.gradingSubmodule ℤ A
local notation "ℬ" => DGAlgebra.gradingSubmodule ℤ B

/-- The external tensor product `e ⊗ f : M ⊗ N ≅ M' ⊗ N'` of isomorphisms of dg modules. -/
def tensorEquiv (e : M ≃ᵈᵍ[A] M') (f : N ≃ᵈᵍ[B] N') : (M ⊗[ℤ] N) ≃ᵈᵍ[𝒜 ᵍ⊗[ℤ] ℬ] (M' ⊗[ℤ] N') where
  toFun := tensorMap (e : M →+ M') (f : N →+ N')
  invFun := tensorMap (e.symm : M' →+ M) (f.symm : N' →+ N)
  left_inv x := by
    induction x using TensorProduct.inductionOn with
    | tmul m n => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  right_inv x := by
    induction x using TensorProduct.inductionOn with
    | tmul m n => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  map_add' := map_add _
  map_smul' x y := tensorMap_smul _ _ (fun a m => map_smul e a m) (fun b n => map_smul f b n)
    (fun hm => e.map_mem hm) x y
  map_mem' hx := tensorMap_mem _ _ (fun hm => e.map_mem hm) (fun hn => f.map_mem hn) hx
  map_d' x := tensorMap_d _ _ (fun hm => e.map_mem hm) e.map_d f.map_d x

@[simp]
theorem tensorEquiv_tmul (e : M ≃ᵈᵍ[A] M') (f : N ≃ᵈᵍ[B] N') (m : M) (n : N) :
    tensorEquiv e f (m ⊗ₜ n) = e m ⊗ₜ f n := rfl

variable {A' B' : Type*} [Ring A'] [DGAddCommGroup A'] [DGRing A'] [Ring B'] [DGAddCommGroup B']
  [DGRing B'] [Module A'ᵐᵒᵖ M] [DGRightModule A' M] [Module A'ᵐᵒᵖ M'] [DGRightModule A' M']
  [Module B'ᵐᵒᵖ N] [DGRightModule B' N] [Module B'ᵐᵒᵖ N'] [DGRightModule B' N']

local notation "𝒜'" => DGAlgebra.gradingSubmodule ℤ A'
local notation "ℬ'" => DGAlgebra.gradingSubmodule ℤ B'

theorem tensorEquiv_op_smul (e : M ≃ᵈᵍ[A] M') (f : N ≃ᵈᵍ[B] N')
    (he : ∀ (a : A') (m : M), e (op a • m) = op a • e m)
    (hf : ∀ (b : B') (n : N), f (op b • n) = op b • f n) (x : 𝒜' ᵍ⊗[ℤ] ℬ') (y : M ⊗[ℤ] N) :
    tensorEquiv e f (op x • y) = op x • tensorEquiv e f y := by
  induction x using GradedTensorProduct.induction_on_tmul (R := ℤ) with
  | zero => rw [zero_op_smul', map_zero, zero_op_smul']
  | add x x' hx hx' => rw [add_op_smul', map_add, hx, hx', add_op_smul']
  | @tmul i j a ha b hb =>
    induction y using DG.tensor_induction_on with
    | zero => rw [op_smul_zero', map_zero, op_smul_zero']
    | add y y' hy hy' => rw [op_smul_add', map_add, hy, hy', map_add, op_smul_add']
    | @tmul p q m n =>
      rw [tmul_op_smul_tmul ha b (m : M) n.2, Units.smul_def, map_zsmul, tensorEquiv_tmul,
        tensorEquiv_tmul, he, hf, tmul_op_smul_tmul ha b (e m) (f.map_mem n.2), Units.smul_def]

end TensorEquiv

end ExternalTensor

end DG
