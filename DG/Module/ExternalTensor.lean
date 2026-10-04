import DG.Module.TensorProduct
import DG.Algebra.TensorProduct

/-!
# The external tensor product of dg modules

For dg rings `A`, `B` (regarded as dg `ℤ`-algebras), a left dg `A`-module `M` and a left dg
`B`-module `N`, the tensor product `M ⊗[ℤ] N` of dg abelian groups
(`d (m ⊗ n) = d m ⊗ n + (-1)^{|m|} m ⊗ d n`) is a dg module over the graded tensor product
`A ⊗ B = A ᵍ⊗[ℤ] B` (`DG.ExternalTensor.instDGModule`), with the Koszul sign rule

`(a ⊗ b) • (m ⊗ n) = (-1)^{|b| |m|} (a • m) ⊗ (b • n)`

(`DG.ExternalTensor.tmul_smul_tmul`). The action is the ring homomorphism
`DG.ExternalTensor.actionHom : A ⊗ B →+* End(M ⊗ N)`. Tensor products of `A`- and `B`-linear
maps of degree `0` are `A ⊗ B`-linear (`DG.ExternalTensor.tensorMap_smul`,
`DG.ExternalTensor.tensorLinearMap`); with `DG.tensorMap_mem` and `DG.tensorMap_d` they are maps
of dg modules.
-/

open scoped TensorProduct
open DirectSum

noncomputable section

namespace DG

namespace ExternalTensor

private theorem ks_eq {m n : ℤ} (h : Even (m - n)) : koszulSign m = koszulSign n :=
  (Int.negOnePow_eq_iff m n).mpr h

section Twist

variable (B : Type*) [AddCommGroup B] [DGAddCommGroup B]

/-- The Koszul twist `b ↦ (-1)^{|b| i} b` by an integer `i`. -/
def twist (i : ℤ) : B →+ B :=
  liftHomogeneous (grading (M := B)) fun k =>
    ((koszulSign (k * i) : ℤ) • (grading (M := B) k).subtype)

variable {B}

theorem twist_of_mem (i : ℤ) {k : ℤ} {b : B} (hb : b ∈ grading k) :
    twist B i b = koszulSign (k * i) • b := by
  rw [twist, liftHomogeneous_of_mem _ _ hb, Units.smul_def]
  rfl

end Twist

variable {A B : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B]
  {M : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module B N] [DGModule B N]

local notation "𝒜" => DGAlgebra.gradingSubmodule ℤ A
local notation "ℬ" => DGAlgebra.gradingSubmodule ℤ B

variable (M N) in
/-- The action of `a ⊗ b` on `M ⊗ N`, `m ⊗ n ↦ (-1)^{|b| |m|} (a • m) ⊗ (b • n)`. -/
def act (a : A) (b : B) : M ⊗[ℤ] N →+ M ⊗[ℤ] N :=
  tensorLiftHomogeneous fun i _ =>
    AddMonoidHom.mk' (fun m => AddMonoidHom.mk' (fun n => (a • (m : M)) ⊗ₜ (twist B i b • (n : N)))
      fun n n' => by simp [smul_add, TensorProduct.tmul_add])
      fun m m' => by ext n; simp [smul_add, TensorProduct.add_tmul]

omit [DGAddCommGroup A] [DGRing A] [DGRing B] [DGModule A M] [DGModule B N] in
theorem act_tmul (a : A) (b : B) {i j : ℤ} {m : M} (hm : m ∈ grading i) {n : N}
    (hn : n ∈ grading j) : act M N a b (m ⊗ₜ n) = (a • m) ⊗ₜ (twist B i b • n) :=
  tensorLiftHomogeneous_tmul _ hm hn

omit [DGAddCommGroup A] [DGRing A] [DGRing B] [DGModule A M] [DGModule B N] in
theorem act_tmul_of_mem (a : A) {k : ℤ} {b : B} (hb : b ∈ grading k) {i : ℤ} {m : M}
    (hm : m ∈ grading i) (n : N) :
    act M N a b (m ⊗ₜ n) = koszulSign (k * i) • ((a • m) ⊗ₜ (b • n)) := by
  induction n using DG.induction_on with
  | h_zero => simp
  | h_homogeneous n =>
    rw [act_tmul a b hm n.2, twist_of_mem i hb, Units.smul_def, Units.smul_def, smul_assoc,
      TensorProduct.tmul_smul]
  | h_add n n' hn hn' => rw [TensorProduct.tmul_add, map_add, hn, hn', smul_add,
      TensorProduct.tmul_add, smul_add]

variable (M N) in
/-- The action as a bi-additive map. -/
def actBilin : A →+ B →+ AddMonoid.End (M ⊗[ℤ] N) :=
  AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun b => act M N a b) fun b b' =>
      tensor_addHom_ext fun m n => by
        change act M N a (b + b') _ = act M N a b _ + act M N a b' _
        rw [act_tmul a _ m.2 n.2, act_tmul a _ m.2 n.2, act_tmul a _ m.2 n.2, map_add, add_smul,
          TensorProduct.tmul_add])
    fun a a' => by
      ext b : 1
      refine tensor_addHom_ext fun m n => ?_
      change act M N (a + a') b _ = act M N a b _ + act M N a' b _
      rw [act_tmul _ b m.2 n.2, act_tmul _ b m.2 n.2, act_tmul _ b m.2 n.2, add_smul,
        TensorProduct.add_tmul]

variable (M N) in
/-- The action of `A ⊗ B` on `M ⊗ N`, as an additive map to the endomorphisms. -/
def actionAdd : (𝒜 ᵍ⊗[ℤ] ℬ) →+ AddMonoid.End (M ⊗[ℤ] N) :=
  (TensorProduct.liftAddHom (actBilin M N) fun r a b => by
      rw [map_zsmul, AddMonoidHom.zsmul_apply, map_zsmul]).comp
    (_root_.GradedTensorProduct.of ℤ 𝒜 ℬ).symm.toLinearMap.toAddMonoidHom

omit [DGModule A M] [DGModule B N] in
theorem actionAdd_tmul (a : A) (b : B) :
    actionAdd M N (a ᵍ⊗ₜ[ℤ] b) = act M N a b := rfl

omit [DGModule B N] in
theorem tmul_mul_tmul_act {j i' j' : ℤ} (a : A) {b : B}
    (hb : b ∈ grading j) {a' : A} (ha' : a' ∈ grading i') {b' : B} (hb' : b' ∈ grading j')
    (x : M ⊗[ℤ] N) :
    actionAdd M N ((a ᵍ⊗ₜ[ℤ] b : 𝒜 ᵍ⊗[ℤ] ℬ) * (a' ᵍ⊗ₜ[ℤ] b')) x =
      act M N a b (act M N a' b' x) := by
  rw [GradedTensorProduct.tmul_mul_tmul 𝒜 ℬ a hb ha' b', Units.smul_def, map_zsmul,
    actionAdd_tmul]
  induction x using tensor_induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, ← hx, ← hy]
  | @tmul p q m n =>
    change ((koszulSign (j * i') : ℤ) • act M N (a * a') (b * b')) ((m : M) ⊗ₜ (n : N)) = _
    rw [AddMonoidHom.zsmul_apply, act_tmul_of_mem _ (mul_mem_grading hb hb') m.2,
      act_tmul_of_mem _ hb' m.2, map_units_zsmul,
      act_tmul_of_mem _ hb (smul_mem_grading ha' m.2), smul_smul, smul_smul, mul_smul, mul_smul,
      ← Units.smul_def, smul_smul, ← koszulSign_add, ← koszulSign_add]
    congr 1
    exact ks_eq ⟨0, by ring⟩

variable (M N) in
/-- The action of `A ⊗ B` on `M ⊗ N`, a ring homomorphism. -/
def actionHom : (𝒜 ᵍ⊗[ℤ] ℬ) →+* AddMonoid.End (M ⊗[ℤ] N) where
  __ := actionAdd M N
  map_one' := by
    show actionAdd M N 1 = (1 : AddMonoid.End (M ⊗[ℤ] N))
    refine AddMonoidHom.ext fun x => ?_
    show act M N 1 1 x = x
    induction x using tensor_induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, hx, hy]
    | tmul m n =>
      rw [act_tmul_of_mem _ (one_mem_grading (A := B)) m.2, zero_mul, koszulSign_zero, one_smul,
        one_smul, one_smul]
  map_mul' x y := by
    show actionAdd M N (x * y) = actionAdd M N x * actionAdd M N y
    induction x using GradedTensorProduct.induction_on_tmul (R := ℤ) with
    | zero => rw [zero_mul, map_zero, zero_mul]
    | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]
    | @tmul i j a ha b hb =>
      induction y using GradedTensorProduct.induction_on_tmul (R := ℤ) with
      | zero => rw [mul_zero, map_zero, mul_zero]
      | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
      | @tmul i' j' a' ha' b' hb' =>
        ext x
        exact tmul_mul_tmul_act a hb ha' hb' x

instance instModule : Module (𝒜 ᵍ⊗[ℤ] ℬ) (M ⊗[ℤ] N) :=
  Module.compHom (M ⊗[ℤ] N) (actionHom M N)

omit [DGModule B N] in
theorem smul_def (x : 𝒜 ᵍ⊗[ℤ] ℬ) (y : M ⊗[ℤ] N) : x • y = actionHom M N x y := rfl

omit [DGModule B N] in
/-- **The Koszul sign rule** `(a ⊗ b) • (m ⊗ n) = (-1)^{|b| |m|} (a • m) ⊗ (b • n)`. -/
theorem tmul_smul_tmul (a : A) {k : ℤ} {b : B} (hb : b ∈ grading k) {i : ℤ} {m : M}
    (hm : m ∈ grading i) (n : N) :
    (a ᵍ⊗ₜ[ℤ] b : 𝒜 ᵍ⊗[ℤ] ℬ) • (m ⊗ₜ[ℤ] n) = koszulSign (k * i) • ((a • m) ⊗ₜ (b • n)) :=
  act_tmul_of_mem a hb hm n

omit [DGRing A] [DGRing B] in
theorem act_mem {i j : ℤ} {a : A} (ha : a ∈ grading i) {b : B} (hb : b ∈ grading j) {q : ℤ}
    {y : M ⊗[ℤ] N} (hy : y ∈ grading q) : act M N a b y ∈ grading (q + (i + j)) := by
  refine map_mem_grading_of_tmul (act M N a b) (i + j) (fun {i' j' m n} hm hn => ?_) hy
  rw [act_tmul_of_mem a hb hm n, Units.smul_def]
  refine zsmul_mem ?_ _
  have := tmul_mem_grading (smul_mem_grading ha hm) (smul_mem_grading hb hn)
  rwa [show i + i' + (j + j') = i' + j' + (i + j) by ring] at this

private theorem ks_val (n : ℤ) : (koszulSign n : ℤ) = if Even n then 1 else -1 := by
  split_ifs with h
  · rw [koszulSign, Int.negOnePow_even n h]; rfl
  · rw [koszulSign, Int.negOnePow_odd n (Int.not_even_iff_odd.mp h)]; rfl

omit [DGModule B N] in
theorem smul_units_smul (x : 𝒜 ᵍ⊗[ℤ] ℬ) (u : ℤˣ) (y : M ⊗[ℤ] N) : x • (u • y) = u • (x • y) := by
  rw [smul_def, smul_def]
  exact map_units_zsmul (actionHom M N x : M ⊗[ℤ] N →+ M ⊗[ℤ] N) u y

omit [DGModule B N] in
theorem units_smul_smul (u : ℤˣ) (x : 𝒜 ᵍ⊗[ℤ] ℬ) (y : M ⊗[ℤ] N) : (u • x) • y = u • (x • y) := by
  rw [smul_def, smul_def, Units.smul_def, map_zsmul, Units.smul_def]
  rfl

theorem d_tmul_smul_tmul {i j k : ℤ} {a : A} (ha : a ∈ grading i) {b : B} (hb : b ∈ grading j)
    {m : M} (hm : m ∈ grading k) (n : N) :
    d ((a ᵍ⊗ₜ[ℤ] b : 𝒜 ᵍ⊗[ℤ] ℬ) • (m ⊗ₜ[ℤ] n)) =
      d (a ᵍ⊗ₜ[ℤ] b : 𝒜 ᵍ⊗[ℤ] ℬ) • (m ⊗ₜ[ℤ] n) +
        koszulSign (i + j) • ((a ᵍ⊗ₜ[ℤ] b : 𝒜 ᵍ⊗[ℤ] ℬ) • d (m ⊗ₜ[ℤ] n)) := by
  rw [tmul_smul_tmul a hb hm n, d_units_smul, d_tmul_of_mem (smul_mem_grading ha hm),
    d_smul ha m, d_smul hb n, GradedTensorProduct.d_tmul ha b, add_smul, d_tmul_of_mem hm n,
    units_smul_smul, smul_add (a ᵍ⊗ₜ[ℤ] b : 𝒜 ᵍ⊗[ℤ] ℬ), smul_units_smul,
    tmul_smul_tmul (d a) hb hm n,
    tmul_smul_tmul a (d_mem hb) hm n, tmul_smul_tmul a hb (d_mem hm) n,
    tmul_smul_tmul a hb hm (d n)]
  simp only [Units.smul_def, TensorProduct.add_tmul, TensorProduct.tmul_add,
    TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add, smul_smul, ks_val]
  by_cases hi : Even i <;> by_cases hj : Even j <;> by_cases hk : Even k <;>
    simp [Int.even_add, Int.even_mul, ← Int.not_even_iff_odd, hi, hj, hk] <;> abel

omit [DGModule B N] in
theorem zero_smul' (y : M ⊗[ℤ] N) : (0 : 𝒜 ᵍ⊗[ℤ] ℬ) • y = 0 := by
  rw [smul_def, map_zero]; rfl

omit [DGModule B N] in
theorem smul_zero' (x : 𝒜 ᵍ⊗[ℤ] ℬ) : x • (0 : M ⊗[ℤ] N) = 0 := by
  rw [smul_def, map_zero]

omit [DGModule B N] in
theorem add_smul' (x x' : 𝒜 ᵍ⊗[ℤ] ℬ) (y : M ⊗[ℤ] N) : (x + x') • y = x • y + x' • y := by
  rw [smul_def, smul_def, smul_def, map_add]; rfl

omit [DGModule B N] in
theorem smul_add' (x : 𝒜 ᵍ⊗[ℤ] ℬ) (y y' : M ⊗[ℤ] N) : x • (y + y') = x • y + x • y' := by
  rw [smul_def, smul_def, smul_def, map_add]

theorem smul_mem_grading' {p q : ℤ} {x : 𝒜 ᵍ⊗[ℤ] ℬ} (hx : x ∈ grading p) {y : M ⊗[ℤ] N}
    (hy : y ∈ grading q) : x • y ∈ grading (p + q) := by
  refine GradedTensorProduct.grading_induction 𝒜 ℬ hx
    (motive := fun x => x • y ∈ grading (p + q)) ?_ ?_ ?_
  · rw [zero_smul']; exact zero_mem _
  · intro i j a b hij
    have := act_mem a.2 b.2 hy
    rw [show q + (i + j) = p + q by omega] at this
    exact this
  · intro x x' hx hx'
    rw [add_smul']
    exact add_mem hx hx'

theorem d_smul_tmul {i j : ℤ} {a : A} (ha : a ∈ grading i) {b : B} (hb : b ∈ grading j)
    (y : M ⊗[ℤ] N) :
    d ((a ᵍ⊗ₜ[ℤ] b : 𝒜 ᵍ⊗[ℤ] ℬ) • y) =
      d (a ᵍ⊗ₜ[ℤ] b : 𝒜 ᵍ⊗[ℤ] ℬ) • y + koszulSign (i + j) • ((a ᵍ⊗ₜ[ℤ] b : 𝒜 ᵍ⊗[ℤ] ℬ) • d y) := by
  induction y using tensor_induction_on with
  | zero => simp only [d_zero, smul_zero, add_zero]
  | add y y' hy hy' =>
    simp only [d_add, hy, hy', smul_add]
    abel
  | tmul m n =>
    obtain ⟨m, hm⟩ := m
    obtain ⟨n, -⟩ := n
    exact d_tmul_smul_tmul ha hb hm n

theorem d_smul_of_mem {p : ℤ} {x : 𝒜 ᵍ⊗[ℤ] ℬ} (hx : x ∈ grading p) (y : M ⊗[ℤ] N) :
    d (x • y) = d x • y + koszulSign p • (x • d y) := by
  refine GradedTensorProduct.grading_induction 𝒜 ℬ hx
    (motive := fun x => d (x • y) = d x • y + koszulSign p • (x • d y)) ?_ ?_ ?_
  · rw [zero_smul', d_zero, d_zero, zero_smul', zero_smul', smul_zero, add_zero]
  · intro i j a b hij
    subst hij
    exact d_smul_tmul a.2 b.2 y
  · intro x x' hx hx'
    rw [add_smul', d_add, hx, hx', d_add, add_smul', add_smul', smul_add]
    abel

/-- **`M ⊗ N` is a dg module over `A ⊗ B`.** -/
instance instDGModule : DGModule (𝒜 ᵍ⊗[ℤ] ℬ) (M ⊗[ℤ] N) where
  smul_mem _ _ _ _ hx hy := smul_mem_grading' hx hy
  d_smul' hx y := d_smul_of_mem hx y

variable {M' : Type*} [AddCommGroup M'] [DGAddCommGroup M'] [Module A M'] [DGModule A M']
  {N' : Type*} [AddCommGroup N'] [DGAddCommGroup N'] [Module B N'] [DGModule B N']

omit [DGModule B N] [DGModule B N'] in
/-- **Functoriality**: the tensor product of an `A`-linear and a `B`-linear map of degree `0` is
`A ⊗ B`-linear. -/
theorem tensorMap_smul (f : M →+ M') (g : N →+ N') (hf : ∀ (a : A) m, f (a • m) = a • f m)
    (hg : ∀ (b : B) n, g (b • n) = b • g n)
    (hfm : ∀ {k : ℤ} {m : M}, m ∈ grading k → f m ∈ grading k)
    (x : 𝒜 ᵍ⊗[ℤ] ℬ) (y : M ⊗[ℤ] N) : tensorMap f g (x • y) = x • tensorMap f g y := by
  induction x using GradedTensorProduct.induction_on_tmul (R := ℤ) with
  | zero => rw [zero_smul', zero_smul', map_zero]
  | add x x' hx hx' => rw [add_smul', map_add, hx, hx', add_smul']
  | @tmul i j a ha b hb =>
    induction y using tensor_induction_on with
    | zero => rw [smul_zero', map_zero, smul_zero']
    | add y y' hy hy' => rw [smul_add', map_add, hy, hy', map_add, smul_add']
    | tmul m n =>
      rw [tmul_smul_tmul a hb m.2 (n : N), tensorMap_tmul, tmul_smul_tmul a hb (hfm m.2) (g n),
        map_units_zsmul, tensorMap_tmul, hf, hg]

/-- The tensor product of linear maps, as an `A ⊗ B`-linear map. -/
def tensorLinearMap (f : M →ₗ[A] M') (g : N →ₗ[B] N')
    (hfm : ∀ {k : ℤ} {m : M}, m ∈ grading k → f m ∈ grading k) :
    (M ⊗[ℤ] N) →ₗ[𝒜 ᵍ⊗[ℤ] ℬ] (M' ⊗[ℤ] N') where
  toFun := tensorMap f.toAddMonoidHom g.toAddMonoidHom
  map_add' := map_add _
  map_smul' x y := tensorMap_smul _ _ (fun a m => f.map_smul a m) (fun b n => g.map_smul b n)
    hfm x y

end ExternalTensor

end DG
