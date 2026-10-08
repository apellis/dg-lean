import DG.Module.ExternalBimodule
import DG.Module.TensorProductOver
import DG.Module.Equiv

/-!
# The interchange isomorphism for external tensor products

For dg rings `A'`, `B'`, a right dg `A'`-module `M`, a right dg `B'`-module `N`, a left dg
`A'`-module `P` and a left dg `B'`-module `Q`, the tensor product over `A' ⊗ B'` of the external
tensor products `M ⊗ N` (a right `A' ⊗ B'`-module, `DG.ExternalTensor.instModuleOp`) and `P ⊗ Q`
is the external tensor product of `M ⊗_{A'} P` and `N ⊗_{B'} Q`:

`(M ⊗ N) ⊗_{A' ⊗ B'} (P ⊗ Q) ≅ (M ⊗_{A'} P) ⊗ (N ⊗_{B'} Q)`,
`(m ⊗ n) ⊗ (p ⊗ q) ↦ (-1)^{|n| |p|} (m ⊗ p) ⊗ (n ⊗ q)`

(`DG.ExternalTensor.interchange`, `DG.ExternalTensor.interchange_tmul`), an isomorphism of dg
abelian groups, and of dg `A ⊗ B`-modules when `M` is a dg `(A, A')`-bimodule and `N` a dg
`(B, B')`-bimodule (`DG.ExternalTensor.interchangeEquiv`).
-/

open scoped TensorProduct
open DirectSum MulOpposite

noncomputable section

set_option linter.unusedSectionVars false

namespace DG

namespace ExternalTensor

open TensorProductOver

section Interchange

variable {A' B' : Type*} [Ring A'] [DGAddCommGroup A'] [DGRing A'] [Ring B'] [DGAddCommGroup B']
  [DGRing B']
  {M : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A'ᵐᵒᵖ M] [DGRightModule A' M]
  {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module B'ᵐᵒᵖ N] [DGRightModule B' N]
  {P : Type*} [AddCommGroup P] [DGAddCommGroup P] [Module A' P] [DGModule A' P]
  {Q : Type*} [AddCommGroup Q] [DGAddCommGroup Q] [Module B' Q] [DGModule B' Q]

local notation "𝒜'" => DGAlgebra.gradingSubmodule ℤ A'
local notation "ℬ'" => DGAlgebra.gradingSubmodule ℤ B'
local notation "X" => TensorProductOver A' M P ⊗[ℤ] TensorProductOver B' N Q
local notation "T" => TensorProductOver (𝒜' ᵍ⊗[ℤ] ℬ') (M ⊗[ℤ] N) (P ⊗[ℤ] Q)

private theorem ks_eq'' {m n : ℤ} (h : Even (m - n)) : koszulSign m = koszulSign n :=
  (Int.negOnePow_eq_iff m n).mpr h

/-! ### The forward map -/

variable (P Q) in
/-- For fixed `m`, `n` and a degree `j` (that of `n`), `p ⊗ q ↦ (m ⊗ ε_j(p)) ⊗ (n ⊗ q)`, where
`ε_j(p) = (-1)^{j |p|} p`. -/
def ichInner (m : M) (n : N) (j : ℤ) : P ⊗[ℤ] Q →+ X :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun p => AddMonoidHom.mk'
      (fun q => TensorProductOver.tmul A' m (twist P j p) ⊗ₜ[ℤ] TensorProductOver.tmul B' n q)
      fun q q' => by rw [tmul_add, TensorProduct.tmul_add])
      fun p p' => by
        ext q
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, tmul_add,
          TensorProduct.add_tmul])
    fun r p q => by
      change TensorProductOver.tmul A' m (twist P j (r • p)) ⊗ₜ[ℤ] TensorProductOver.tmul B' n q =
        TensorProductOver.tmul A' m (twist P j p) ⊗ₜ[ℤ] TensorProductOver.tmul B' n (r • q)
      rw [map_zsmul, TensorProductOver.tmul_zsmul, TensorProductOver.tmul_zsmul,
        TensorProduct.smul_tmul]

theorem ichInner_tmul (m : M) (n : N) (j : ℤ) (p : P) (q : Q) :
    ichInner P Q m n j (p ⊗ₜ q) = TensorProductOver.tmul A' m (twist P j p) ⊗ₜ[ℤ] TensorProductOver.tmul B' n q := rfl

variable (A' B' M N P Q) in
/-- The bi-additive map `(m ⊗ n, p ⊗ q) ↦ (-1)^{|n| |p|} (m ⊗ p) ⊗ (n ⊗ q)`. -/
def ichAux : M ⊗[ℤ] N →+ P ⊗[ℤ] Q →+ X :=
  tensorLiftHomogeneous (M := M) (N := N) fun _ j =>
    AddMonoidHom.mk' (fun m => AddMonoidHom.mk' (fun n => ichInner P Q (m : M) (n : N) j)
      fun n n' => tensor_addHom_ext fun p q => by
        simp only [AddMonoidHom.add_apply, ichInner_tmul, AddMemClass.coe_add,
          TensorProductOver.add_tmul, TensorProduct.tmul_add])
      fun m m' => by
        ext n : 1
        refine tensor_addHom_ext fun p q => ?_
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, ichInner_tmul,
          AddMemClass.coe_add, TensorProductOver.add_tmul, TensorProduct.add_tmul]

theorem ichAux_tmul_tmul {i j k : ℤ} {m : M} (hm : m ∈ grading i) {n : N} (hn : n ∈ grading j)
    {p : P} (hp : p ∈ grading k) (q : Q) :
    ichAux A' B' M N P Q (m ⊗ₜ n) (p ⊗ₜ q) = koszulSign (k * j) • (TensorProductOver.tmul A' m p ⊗ₜ[ℤ] TensorProductOver.tmul B' n q) := by
  rw [ichAux, tensorLiftHomogeneous_tmul _ hm hn]
  change ichInner P Q m n j (p ⊗ₜ q) = _
  rw [ichInner_tmul, twist_of_mem j hp, tmul_units_smul, Units.smul_def, Units.smul_def,
    TensorProduct.smul_tmul']

theorem ichAux_balanced (x : 𝒜' ᵍ⊗[ℤ] ℬ') (y : M ⊗[ℤ] N) (z : P ⊗[ℤ] Q) :
    ichAux A' B' M N P Q (op x • y) z = ichAux A' B' M N P Q y (x • z) := by
  induction x using GradedTensorProduct.induction_on_tmul (R := ℤ) with
  | zero => rw [zero_op_smul', zero_smul' (A := A') (B := B'), map_zero, map_zero, AddMonoidHom.zero_apply]
  | add x x' hx hx' => rw [add_op_smul', map_add, AddMonoidHom.add_apply, hx, hx', add_smul' (A := A') (B := B'),
      map_add]
  | @tmul i' j' a ha b hb =>
    induction y using tensor_induction_on with
    | zero => simp only [op_smul_zero', map_zero, AddMonoidHom.zero_apply]
    | add y y' hy hy' => rw [op_smul_add', map_add, map_add, AddMonoidHom.add_apply,
        AddMonoidHom.add_apply, hy, hy']
    | @tmul i j m n =>
      induction z using tensor_induction_on with
      | zero => rw [map_zero, smul_zero' (A := A') (B := B'), map_zero]
      | add z z' hz hz' => rw [map_add, hz, hz', smul_add' (A := A') (B := B'), map_add]
      | @tmul k l p q =>
        have h1 := tmul_op_smul_tmul ha b (m : M) n.2
        have h2 := ExternalTensor.tmul_smul_tmul (M := P) (N := Q) a hb p.2 (q : Q)
        rw [h1, h2, Units.smul_def, Units.smul_def, map_zsmul, AddMonoidHom.zsmul_apply, map_zsmul,
          ichAux_tmul_tmul (op_smul_mem_grading ha m.2) (op_smul_mem_grading hb n.2) p.2,
          ichAux_tmul_tmul m.2 n.2 (smul_mem_grading ha p.2), TensorProductOver.op_smul_tmul,
          TensorProductOver.op_smul_tmul, Units.smul_def, Units.smul_def, smul_smul, smul_smul,
          ← Units.val_mul, ← Units.val_mul, ← koszulSign_add, ← koszulSign_add]
        rw [ks_eq'' (m := i' * j + k * (j + j')) (n := j' * k + (i' + k) * j) ⟨0, by ring⟩]

variable (A' B' M N P Q) in
/-- **The interchange map** `(M ⊗ N) ⊗_{A' ⊗ B'} (P ⊗ Q) → (M ⊗_{A'} P) ⊗ (N ⊗_{B'} Q)`,
`(m ⊗ n) ⊗ (p ⊗ q) ↦ (-1)^{|n| |p|} (m ⊗ p) ⊗ (n ⊗ q)`. -/
def interchange : T →+ X :=
  TensorProductOver.lift (ichAux A' B' M N P Q) fun x y z => ichAux_balanced x y z

theorem interchange_tmul {i j k : ℤ} {m : M} (hm : m ∈ grading i) {n : N} (hn : n ∈ grading j)
    {p : P} (hp : p ∈ grading k) (q : Q) :
    interchange A' B' M N P Q (tmul _ (m ⊗ₜ n) (p ⊗ₜ q)) =
      koszulSign (k * j) • (TensorProductOver.tmul A' m p ⊗ₜ[ℤ] TensorProductOver.tmul B' n q) :=
  ichAux_tmul_tmul hm hn hp q

/-! ### The inverse map -/

theorem tmul_op_smul_left_eq {i j : ℤ} {a : A'} (ha : a ∈ grading i) (m : M) {n : N}
    (hn : n ∈ grading j) :
    (op a • m) ⊗ₜ[ℤ] n =
      koszulSign (i * j) • (op (a ᵍ⊗ₜ[ℤ] (1 : B') : 𝒜' ᵍ⊗[ℤ] ℬ') • (m ⊗ₜ[ℤ] n)) := by
  rw [tmul_op_smul_tmul ha 1 m hn, op_one, one_smul, smul_smul, Int.units_mul_self, one_smul]

theorem units_smul_tmul' (u : ℤˣ) (p : P) (q : Q) : (u • p) ⊗ₜ[ℤ] q = u • (p ⊗ₜ[ℤ] q) := by
  rw [Units.smul_def, Units.smul_def, TensorProduct.smul_tmul']

theorem ichInvInner_balanced {j : ℤ} (n : grading (M := N) j) (q : Q) (a : A') (m : M) (p : P) :
    TensorProductOver.tmul (𝒜' ᵍ⊗[ℤ] ℬ') ((op a • m) ⊗ₜ[ℤ] (n : N)) (twist P j p ⊗ₜ[ℤ] q) =
      TensorProductOver.tmul (𝒜' ᵍ⊗[ℤ] ℬ') (m ⊗ₜ[ℤ] (n : N)) (twist P j (a • p) ⊗ₜ[ℤ] q) := by
  induction a using DG.induction_on with
  | h_zero => simp
  | h_add a a' ha ha' =>
    rw [op_add, add_smul, TensorProduct.add_tmul, TensorProductOver.add_tmul, ha, ha', add_smul,
      map_add, TensorProduct.add_tmul, TensorProductOver.tmul_add]
  | @h_homogeneous i a =>
    induction p using DG.induction_on with
    | h_zero => simp
    | h_add p p' hp hp' =>
      rw [map_add, TensorProduct.add_tmul, TensorProductOver.tmul_add, hp, hp', smul_add, map_add,
        TensorProduct.add_tmul, TensorProductOver.tmul_add]
    | @h_homogeneous k p =>
      rw [twist_of_mem j p.2, twist_of_mem j (smul_mem_grading a.2 p.2), units_smul_tmul',
        units_smul_tmul', TensorProductOver.tmul_units_smul, TensorProductOver.tmul_units_smul,
        tmul_op_smul_left_eq (B' := B') a.2 m n.2, TensorProductOver.units_smul_tmul,
        TensorProductOver.op_smul_tmul,
        ExternalTensor.tmul_smul_tmul (M := P) (N := Q) (a : A') (one_mem_grading (A := B')) p.2 q]
      simp only [zero_mul, koszulSign_zero, one_smul]
      rw [smul_smul, ← koszulSign_add,
        ks_eq'' (m := k * j + i * j) (n := (i + k) * j) ⟨0, by ring⟩]

variable (A' B' M N P Q) in
/-- For `n` of degree `j` and `q`, the map `m ⊗ p ↦ (m ⊗ n) ⊗ (ε_j(p) ⊗ q)` out of `M ⊗_{A'} P`. -/
def ichInvInner {j : ℤ} (n : grading (M := N) j) (q : Q) : TensorProductOver A' M P →+ T :=
  TensorProductOver.lift
    (AddMonoidHom.mk' (fun m => AddMonoidHom.mk'
      (fun p => TensorProductOver.tmul (𝒜' ᵍ⊗[ℤ] ℬ') (m ⊗ₜ[ℤ] (n : N)) (twist P j p ⊗ₜ[ℤ] q))
      fun p p' => by rw [map_add, TensorProduct.add_tmul, TensorProductOver.tmul_add])
      fun m m' => by
        ext p
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, TensorProduct.add_tmul,
          TensorProductOver.add_tmul])
    fun a m p => ichInvInner_balanced n q a m p

theorem ichInvInner_tmul {j : ℤ} (n : grading (M := N) j) (q : Q) (m : M) (p : P) :
    ichInvInner A' B' M N P Q n q (TensorProductOver.tmul A' m p) =
      TensorProductOver.tmul (𝒜' ᵍ⊗[ℤ] ℬ') (m ⊗ₜ[ℤ] (n : N)) (twist P j p ⊗ₜ[ℤ] q) := rfl

variable (A' B' M N P Q) in
/-- The map `n ↦ q ↦ (u ↦ …)` on homogeneous `n`, extended additively. -/
def ichInvN : N →+ Q →+ (TensorProductOver A' M P →+ T) :=
  liftHomogeneous (grading (M := N)) fun _ =>
    AddMonoidHom.mk' (fun n => AddMonoidHom.mk' (fun q => ichInvInner A' B' M N P Q n q)
      fun q q' => TensorProductOver.addHom_ext fun m p => by
        simp only [AddMonoidHom.add_apply, ichInvInner_tmul, TensorProduct.tmul_add,
          TensorProductOver.tmul_add])
      fun n n' => by
        ext q : 1
        refine TensorProductOver.addHom_ext fun m p => ?_
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, ichInvInner_tmul,
          AddMemClass.coe_add, TensorProduct.tmul_add, TensorProductOver.add_tmul]

theorem ichInvN_tmul {j k : ℤ} {n : N} (hn : n ∈ grading j) (q : Q) (m : M) {p : P}
    (hp : p ∈ grading k) :
    ichInvN A' B' M N P Q n q (TensorProductOver.tmul A' m p) =
      koszulSign (k * j) • TensorProductOver.tmul (𝒜' ᵍ⊗[ℤ] ℬ') (m ⊗ₜ[ℤ] n) (p ⊗ₜ[ℤ] q) := by
  rw [ichInvN, liftHomogeneous_of_mem _ _ hn]
  change ichInvInner A' B' M N P Q ⟨n, hn⟩ q (TensorProductOver.tmul A' m p) = _
  rw [ichInvInner_tmul, twist_of_mem j hp, units_smul_tmul', TensorProductOver.tmul_units_smul]

theorem ichInvN_balanced (b : B') (n : N) (q : Q) :
    ichInvN A' B' M N P Q (op b • n) q = ichInvN A' B' M N P Q n (b • q) := by
  refine TensorProductOver.addHom_ext fun m p => ?_
  induction b using DG.induction_on with
  | h_zero => simp
  | h_add b b' hb hb' => rw [op_add, add_smul, map_add, AddMonoidHom.add_apply,
      AddMonoidHom.add_apply, hb, hb', add_smul, map_add, AddMonoidHom.add_apply]
  | @h_homogeneous l b =>
    induction n using DG.induction_on with
    | h_zero => simp
    | h_add n n' hn hn' => rw [smul_add, map_add, AddMonoidHom.add_apply, AddMonoidHom.add_apply,
        hn, hn', map_add, AddMonoidHom.add_apply, AddMonoidHom.add_apply]
    | @h_homogeneous j n =>
      induction p using DG.induction_on with
      | h_zero => simp
      | h_add p p' hp hp' => rw [TensorProductOver.tmul_add, map_add, hp, hp', map_add]
      | @h_homogeneous k p =>
        have e : m ⊗ₜ[ℤ] (op (b : B') • (n : N)) =
            op ((1 : A') ᵍ⊗ₜ[ℤ] (b : B') : 𝒜' ᵍ⊗[ℤ] ℬ') • (m ⊗ₜ[ℤ] (n : N)) := by
          rw [tmul_op_smul_tmul (one_mem_grading (A := A')) (b : B') m n.2, op_one, one_smul,
            zero_mul, koszulSign_zero, one_smul]
        rw [ichInvN_tmul (op_smul_mem_grading b.2 n.2) q m p.2, ichInvN_tmul n.2 _ m p.2, e,
          TensorProductOver.op_smul_tmul,
          ExternalTensor.tmul_smul_tmul (M := P) (N := Q) (1 : A') b.2 p.2 q, one_smul,
          TensorProductOver.tmul_units_smul, smul_smul, ← koszulSign_add,
          ks_eq'' (m := k * (j + l) + l * k) (n := k * j) ⟨k * l, by ring⟩]

variable (A' B' M N P Q) in
/-- `N ⊗_{B'} Q →+ (M ⊗_{A'} P →+ T)`. -/
def ichInvB : TensorProductOver B' N Q →+ (TensorProductOver A' M P →+ T) :=
  TensorProductOver.lift (ichInvN A' B' M N P Q) fun b n q => ichInvN_balanced b n q

variable (A' B' M N P Q) in
/-- **The inverse interchange map** `(m ⊗ p) ⊗ (n ⊗ q) ↦ (-1)^{|n| |p|} (m ⊗ n) ⊗ (p ⊗ q)`. -/
def interchangeInv : X →+ T :=
  TensorProduct.liftAddHom (ichInvB A' B' M N P Q).flip fun r u v => by
    simp only [AddMonoidHom.flip_apply, map_zsmul, AddMonoidHom.zsmul_apply]

theorem interchangeInv_tmul {j k : ℤ} (m : M) {p : P} (hp : p ∈ grading k) {n : N}
    (hn : n ∈ grading j) (q : Q) :
    interchangeInv A' B' M N P Q (TensorProductOver.tmul A' m p ⊗ₜ[ℤ] TensorProductOver.tmul B' n q) =
      koszulSign (k * j) • TensorProductOver.tmul (𝒜' ᵍ⊗[ℤ] ℬ') (m ⊗ₜ[ℤ] n) (p ⊗ₜ[ℤ] q) :=
  ichInvN_tmul hn q m hp

/-! ### Extensionality on generators -/

theorem T_addHom_ext {Y : Type*} [AddCommGroup Y] {f g : T →+ Y}
    (h : ∀ {a b c e : ℤ} (m : grading (M := M) a) (n : grading (M := N) b)
      (p : grading (M := P) c) (q : grading (M := Q) e),
      f (TensorProductOver.tmul (𝒜' ᵍ⊗[ℤ] ℬ') ((m : M) ⊗ₜ[ℤ] (n : N)) ((p : P) ⊗ₜ[ℤ] (q : Q))) =
        g (TensorProductOver.tmul (𝒜' ᵍ⊗[ℤ] ℬ') ((m : M) ⊗ₜ[ℤ] (n : N)) ((p : P) ⊗ₜ[ℤ] (q : Q)))) :
    f = g := by
  refine TensorProductOver.addHom_ext fun y z => ?_
  induction y using tensor_induction_on with
  | zero => rw [TensorProductOver.zero_tmul, map_zero, map_zero]
  | add y y' hy hy' => rw [TensorProductOver.add_tmul, map_add, map_add, hy, hy']
  | tmul m n =>
    induction z using tensor_induction_on with
    | zero => rw [TensorProductOver.tmul_zero, map_zero, map_zero]
    | add z z' hz hz' => rw [TensorProductOver.tmul_add, map_add, map_add, hz, hz']
    | tmul p q => exact h m n p q

theorem X_addHom_ext {Y : Type*} [AddCommGroup Y] {f g : X →+ Y}
    (h : ∀ {a b c e : ℤ} (m : grading (M := M) a) (n : grading (M := N) b)
      (p : grading (M := P) c) (q : grading (M := Q) e),
      f (TensorProductOver.tmul A' (m : M) (p : P) ⊗ₜ[ℤ] TensorProductOver.tmul B' (n : N) (q : Q)) =
        g (TensorProductOver.tmul A' (m : M) (p : P) ⊗ₜ[ℤ] TensorProductOver.tmul B' (n : N) (q : Q))) :
    f = g := by
  refine AddMonoidHom.ext fun x => ?_
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => rw [map_add, map_add, hx, hx']
  | tmul u v =>
    induction u using TensorProductOver.induction_on with
    | zero => rw [TensorProduct.zero_tmul, map_zero, map_zero]
    | add u u' hu hu' => rw [TensorProduct.add_tmul, map_add, map_add, hu, hu']
    | tmul m p =>
      induction v using TensorProductOver.induction_on with
      | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
      | add v v' hv hv' => rw [TensorProduct.tmul_add, map_add, map_add, hv, hv']
      | tmul n q =>
        induction m using DG.induction_on with
        | h_zero => rw [TensorProductOver.zero_tmul, TensorProduct.zero_tmul, map_zero, map_zero]
        | h_add m m' hm hm' => rw [TensorProductOver.add_tmul, TensorProduct.add_tmul, map_add,
            map_add, hm, hm']
        | h_homogeneous m =>
          induction p using DG.induction_on with
          | h_zero => rw [TensorProductOver.tmul_zero, TensorProduct.zero_tmul, map_zero, map_zero]
          | h_add p p' hp hp' => rw [TensorProductOver.tmul_add, TensorProduct.add_tmul, map_add,
              map_add, hp, hp']
          | h_homogeneous p =>
            induction n using DG.induction_on with
            | h_zero => rw [TensorProductOver.zero_tmul, TensorProduct.tmul_zero, map_zero,
                map_zero]
            | h_add n n' hn hn' => rw [TensorProductOver.add_tmul, TensorProduct.tmul_add, map_add,
                map_add, hn, hn']
            | h_homogeneous n =>
              induction q using DG.induction_on with
              | h_zero => rw [TensorProductOver.tmul_zero, TensorProduct.tmul_zero, map_zero,
                  map_zero]
              | h_add q q' hq hq' => rw [TensorProductOver.tmul_add, TensorProduct.tmul_add,
                  map_add, map_add, hq, hq']
              | h_homogeneous q => exact h m n p q

/-! ### The two maps are mutually inverse -/

theorem interchangeInv_interchange (t : T) :
    interchangeInv A' B' M N P Q (interchange A' B' M N P Q t) = t := by
  have := T_addHom_ext (f := (interchangeInv A' B' M N P Q).comp (interchange A' B' M N P Q))
    (g := AddMonoidHom.id T) fun m n p q => by
      rw [AddMonoidHom.comp_apply, interchange_tmul m.2 n.2 p.2, map_units_zsmul,
        interchangeInv_tmul _ p.2 n.2, smul_smul, Int.units_mul_self, one_smul,
        AddMonoidHom.id_apply]
  exact DFunLike.congr_fun this t

theorem interchange_interchangeInv (x : X) :
    interchange A' B' M N P Q (interchangeInv A' B' M N P Q x) = x := by
  have := X_addHom_ext (f := (interchange A' B' M N P Q).comp (interchangeInv A' B' M N P Q))
    (g := AddMonoidHom.id X) fun m n p q => by
      rw [AddMonoidHom.comp_apply, interchangeInv_tmul _ p.2 n.2, map_units_zsmul,
        interchange_tmul m.2 n.2 p.2, smul_smul, Int.units_mul_self, one_smul,
        AddMonoidHom.id_apply]
  exact DFunLike.congr_fun this x

/-! ### Grading and differential -/

theorem interchange_mem {k : ℤ} {t : T} (ht : t ∈ grading k) :
    interchange A' B' M N P Q t ∈ grading k := by
  refine TensorProductOver.induction_on_mem_grading
    (P := fun t => interchange A' B' M N P Q t ∈ grading k) ?_ ?_ ?_ ?_ ht
  · rw [map_zero]; exact zero_mem _
  · intro i j y z hy hz hij
    change y ∈ tensorGrading M N i at hy
    change z ∈ tensorGrading P Q j at hz
    induction hy using AddSubgroup.closure_induction with
    | mem y hy' =>
      obtain ⟨a, b, rfl, m, hm, n, hn, rfl⟩ := hy'
      induction hz using AddSubgroup.closure_induction with
      | mem z hz' =>
        obtain ⟨c, e, rfl, p, hp, q, hq, rfl⟩ := hz'
        rw [interchange_tmul hm hn hp, Units.smul_def]
        refine zsmul_mem ?_ _
        have := tmul_mem_grading (TensorProductOver.tmul_mem_grading (A := A') hm hp)
          (TensorProductOver.tmul_mem_grading (A := B') hn hq)
        rwa [show a + c + (b + e) = k by omega] at this
      | zero => rw [TensorProductOver.tmul_zero, map_zero]; exact zero_mem _
      | add z z' _ _ h h' => rw [TensorProductOver.tmul_add, map_add]; exact add_mem h h'
      | neg z _ h => rw [TensorProductOver.tmul_neg, map_neg]; exact neg_mem h
    | zero => rw [TensorProductOver.zero_tmul, map_zero]; exact zero_mem _
    | add y y' _ _ h h' => rw [TensorProductOver.add_tmul, map_add]; exact add_mem h h'
    | neg y _ h => rw [TensorProductOver.neg_tmul, map_neg]; exact neg_mem h
  · intro x y hx hy; rw [map_add]; exact add_mem hx hy
  · intro x hx; rw [map_neg]; exact neg_mem hx

private theorem ks_val'' (n : ℤ) : (koszulSign n : ℤ) = if Even n then 1 else -1 := by
  split_ifs with h
  · rw [koszulSign, Int.negOnePow_even n h]; rfl
  · rw [koszulSign, Int.negOnePow_odd n (Int.not_even_iff_odd.mp h)]; rfl

theorem interchange_d_tmul {a b c : ℤ} {m : M} (hm : m ∈ grading a) {n : N} (hn : n ∈ grading b)
    {p : P} (hp : p ∈ grading c) (q : Q) :
    interchange A' B' M N P Q (d (TensorProductOver.tmul (𝒜' ᵍ⊗[ℤ] ℬ') (m ⊗ₜ[ℤ] n) (p ⊗ₜ[ℤ] q))) =
      d (interchange A' B' M N P Q
        (TensorProductOver.tmul (𝒜' ᵍ⊗[ℤ] ℬ') (m ⊗ₜ[ℤ] n) (p ⊗ₜ[ℤ] q))) := by
  rw [TensorProductOver.d_tmul_of_mem (tmul_mem_grading hm hn), d_tmul_of_mem hm n,
    d_tmul_of_mem hp q, TensorProductOver.add_tmul, TensorProductOver.tmul_add,
    TensorProductOver.units_smul_tmul, TensorProductOver.tmul_units_smul]
  simp only [map_add, map_units_zsmul]
  rw [interchange_tmul (d_mem hm) hn hp, interchange_tmul hm (d_mem hn) hp,
    interchange_tmul hm hn (d_mem hp), interchange_tmul hm hn hp, interchange_tmul hm hn hp,
    d_units_smul, d_tmul_of_mem (TensorProductOver.tmul_mem_grading (A := A') hm hp),
    TensorProductOver.d_tmul_of_mem hm, TensorProductOver.d_tmul_of_mem hn]
  simp only [Units.smul_def, TensorProduct.add_tmul, TensorProduct.tmul_add,
    TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add, smul_smul, ks_val'']
  by_cases ha : Even a <;> by_cases hb : Even b <;> by_cases hc : Even c <;>
    simp [Int.even_add, Int.even_mul, ← Int.not_even_iff_odd, ha, hb, hc] <;> abel

theorem interchange_d (t : T) :
    interchange A' B' M N P Q (d t) = d (interchange A' B' M N P Q t) := by
  have := T_addHom_ext (f := (interchange A' B' M N P Q).comp (d : T →+ T))
    (g := (d : X →+ X).comp (interchange A' B' M N P Q)) fun m n p q =>
      interchange_d_tmul m.2 n.2 p.2 (q : Q)
  exact DFunLike.congr_fun this t

variable (A' B' M N P Q) in
/-- **The interchange isomorphism** of dg abelian groups
`(M ⊗ N) ⊗_{A' ⊗ B'} (P ⊗ Q) ≅ (M ⊗_{A'} P) ⊗ (N ⊗_{B'} Q)`. -/
def interchangeAddEquiv : DGAddEquiv T X :=
  DGAddEquiv.ofAddMonoidHom (interchange A' B' M N P Q) (interchangeInv A' B' M N P Q)
    interchangeInv_interchange interchange_interchangeInv (fun ht => interchange_mem ht)
    interchange_d

end Interchange

section Linear

variable {A B A' B' : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B] [Ring A'] [DGAddCommGroup A'] [DGRing A'] [Ring B'] [DGAddCommGroup B'] [DGRing B']
  {M : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M] [Module A'ᵐᵒᵖ M]
  [DGRightModule A' M] [SMulCommClass A A'ᵐᵒᵖ M]
  {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module B N] [DGModule B N] [Module B'ᵐᵒᵖ N]
  [DGRightModule B' N] [SMulCommClass B B'ᵐᵒᵖ N]
  {P : Type*} [AddCommGroup P] [DGAddCommGroup P] [Module A' P] [DGModule A' P]
  {Q : Type*} [AddCommGroup Q] [DGAddCommGroup Q] [Module B' Q] [DGModule B' Q]

local notation "𝒜" => DGAlgebra.gradingSubmodule ℤ A
local notation "ℬ" => DGAlgebra.gradingSubmodule ℤ B
local notation "𝒜'" => DGAlgebra.gradingSubmodule ℤ A'
local notation "ℬ'" => DGAlgebra.gradingSubmodule ℤ B'
local notation "X" => TensorProductOver A' M P ⊗[ℤ] TensorProductOver B' N Q
local notation "T" => TensorProductOver (𝒜' ᵍ⊗[ℤ] ℬ') (M ⊗[ℤ] N) (P ⊗[ℤ] Q)

private theorem ks_eq₃ {m n : ℤ} (h : Even (m - n)) : koszulSign m = koszulSign n :=
  (Int.negOnePow_eq_iff m n).mpr h

theorem interchange_smul (x : 𝒜 ᵍ⊗[ℤ] ℬ) (t : T) :
    interchange A' B' M N P Q (x • t) = x • interchange A' B' M N P Q t := by
  induction x using GradedTensorProduct.induction_on_tmul (R := ℤ) with
  | zero =>
    rw [show (0 : 𝒜 ᵍ⊗[ℤ] ℬ) • t = 0 from zero_smul (𝒜 ᵍ⊗[ℤ] ℬ) t, map_zero,
      show (0 : 𝒜 ᵍ⊗[ℤ] ℬ) • interchange A' B' M N P Q t = 0 from
        zero_smul' (A := A) (B := B) (M := TensorProductOver A' M P)
          (N := TensorProductOver B' N Q) _]
  | add x x' hx hx' =>
    rw [show (x + x') • t = x • t + x' • t from add_smul x x' t, map_add, hx, hx',
      show (x + x') • interchange A' B' M N P Q t = x • interchange A' B' M N P Q t +
        x' • interchange A' B' M N P Q t from
        add_smul' (A := A) (B := B) (M := TensorProductOver A' M P)
          (N := TensorProductOver B' N Q) x x' _]
  | @tmul i j a ha b hb =>
    have := T_addHom_ext
      (f := (interchange A' B' M N P Q).comp
        (DistribSMul.toAddMonoidHom T (a ᵍ⊗ₜ[ℤ] b : 𝒜 ᵍ⊗[ℤ] ℬ)))
      (g := (DistribSMul.toAddMonoidHom X (a ᵍ⊗ₜ[ℤ] b : 𝒜 ᵍ⊗[ℤ] ℬ)).comp
        (interchange A' B' M N P Q)) fun m n p q => by
      simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply]
      rw [TensorProductOver.smul_tmul, ExternalTensor.tmul_smul_tmul a hb m.2 (n : N),
        TensorProductOver.units_smul_tmul, map_units_zsmul,
        interchange_tmul (smul_mem_grading ha m.2) (smul_mem_grading hb n.2) p.2,
        interchange_tmul m.2 n.2 p.2, smul_units_smul,
        ExternalTensor.tmul_smul_tmul a hb (TensorProductOver.tmul_mem_grading (A := A') m.2 p.2),
        smul_smul, smul_smul, ← koszulSign_add, ← koszulSign_add]
      congr 1
      exact ks_eq₃ ⟨0, by ring⟩
    exact DFunLike.congr_fun this t

variable (A B A' B' M N P Q) in
/-- **The interchange isomorphism** `(M ⊗ N) ⊗_{A' ⊗ B'} (P ⊗ Q) ≅ (M ⊗_{A'} P) ⊗ (N ⊗_{B'} Q)`
of dg modules over `A ⊗ B`, `(m ⊗ n) ⊗ (p ⊗ q) ↦ (-1)^{|n| |p|} (m ⊗ p) ⊗ (n ⊗ q)`. -/
def interchangeEquiv : T ≃ᵈᵍ[𝒜 ᵍ⊗[ℤ] ℬ] X where
  toFun := interchange A' B' M N P Q
  invFun := interchangeInv A' B' M N P Q
  left_inv := interchangeInv_interchange
  right_inv := interchange_interchangeInv
  map_add' := map_add _
  map_smul' x t := by rw [RingHom.id_apply]; exact interchange_smul x t
  map_mem' ht := interchange_mem ht
  map_d' t := interchange_d t

theorem interchangeEquiv_tmul {a b c : ℤ} {m : M} (hm : m ∈ grading a) {n : N}
    (hn : n ∈ grading b) {p : P} (hp : p ∈ grading c) (q : Q) :
    interchangeEquiv A B A' B' M N P Q (TensorProductOver.tmul _ (m ⊗ₜ[ℤ] n) (p ⊗ₜ[ℤ] q)) =
      koszulSign (c * b) •
        (TensorProductOver.tmul A' m p ⊗ₜ[ℤ] TensorProductOver.tmul B' n q) :=
  interchange_tmul hm hn hp q

end Linear

section RightLinear

open TensorProductOver.RightAction

variable {A' B' C D : Type*} [Ring A'] [DGAddCommGroup A'] [DGRing A'] [Ring B']
  [DGAddCommGroup B'] [DGRing B'] [Ring C] [DGAddCommGroup C] [DGRing C] [Ring D]
  [DGAddCommGroup D] [DGRing D]
  {M : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A'ᵐᵒᵖ M] [DGRightModule A' M]
  {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module B'ᵐᵒᵖ N] [DGRightModule B' N]
  {P : Type*} [AddCommGroup P] [DGAddCommGroup P] [Module A' P] [DGModule A' P] [Module Cᵐᵒᵖ P]
  [DGRightModule C P] [SMulCommClass A' Cᵐᵒᵖ P]
  {Q : Type*} [AddCommGroup Q] [DGAddCommGroup Q] [Module B' Q] [DGModule B' Q] [Module Dᵐᵒᵖ Q]
  [DGRightModule D Q] [SMulCommClass B' Dᵐᵒᵖ Q]

local notation "𝒜'" => DGAlgebra.gradingSubmodule ℤ A'
local notation "ℬ'" => DGAlgebra.gradingSubmodule ℤ B'
local notation "𝒞" => DGAlgebra.gradingSubmodule ℤ C
local notation "𝒟" => DGAlgebra.gradingSubmodule ℤ D
local notation "X" => TensorProductOver A' M P ⊗[ℤ] TensorProductOver B' N Q
local notation "T" => TensorProductOver (𝒜' ᵍ⊗[ℤ] ℬ') (M ⊗[ℤ] N) (P ⊗[ℤ] Q)

private theorem ks_eq₄ {m n : ℤ} (h : Even (m - n)) : koszulSign m = koszulSign n :=
  (Int.negOnePow_eq_iff m n).mpr h

/-- The interchange map is right `C ⊗ D`-linear when `P`, `Q` are dg bimodules. -/
theorem interchange_op_smul (x : 𝒞 ᵍ⊗[ℤ] 𝒟) (t : T) :
    interchange A' B' M N P Q (op x • t) = op x • interchange A' B' M N P Q t := by
  induction x using GradedTensorProduct.induction_on_tmul (R := ℤ) with
  | zero =>
    rw [show op (0 : 𝒞 ᵍ⊗[ℤ] 𝒟) • t = 0 by rw [op_zero]; exact zero_smul (𝒞 ᵍ⊗[ℤ] 𝒟)ᵐᵒᵖ t, map_zero,
      zero_op_smul' (A' := C) (B' := D)]
  | add x x' hx hx' =>
    rw [show op (x + x') • t = op x • t + op x' • t by rw [op_add]; exact add_smul (op x) (op x') t, map_add,
      hx, hx', add_op_smul' (A' := C) (B' := D)]
  | @tmul i j c hc d hd =>
    have := T_addHom_ext
      (f := (interchange A' B' M N P Q).comp
        (DistribSMul.toAddMonoidHom T (op (c ᵍ⊗ₜ[ℤ] d : 𝒞 ᵍ⊗[ℤ] 𝒟))))
      (g := (DistribSMul.toAddMonoidHom X (op (c ᵍ⊗ₜ[ℤ] d : 𝒞 ᵍ⊗[ℤ] 𝒟))).comp
        (interchange A' B' M N P Q)) fun m n p q => by
      simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply]
      rw [TensorProductOver.op_smul_tmul_right, tmul_op_smul_tmul hc d (p : P) q.2,
        TensorProductOver.tmul_units_smul, map_units_zsmul,
        interchange_tmul m.2 n.2 (op_smul_mem_grading hc p.2),
        interchange_tmul m.2 n.2 p.2, op_smul_units_smul,
        tmul_op_smul_tmul hc d (TensorProductOver.tmul A' (m : M) (p : P))
          (TensorProductOver.tmul_mem_grading (A := B') n.2 q.2),
        TensorProductOver.op_smul_tmul_right, TensorProductOver.op_smul_tmul_right,
        smul_smul, smul_smul, ← koszulSign_add, ← koszulSign_add]
      congr 1
      exact ks_eq₄ ⟨0, by ring⟩
    exact DFunLike.congr_fun this t

end RightLinear

end ExternalTensor

end DG
