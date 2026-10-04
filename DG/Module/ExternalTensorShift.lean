import DG.Module.ExternalTensor
import DG.Module.Shift

/-!
# Shifts and the external tensor product

For dg rings `A`, `B`, a dg `A`-module `M` and a dg `B`-module `N`, the shift in the first
variable commutes with the external tensor product without sign:

`M⟦n⟧ ⊠ N ≅ (M ⊠ N)⟦n⟧`, `mk m ⊗ x ↦ mk (m ⊗ x)` (`DG.ExternalTensor.shiftLeftEquiv`),

an isomorphism of dg modules over `A ⊗ B`. (With the conventions of `DG.Shift`, the differential
of `M⟦n⟧` is `(-1)ⁿ d` and the action is twisted by `(-1)^{n|a|}`; both signs match.) In the
second variable the Koszul sign appears:

`M ⊠ N⟦n⟧ ≅ (M ⊠ N)⟦n⟧`, `m ⊗ mk x ↦ (-1)^{n |m|} mk (m ⊗ x)` (`DG.ExternalTensor.shiftRightEquiv`).
-/

open scoped TensorProduct

noncomputable section

namespace DG

namespace ExternalTensor

private theorem ks_val (n : ℤ) : (koszulSign n : ℤ) = if Even n then 1 else -1 := by
  split_ifs with h
  · rw [koszulSign, Int.negOnePow_even n h]; rfl
  · rw [koszulSign, Int.negOnePow_odd n (Int.not_even_iff_odd.mp h)]; rfl

private theorem ks_eq {m n : ℤ} (h : Even (m - n)) : koszulSign m = koszulSign n :=
  (Int.negOnePow_eq_iff m n).mpr h

variable {A B : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B]
  {M : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module B N] [DGModule B N]

local notation "𝒜" => DGAlgebra.gradingSubmodule ℤ A
local notation "ℬ" => DGAlgebra.gradingSubmodule ℤ B
local notation "AB" => 𝒜 ᵍ⊗[ℤ] ℬ

variable (n : ℤ)

variable (M N) in
/-- The underlying additive map `M⟦n⟧ ⊠ N → (M ⊠ N)⟦n⟧`, `mk m ⊗ x ↦ mk (m ⊗ x)`. -/
def shiftLeftAddEquiv : (Shift n M ⊗[ℤ] N) ≃+ Shift n (M ⊗[ℤ] N) :=
  (TensorProduct.congr (Shift.unmk n (M := M)).toIntLinearEquiv
    (LinearEquiv.refl ℤ N)).toAddEquiv.trans (Shift.mk n)

omit [DGAddCommGroup M] [DGAddCommGroup N] in
theorem shiftLeftAddEquiv_tmul (m : M) (x : N) :
    shiftLeftAddEquiv M N n (Shift.mk n m ⊗ₜ x) = Shift.mk n (m ⊗ₜ x) := rfl

omit [DGModule B N] in
theorem shiftLeftAddEquiv_smul_tmul (a : A) {j : ℤ} {b : B} (hb : b ∈ grading j) {p : ℤ}
    {m : Shift n M} (hm : m ∈ grading p) (x : N) :
    shiftLeftAddEquiv M N n ((a ᵍ⊗ₜ[ℤ] b : AB) • (m ⊗ₜ x)) =
      (a ᵍ⊗ₜ[ℤ] b : AB) • shiftLeftAddEquiv M N n (m ⊗ₜ x) := by
  obtain ⟨m, rfl⟩ := Shift.mk_surjective m
  induction a using DG.induction_on with
  | h_zero =>
    rw [GradedTensorProduct.zero_tmul, zero_smul', map_zero]
    exact (zero_smul AB (shiftLeftAddEquiv M N n (Shift.mk n m ⊗ₜ x))).symm
  | h_add a a' ha ha' =>
    rw [GradedTensorProduct.add_tmul, add_smul', map_add, ha, ha']
    exact (add_smul _ _ _).symm
  | h_homogeneous a =>
    rename_i i
    have hut : ∀ (u : ℤˣ) (y : M) (z : N), (u • y) ⊗ₜ[ℤ] z = u • (y ⊗ₜ[ℤ] z) := fun u y z => by
      rw [Units.smul_def, Units.smul_def, TensorProduct.smul_tmul']
    rw [tmul_smul_tmul (a : A) hb hm x, Units.smul_def, map_zsmul, ← Units.smul_def,
      Shift.smul_mk a.2, shiftLeftAddEquiv_tmul, shiftLeftAddEquiv_tmul,
      Shift.smul_mk (GradedTensorProduct.tmul_mem_grading (R := ℤ) a.2 hb),
      tmul_smul_tmul (a : A) hb (Shift.mem_grading_iff.mp hm) x, hut, ← Shift.mk_units_smul,
      smul_smul, smul_smul, ← koszulSign_add, ← koszulSign_add]
    congr 2
    exact ks_eq ⟨-(n * j), by ring⟩

variable (M N) in
/-- **`M⟦n⟧ ⊠ N ≅ (M ⊠ N)⟦n⟧`** as dg modules over `A ⊗ B`, `mk m ⊗ x ↦ mk (m ⊗ x)`. -/
def shiftLeftEquiv : (Shift n M ⊗[ℤ] N) ≃ᵈᵍ[AB] Shift n (M ⊗[ℤ] N) where
  __ := shiftLeftAddEquiv M N n
  map_smul' x y := by
    change shiftLeftAddEquiv M N n (x • y) = x • shiftLeftAddEquiv M N n y
    induction x using GradedTensorProduct.induction_on_tmul (R := ℤ) with
    | zero =>
      rw [zero_smul', map_zero]
      exact (zero_smul AB (shiftLeftAddEquiv M N n y)).symm
    | add x x' hx hx' =>
      rw [add_smul', map_add, hx, hx']
      exact (add_smul _ _ _).symm
    | @tmul i j a ha b hb =>
      induction y using DG.tensor_induction_on with
      | zero =>
        rw [smul_zero', map_zero]
        exact (smul_zero _).symm
      | add y y' hy hy' =>
        rw [smul_add', map_add, hy, hy', map_add]
        exact (smul_add _ _ _).symm
      | tmul m x =>
        obtain ⟨m, hm⟩ := m
        obtain ⟨x, -⟩ := x
        exact shiftLeftAddEquiv_smul_tmul n a hb hm x
  map_mem' {k y} hy := by
    have := map_mem_grading_of_tmul (shiftLeftAddEquiv M N n).toAddMonoidHom 0
      (fun {i j m x} hm hx => by
        obtain ⟨m, rfl⟩ := Shift.mk_surjective m
        change Shift.mk n (m ⊗ₜ x) ∈ grading (i + j + 0)
        rw [Shift.mem_grading_iff]
        have := tmul_mem_grading (Shift.mem_grading_iff.mp hm) hx
        rwa [show i + n + j = i + j + 0 + n by ring] at this) hy
    rwa [add_zero] at this
  map_d' y := by
    change shiftLeftAddEquiv M N n (d y) = d (shiftLeftAddEquiv M N n y)
    induction y using DG.tensor_induction_on with
    | zero => simp
    | add y y' hy hy' => rw [d_add, map_add, hy, hy', map_add, d_add]
    | @tmul i j m x =>
      obtain ⟨m, hm⟩ := m
      obtain ⟨x, -⟩ := x
      obtain ⟨m, rfl⟩ := Shift.mk_surjective m
      have hut : ∀ (u : ℤˣ) (y : M) (z : N), (u • y) ⊗ₜ[ℤ] z = u • (y ⊗ₜ[ℤ] z) := fun u y z => by
        rw [Units.smul_def, Units.smul_def, TensorProduct.smul_tmul']
      rw [d_tmul_of_mem hm, map_add, Units.smul_def, map_zsmul, ← Units.smul_def,
        Shift.d_mk, shiftLeftAddEquiv_tmul, shiftLeftAddEquiv_tmul, shiftLeftAddEquiv_tmul,
        Shift.d_mk, d_tmul_of_mem (Shift.mem_grading_iff.mp hm), hut, smul_add, smul_smul,
        ← koszulSign_add, ← Shift.mk_units_smul, ← Shift.mk_add]
      congr 3
      exact ks_eq ⟨-n, by ring⟩

omit [DGModule B N] in
theorem shiftLeftEquiv_tmul (m : M) (x : N) :
    shiftLeftEquiv (A := A) (B := B) M N n (Shift.mk n m ⊗ₜ x) = Shift.mk n (m ⊗ₜ x) := rfl

/-! ### The second variable -/

variable (M) in
/-- The Koszul twist `m ↦ (-1)^{n |m|} m`, an involutive additive equivalence. -/
def twistAddEquiv : M ≃+ M where
  toFun := twist M n
  invFun := twist M n
  left_inv m := by
    induction m using DG.induction_on with
    | h_zero => simp
    | h_add m m' hm hm' => rw [map_add, map_add, hm, hm']
    | h_homogeneous m =>
      rw [twist_of_mem n m.2, Units.smul_def, map_zsmul, twist_of_mem n m.2, Units.smul_def,
        smul_smul, ← Units.val_mul, ← koszulSign_add, ← two_mul,
        koszulSign_even (even_two_mul _)]
      simp
  right_inv m := by
    induction m using DG.induction_on with
    | h_zero => simp
    | h_add m m' hm hm' => rw [map_add, map_add, hm, hm']
    | h_homogeneous m =>
      rw [twist_of_mem n m.2, Units.smul_def, map_zsmul, twist_of_mem n m.2, Units.smul_def,
        smul_smul, ← Units.val_mul, ← koszulSign_add, ← two_mul,
        koszulSign_even (even_two_mul _)]
      simp
  map_add' := map_add _

variable (M N) in
/-- The underlying additive map `M ⊠ N⟦n⟧ → (M ⊠ N)⟦n⟧`,
`m ⊗ mk x ↦ (-1)^{n |m|} mk (m ⊗ x)`. -/
def shiftRightAddEquiv : (M ⊗[ℤ] Shift n N) ≃+ Shift n (M ⊗[ℤ] N) :=
  (TensorProduct.congr (twistAddEquiv M n).toIntLinearEquiv
    (Shift.unmk n (M := N)).toIntLinearEquiv).toAddEquiv.trans (Shift.mk n)

omit [DGAddCommGroup N] in
theorem shiftRightAddEquiv_tmul {i : ℤ} {m : M} (hm : m ∈ grading i) (x : N) :
    shiftRightAddEquiv M N n (m ⊗ₜ Shift.mk n x) = koszulSign (i * n) • Shift.mk n (m ⊗ₜ x) := by
  change Shift.mk n (twist M n m ⊗ₜ x) = _
  rw [twist_of_mem n hm, Units.smul_def, Units.smul_def, ← TensorProduct.smul_tmul']
  rfl

omit [DGModule B N] in
theorem shiftRightAddEquiv_smul_tmul (a : A) {j : ℤ} {b : B} (hb : b ∈ grading j) {p : ℤ}
    {m : M} (hm : m ∈ grading p) (x : Shift n N) :
    shiftRightAddEquiv M N n ((a ᵍ⊗ₜ[ℤ] b : AB) • (m ⊗ₜ x)) =
      (a ᵍ⊗ₜ[ℤ] b : AB) • shiftRightAddEquiv M N n (m ⊗ₜ x) := by
  obtain ⟨x, rfl⟩ := Shift.mk_surjective x
  induction a using DG.induction_on with
  | h_zero =>
    rw [GradedTensorProduct.zero_tmul, zero_smul', map_zero]
    exact (zero_smul AB (shiftRightAddEquiv M N n (m ⊗ₜ Shift.mk n x))).symm
  | h_add a a' ha ha' =>
    rw [GradedTensorProduct.add_tmul, add_smul', map_add, ha, ha']
    exact (add_smul _ _ _).symm
  | h_homogeneous a =>
    rename_i i
    have hut : ∀ (u : ℤˣ) (y : M) (z : Shift n N), y ⊗ₜ[ℤ] (u • z) = u • (y ⊗ₜ[ℤ] z) :=
      fun u y z => by rw [Units.smul_def, Units.smul_def, TensorProduct.tmul_smul]
    have hab := GradedTensorProduct.tmul_mem_grading (R := ℤ) a.2 hb
    rw [tmul_smul_tmul (a : A) hb hm (Shift.mk n x), Shift.smul_mk hb, Shift.mk_units_smul, hut,
      smul_smul, Units.smul_def, map_zsmul, shiftRightAddEquiv_tmul n (smul_mem_grading a.2 hm),
      shiftRightAddEquiv_tmul n hm, Units.smul_def (koszulSign (p * n)),
      smul_comm (a ᵍ⊗ₜ[ℤ] b : AB) ((koszulSign (p * n) : ℤˣ) : ℤ), Shift.smul_mk hab,
      tmul_smul_tmul (a : A) hb hm x, Shift.mk_units_smul, Shift.mk_units_smul, smul_smul,
      Units.smul_def, Units.smul_def, smul_smul, smul_smul, ← Units.val_mul, ← Units.val_mul]
    simp only [← koszulSign_add]
    congr 3
    ring

variable (M N) in
/-- **`M ⊠ N⟦n⟧ ≅ (M ⊠ N)⟦n⟧`** as dg modules over `A ⊗ B`,
`m ⊗ mk x ↦ (-1)^{n |m|} mk (m ⊗ x)`. -/
def shiftRightEquiv : (M ⊗[ℤ] Shift n N) ≃ᵈᵍ[AB] Shift n (M ⊗[ℤ] N) where
  __ := shiftRightAddEquiv M N n
  map_smul' x y := by
    change shiftRightAddEquiv M N n (x • y) = x • shiftRightAddEquiv M N n y
    induction x using GradedTensorProduct.induction_on_tmul (R := ℤ) with
    | zero =>
      rw [zero_smul', map_zero]
      exact (zero_smul AB (shiftRightAddEquiv M N n y)).symm
    | add x x' hx hx' =>
      rw [add_smul', map_add, hx, hx']
      exact (add_smul _ _ _).symm
    | @tmul i j a ha b hb =>
      induction y using DG.tensor_induction_on with
      | zero =>
        rw [smul_zero', map_zero]
        exact (smul_zero _).symm
      | add y y' hy hy' =>
        rw [smul_add', map_add, hy, hy', map_add]
        exact (smul_add _ _ _).symm
      | tmul m x =>
        obtain ⟨m, hm⟩ := m
        obtain ⟨x, -⟩ := x
        exact shiftRightAddEquiv_smul_tmul n a hb hm x
  map_mem' {k y} hy := by
    have := map_mem_grading_of_tmul (shiftRightAddEquiv M N n).toAddMonoidHom 0
      (fun {i j m x} hm hx => by
        obtain ⟨x, rfl⟩ := Shift.mk_surjective x
        change shiftRightAddEquiv M N n (m ⊗ₜ Shift.mk n x) ∈ grading (i + j + 0)
        rw [shiftRightAddEquiv_tmul n hm, ← Shift.mk_units_smul, Shift.mem_grading_iff]
        rw [Units.smul_def]
        refine zsmul_mem ?_ _
        have := tmul_mem_grading hm (Shift.mem_grading_iff.mp hx)
        rwa [show i + (j + n) = i + j + 0 + n by ring] at this) hy
    rwa [add_zero] at this
  map_d' y := by
    change shiftRightAddEquiv M N n (d y) = d (shiftRightAddEquiv M N n y)
    induction y using DG.tensor_induction_on with
    | zero => simp
    | add y y' hy hy' => rw [d_add, map_add, hy, hy', map_add, d_add]
    | @tmul i j m x =>
      obtain ⟨m, hm⟩ := m
      obtain ⟨x, -⟩ := x
      obtain ⟨x, rfl⟩ := Shift.mk_surjective x
      have hut : ∀ (u : ℤˣ) (y : M) (z : Shift n N), y ⊗ₜ[ℤ] (u • z) = u • (y ⊗ₜ[ℤ] z) :=
        fun u y z => by rw [Units.smul_def, Units.smul_def, TensorProduct.tmul_smul]
      have hut' : ∀ (u : ℤˣ) (y : M) (z : N), y ⊗ₜ[ℤ] (u • z) = u • (y ⊗ₜ[ℤ] z) :=
        fun u y z => by rw [Units.smul_def, Units.smul_def, TensorProduct.tmul_smul]
      rw [d_tmul_of_mem hm, Shift.d_mk, Shift.mk_units_smul, hut, map_add, Units.smul_def,
        map_zsmul, Units.smul_def, map_zsmul, shiftRightAddEquiv_tmul n (d_mem hm),
        shiftRightAddEquiv_tmul n hm, shiftRightAddEquiv_tmul n hm, d_units_smul,
        Shift.d_mk, d_tmul_of_mem hm, smul_add]
      simp only [map_add, Units.smul_def, smul_add, smul_smul, map_zsmul, ks_val]
      by_cases hi : Even i <;> by_cases hn : Even n <;>
        simp [Int.even_mul, ← Int.not_even_iff_odd, hi, hn]

omit [DGModule B N] in
theorem shiftRightEquiv_tmul {i : ℤ} {m : M} (hm : m ∈ grading i) (x : N) :
    shiftRightEquiv (A := A) (B := B) M N n (m ⊗ₜ Shift.mk n x) =
      koszulSign (i * n) • Shift.mk n (m ⊗ₜ x) :=
  shiftRightAddEquiv_tmul n hm x

end ExternalTensor

end DG
