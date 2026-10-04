import DG.Module.ExternalTensor
import DG.Module.Shift

/-!
# Shifts and the external tensor product

For dg rings `A`, `B`, a dg `A`-module `M` and a dg `B`-module `N`, the shift in the first
variable commutes with the external tensor product without sign:

`M⟦n⟧ ⊠ N ≅ (M ⊠ N)⟦n⟧`, `mk m ⊗ x ↦ mk (m ⊗ x)` (`DG.ExternalTensor.shiftLeftEquiv`),

an isomorphism of dg modules over `A ⊗ B`. (With the conventions of `DG.Shift`, the differential
of `M⟦n⟧` is `(-1)ⁿ d` and the action is twisted by `(-1)^{n|a|}`; both signs match.)
-/

open scoped TensorProduct

noncomputable section

namespace DG

namespace ExternalTensor

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

end ExternalTensor

end DG
