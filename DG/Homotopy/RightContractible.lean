import DG.Homotopy.BimoduleTensor
import DG.Module.TensorProduct
import DG.Module.Right

/-!
# Bimodules over a right acyclic dg ring are contractible on the left

Let `M` be a dg `(A, B)`-bimodule and `t ∈ B` an element of degree `-1` with `d t = 1`. Then the
left `A`-linear map `m ↦ (-1)^{|m|} m t` of degree `-1` (`DG.rightHomotopy`) is a contracting
homotopy: `m = d(h m) + h(d m)` (`DG.rightHomotopy_comm`). So `M` is contractible as a left dg
`A`-module (`DG.isContractible_of_d_op_smul_eq_one`). The homotopy is left `A`-linear because it
acts on the right.
-/

noncomputable section

open MulOpposite

namespace DG

section Contractible

variable {A B M : Type*} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [DGBimodule A B M]
  {t : B} (ht : t ∈ grading (-1)) (hd : d t = 1)

/-- The left `A`-linear map `m ↦ (-1)^{|m|} m t` of degree `-1`. -/
def rightHomotopy : Cochain A M M (-1) where
  toFun m := op t • gradeInvolution M m
  map_zero' := by rw [map_zero, smul_zero]
  map_add' m m' := by rw [map_add, smul_add]
  map_mem' i m hm := op_smul_mem_grading ht (gradeInvolution_mem hm)
  map_smul' {i a} ha m := by
    induction m using DG.induction_on with
    | h_zero => rw [smul_zero, map_zero, smul_zero, smul_zero, smul_zero]
    | @h_homogeneous j m =>
      rw [gradeInvolution_of_mem (smul_mem_grading ha m.2), gradeInvolution_of_mem m.2,
        smul_comm (op t) (koszulSign (i + j)), smul_comm (op t) (koszulSign j),
        smul_comm a (koszulSign j), (smul_comm a (op t) _).symm, smul_smul, koszulSign_add,
        koszulSign_neg_one_mul]
    | h_add m m' hm hm' => rw [smul_add, map_add, smul_add, hm, hm', map_add, smul_add, smul_add, smul_add]

theorem rightHomotopy_apply (m : M) : rightHomotopy (A := A) ht m = op t • gradeInvolution M m := rfl

include hd in
theorem rightHomotopy_comm (m : M) :
    m = d (rightHomotopy (A := A) ht m) + rightHomotopy (A := A) ht (d m) := by
  induction m using DG.induction_on with
  | h_zero => rw [map_zero, d_zero, map_zero, add_zero]
  | @h_homogeneous j m =>
    rw [rightHomotopy_apply, rightHomotopy_apply, gradeInvolution_of_mem m.2,
      gradeInvolution_of_mem (d_mem m.2), smul_comm (op t) (koszulSign j) (m : M), d_units_smul,
      d_op_smul m.2, hd, op_one, one_smul, smul_add, smul_smul (koszulSign j) (koszulSign j),
      ← koszulSign_add, koszulSign_even (Even.add_self j), one_smul,
      smul_comm (op t) (koszulSign (j + 1)) (d (m : M)), koszulSign_add, koszulSign_odd odd_one,
      mul_neg, mul_one, Units.neg_smul]
    abel
  | h_add m m' hm hm' =>
    rw [map_add, map_add, d_add, map_add]
    conv_lhs => rw [hm, hm']
    abel

include ht hd in
/-- **A dg `(A, B)`-bimodule is contractible as a left dg `A`-module** if `d t = 1` for some `t ∈ B` of
degree `-1`. -/
theorem isContractible_of_d_op_smul_eq_one : IsContractible A M :=
  ⟨DGHomotopy.mk' (rightHomotopy ht) fun m => by
    rw [DGModuleHom.zero_apply, add_zero]; exact rightHomotopy_comm ht hd m⟩

end Contractible

end DG
