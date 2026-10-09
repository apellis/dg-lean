import DG.Module.Shift
import DG.Module.Right
import DG.Module.TensorProduct

/-!
# Regrading a dg bimodule

For a dg `(A, B)`-bimodule `M` and `n : ℤ`, `Regrade n M` is `M` with the grading
`(Regrade n M)ᵏ = Mᵏ⁺ⁿ`, the same differential and the same left action, and the right action
twisted by `(-1)^{n |b|}` (`DG.Shift.twist B n`): the shift convention in which the Koszul sign
is carried by the right action. It is again a dg `(A, B)`-bimodule (`Regrade.instDGBimodule`).
(`DG.Shift n M` is the other convention: `d` multiplied by `(-1)^n` and the left action
twisted.)

`signTwist M n` is the additive involution `m ↦ (-1)^{n |m|} m` of a dg abelian group.
-/

noncomputable section

set_option linter.unusedSectionVars false

open DirectSum MulOpposite

namespace DG

universe u

/-- `M` regraded by `n`: `(Regrade n M)ᵏ = Mᵏ⁺ⁿ`. -/
def Regrade (_n : ℤ) (M : Type u) : Type u := M

namespace Regrade

variable (n : ℤ) {M : Type u}

instance [AddCommGroup M] : AddCommGroup (Regrade n M) := inferInstanceAs (AddCommGroup M)

/-- The identity `M → Regrade n M`. -/
def mk [AddCommGroup M] : M ≃+ Regrade n M := AddEquiv.refl M

variable {n}

instance [AddCommGroup M] [DGAddCommGroup M] : DGAddCommGroup (Regrade n M) where
  grading k := grading (M := M) (k + n)
  decomposition := Decomposition.reindex (grading (M := M)) (Equiv.addRight n)
  d := (d : M →+ M)
  d_mem' {k m} hm := by
    have hm' : (mk n).symm m ∈ grading (M := M) (k + n) := hm
    change (d : M →+ M) ((mk n).symm m) ∈ grading (M := M) (k + 1 + n)
    rw [add_right_comm]
    exact d_mem hm'
  d_d' m := d_d (M := M) ((mk n).symm m)

theorem mem_grading_iff [AddCommGroup M] [DGAddCommGroup M] {k : ℤ} {m : M} :
    mk n m ∈ grading k ↔ m ∈ grading (M := M) (k + n) := Iff.rfl

theorem d_mk [AddCommGroup M] [DGAddCommGroup M] (m : M) : d (mk n m) = mk n (d m) := rfl

section Left

variable {A : Type*} [Ring A] [DGAddCommGroup A] [AddCommGroup M] [Module A M]

instance : Module A (Regrade n M) := Module.compHom M (RingHom.id A)

theorem smul_mk (a : A) (m : M) : a • mk n m = mk n (a • m) := rfl

variable [DGAddCommGroup M]

instance [DGModule A M] : DGModule A (Regrade n M) where
  smul_mem {i j} a m ha hm := by
    have hm' : (mk n).symm m ∈ grading (M := M) (j + n) := hm
    change a • (mk n).symm m ∈ grading (M := M) (i + j + n)
    rw [add_assoc]
    exact smul_mem_grading ha hm'
  d_smul' {i} a ha m := d_smul (M := M) ha ((mk n).symm m)

end Left

section Right

variable {B : Type*} [Ring B] [DGAddCommGroup B] [DGRing B] [AddCommGroup M] [DGAddCommGroup M]
  [Module Bᵐᵒᵖ M]

/-- The right action twisted by `(-1)^{n |b|}`. -/
instance : Module Bᵐᵒᵖ (Regrade n M) :=
  Module.compHom M (RingHom.op (Shift.twist B n))

theorem op_smul_mk (b : B) (m : M) : op b • mk n m = mk n (op (Shift.twist B n b) • m) := rfl

theorem op_smul_mk_of_mem {i : ℤ} {b : B} (hb : b ∈ grading i) (m : M) :
    op b • mk n m = mk n (koszulSign (n * i) • (op b • m)) := by
  rw [op_smul_mk, Shift.twist_of_mem hb, Units.smul_def, MulOpposite.op_smul, smul_assoc,
    ← Units.smul_def]

instance [DGRightModule B M] : DGRightModule B (Regrade n M) where
  op_smul_mem' {i j b m} hb hm := by
    rw [show m = mk n ((mk n).symm m) from rfl, op_smul_mk_of_mem hb]
    change koszulSign (n * i) • (op b • ((mk n).symm m)) ∈ grading (M := M) (j + i + n)
    rw [show j + i + n = j + n + i by ring]
    have hm' : (mk n).symm m ∈ grading (M := M) (j + n) := hm
    exact zsmul_mem (op_smul_mem_grading (M := M) hb hm') _
  d_op_smul' {j m} hm b := by
    have key : ∀ (b : B) (m' : M), m' ∈ grading (M := M) (j + n) →
        d (op (Shift.twist B n b) • m') =
          op (Shift.twist B n b) • d m' + koszulSign j • (op (Shift.twist B n (d b)) • m') := by
      intro b m' hm'
      induction b using DG.induction_on with
      | h_zero => simp
      | @h_homogeneous i b =>
        rw [Shift.twist_of_mem b.2, Shift.twist_of_mem (d_mem b.2)]
        simp only [Units.smul_def, MulOpposite.op_smul, smul_assoc, d_zsmul, d_op_smul hm', smul_add,
          smul_smul]
        rw [← Units.val_mul, ← Units.val_mul, ← koszulSign_add, ← koszulSign_add,
          show n * i + (j + n) = j + n * (i + 1) by ring]
      | h_add b b' hb hb' =>
        simp only [map_add, op_add, add_smul, smul_add] at hb hb' ⊢
        rw [hb, hb']
        abel
    exact key b ((mk n).symm m) hm

end Right

section Bimodule

variable {A B : Type*} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B] [DGRing B]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]

instance [SMulCommClass A Bᵐᵒᵖ M] : SMulCommClass A Bᵐᵒᵖ (Regrade n M) where
  smul_comm a b m := smul_comm a (op (Shift.twist B n (unop b))) (show M from m)

/-- **`Regrade n M` is a dg bimodule.** -/
instance instDGBimodule [DGBimodule A B M] : DGBimodule A B (Regrade n M) := DGBimodule.mk'

end Bimodule

end Regrade

/-! ### The sign twist `m ↦ (-1)^{n |m|} m` -/

section SignTwist

variable (M : Type u) [AddCommGroup M] [DGAddCommGroup M]

/-- `m ↦ (-1)^{n |m|} • m` on homogeneous elements. -/
def signTwist (n : ℤ) : M →+ M :=
  liftHomogeneous (grading (M := M)) fun k => ((koszulSign (n * k) : ℤ) • (grading (M := M) k).subtype)

variable {M}

theorem signTwist_of_mem (n : ℤ) {k : ℤ} {m : M} (hm : m ∈ grading k) :
    signTwist M n m = koszulSign (n * k) • m := by
  rw [signTwist, liftHomogeneous_of_mem _ _ hm, Units.smul_def]
  rfl

theorem signTwist_mem (n : ℤ) {k : ℤ} {m : M} (hm : m ∈ grading k) : signTwist M n m ∈ grading k := by
  rw [signTwist_of_mem n hm, Units.smul_def]
  exact zsmul_mem hm _

@[simp]
theorem signTwist_signTwist (n : ℤ) (m : M) : signTwist M n (signTwist M n m) = m := by
  induction m using induction_on with
  | h_zero => simp
  | h_homogeneous m =>
    rw [signTwist_of_mem n m.2, map_units_zsmul, signTwist_of_mem n m.2, smul_smul, Int.units_mul_self,
      one_smul]
  | h_add m m' hm hm' => rw [map_add, map_add, hm, hm']

theorem d_signTwist (n : ℤ) (m : M) : d (signTwist M n m) = koszulSign n • signTwist M n (d m) := by
  induction m using induction_on with
  | h_zero => simp
  | @h_homogeneous k m =>
    have e : koszulSign (n * k) = koszulSign n * koszulSign (n * (k + 1)) := by
      rw [mul_add, mul_one, koszulSign_add, mul_comm (koszulSign (n * k)), ← mul_assoc,
        Int.units_mul_self, one_mul]
    rw [signTwist_of_mem n m.2, signTwist_of_mem n (d_mem m.2), d_units_smul, e, mul_smul]
  | h_add m m' hm hm' => simp only [map_add, hm, hm', smul_add]

theorem signTwist_smul_of_mem {A : Type*} [Ring A] [DGAddCommGroup A] [Module A M] [DGModule A M]
    (n : ℤ) {i : ℤ} {a : A} (ha : a ∈ grading i) (m : M) :
    signTwist M n (a • m) = koszulSign (n * i) • (a • signTwist M n m) := by
  induction m using DG.induction_on with
  | h_zero => simp
  | @h_homogeneous j m =>
    rw [signTwist_of_mem n (smul_mem_grading ha m.2), signTwist_of_mem n m.2,
      smul_comm a (koszulSign (n * j)) (m : M), smul_smul, ← koszulSign_add, ← mul_add]
  | h_add m m' hm hm' => rw [smul_add, map_add, hm, hm', map_add, smul_add, smul_add]

theorem signTwist_op_smul_of_mem {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] [Module Aᵐᵒᵖ M]
    [DGRightModule A M] (n : ℤ) {i : ℤ} {a : A} (ha : a ∈ grading i) (m : M) :
    signTwist M n (op a • m) = koszulSign (n * i) • (op a • signTwist M n m) := by
  induction m using DG.induction_on with
  | h_zero => simp
  | @h_homogeneous j m =>
    rw [signTwist_of_mem n (op_smul_mem_grading ha m.2), signTwist_of_mem n m.2,
      smul_comm (op a) (koszulSign (n * j)) (m : M), smul_smul, ← koszulSign_add, ← mul_add, add_comm i j]
  | h_add m m' hm hm' => rw [smul_add, map_add, hm, hm', map_add, smul_add, smul_add]

end SignTwist

end DG
