import DG.Derived.RightDual
import DG.Module.TensorProductOver

/-!
# Morita bimodule isomorphisms for a module with a finite right basis

Let `A`, `E` be dg rings and `M` a dg `(E, A)`-bimodule with a finite homogeneous right basis
`R : RightBasis A M ι`, on which `E` acts *fully* (`FullAction`): faithfully, by every right
`A`-linear additive endomorphism, and detecting degrees. Then, with `M^∨ = HOM_A(M, A)`
(`RightDual A M`):

* `FullAction.rho z f ∈ E`: the element acting as the rank-one map `w ↦ z · f(w)`; it is
  bi-additive, balanced, `E`-bilinear, homogeneous of degree `|z| + |f|`, and
  `d (rho z f) = rho (d z) f + (-1)^{|z|} rho z (d f)` (`FullAction.d_rho`).
* `FullAction.mulEquiv R : M ⊗_A M^∨ ≅ E`, `z ⊗ f ↦ rho z f`, an isomorphism of dg
  `(E, E)`-bimodules (`FullAction.mulEquiv_op_smul` for the right action).
* `FullAction.evEquiv R : M^∨ ⊗_E M ≅ A`, `f ⊗ z ↦ f(z)`, an isomorphism of dg `(A, A)`-bimodules
  (`FullAction.evEquiv_op_smul`), for a nonempty basis.

No signs occur: `rho z f` acts by `w ↦ z f(w)` (right action of `f(w)`), `f ⊗ z ↦ f(z)`, and the
differentials match by the Leibniz rules of `M` and the Hom-complex differential of `M^∨`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MulOpposite

namespace DG

open TensorProductOver TensorProductOver.RightAction

variable {E A M : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] [AddCommGroup M] [DGAddCommGroup M]
  [Module Aᵐᵒᵖ M]

/-! ### Coefficients of `M ⊗_A M^∨` along a basis -/

section Coeff

variable [DGRightModule A M] {ι : Type*} [Fintype ι] (R : RightBasis A M ι)

/-- The coefficient of `δ_i` in an element of `M ⊗_A M^∨`: `z ⊗ f ↦ z · f(b_i)`. -/
def coeffTensor (i : ι) : TensorProductOver A M (RightDual A M) →+ M :=
  lift (AddMonoidHom.mk' (fun z => AddMonoidHom.mk' (fun f => op (RightDual.toHom f (R.b i)) • z)
      fun f f' => by rw [RightDual.toHom_add, AddMonoidHom.add_apply, op_add, add_smul])
      fun z z' => by ext f; exact smul_add _ z z')
    fun a z f => by
      change op (RightDual.toHom f (R.b i)) • op a • z = op (RightDual.toHom (a • f) (R.b i)) • z
      rw [RightDual.toHom_smul, smul_smul, op_mul]

theorem eq_sum_coeffTensor (t : TensorProductOver A M (RightDual A M)) :
    t = ∑ i, tmul A (coeffTensor R i t) (R.δ i) := by
  induction t using TensorProductOver.induction_on with
  | zero => simp [map_zero, zero_tmul]
  | tmul z f =>
    conv_lhs => rw [← R.dualBasis.sum_coeff f]
    rw [← TensorProductOver.tmulAddHom_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProductOver.tmulAddHom_apply]
    rw [← op_smul_tmul]
    rfl
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_add, add_tmul]



end Coeff

variable [Ring E] [DGAddCommGroup E] [DGRing E] [Module E M] [DGBimodule E A M]

variable (E A M) in
/-- `E` acts on the right dg `A`-module `M` *fully*: faithfully, by every right `A`-linear
additive endomorphism, and an element shifting all degrees by `i` has degree `i`. -/
structure FullAction : Prop where
  faithful : ∀ e : E, (∀ w : M, e • w = 0) → e = 0
  full : ∀ φ : M →+ M, (∀ (a : A) (x : M), φ (op a • x) = op a • φ x) →
    ∃ e : E, ∀ w : M, e • w = φ w
  mem_grading : ∀ (e : E) (i : ℤ),
    (∀ (j : ℤ) (w : M), w ∈ grading j → e • w ∈ grading (i + j)) → e ∈ grading i

omit [DGRing A] in
theorem rankOne_op_smul (z : M) (f : RightDual A M) (a : A) (x : M) :
    rankOne z (RightDual.toHom f) (op a • x) = op a • rankOne z (RightDual.toHom f) x := by
  rw [rankOne_apply, rankOne_apply, RightDual.map_op_smul, op_mul, mul_smul]

namespace FullAction

variable (H : FullAction E A M)
include H

theorem ext {e e' : E} (h : ∀ w : M, e • w = e' • w) : e = e' :=
  sub_eq_zero.mp (H.faithful _ fun w => by rw [sub_smul, h, sub_self])

/-- The element of `E` acting as the rank-one map `w ↦ z · f(w)`. -/
def rho (z : M) (f : RightDual A M) : E :=
  (H.full _ (rankOne_op_smul z f)).choose

theorem rho_smul (z : M) (f : RightDual A M) (w : M) :
    H.rho z f • w = op (RightDual.toHom f w) • z :=
  (H.full _ (rankOne_op_smul z f)).choose_spec w

theorem rho_add_left (z z' : M) (f : RightDual A M) :
    H.rho (z + z') f = H.rho z f + H.rho z' f :=
  H.ext fun w => by rw [add_smul, rho_smul, rho_smul, rho_smul, smul_add]

theorem rho_add_right (z : M) (f f' : RightDual A M) :
    H.rho z (f + f') = H.rho z f + H.rho z f' :=
  H.ext fun w => by
    rw [add_smul, rho_smul, rho_smul, rho_smul, RightDual.toHom_add, AddMonoidHom.add_apply,
      op_add, add_smul]

theorem rho_zero_left (f : RightDual A M) : H.rho 0 f = 0 :=
  H.ext fun w => by rw [rho_smul, smul_zero, zero_smul]

theorem rho_zero_right (z : M) : H.rho z 0 = 0 :=
  H.ext fun w => by
    rw [rho_smul, zero_smul, show RightDual.toHom (0 : RightDual A M) = 0 from rfl,
      AddMonoidHom.zero_apply, op_zero, zero_smul]

theorem rho_balanced (a : A) (z : M) (f : RightDual A M) :
    H.rho (op a • z) f = H.rho z (a • f) :=
  H.ext fun w => by
    rw [rho_smul, rho_smul, RightDual.toHom_smul, smul_smul, op_mul]

theorem rho_smul_left (e : E) (z : M) (f : RightDual A M) : H.rho (e • z) f = e * H.rho z f :=
  H.ext fun w => by rw [rho_smul, mul_smul, rho_smul, smul_comm e]

theorem rho_op_smul (e : E) (z : M) (f : RightDual A M) : H.rho z (op e • f) = H.rho z f * e :=
  H.ext fun w => by rw [rho_smul, mul_smul, rho_smul, RightDual.toHom_op_smul]

theorem rho_mem {i k : ℤ} {z : M} (hz : z ∈ grading i) {f : RightDual A M} (hf : f ∈ grading k) :
    H.rho z f ∈ grading (i + k) :=
  H.mem_grading _ _ fun j w hw => by
    rw [rho_smul]
    have h := op_smul_mem_grading (RightDual.apply_mem_grading hf hw) hz
    rwa [show i + (j + k) = i + k + j by ring] at h

theorem d_rho {i k : ℤ} {z : M} (hz : z ∈ grading i) {f : RightDual A M} (hf : f ∈ grading k) :
    d (H.rho z f) = H.rho (d z) f + koszulSign i • H.rho z (d f) := by
  refine H.ext fun w => ?_
  induction w using DG.induction_on with
  | h_zero => rw [smul_zero, smul_zero]
  | h_add w w' hw hw' => rw [smul_add, smul_add, hw, hw']
  | @h_homogeneous j w =>
    have hL := d_smul (H.rho_mem hz hf) (w : M)
    have hdfw : d (RightDual.toHom f w) =
        RightDual.toHom (d f) w + koszulSign k • RightDual.toHom f (d (w : M)) := by
      rw [RightDual.d_apply_of_mem hf]; abel
    rw [rho_smul, d_op_smul hz, hdfw, rho_smul] at hL
    rw [add_smul, Units.smul_def, smul_assoc, rho_smul, rho_smul]
    rw [Units.smul_def (koszulSign k), MulOpposite.op_add, MulOpposite.op_smul, add_smul,
      smul_assoc, koszulSign_add] at hL
    refine (eq_sub_of_add_eq hL.symm).trans ?_
    rcases Int.units_eq_one_or (koszulSign i) with hi | hi <;>
      rcases Int.units_eq_one_or (koszulSign k) with hk | hk <;>
      simp only [hi, hk, Units.val_one, Units.val_neg, one_smul, neg_smul, one_mul, mul_one,
        neg_mul, neg_neg, smul_add, Units.neg_smul] <;>
      abel

/-! ### `M ⊗_A M^∨ ≅ E` -/

/-- The bi-additive map `(z, f) ↦ rho z f`. -/
def rhoHom : M →+ RightDual A M →+ E :=
  AddMonoidHom.mk' (fun z => AddMonoidHom.mk' (H.rho z) (H.rho_add_right z)) fun z z' => by
    ext f
    exact H.rho_add_left z z' f

/-- `z ⊗ f ↦ rho z f`. -/
def mulHom : TensorProductOver A M (RightDual A M) →+ E :=
  lift H.rhoHom fun a z f => H.rho_balanced a z f

@[simp] theorem mulHom_tmul (z : M) (f : RightDual A M) :
    H.mulHom (tmul A z f) = H.rho z f := rfl

theorem mulHom_smul (e : E) (t : TensorProductOver A M (RightDual A M)) :
    H.mulHom (e • t) = e * H.mulHom t := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, mul_zero]
  | tmul z f => rw [smul_tmul, mulHom_tmul, mulHom_tmul, rho_smul_left]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, mul_add]

theorem mulHom_op_smul (e : E) (t : TensorProductOver A M (RightDual A M)) :
    H.mulHom (op e • t) = H.mulHom t * e := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, zero_mul]
  | tmul z f => rw [op_smul_tmul_right, mulHom_tmul, mulHom_tmul, rho_op_smul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, add_mul]

theorem mulHom_mem {k : ℤ} {t : TensorProductOver A M (RightDual A M)} (ht : t ∈ grading k) :
    H.mulHom t ∈ grading k := by
  refine induction_on_mem_grading (P := fun t => H.mulHom t ∈ grading k) ?_ ?_ ?_ ?_ ht
  · rw [map_zero]; exact zero_mem _
  · intro i j z f hz hf hij
    rw [mulHom_tmul, ← hij]
    exact H.rho_mem hz hf
  · intro x y hx hy; rw [map_add]; exact add_mem hx hy
  · intro x hx; rw [map_neg]; exact neg_mem hx

theorem mulHom_d (t : TensorProductOver A M (RightDual A M)) : H.mulHom (d t) = d (H.mulHom t) := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [d_zero, map_zero, d_zero]
  | add x y hx hy => rw [d_add, map_add, hx, hy, map_add, d_add]
  | tmul z f =>
    induction z using DG.induction_on with
    | h_zero => rw [zero_tmul, d_zero, map_zero, d_zero]
    | h_add z z' hz hz' => rw [add_tmul, d_add, map_add, hz, hz', map_add, d_add]
    | @h_homogeneous i z =>
      induction f using DG.induction_on with
      | h_zero => rw [tmul_zero, d_zero, map_zero, d_zero]
      | h_add f f' hf hf' => rw [tmul_add, d_add, map_add, hf, hf', map_add, d_add]
      | @h_homogeneous k f =>
        rw [TensorProductOver.d_tmul_of_mem z.2, map_add, map_units_zsmul, mulHom_tmul, mulHom_tmul, mulHom_tmul,
          H.d_rho z.2 f.2]

variable {ι : Type*} [Fintype ι] (R : RightBasis A M ι)
include R

theorem mulHom_surjective : Function.Surjective H.mulHom := fun e => by
  refine ⟨∑ i, tmul A (e • R.b i) (R.δ i), H.ext fun w => ?_⟩
  rw [map_sum, Finset.sum_smul]
  simp only [mulHom_tmul, rho_smul, RightBasis.toHom_δ]
  conv_rhs => rw [← R.sum_coeff w]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => (smul_comm e _ _).symm

theorem mulHom_smul_basis [DecidableEq ι] (t : TensorProductOver A M (RightDual A M)) (j : ι) :
    H.mulHom t • R.b j = coeffTensor R j t := by
  conv_lhs => rw [eq_sum_coeffTensor R t]
  rw [map_sum, Finset.sum_smul, Finset.sum_eq_single j]
  · rw [mulHom_tmul, rho_smul, RightBasis.toHom_δ, R.coeff_basis, Pi.single_eq_same, op_one,
      one_smul]
  · intro i _ hij
    rw [mulHom_tmul, rho_smul, RightBasis.toHom_δ, R.coeff_basis, Pi.single_eq_of_ne hij, op_zero,
      zero_smul]
  · intro hj; exact absurd (Finset.mem_univ j) hj

theorem mulHom_injective : Function.Injective H.mulHom := by
  classical
  rw [injective_iff_map_eq_zero]
  intro t ht
  rw [eq_sum_coeffTensor R t]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← H.mulHom_smul_basis R t i, ht, zero_smul, zero_tmul]

/-- **`M ⊗_A M^∨ ≅ E`** as dg `E`-modules, `z ⊗ f ↦ rho z f`; it is also right `E`-linear
(`mulEquiv_op_smul`). -/
def mulEquiv : TensorProductOver A M (RightDual A M) ≃ᵈᵍ[E] E where
  toLinearEquiv := LinearEquiv.ofBijective
    { toFun := H.mulHom
      map_add' := map_add _
      map_smul' := fun e t => by rw [H.mulHom_smul, smul_eq_mul, RingHom.id_apply] }
    ⟨H.mulHom_injective R, H.mulHom_surjective R⟩
  map_mem' ht := H.mulHom_mem ht
  map_d' t := H.mulHom_d t

@[simp] theorem mulEquiv_tmul (z : M) (f : RightDual A M) :
    H.mulEquiv R (tmul A z f) = H.rho z f := rfl

theorem mulEquiv_op_smul (e : E) (t : TensorProductOver A M (RightDual A M)) :
    H.mulEquiv R (op e • t) = op e • H.mulEquiv R t := by
  change H.mulHom (op e • t) = op e • H.mulHom t
  rw [mulHom_op_smul, MulOpposite.smul_eq_mul_unop, unop_op]

end FullAction

/-! ### `M^∨ ⊗_E M ≅ A` -/

namespace FullAction

variable (H : FullAction E A M)

omit [DGRing E] in
/-- The evaluation `f ⊗ z ↦ f(z)`. -/
def evHom : TensorProductOver E (RightDual A M) M →+ A :=
  lift (RightDual.toHomAddHom A M) fun e f z => by
    change RightDual.toHom (op e • f) z = RightDual.toHom f (e • z)
    rw [RightDual.toHom_op_smul]

omit [DGRing E] in
@[simp] theorem evHom_tmul (f : RightDual A M) (z : M) : evHom (tmul E f z) = RightDual.toHom f z :=
  rfl

omit [DGRing E] in
theorem evHom_smul (a : A) (t : TensorProductOver E (RightDual A M) M) :
    evHom (a • t) = a * evHom t := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, mul_zero]
  | tmul f z => rw [smul_tmul, evHom_tmul, evHom_tmul, RightDual.toHom_smul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, mul_add]

omit [DGRing E] in
theorem evHom_op_smul (a : A) (t : TensorProductOver E (RightDual A M) M) :
    evHom (op a • t) = evHom t * a := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, zero_mul]
  | tmul f z => rw [op_smul_tmul_right, evHom_tmul, evHom_tmul, RightDual.map_op_smul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, add_mul]

omit [DGRing E] in
theorem evHom_mem {k : ℤ} {t : TensorProductOver E (RightDual A M) M} (ht : t ∈ grading k) :
    evHom t ∈ grading k := by
  refine induction_on_mem_grading (P := fun t => evHom t ∈ grading k) ?_ ?_ ?_ ?_ ht
  · rw [map_zero]; exact zero_mem _
  · intro i j f z hf hz hij
    rw [evHom_tmul, ← hij, add_comm]
    exact RightDual.apply_mem_grading hf hz
  · intro x y hx hy; rw [map_add]; exact add_mem hx hy
  · intro x hx; rw [map_neg]; exact neg_mem hx

omit [DGRing E] in
theorem evHom_d (t : TensorProductOver E (RightDual A M) M) : evHom (d t) = d (evHom t) := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [d_zero, map_zero, d_zero]
  | add x y hx hy => rw [d_add, map_add, hx, hy, map_add, d_add]
  | tmul f z =>
    induction f using DG.induction_on with
    | h_zero => rw [zero_tmul, d_zero, map_zero, d_zero]
    | h_add f f' hf hf' => rw [add_tmul, d_add, map_add, hf, hf', map_add, d_add]
    | @h_homogeneous k f =>
      rw [TensorProductOver.d_tmul_of_mem f.2, map_add, map_units_zsmul, evHom_tmul, evHom_tmul, evHom_tmul,
        RightDual.d_apply_of_mem f.2, sub_add_cancel]

variable {ι : Type*} [Fintype ι] (R : RightBasis A M ι)

theorem evHom_basis (a : A) (i : ι) : evHom (tmul E (a • R.δ i) (R.b i)) = a := by
  classical
  rw [evHom_tmul, RightDual.toHom_smul, RightBasis.toHom_δ, R.coeff_basis, Pi.single_eq_same,
    mul_one]

include H in
theorem eq_tmul_evHom (i : ι) (t : TensorProductOver E (RightDual A M) M) :
    t = tmul E (evHom t • R.δ i) (R.b i) := by
  classical
  induction t using TensorProductOver.induction_on with
  | zero => rw [map_zero, zero_smul, zero_tmul]
  | tmul f z =>
    have hz : H.rho z (R.δ i) • R.b i = z := by
      rw [rho_smul, RightBasis.toHom_δ, R.coeff_basis, Pi.single_eq_same, op_one, one_smul]
    have hf : op (H.rho z (R.δ i)) • f = RightDual.toHom f z • R.δ i := RightDual.ext fun w => by
      rw [RightDual.toHom_op_smul, rho_smul, RightDual.map_op_smul, RightDual.toHom_smul,
        RightBasis.toHom_δ]
    calc tmul E f z = tmul E f (H.rho z (R.δ i) • R.b i) := by rw [hz]
      _ = tmul E (op (H.rho z (R.δ i)) • f) (R.b i) := (op_smul_tmul _ _ _).symm
      _ = _ := by rw [hf, evHom_tmul]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    rw [map_add, add_smul, add_tmul]

include H R in
theorem evHom_injective (i : ι) : Function.Injective (evHom (E := E) (A := A) (M := M)) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  rw [H.eq_tmul_evHom R i t, ht, zero_smul, zero_tmul]

include R in
theorem evHom_surjective (i : ι) : Function.Surjective (evHom (E := E) (A := A) (M := M)) :=
  fun a => ⟨_, evHom_basis R a i⟩

include H in
/-- **`M^∨ ⊗_E M ≅ A`** as dg `A`-modules, `f ⊗ z ↦ f(z)`, for a nonempty basis; it is also
right `A`-linear (`evEquiv_op_smul`). -/
def evEquiv [Nonempty ι] : TensorProductOver E (RightDual A M) M ≃ᵈᵍ[A] A where
  toLinearEquiv := LinearEquiv.ofBijective
    { toFun := evHom
      map_add' := map_add _
      map_smul' := fun a t => by rw [evHom_smul, smul_eq_mul, RingHom.id_apply] }
    ⟨H.evHom_injective R (Classical.arbitrary ι), evHom_surjective (E := E) R (Classical.arbitrary ι)⟩
  map_mem' ht := evHom_mem ht
  map_d' t := evHom_d t

include H in
@[simp] theorem evEquiv_tmul [Nonempty ι] (f : RightDual A M) (z : M) :
    H.evEquiv R (tmul E f z) = RightDual.toHom f z := rfl

include H in
theorem evEquiv_op_smul [Nonempty ι] (a : A) (t : TensorProductOver E (RightDual A M) M) :
    H.evEquiv R (op a • t) = op a • H.evEquiv R t := by
  change evHom (op a • t) = op a • evHom t
  rw [evHom_op_smul, MulOpposite.smul_eq_mul_unop, unop_op]

end FullAction

end DG
