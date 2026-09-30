import DG.Module.End
import DG.Module.Right

/-!
# A dg module as a dg bimodule over its endomorphism dg ring

Let `A` be a dg ring and `M` a dg `A`-module. The endomorphism dg ring `END_A(M)`
(`DG.DGModule.END A M`, with product `f * g = (-1)^{|f||g|} • g ∘ f`) acts on `M` on the right by
the Koszul-signed evaluation `x · f = (-1)^{|f||x|} • f x` (`DG.DGModule.END.rightAction`). This
file shows that this makes `M` a dg `(A, END_A(M))`-bimodule, and that right actions of dg rings
on `M` commuting with `A` are the same as dg ring homomorphisms into `END_A(M)`.

## Main definitions and results

* `DG.DGModule.END.instModuleOp`: the right action as a module structure
  `Module (END A M)ᵐᵒᵖ M`, `op F • x = x · F`.
* `DG.DGModule.END.instDGRightModule`: `M` is a dg right `END A M`-module; the right Leibniz
  rule `d (x · F) = d x · F + (-1)^{|x|} • (x · d F)` is a consequence of the definition
  `δ f = d ∘ f - (-1)^{|f|} • f ∘ d` of the differential of the Hom complex.
* `DG.DGModule.END.instSMulCommClass`, `DG.DGModule.END.instDGBimodule`: the actions of `A` and
  of `END A M` commute, by the signed `A`-linearity of cochains, so `M` is a dg
  `(A, END A M)`-bimodule.
* `DG.DGModule.END.ext_op_smul`: `M` is a faithful right `END A M`-module.
* `DG.DGBimodule.toEND`: for a dg `(A, B)`-bimodule `M`, the ring homomorphism
  `B →+* END A M` sending `b` to the endomorphism acting by `x ↦ x • b` (on `b ∈ Bⁿ`, the
  cochain `x ↦ (-1)^{n |x|} • (x • b)`); it preserves degrees and differentials
  (`DG.DGBimodule.toEND_mem_grading`, `DG.DGBimodule.toEND_d`).
* `DG.DGBimodule.endEquivOfGenerator`: if `m₀ ∈ M` generates `M` as a left `A`-module,
  `b ↦ m₀ • b` is injective and every `m₀ · F` is of the form `m₀ • b`, then `toEND` is an
  isomorphism of dg rings `END A M ≃+* B`. This is applied to corner rings in
  `DG.Module.CornerEnd`.

## Instances

The instances of this file are on `(END A M)ᵐᵒᵖ`, which is not the multiplicative opposite of
any other ring acting on `M`, so they do not overlap with existing actions (for instance the
right action `Module Aᵐᵒᵖ A` of a ring on itself when `M = A`).
-/

open DirectSum MulOpposite

namespace DG

namespace DGModule.END

section Module

variable {A : Type*} {M : Type*} [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]

/-- The right action of `END A M` on `M`, `op F • x = x · F`, the Koszul-signed evaluation
`x · f = (-1)^{|f||x|} • f x` on homogeneous elements (`DG.DGModule.END.rightAction`). -/
instance instModuleOp : Module (END A M)ᵐᵒᵖ M where
  smul F x := signedEval A M F.unop x
  one_smul x := by
    show signedEval A M (unop 1) x = x
    rw [unop_one, signedEval_one]; rfl
  mul_smul F G x := by
    show signedEval A M (unop (F * G)) x = signedEval A M F.unop (signedEval A M G.unop x)
    rw [unop_mul, signedEval_mul]; rfl
  smul_zero F := map_zero (signedEval A M F.unop)
  smul_add F := map_add (signedEval A M F.unop)
  add_smul F G x := by
    show signedEval A M (unop (F + G)) x = signedEval A M F.unop x + signedEval A M G.unop x
    rw [unop_add, map_add]; rfl
  zero_smul x := by
    show signedEval A M (unop 0) x = 0
    rw [unop_zero, map_zero]; rfl

theorem op_smul_eq_signedEval (F : END A M) (x : M) : op F • x = signedEval A M F x := rfl

theorem op_smul_eq_rightAction (F : END A M) (x : M) :
    op F • x = (rightAction A M F).unop x := rfl

theorem op_of_smul {n : ℤ} (f : Cochain A M M n) {i : ℤ} {x : M} (hx : x ∈ grading i) :
    op (DirectSum.of (fun n => Cochain A M M n) n f) • x = koszulSign (n * i) • f x := by
  rw [op_smul_eq_signedEval, signedEval_of, Cochain.signedApply_of_mem f hx]

/-- The homogeneous components of `x · F`: for `x` of degree `i`, the component of degree
`i + n` of `x · F` is `(-1)^{n i} • F n x`. -/
theorem decompose_op_smul (F : END A M) (n : ℤ) {i : ℤ} {x : M} (hx : x ∈ grading i) :
    (decompose (grading (M := M)) (op F • x) (i + n) : M) = koszulSign (n * i) • F n x := by
  induction F using DirectSum.induction_on with
  | zero => simp [Cochain.zero_apply]
  | of k f =>
    have hf := units_smul_mem_grading (koszulSign (k * i)) (f.map_mem hx)
    rw [op_of_smul f hx]
    by_cases hk : k = n
    · subst hk
      rw [DirectSum.of_eq_same, decompose_of_mem_same _ hf]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hk), decompose_of_mem_ne _ hf (by omega),
        Cochain.zero_apply, smul_zero]
  | add F G hF hG =>
    rw [op_add, add_smul, decompose_add, DirectSum.add_apply, AddMemClass.coe_add, hF, hG,
      DirectSum.add_apply, Cochain.add_apply, smul_add]

/-- `M` is a faithful right `END A M`-module: an element of `END A M` is determined by its
action on `M`. -/
theorem ext_op_smul {F G : END A M} (h : ∀ x : M, op F • x = op G • x) : F = G := by
  ext n x
  induction x using DG.induction_on with
  | h_zero => simp
  | h_homogeneous x =>
    have hF := decompose_op_smul F n x.2
    rw [h, decompose_op_smul G n x.2] at hF
    exact (smul_left_cancel_iff _).mp hF.symm
  | h_add x y hx hy => rw [map_add, map_add, hx, hy]

theorem op_smul_injective : Function.Injective fun F : END A M => (op F • · : M → M) :=
  fun _ _ h => ext_op_smul fun x => congrFun h x

end Module

section DG

variable {A : Type*} {M : Type*} [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]

/-- `M` is a dg right `END A M`-module. The right Leibniz rule
`d (x · F) = d x · F + (-1)^{|x|} • (x · d F)` follows from the definition of the differential
of the Hom complex, `δ f = d ∘ f - (-1)^{|f|} • f ∘ d`. -/
instance instDGRightModule : DGRightModule (END A M) M where
  op_smul_mem' := by
    rintro i j _ x ⟨f, rfl⟩ hx
    rw [op_of_smul f hx]
    exact units_smul_mem_grading _ (f.map_mem hx)
  d_op_smul' {j x} hx F := by
    induction F using DirectSum.induction_on with
    | zero => simp
    | of n f =>
      rw [HOM.d_of, op_of_smul f hx, op_of_smul f (d_mem hx), op_of_smul _ hx,
        δ_apply n (n + 1) rfl, d_units_smul]
      simp only [mul_add, add_mul, mul_one, one_mul, koszulSign_add, smul_sub, smul_smul]
      rcases Int.units_eq_one_or (koszulSign n) with h₁ | h₁ <;>
      rcases Int.units_eq_one_or (koszulSign j) with h₂ | h₂ <;>
      rcases Int.units_eq_one_or (koszulSign (n * j)) with h₃ | h₃ <;>
      simp [h₁, h₂, h₃]
    | add F G hF hG =>
      rw [op_add, add_smul, d_add, hF, hG, d_add, op_add, add_smul, add_smul, smul_add]
      abel

/-- The differential of `END A M` in terms of the action: for `x` of degree `j`,
`x · d F = (-1)^{j} • (d (x · F) - d x · F)`. -/
theorem op_d_smul {j : ℤ} {x : M} (hx : x ∈ grading j) (F : END A M) :
    op (d F) • x = koszulSign j • (d (op F • x) - op F • d x) := by
  rw [d_op_smul hx, add_sub_cancel_left, smul_smul, Int.units_mul_self, one_smul]

/-- The left action of `A` and the right action of `END A M` on `M` commute:
`a • (x · F) = (a • x) · F`, by the Koszul-signed `A`-linearity of cochains. -/
instance instSMulCommClass : SMulCommClass A (END A M)ᵐᵒᵖ M where
  smul_comm a F x := by
    induction F using MulOpposite.rec' with | _ F => ?_
    induction F using DirectSum.induction_on with
    | zero => simp
    | of n f =>
      induction a using DG.induction_on with
      | h_zero => simp
      | h_homogeneous a =>
        induction x using DG.induction_on with
        | h_zero => simp
        | h_homogeneous x =>
          rw [op_of_smul f x.2, op_of_smul f (smul_mem_grading a.2 x.2), f.map_smul a.2,
            smul_smul, smul_comm, mul_add, koszulSign_add, mul_comm (koszulSign (n * _)),
            mul_assoc, Int.units_mul_self, mul_one]
        | h_add x y hx hy => rw [smul_add, smul_add, smul_add, smul_add, hx, hy]
      | h_add a b ha hb => rw [add_smul, add_smul, smul_add, ha, hb]
    | add F G hF hG => rw [op_add, add_smul, add_smul, smul_add, hF, hG]

/-- If `m₀` generates `M` as a left `A`-module, two elements of `END A M` with the same
action on `m₀` are equal. -/
theorem eq_of_op_smul_eq {m₀ : M} (hgen : ∀ x : M, ∃ a : A, a • m₀ = x) {F G : END A M}
    (h : op F • m₀ = op G • m₀) : F = G :=
  ext_op_smul fun x => by
    obtain ⟨a, rfl⟩ := hgen x
    rw [← smul_comm a (op F) m₀, h, smul_comm]

/-- A dg `A`-module `M` is a dg `(A, END_A(M))`-bimodule. -/
instance instDGBimodule : DGBimodule A (END A M) M := DGBimodule.mk'

end DG

end DGModule.END

/-! ### Right actions as dg ring homomorphisms into `END` -/

/-- A graded additive map (one preserving the degrees) commutes with the homogeneous
projections. -/
theorem coe_decompose_map {M N : Type*} [AddCommGroup M] [DGAddCommGroup M] [AddCommGroup N]
    [DGAddCommGroup N] (f : M →+ N) (hf : ∀ {i : ℤ} {x : M}, x ∈ grading i → f x ∈ grading i)
    (x : M) (n : ℤ) :
    (decompose (grading (M := N)) (f x) n : N) = f (decompose (grading (M := M)) x n) := by
  induction x using DG.induction_on with
  | h_zero => simp
  | @h_homogeneous i x =>
    by_cases hi : i = n
    · subst hi
      rw [decompose_of_mem_same _ (hf x.2), decompose_of_mem_same _ x.2]
    · rw [decompose_of_mem_ne _ (hf x.2) hi, decompose_of_mem_ne _ x.2 hi, map_zero]
  | h_add x y hx hy =>
    rw [map_add, decompose_add, DirectSum.add_apply, AddMemClass.coe_add, hx, hy,
      decompose_add, DirectSum.add_apply, AddMemClass.coe_add, map_add]

namespace DGBimodule

section SignedRightMul

variable {B : Type*} (M : Type*) [Ring B] [AddCommGroup M] [DGAddCommGroup M] [Module Bᵐᵒᵖ M]

/-- The Koszul-signed right multiplication by `b` of degree `n`: the additive map sending
`x ∈ Mʲ` to `(-1)^{n j} • (x • b)`. -/
def signedRightMul (n : ℤ) (b : B) : M →+ M :=
  liftHomogeneous (grading (M := M)) fun j =>
    koszulSign (n * j) •
      (DistribSMul.toAddMonoidHom M (op b)).comp (AddSubgroup.subtype (grading j))

variable {M}

theorem signedRightMul_of_mem (n : ℤ) (b : B) {j : ℤ} {x : M} (hx : x ∈ grading j) :
    signedRightMul M n b x = koszulSign (n * j) • (op b • x) := by
  rw [signedRightMul, liftHomogeneous_of_mem _ _ hx, Units.smul_def, Units.smul_def]
  rfl

theorem signedRightMul_add (n : ℤ) (b b' : B) :
    signedRightMul M n (b + b') = signedRightMul M n b + signedRightMul M n b' :=
  decompose_addHom_ext (grading (M := M)) fun _ x => by
    rw [AddMonoidHom.add_apply, signedRightMul_of_mem _ _ x.2, signedRightMul_of_mem _ _ x.2,
      signedRightMul_of_mem _ _ x.2, op_add, add_smul, smul_add]

theorem signedRightMul_zero (n : ℤ) : signedRightMul M n (0 : B) = 0 :=
  decompose_addHom_ext (grading (M := M)) fun _ x => by
    rw [AddMonoidHom.zero_apply, signedRightMul_of_mem _ _ x.2, op_zero, zero_smul, smul_zero]

end SignedRightMul

variable (A : Type*) {B : Type*} (M : Type*) [Ring A] [DGAddCommGroup A] [Ring B]
  [DGAddCommGroup B] [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [DGBimodule A B M]

/-- The right multiplication by a homogeneous `b ∈ Bⁿ` as a cochain of degree `n`,
`x ↦ (-1)^{n |x|} • (x • b)`; its right action on `M` is `x · F = x • b`
(`DG.DGBimodule.op_toEND_smul`). -/
def rightMulCochain {n : ℤ} (b : grading (M := B) n) : Cochain A M M n where
  toAddMonoidHom := signedRightMul M n (b : B)
  map_mem' i x hx := by
    show signedRightMul M n (b : B) x ∈ _
    rw [signedRightMul_of_mem _ _ hx]
    exact units_smul_mem_grading _ (op_smul_mem_grading b.2 hx)
  map_smul' {i a} ha x := by
    show signedRightMul M n (b : B) (a • x) = _ • (a • signedRightMul M n (b : B) x)
    induction x using DG.induction_on with
    | h_zero => simp
    | h_homogeneous x =>
      rw [signedRightMul_of_mem _ _ (smul_mem_grading ha x.2), signedRightMul_of_mem _ _ x.2,
        ← DGBimodule.smul_op_smul a (b : B) (x : M), smul_comm a (koszulSign (n * _)), smul_smul,
        mul_add,
        koszulSign_add]
    | h_add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add, smul_add]

@[simp]
theorem rightMulCochain_apply {n : ℤ} (b : grading (M := B) n) (x : M) :
    rightMulCochain A M b x = signedRightMul M n (b : B) x := rfl

/-- `DG.DGBimodule.rightMulCochain` as an additive map. -/
def rightMulCochainHom (n : ℤ) : grading (M := B) n →+ Cochain A M M n where
  toFun := rightMulCochain A M
  map_zero' := Cochain.ext fun x => by
    rw [rightMulCochain_apply, ZeroMemClass.coe_zero, signedRightMul_zero]; rfl
  map_add' b b' := Cochain.ext fun x => by
    rw [rightMulCochain_apply, AddMemClass.coe_add, signedRightMul_add]; rfl

/-- The additive map `B →+ END A M` underlying `DG.DGBimodule.toEND`. -/
def toENDAddHom : B →+ DGModule.END A M :=
  liftHomogeneous (grading (M := B)) fun n =>
    (DirectSum.of (fun n => Cochain A M M n) n).comp (rightMulCochainHom A M n)

variable {A M}

theorem toENDAddHom_of_mem {n : ℤ} {b : B} (hb : b ∈ grading n) :
    toENDAddHom A M b = DirectSum.of (fun n => Cochain A M M n) n (rightMulCochain A M ⟨b, hb⟩) :=
  liftHomogeneous_of_mem _ _ hb

theorem op_toENDAddHom_smul (b : B) (x : M) : op (toENDAddHom A M b) • x = op b • x := by
  induction b using DG.induction_on with
  | h_zero => simp
  | @h_homogeneous n b =>
    rw [toENDAddHom_of_mem b.2]
    induction x using DG.induction_on with
    | h_zero => simp
    | h_homogeneous x =>
      rw [DGModule.END.op_of_smul _ x.2, rightMulCochain_apply, signedRightMul_of_mem _ _ x.2,
        smul_smul, Int.units_mul_self, one_smul]
    | h_add x y hx hy => rw [smul_add, smul_add, hx, hy]
  | h_add b b' hb hb' => rw [map_add, op_add, add_smul, hb, hb', op_add, add_smul]

variable (A M)

/-- The right action of `B` on a dg `(A, B)`-bimodule `M` as a ring homomorphism
`B →+* END_A(M)`: `b` is sent to the endomorphism whose right action on `M` is `x · b`
(`DG.DGBimodule.op_toEND_smul`); on `b ∈ Bⁿ` it is the cochain `x ↦ (-1)^{n |x|} • (x • b)` of
degree `n`. It preserves the degrees (`DG.DGBimodule.toEND_mem_grading`) and commutes with the
differentials (`DG.DGBimodule.toEND_d`), so it is a morphism of dg rings. -/
def toEND : B →+* DGModule.END A M where
  __ := toENDAddHom A M
  map_one' := DGModule.END.ext_op_smul fun x => by
    show op (toENDAddHom A M 1) • x = _
    rw [op_toENDAddHom_smul, op_one, one_smul, op_one, one_smul]
  map_mul' b b' := DGModule.END.ext_op_smul fun x => by
    show op (toENDAddHom A M (b * b')) • x =
      op (toENDAddHom A M b * toENDAddHom A M b') • x
    rw [op_toENDAddHom_smul, op_mul, mul_smul, op_mul, mul_smul, op_toENDAddHom_smul,
      op_toENDAddHom_smul]

variable {A M}

@[simp]
theorem op_toEND_smul (b : B) (x : M) : op (toEND A M b) • x = op b • x :=
  op_toENDAddHom_smul b x

theorem toEND_of_mem {n : ℤ} {b : B} (hb : b ∈ grading n) :
    toEND A M b = DirectSum.of (fun n => Cochain A M M n) n (rightMulCochain A M ⟨b, hb⟩) :=
  toENDAddHom_of_mem hb

theorem toEND_mem_grading {n : ℤ} {b : B} (hb : b ∈ grading n) : toEND A M b ∈ grading n :=
  ⟨_, (toEND_of_mem hb).symm⟩

/-- `DG.DGBimodule.toEND` commutes with the differentials. -/
theorem toEND_d (b : B) : toEND A M (d b) = d (toEND A M b) := by
  refine DGModule.END.ext_op_smul fun x => ?_
  induction x using DG.induction_on with
  | h_zero => simp
  | h_homogeneous x =>
    rw [DGModule.END.op_d_smul x.2, op_toEND_smul, op_toEND_smul, op_toEND_smul,
      d_op_smul x.2 b, add_sub_cancel_left, smul_smul, Int.units_mul_self, one_smul]
  | h_add x y hx hy => rw [smul_add, smul_add, hx, hy]

theorem coe_decompose_toEND (b : B) (n : ℤ) :
    (decompose (grading (M := DGModule.END A M)) (toEND A M b) n : DGModule.END A M) =
      toEND A M (decompose (grading (M := B)) b n : B) :=
  coe_decompose_map (toEND A M).toAddMonoidHom (fun hb => toEND_mem_grading hb) b n

theorem toEND_mem_grading_iff (hinj : Function.Injective (toEND A M : B → DGModule.END A M))
    {n : ℤ} {b : B} : toEND A M b ∈ grading n ↔ b ∈ grading n := by
  refine ⟨fun h => ?_, toEND_mem_grading⟩
  have h' := decompose_of_mem_same _ h
  rw [coe_decompose_toEND] at h'
  rw [← hinj h']
  exact Subtype.property _

/-! ### Endomorphism rings of cyclic bimodules -/

variable (A M)

/-- Let `M` be a dg `(A, B)`-bimodule and `m₀ ∈ M` an element generating `M` as a left
`A`-module and such that `b ↦ m₀ • b` is injective. Given `φ : END_A(M) → B` with
`m₀ · F = m₀ • φ F` for all `F`, the ring homomorphism `DG.DGBimodule.toEND : B →+* END_A(M)` is
an isomorphism with inverse `φ`; this is the ring isomorphism `END_A(M) ≃+* B` given by `φ`.
It is an isomorphism of dg rings: it preserves the degrees
(`DG.DGBimodule.endEquivOfGenerator_mem_grading_iff`) and the differentials
(`DG.DGBimodule.endEquivOfGenerator_d`). -/
def endEquivOfGenerator (m₀ : M) (hgen : ∀ x : M, ∃ a : A, a • m₀ = x)
    (hinj : Function.Injective fun b : B => op b • m₀) (φ : DGModule.END A M → B)
    (hφ : ∀ F, op (φ F) • m₀ = op F • m₀) : DGModule.END A M ≃+* B :=
  RingEquiv.symm
    { toEND A M with
      invFun := φ
      left_inv := fun b => hinj (by
        show op (φ (toEND A M b)) • m₀ = op b • m₀
        rw [hφ, op_toEND_smul])
      right_inv := fun F => DGModule.END.eq_of_op_smul_eq hgen (by
        show op (toEND A M (φ F)) • m₀ = op F • m₀
        rw [op_toEND_smul, hφ]) }

variable {A M} {m₀ : M} {hgen : ∀ x : M, ∃ a : A, a • m₀ = x}
  {hinj : Function.Injective fun b : B => op b • m₀} {φ : DGModule.END A M → B}
  {hφ : ∀ F, op (φ F) • m₀ = op F • m₀}

@[simp]
theorem endEquivOfGenerator_apply (F : DGModule.END A M) :
    endEquivOfGenerator A M m₀ hgen hinj φ hφ F = φ F := rfl

@[simp]
theorem endEquivOfGenerator_symm_apply (b : B) :
    (endEquivOfGenerator A M m₀ hgen hinj φ hφ).symm b = toEND A M b := rfl

/-- The isomorphism `DG.DGBimodule.endEquivOfGenerator` commutes with the differentials. -/
theorem endEquivOfGenerator_d (F : DGModule.END A M) :
    endEquivOfGenerator A M m₀ hgen hinj φ hφ (d F) =
      d (endEquivOfGenerator A M m₀ hgen hinj φ hφ F) := by
  apply (endEquivOfGenerator A M m₀ hgen hinj φ hφ).symm.injective
  rw [RingEquiv.symm_apply_apply, endEquivOfGenerator_symm_apply, toEND_d,
    ← endEquivOfGenerator_symm_apply (hgen := hgen) (hinj := hinj) (hφ := hφ),
    RingEquiv.symm_apply_apply]

/-- The isomorphism `DG.DGBimodule.endEquivOfGenerator` preserves the degrees. -/
theorem endEquivOfGenerator_mem_grading_iff {n : ℤ} {F : DGModule.END A M} :
    endEquivOfGenerator A M m₀ hgen hinj φ hφ F ∈ grading n ↔ F ∈ grading n := by
  have hinj' : Function.Injective (toEND A M : B → DGModule.END A M) :=
    (endEquivOfGenerator A M m₀ hgen hinj φ hφ).symm.injective
  conv_rhs => rw [← (endEquivOfGenerator A M m₀ hgen hinj φ hφ).symm_apply_apply F]
  rw [endEquivOfGenerator_symm_apply, toEND_mem_grading_iff hinj']

end DGBimodule

end DG
