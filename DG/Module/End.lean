import DG.Module.Hom

/-!
# The endomorphism dg ring of a dg module

Let `A` be a dg ring and `M` a dg `A`-module. This file makes the Hom complex
`END_A(M) = HOM_A(M, M)` (`DG.DGModule.END A M`) into a dg ring acting on `M` on the right.

## Main definitions and results

* `DG.DGModule.END A M := HOM A M M`, a `Ring` through the `DirectSum.GRing` instance
  `DG.DGModule.END.instGRing`, whose product on homogeneous elements `f` of degree `m` and `g` of
  degree `n` is
  `f * g = (-1)^{m n} • g ∘ f` (`DG.DGModule.END.of_mul_of`).
* `DG.DGModule.END.instDGRing`: `END A M` is a dg ring; the Leibniz rule
  `d (f * g) = d f * g + (-1)^{|f|} • (f * d g)` is `DG.DGModule.END.d_of_mul_of`.
* `DG.DGModule.END.rightAction`: the right action of `END A M` on `M`,
  `x · f = (-1)^{|f||x|} • f x` for homogeneous `f` and `x`, as a ring homomorphism
  `END A M →+* (AddMonoid.End M)ᵐᵒᵖ`.

## Conventions

The product is fixed by the requirement that `END A M` act on `M` on the right by
`x · f = (-1)^{|f||x|} • f x` (the convention of `ROADMAP.md`, item 2.3): the identity
`(x · f) · g = x · (f * g)` forces `f * g = (-1)^{|f||g|} • g ∘ f`. With this product the
differential `δ` of the Hom complex satisfies the Leibniz rule, as it does for the composition
product `f * g = f ∘ g`, but not for the unsigned diagrammatic product `g ∘ f` used by
`DG.GradedEND` (which carries no differential). Thus `END A M` is the graded opposite
(with the Koszul-signed opposite product) of the composition dg ring.
-/

open DirectSum

namespace DG

namespace DGModule

section Ring

variable (A : Type*) (M : Type*) [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]

/-- The endomorphism dg ring `END_A(M) = HOM_A(M, M)`, with product
`f * g = (-1)^{|f||g|} • g ∘ f` on homogeneous elements. -/
abbrev END : Type _ := HOM A M M

namespace END

variable {A M}

/-- The graded product of `END A M`: for `f` of degree `m` and `g` of degree `n`,
`f * g = (-1)^{m n} • g ∘ f`. -/
instance instGMul : GradedMonoid.GMul fun n => Cochain A M M n :=
  ⟨fun {m n} f g => koszulSign (m * n) • g.comp f rfl⟩

/-- The graded unit of `END A M` is the identity. -/
instance instGOne : GradedMonoid.GOne fun n => Cochain A M M n := ⟨Cochain.id A M⟩

theorem gMul_def {m n : ℤ} (f : Cochain A M M m) (g : Cochain A M M n) :
    (GradedMonoid.GMul.mul f g : Cochain A M M (m + n)) = koszulSign (m * n) • g.comp f rfl :=
  rfl

theorem gOne_def : (GradedMonoid.GOne.one : Cochain A M M 0) = Cochain.id A M := rfl

theorem gMul_apply {m n : ℤ} (f : Cochain A M M m) (g : Cochain A M M n) (x : M) :
    (GradedMonoid.GMul.mul f g : Cochain A M M (m + n)) x = koszulSign (m * n) • g (f x) :=
  rfl

variable (A M)

/-- The cochains `Cochain A M M n` form a graded ring for the product
`f * g = (-1)^{|f||g|} • g ∘ f`. -/
instance instGRing : DirectSum.GRing fun n => Cochain A M M n where
  mul_zero _ := by rw [gMul_def, Cochain.zero_comp, smul_zero]
  zero_mul _ := by rw [gMul_def, Cochain.comp_zero, smul_zero]
  mul_add _ _ _ := by rw [gMul_def, gMul_def, gMul_def, Cochain.add_comp, smul_add]
  add_mul _ _ _ := by rw [gMul_def, gMul_def, gMul_def, Cochain.comp_add, smul_add]
  one_mul f := Sigma.ext (zero_add _) (Cochain.heq_of_forall (zero_add _) fun x => by
    show koszulSign (0 * f.1) • f.2 x = f.2 x
    rw [zero_mul, koszulSign, Int.negOnePow_zero, one_smul])
  mul_one f := Sigma.ext (add_zero _) (Cochain.heq_of_forall (add_zero _) fun x => by
    show koszulSign (f.1 * 0) • f.2 x = f.2 x
    rw [mul_zero, koszulSign, Int.negOnePow_zero, one_smul])
  mul_assoc f g h := Sigma.ext (add_assoc _ _ _) (Cochain.heq_of_forall (add_assoc _ _ _)
    fun x => by
      show koszulSign ((f.1 + g.1) * h.1) • h.2 (koszulSign (f.1 * g.1) • g.2 (f.2 x)) =
        koszulSign (f.1 * (g.1 + h.1)) • (koszulSign (g.1 * h.1) • h.2 (g.2 (f.2 x)))
      rw [Cochain.map_units_smul, smul_smul, smul_smul, add_mul, mul_add, koszulSign_add,
        koszulSign_add]
      congr 1
      ac_rfl)
  natCast k := k • Cochain.id A M
  natCast_zero := zero_nsmul _
  natCast_succ k := succ_nsmul _ k
  intCast k := k • Cochain.id A M
  intCast_ofNat k := natCast_zsmul _ k
  intCast_negSucc_ofNat k := negSucc_zsmul _ k

noncomputable example : Ring (END A M) := inferInstance

variable {A M}

theorem one_def : (1 : END A M) = DirectSum.of (fun n => Cochain A M M n) 0 (Cochain.id A M) :=
  rfl

/-- The product of homogeneous elements of `END A M`: `f * g = (-1)^{m n} • g ∘ f`. -/
theorem of_mul_of {m n : ℤ} (f : Cochain A M M m) (g : Cochain A M M n) :
    (DirectSum.of (fun n => Cochain A M M n) m f * DirectSum.of _ n g : END A M) =
      DirectSum.of _ (m + n) (koszulSign (m * n) • g.comp f rfl) :=
  DirectSum.of_mul_of f g

end END

end Ring

section DGRing

variable (A : Type*) (M : Type*) [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]

namespace END

variable {A M}

/-- The Leibniz rule for the product of two homogeneous elements of `END A M`. -/
theorem d_of_mul_of {m n : ℤ} (f : Cochain A M M m) (g : Cochain A M M n) :
    d (DirectSum.of (fun n => Cochain A M M n) m f * DirectSum.of _ n g : END A M) =
      d (DirectSum.of (fun n => Cochain A M M n) m f : END A M) * DirectSum.of _ n g +
        koszulSign m • (DirectSum.of (fun n => Cochain A M M n) m f *
          d (DirectSum.of (fun n => Cochain A M M n) n g : END A M)) := by
  rw [of_mul_of, HOM.d_of, HOM.d_of, HOM.d_of, of_mul_of, of_mul_of,
    HOM.of_congr (show m + 1 + n = m + n + 1 by ring)
      (g := koszulSign ((m + 1) * n) • g.comp (δ m (m + 1) f) (by ring)) (fun _ => rfl),
    HOM.of_congr (show m + (n + 1) = m + n + 1 by ring)
      (g := koszulSign (m * (n + 1)) • (δ n (n + 1) g).comp f (by ring)) (fun _ => rfl),
    ← HOM.of_units_smul, ← map_add]
  congr 1
  rw [δ_units_smul, δ_comp f g rfl (m + 1) (n + 1) (m + n + 1) rfl rfl rfl]
  ext x
  simp only [Cochain.add_apply, Cochain.units_smul_apply, Cochain.comp_apply, smul_add,
    smul_smul, add_mul, mul_add, one_mul, mul_one, koszulSign_add, Int.units_mul_self]
  rw [mul_left_comm, Int.units_mul_self, mul_one, add_comm]

variable (A M)

/-- `END A M` is a dg ring: its grading is a ring grading and the differential of the Hom
complex satisfies the graded Leibniz rule for the product `f * g = (-1)^{|f||g|} • g ∘ f`. -/
noncomputable instance instDGRing : DGRing (END A M) where
  toGradedMonoid := inferInstanceAs (SetLike.GradedMonoid (summand fun n => Cochain A M M n))
  d_mul' := by
    rintro n _ ⟨f, rfl⟩ b
    induction b using DirectSum.induction_on with
    | zero => simp
    | of m g => exact d_of_mul_of f g
    | add b b' hb hb' => rw [mul_add, d_add, hb, hb', d_add, mul_add, mul_add, smul_add]; abel

end END

end DGRing

end DGModule

/-! ### The right action of `END A M` on `M` -/

namespace Cochain

variable {A : Type*} {M N : Type*} [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N]

/-- The Koszul-signed evaluation of a cochain `z` of degree `n`: the additive map sending
`x ∈ Mⁱ` to `(-1)^{n i} • z x`. -/
def signedApply {n : ℤ} (z : Cochain A M N n) : M →+ N :=
  liftHomogeneous (grading (M := M)) fun i =>
    koszulSign (n * i) • (z : M →+ N).comp (AddSubgroup.subtype (grading i))

theorem signedApply_of_mem {n : ℤ} (z : Cochain A M N n) {i : ℤ} {x : M}
    (hx : x ∈ grading i) : z.signedApply x = koszulSign (n * i) • z x := by
  rw [signedApply, liftHomogeneous_of_mem _ _ hx, Units.smul_def, Units.smul_def]
  rfl

variable (A M N) in
/-- `Cochain.signedApply` as an additive map. -/
def signedApplyHom (n : ℤ) : Cochain A M N n →+ (M →+ N) where
  toFun := signedApply
  map_zero' := decompose_addHom_ext (grading (M := M)) fun i x => by
    rw [signedApply_of_mem _ x.2]; simp
  map_add' z₁ z₂ := decompose_addHom_ext (grading (M := M)) fun i x => by
    simp [signedApply_of_mem _ x.2, smul_add]

@[simp]
theorem signedApplyHom_apply {n : ℤ} (z : Cochain A M N n) :
    signedApplyHom A M N n z = z.signedApply := rfl

end Cochain

namespace DGModule.END

variable {A : Type*} {M : Type*} [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]

variable (A M) in
/-- The Koszul-signed evaluation of `END A M` on `M`, as an additive map: on a homogeneous `f`
it is `Cochain.signedApply f`, `x ↦ (-1)^{|f||x|} • f x`. -/
def signedEval : END A M →+ (M →+ M) :=
  DirectSum.toAddMonoid fun n => Cochain.signedApplyHom A M M n

@[simp]
theorem signedEval_of {n : ℤ} (f : Cochain A M M n) :
    signedEval A M (DirectSum.of (fun n => Cochain A M M n) n f) = f.signedApply := by
  rw [signedEval, DirectSum.toAddMonoid_of]; rfl

theorem signedEval_of_mul_of {m n : ℤ} (f : Cochain A M M m) (g : Cochain A M M n) :
    signedEval A M (DirectSum.of (fun n => Cochain A M M n) m f * DirectSum.of _ n g : END A M) =
      g.signedApply.comp f.signedApply := by
  rw [of_mul_of, signedEval_of]
  refine decompose_addHom_ext (grading (M := M)) fun i x => ?_
  show _ = g.signedApply (f.signedApply x)
  have hu (u : ℤˣ) (y : M) : g.signedApply (u • y) = u • g.signedApply y := by
    rw [Units.smul_def, Units.smul_def, map_zsmul]
  rw [Cochain.signedApply_of_mem _ x.2, Cochain.signedApply_of_mem _ x.2, hu,
    Cochain.signedApply_of_mem _ (f.map_mem x.2), Cochain.units_smul_apply, Cochain.comp_apply,
    smul_smul, smul_smul]
  congr 1
  simp only [← koszulSign_add]
  congr 1
  ring

@[simp]
theorem signedEval_one : signedEval A M 1 = AddMonoidHom.id M := by
  rw [one_def, signedEval_of]
  refine decompose_addHom_ext (grading (M := M)) fun i x => ?_
  rw [Cochain.signedApply_of_mem _ x.2, zero_mul, koszulSign, Int.negOnePow_zero, one_smul]
  rfl

/-- The signed evaluation is anti-multiplicative, `x · (F * G) = (x · F) · G`. -/
theorem signedEval_mul (F G : END A M) :
    signedEval A M (F * G) = (signedEval A M G).comp (signedEval A M F) := by
  induction F using DirectSum.induction_on with
  | zero => simp
  | of m f =>
    induction G using DirectSum.induction_on with
    | zero => simp
    | of n g => rw [signedEval_of_mul_of, signedEval_of, signedEval_of]
    | add G₁ G₂ h₁ h₂ => simp [mul_add, h₁, h₂, AddMonoidHom.add_comp]
  | add F₁ F₂ h₁ h₂ => simp [add_mul, h₁, h₂, AddMonoidHom.comp_add]

variable (A M) in
/-- The right action of `END A M` on `M`, `x · f = (-1)^{|f||x|} • f x` for homogeneous `f` and
`x`, as a ring homomorphism to the multiplicative opposite of `AddMonoid.End M`. -/
def rightAction : END A M →+* (AddMonoid.End M)ᵐᵒᵖ where
  toFun F := MulOpposite.op (signedEval A M F)
  map_one' := by rw [signedEval_one]; rfl
  map_mul' F G := by rw [signedEval_mul, ← MulOpposite.op_mul]; rfl
  map_zero' := by simp
  map_add' F G := by simp

theorem rightAction_apply (F : END A M) (x : M) :
    (rightAction A M F).unop x = signedEval A M F x := rfl

theorem rightAction_of_apply {n : ℤ} (f : Cochain A M M n) {i : ℤ} {x : M}
    (hx : x ∈ grading i) :
    (rightAction A M (DirectSum.of (fun n => Cochain A M M n) n f)).unop x =
      koszulSign (n * i) • f x := by
  rw [rightAction_apply, signedEval_of, Cochain.signedApply_of_mem f hx]

end DGModule.END

end DG
