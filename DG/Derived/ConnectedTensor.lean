import DG.Derived.ConnectedK0
import DG.Algebra.TensorProduct

/-!
# Low-degree cohomology of tensor products of connected dg rings

Let `A` and `B` be connected dg rings (`DG.IsConnectedInt`: concentrated in non-negative degrees
with degree-`0` part `ℤ · 1`), with `B¹` free of finite rank over `ℤ`, and let `C = A ⊗ B` be their
graded tensor product (over `ℤ`, with the Koszul sign rule). If every degree-`1` cocycle of `A`
and of `B` vanishes (`H¹ = 0`) and `H²(A)`, `H²(B)` are torsion-free, then the same holds for `C`
(`DG.ConnectedTensor.cocycle_one_eq_zero`, `DG.ConnectedTensor.exists_eq_d_of_zsmul_eq_d`); in
cohomological form, `DG.ConnectedTensor.cohomology_one_eq_zero` and
`DG.ConnectedTensor.cohomology_two_torsionFree`. Together with `DG.DGRing.K0.exists_eq_zsmul_self`
this gives `K₀(A ⊗ B)` for connected `A`, `B` with these properties.

## Proof

In degrees `1` and `2`, `C¹ = A¹ ⊗ 1 + 1 ⊗ B¹` and `C² = A² ⊗ 1 + A¹ ⊗ B¹ + 1 ⊗ B²`
(`DG.ConnectedTensor.exists_deg_one`, `DG.ConnectedTensor.exists_deg_two`). The maps
`a ⊗ b ↦ ε(b) a` and `a ⊗ b ↦ ε(a) b`, `ε` the augmentation (the degree-`0` coefficient), commute
with the differentials and detect the outer summands; for a functional `φ` on `B¹`, the map
`a ⊗ b ↦ φ(b₁) a` (`b₁` the degree-`1` component of `b`) commutes with the differentials and, for
`φ` running over the coordinates of a basis of `B¹`, detects the middle summand `A¹ ⊗ B¹`, on which
it takes values in `Z¹(A) = 0` for a cocycle.
-/

open DirectSum GradedTensorProduct
open scoped TensorProduct

namespace DG

open DegreeZero

namespace ConnectedTensor

set_option linter.unusedSectionVars false

variable {A B : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B]

local notation "𝒜" => DGAlgebra.gradingSubmodule ℤ A
local notation "ℬ" => DGAlgebra.gradingSubmodule ℤ B

/-- The bilinear map `(a, b) ↦ f(b) • a`. -/
def smulRight (f : B →+ ℤ) : A →ₗ[ℤ] B →ₗ[ℤ] A :=
  LinearMap.mk₂ ℤ (fun a b => f b • a) (fun a a' b => smul_add _ _ _)
    (fun n a b => smul_comm _ _ _) (fun a b b' => by rw [map_add, add_smul])
    (fun n a b => by rw [map_zsmul, smul_eq_mul, mul_smul])

/-- The bilinear map `(a, b) ↦ f(a) • b`. -/
def smulLeft (f : A →+ ℤ) : A →ₗ[ℤ] B →ₗ[ℤ] B :=
  LinearMap.mk₂ ℤ (fun a b => f a • b) (fun a a' b => by rw [map_add, add_smul])
    (fun n a b => by rw [map_zsmul, smul_eq_mul, mul_smul]) (fun a b b' => smul_add _ _ _)
    (fun n a b => smul_comm _ _ _)

variable (A B) in
/-- The additive map `C → A` induced by `a ⊗ b ↦ f(b) • a`. -/
noncomputable def pr₁ (f : B →+ ℤ) : (𝒜 ᵍ⊗[ℤ] ℬ) →+ A :=
  ((TensorProduct.lift (smulRight f)) ∘ₗ
    (_root_.GradedTensorProduct.of ℤ 𝒜 ℬ).symm.toLinearMap).toAddMonoidHom

variable (A B) in
/-- The additive map `C → B` induced by `a ⊗ b ↦ f(a) • b`. -/
noncomputable def pr₂ (f : A →+ ℤ) : (𝒜 ᵍ⊗[ℤ] ℬ) →+ B :=
  ((TensorProduct.lift (smulLeft f)) ∘ₗ
    (_root_.GradedTensorProduct.of ℤ 𝒜 ℬ).symm.toLinearMap).toAddMonoidHom

@[simp]
theorem pr₁_tmul (f : B →+ ℤ) (a : A) (b : B) :
    pr₁ A B f (a ᵍ⊗ₜ[ℤ] b : 𝒜 ᵍ⊗[ℤ] ℬ) = f b • a := rfl

@[simp]
theorem pr₂_tmul (f : A →+ ℤ) (a : A) (b : B) :
    pr₂ A B f (a ᵍ⊗ₜ[ℤ] b : 𝒜 ᵍ⊗[ℤ] ℬ) = f a • b := rfl

variable (B) in
/-- The degree-`n` component `b ↦ bₙ`, as an additive map. -/
def comp (n : ℤ) : B →+ B where
  toFun b := (decompose (grading (M := B)) b n : B)
  map_zero' := by simp
  map_add' b b' := by simp

theorem comp_of_mem_same {n : ℤ} {b : B} (hb : b ∈ grading n) : comp B n b = b :=
  decompose_of_mem_same _ hb

theorem comp_of_mem_ne {m n : ℤ} {b : B} (hb : b ∈ grading m) (h : m ≠ n) : comp B n b = 0 :=
  decompose_of_mem_ne _ hb h

theorem comp_mem (n : ℤ) (b : B) : comp B n b ∈ grading n :=
  (decompose (grading (M := B)) b n).2

variable (hA : IsConnectedInt A) (hB : IsConnectedInt B)

/-- The degree-`0` coefficient of a connected dg ring, as an additive map to `ℤ`. -/
noncomputable def coeff₀ (hA : IsConnectedInt A) : A →+ ℤ :=
  hA.augmentation.toRingHom.toAddMonoidHom

theorem coeff₀_apply (a : A) : coeff₀ hA a = hA.augmentation a := rfl

theorem coeff₀_one : coeff₀ hA (1 : A) = 1 := map_one hA.augmentation

theorem coeff₀_d (a : A) : coeff₀ hA (d a) = 0 := by
  rw [coeff₀_apply, hA.augmentation.map_d]
  rfl

theorem coeff₀_of_mem {n : ℤ} (hn : n ≠ 0) {a : A} (ha : a ∈ grading n) : coeff₀ hA a = 0 := by
  have h := hA.augmentation.map_mem ha
  exact (mem_grading_iff.mp h).resolve_left hn

theorem eq_intCast_of_mem_zero {a : A} (ha : a ∈ grading 0) : a = ((coeff₀ hA a : ℤ) : A) := by
  obtain ⟨z, rfl⟩ := hA.exists_intCast a ha
  rw [coeff₀_apply, hA.augmentation_intCast]

/-! ### Chain maps -/

/-- `a ⊗ b ↦ ψ(b) • a` commutes with the differentials if `ψ` vanishes on coboundaries. -/
theorem pr₁_d_of (ψ : B →+ ℤ) (hψ : ∀ b, ψ (d b) = 0) (x : 𝒜 ᵍ⊗[ℤ] ℬ) :
    pr₁ A B ψ (d x) = d (pr₁ A B ψ x) := by
  induction x using GradedTensorProduct.induction_on_tmul with
  | zero => simp
  | @tmul i j a ha b hb =>
    rw [GradedTensorProduct.d_tmul ha, map_add, pr₁_tmul, Units.smul_def, map_zsmul, pr₁_tmul,
      hψ, zero_smul, smul_zero, add_zero, pr₁_tmul, map_zsmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, d_add]

theorem pr₁_d (x : 𝒜 ᵍ⊗[ℤ] ℬ) : pr₁ A B (coeff₀ hB) (d x) = d (pr₁ A B (coeff₀ hB) x) := by
  induction x using GradedTensorProduct.induction_on_tmul with
  | zero => simp
  | @tmul i j a ha b hb =>
    rw [GradedTensorProduct.d_tmul ha, map_add, pr₁_tmul, Units.smul_def, map_zsmul, pr₁_tmul,
      coeff₀_d, zero_smul, smul_zero, add_zero, pr₁_tmul, map_zsmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, d_add]

theorem pr₂_d (x : 𝒜 ᵍ⊗[ℤ] ℬ) : pr₂ A B (coeff₀ hA) (d x) = d (pr₂ A B (coeff₀ hA) x) := by
  induction x using GradedTensorProduct.induction_on_tmul with
  | zero => simp
  | @tmul i j a ha b hb =>
    rw [GradedTensorProduct.d_tmul ha, map_add, pr₂_tmul, Units.smul_def, map_zsmul, pr₂_tmul,
      coeff₀_d, zero_smul, zero_add, pr₂_tmul, map_zsmul]
    by_cases hi : i = 0
    · subst hi
      rw [koszulSign_zero, Units.val_one, one_smul]
    · rw [coeff₀_of_mem hA hi ha, zero_smul, smul_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, d_add]

include hB in
/-- For `φ : B →+ ℤ`, the map `a ⊗ b ↦ φ(b₁) • a` commutes with the differentials. -/
theorem pr₁_comp_d (φ : B →+ ℤ) (x : 𝒜 ᵍ⊗[ℤ] ℬ) :
    pr₁ A B (φ.comp (comp B 1)) (d x) = d (pr₁ A B (φ.comp (comp B 1)) x) := by
  have hd1 : ∀ {j : ℤ} {b : B}, b ∈ grading j → comp B 1 (d b) = 0 := by
    intro j b hb
    by_cases hj : j = 0
    · subst hj
      obtain ⟨z, rfl⟩ := hB.exists_intCast b hb
      rw [d_intCast, map_zero]
    · exact comp_of_mem_ne (d_mem hb) (by omega)
  induction x using GradedTensorProduct.induction_on_tmul with
  | zero => simp
  | @tmul i j a ha b hb =>
    rw [GradedTensorProduct.d_tmul ha, map_add, pr₁_tmul, Units.smul_def, map_zsmul, pr₁_tmul,
      AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hd1 hb, map_zero, zero_smul, smul_zero,
      add_zero, pr₁_tmul, map_zsmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, d_add]

/-! ### Degrees `1` and `2` -/

theorem tmul_intCast (a : A) (z : ℤ) :
    (a ᵍ⊗ₜ[ℤ] (z : B) : 𝒜 ᵍ⊗[ℤ] ℬ) = (z • a) ᵍ⊗ₜ[ℤ] (1 : B) := by
  rw [show (z : B) = z • (1 : B) from (zsmul_one z).symm]
  change _root_.GradedTensorProduct.of ℤ 𝒜 ℬ (a ⊗ₜ (z • (1 : B))) =
    _root_.GradedTensorProduct.of ℤ 𝒜 ℬ ((z • a) ⊗ₜ (1 : B))
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']

theorem intCast_tmul (z : ℤ) (b : B) :
    ((z : A) ᵍ⊗ₜ[ℤ] b : 𝒜 ᵍ⊗[ℤ] ℬ) = (1 : A) ᵍ⊗ₜ[ℤ] (z • b) := by
  rw [show (z : A) = z • (1 : A) from (zsmul_one z).symm]
  change _root_.GradedTensorProduct.of ℤ 𝒜 ℬ ((z • (1 : A)) ⊗ₜ b) =
    _root_.GradedTensorProduct.of ℤ 𝒜 ℬ ((1 : A) ⊗ₜ (z • b))
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']

theorem eq_zero_of_mem_neg' (hA : IsConnectedInt A) {n : ℤ} (hn : n < 0) {a : A}
    (ha : a ∈ grading n) : a = 0 :=
  hA.eq_zero_of_mem_neg hn ha

include hA hB in
/-- `C¹ = A¹ ⊗ 1 + 1 ⊗ B¹`. -/
theorem exists_deg_one {x : 𝒜 ᵍ⊗[ℤ] ℬ} (hx : x ∈ grading 1) :
    ∃ a ∈ grading (M := A) 1, ∃ b ∈ grading (M := B) 1,
      x = a ᵍ⊗ₜ[ℤ] (1 : B) + (1 : A) ᵍ⊗ₜ[ℤ] b := by
  suffices H : ∀ y : 𝒜 ᵍ⊗[ℤ] ℬ, ∃ a ∈ grading (M := A) 1, ∃ b ∈ grading (M := B) 1,
      (decompose (grading (M := 𝒜 ᵍ⊗[ℤ] ℬ)) y 1 : 𝒜 ᵍ⊗[ℤ] ℬ) =
        a ᵍ⊗ₜ[ℤ] (1 : B) + (1 : A) ᵍ⊗ₜ[ℤ] b by
    obtain ⟨a, ha, b, hb, h⟩ := H x
    exact ⟨a, ha, b, hb, by rw [← h, decompose_of_mem_same _ hx]⟩
  intro y
  induction y using GradedTensorProduct.induction_on_tmul with
  | zero =>
    exact ⟨0, zero_mem _, 0, zero_mem _, by
      rw [decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero,
        GradedTensorProduct.zero_tmul, GradedTensorProduct.tmul_zero, add_zero]⟩
  | @tmul i j a ha b hb =>
    have hab := GradedTensorProduct.tmul_mem_grading (R := ℤ) ha hb
    by_cases hij : i + j = 1
    · rw [decompose_of_mem_same _ (hij ▸ hab)]
      by_cases hi : i < 0
      · rw [eq_zero_of_mem_neg' hA hi ha, GradedTensorProduct.zero_tmul]
        exact ⟨0, zero_mem _, 0, zero_mem _, by
          rw [GradedTensorProduct.zero_tmul, GradedTensorProduct.tmul_zero, add_zero]⟩
      by_cases hj : j < 0
      · rw [eq_zero_of_mem_neg' hB hj hb, GradedTensorProduct.tmul_zero]
        exact ⟨0, zero_mem _, 0, zero_mem _, by
          rw [GradedTensorProduct.zero_tmul, GradedTensorProduct.tmul_zero, add_zero]⟩
      rcases (show (i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 1) by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [eq_intCast_of_mem_zero hB hb, tmul_intCast]
        exact ⟨_, zsmul_mem ha _, 0, zero_mem _, by rw [GradedTensorProduct.tmul_zero, add_zero]⟩
      · rw [eq_intCast_of_mem_zero hA ha, intCast_tmul]
        exact ⟨0, zero_mem _, _, zsmul_mem hb _, by rw [GradedTensorProduct.zero_tmul, zero_add]⟩
    · rw [decompose_of_mem_ne _ hab hij]
      exact ⟨0, zero_mem _, 0, zero_mem _, by
        rw [GradedTensorProduct.zero_tmul, GradedTensorProduct.tmul_zero, add_zero]⟩
  | add y y' hy hy' =>
    obtain ⟨a, ha, b, hb, h⟩ := hy
    obtain ⟨a', ha', b', hb', h'⟩ := hy'
    refine ⟨a + a', add_mem ha ha', b + b', add_mem hb hb', ?_⟩
    rw [decompose_add, DirectSum.add_apply, AddMemClass.coe_add, h, h',
      GradedTensorProduct.add_tmul, GradedTensorProduct.tmul_add]
    abel

variable (A B) in
/-- The span of the pure tensors `a ⊗ b` with `a ∈ A¹`, `b ∈ B¹`. -/
noncomputable def tensorOneOne : AddSubgroup (𝒜 ᵍ⊗[ℤ] ℬ) :=
  AddSubgroup.closure {x | ∃ a ∈ grading (M := A) 1, ∃ b ∈ grading (M := B) 1,
    x = a ᵍ⊗ₜ[ℤ] b}

include hA hB in
/-- `C² = A² ⊗ 1 + A¹ ⊗ B¹ + 1 ⊗ B²`. -/
theorem exists_deg_two {x : 𝒜 ᵍ⊗[ℤ] ℬ} (hx : x ∈ grading 2) :
    ∃ α ∈ grading (M := A) 2, ∃ β ∈ grading (M := B) 2, ∃ t ∈ tensorOneOne A B,
      x = α ᵍ⊗ₜ[ℤ] (1 : B) + t + (1 : A) ᵍ⊗ₜ[ℤ] β := by
  suffices H : ∀ y : 𝒜 ᵍ⊗[ℤ] ℬ, ∃ α ∈ grading (M := A) 2, ∃ β ∈ grading (M := B) 2,
      ∃ t ∈ tensorOneOne A B, (decompose (grading (M := 𝒜 ᵍ⊗[ℤ] ℬ)) y 2 : 𝒜 ᵍ⊗[ℤ] ℬ) =
        α ᵍ⊗ₜ[ℤ] (1 : B) + t + (1 : A) ᵍ⊗ₜ[ℤ] β by
    obtain ⟨α, hα, β, hβ, t, ht, h⟩ := H x
    exact ⟨α, hα, β, hβ, t, ht, by rw [← h, decompose_of_mem_same _ hx]⟩
  have hzero : ∃ α ∈ grading (M := A) 2, ∃ β ∈ grading (M := B) 2, ∃ t ∈ tensorOneOne A B,
      (0 : 𝒜 ᵍ⊗[ℤ] ℬ) = α ᵍ⊗ₜ[ℤ] (1 : B) + t + (1 : A) ᵍ⊗ₜ[ℤ] β :=
    ⟨0, zero_mem _, 0, zero_mem _, 0, zero_mem _, by
      rw [GradedTensorProduct.zero_tmul, GradedTensorProduct.tmul_zero, add_zero, add_zero]⟩
  intro y
  induction y using GradedTensorProduct.induction_on_tmul with
  | zero => rw [decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]; exact hzero
  | @tmul i j a ha b hb =>
    have hab := GradedTensorProduct.tmul_mem_grading (R := ℤ) ha hb
    by_cases hij : i + j = 2
    · rw [decompose_of_mem_same _ (hij ▸ hab)]
      by_cases hi : i < 0
      · rw [eq_zero_of_mem_neg' hA hi ha, GradedTensorProduct.zero_tmul]
        exact hzero
      by_cases hj : j < 0
      · rw [eq_zero_of_mem_neg' hB hj hb, GradedTensorProduct.tmul_zero]
        exact hzero
      rcases (show (i = 2 ∧ j = 0) ∨ (i = 1 ∧ j = 1) ∨ (i = 0 ∧ j = 2) by omega) with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [eq_intCast_of_mem_zero hB hb, tmul_intCast]
        exact ⟨_, zsmul_mem ha _, 0, zero_mem _, 0, zero_mem _, by
          rw [GradedTensorProduct.tmul_zero, add_zero, add_zero]⟩
      · exact ⟨0, zero_mem _, 0, zero_mem _, a ᵍ⊗ₜ[ℤ] b,
          AddSubgroup.subset_closure ⟨a, ha, b, hb, rfl⟩, by
          rw [GradedTensorProduct.zero_tmul, GradedTensorProduct.tmul_zero, zero_add, add_zero]⟩
      · rw [eq_intCast_of_mem_zero hA ha, intCast_tmul]
        exact ⟨0, zero_mem _, _, zsmul_mem hb _, 0, zero_mem _, by
          rw [GradedTensorProduct.zero_tmul, zero_add, zero_add]⟩
    · rw [decompose_of_mem_ne _ hab hij]
      exact hzero
  | add y y' hy hy' =>
    obtain ⟨α, hα, β, hβ, t, ht, h⟩ := hy
    obtain ⟨α', hα', β', hβ', t', ht', h'⟩ := hy'
    refine ⟨α + α', add_mem hα hα', β + β', add_mem hβ hβ', t + t', add_mem ht ht', ?_⟩
    rw [decompose_add, DirectSum.add_apply, AddMemClass.coe_add, h, h',
      GradedTensorProduct.add_tmul, GradedTensorProduct.tmul_add]
    abel

/-! ### Values of the chain maps -/

theorem pr₁_one_tmul {b : B} (hb : b ∈ grading (M := B) 1 ∨ b ∈ grading (M := B) 2) :
    pr₁ A B (coeff₀ hB) ((1 : A) ᵍ⊗ₜ[ℤ] b) = 0 := by
  rw [pr₁_tmul]
  rcases hb with hb | hb
  · rw [coeff₀_of_mem hB one_ne_zero hb, zero_smul]
  · rw [coeff₀_of_mem hB two_ne_zero hb, zero_smul]

theorem pr₁_tmul_one (a : A) : pr₁ A B (coeff₀ hB) (a ᵍ⊗ₜ[ℤ] (1 : B)) = a := by
  rw [pr₁_tmul, coeff₀_one, one_smul]

theorem pr₂_tmul_one {a : A} (ha : a ∈ grading (M := A) 1 ∨ a ∈ grading (M := A) 2) :
    pr₂ A B (coeff₀ hA) (a ᵍ⊗ₜ[ℤ] (1 : B)) = 0 := by
  rw [pr₂_tmul]
  rcases ha with ha | ha
  · rw [coeff₀_of_mem hA one_ne_zero ha, zero_smul]
  · rw [coeff₀_of_mem hA two_ne_zero ha, zero_smul]

theorem pr₂_one_tmul (b : B) : pr₂ A B (coeff₀ hA) ((1 : A) ᵍ⊗ₜ[ℤ] b) = b := by
  rw [pr₂_tmul, coeff₀_one, one_smul]

theorem pr₁_tensorOneOne {t : 𝒜 ᵍ⊗[ℤ] ℬ} (ht : t ∈ tensorOneOne A B) :
    pr₁ A B (coeff₀ hB) t = 0 := by
  induction ht using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    rw [pr₁_tmul, coeff₀_of_mem hB one_ne_zero hb, zero_smul]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | neg x _ hx => rw [map_neg, hx, neg_zero]

theorem pr₂_tensorOneOne {t : 𝒜 ᵍ⊗[ℤ] ℬ} (ht : t ∈ tensorOneOne A B) :
    pr₂ A B (coeff₀ hA) t = 0 := by
  induction ht using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    rw [pr₂_tmul, coeff₀_of_mem hA one_ne_zero ha, zero_smul]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | neg x _ hx => rw [map_neg, hx, neg_zero]

theorem d_tmul_one (a : A) : d (a ᵍ⊗ₜ[ℤ] (1 : B) : 𝒜 ᵍ⊗[ℤ] ℬ) = d a ᵍ⊗ₜ[ℤ] (1 : B) := by
  rw [GradedTensorProduct.d_tmul', d_one, GradedTensorProduct.tmul_zero, add_zero]

theorem d_one_tmul (b : B) : d ((1 : A) ᵍ⊗ₜ[ℤ] b : 𝒜 ᵍ⊗[ℤ] ℬ) = (1 : A) ᵍ⊗ₜ[ℤ] d b := by
  rw [GradedTensorProduct.d_tmul one_mem_grading, d_one, GradedTensorProduct.zero_tmul,
    zero_add, koszulSign_zero, one_smul]

/-! ### The main statements -/

include hA hB in
/-- **`Z¹(A ⊗ B) = 0`** if `Z¹(A) = 0` and `Z¹(B) = 0`. -/
theorem cocycle_one_eq_zero (hA₁ : ∀ a ∈ grading (M := A) 1, d a = 0 → a = 0)
    (hB₁ : ∀ b ∈ grading (M := B) 1, d b = 0 → b = 0) {z : 𝒜 ᵍ⊗[ℤ] ℬ} (hz : z ∈ grading 1)
    (hdz : d z = 0) : z = 0 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_deg_one hA hB hz
  have h₁ : pr₁ A B (coeff₀ hB) (a ᵍ⊗ₜ[ℤ] (1 : B) + (1 : A) ᵍ⊗ₜ[ℤ] b) = a := by
    rw [map_add, pr₁_tmul_one, pr₁_one_tmul hB (Or.inl hb), add_zero]
  have h₂ : pr₂ A B (coeff₀ hA) (a ᵍ⊗ₜ[ℤ] (1 : B) + (1 : A) ᵍ⊗ₜ[ℤ] b) = b := by
    rw [map_add, pr₂_tmul_one hA (Or.inl ha), pr₂_one_tmul, zero_add]
  have ha0 : a = 0 := hA₁ a ha (by rw [← h₁, ← pr₁_d, hdz, map_zero])
  have hb0 : b = 0 := hB₁ b hb (by rw [← h₂, ← pr₂_d, hdz, map_zero])
  rw [ha0, hb0, GradedTensorProduct.zero_tmul, GradedTensorProduct.tmul_zero, add_zero]

/-! ### `A¹ ⊗ B¹` -/

variable (B) in
/-- The degree-`1` component `B → B¹`. -/
def comp₁ : B →+ grading (M := B) 1 where
  toFun b := decompose (grading (M := B)) b 1
  map_zero' := by simp
  map_add' b b' := by simp

theorem coe_comp₁ (b : B) : (comp₁ B b : B) = decompose (grading (M := B)) b 1 := rfl

include hB in
theorem comp₁_d (b : B) : comp₁ B (d b) = 0 := by
  apply Subtype.ext
  rw [coe_comp₁, ZeroMemClass.coe_zero]
  have h := decompose_d b 0
  rw [zero_add] at h
  rw [h]
  obtain ⟨z, hz⟩ := hB.exists_intCast _ (decompose (grading (M := B)) b 0).2
  rw [← hz, d_intCast]

/-- The coordinate functionals of a basis of `B¹`, extended to `B` through `b ↦ b₁`. -/
noncomputable def coord {ι : Type*} (e : Module.Basis ι ℤ (grading (M := B) 1)) (j : ι) :
    B →+ ℤ :=
  (e.coord j).toAddMonoidHom.comp (comp₁ B)

theorem coord_of_mem {ι : Type*} (e : Module.Basis ι ℤ (grading (M := B) 1)) (j : ι) {b : B}
    (hb : b ∈ grading (M := B) 1) : coord e j b = e.repr ⟨b, hb⟩ j := by
  have : comp₁ B b = ⟨b, hb⟩ := Subtype.ext (decompose_of_mem_same _ hb)
  simp [coord, this]

theorem gtmul_sum {ι : Type*} (s : Finset ι) (a : A) (f : ι → B) :
    (a ᵍ⊗ₜ[ℤ] (∑ j ∈ s, f j) : 𝒜 ᵍ⊗[ℤ] ℬ) = ∑ j ∈ s, a ᵍ⊗ₜ[ℤ] f j := by
  change _root_.GradedTensorProduct.of ℤ 𝒜 ℬ (a ⊗ₜ (∑ j ∈ s, f j)) = _
  rw [TensorProduct.tmul_sum, map_sum]

theorem zsmul_gtmul (n : ℤ) (a : A) (b : B) :
    ((n • a) ᵍ⊗ₜ[ℤ] b : 𝒜 ᵍ⊗[ℤ] ℬ) = a ᵍ⊗ₜ[ℤ] (n • b) := by
  change _root_.GradedTensorProduct.of ℤ 𝒜 ℬ ((n • a) ⊗ₜ b) =
    _root_.GradedTensorProduct.of ℤ 𝒜 ℬ (a ⊗ₜ (n • b))
  rw [TensorProduct.smul_tmul]

/-- Reconstruction of an element of `A¹ ⊗ B¹` from its coordinates. -/
theorem eq_sum_of_mem_tensorOneOne {ι : Type*} [Fintype ι]
    (e : Module.Basis ι ℤ (grading (M := B) 1)) {t : 𝒜 ᵍ⊗[ℤ] ℬ} (ht : t ∈ tensorOneOne A B) :
    t = ∑ j, pr₁ A B (coord e j) t ᵍ⊗ₜ[ℤ] (e j : B) := by
  induction ht using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    simp only [pr₁_tmul, coord_of_mem e _ hb, zsmul_gtmul]
    rw [← gtmul_sum]
    congr 1
    calc b = ((⟨b, hb⟩ : grading (M := B) 1) : B) := rfl
      _ = ((∑ j, e.repr ⟨b, hb⟩ j • e j : grading (M := B) 1) : B) := by rw [e.sum_repr]
      _ = _ := by simp only [AddSubgroup.val_finsetSum, AddSubgroup.coe_zsmul]
  | zero => simp [GradedTensorProduct.zero_tmul]
  | add x y _ _ hx hy =>
    conv_lhs => rw [hx, hy]
    simp only [map_add, GradedTensorProduct.add_tmul, Finset.sum_add_distrib]
  | neg x _ hx =>
    conv_lhs => rw [hx]
    have hneg : ∀ (a : A) (b : B), ((-a) ᵍ⊗ₜ[ℤ] b : 𝒜 ᵍ⊗[ℤ] ℬ) = -(a ᵍ⊗ₜ[ℤ] b) := fun a b => by
      change _root_.GradedTensorProduct.of ℤ 𝒜 ℬ ((-a) ⊗ₜ b) = -_
      rw [TensorProduct.neg_tmul, map_neg]
    simp only [map_neg, hneg, Finset.sum_neg_distrib]

theorem pr₁_coord_mem {ι : Type*} (e : Module.Basis ι ℤ (grading (M := B) 1)) (j : ι)
    {t : 𝒜 ᵍ⊗[ℤ] ℬ} (ht : t ∈ tensorOneOne A B) : pr₁ A B (coord e j) t ∈ grading (M := A) 1 := by
  induction ht using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    rw [pr₁_tmul]
    exact zsmul_mem ha _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

include hA hB in
/-- **`H²(A ⊗ B)` is torsion-free** (in cocycle form) if `Z¹(A) = 0`, `H²(A)` and `H²(B)` are
torsion-free, and `B¹` has a finite basis. -/
theorem exists_eq_d_of_zsmul_eq_d (hA₁ : ∀ a ∈ grading (M := A) 1, d a = 0 → a = 0)
    (hA₂ : ∀ m : ℤ, m ≠ 0 → ∀ α ∈ grading (M := A) 2, d α = 0 → ∀ a ∈ grading (M := A) 1,
      m • α = d a → ∃ a' ∈ grading (M := A) 1, α = d a')
    (hB₂ : ∀ m : ℤ, m ≠ 0 → ∀ β ∈ grading (M := B) 2, d β = 0 → ∀ b ∈ grading (M := B) 1,
      m • β = d b → ∃ b' ∈ grading (M := B) 1, β = d b')
    {ι : Type*} [Fintype ι] (e : Module.Basis ι ℤ (grading (M := B) 1)) {m : ℤ} (hm : m ≠ 0)
    {z : 𝒜 ᵍ⊗[ℤ] ℬ} (hz : z ∈ grading 2) (hdz : d z = 0) {w : 𝒜 ᵍ⊗[ℤ] ℬ} (hw : w ∈ grading 1)
    (hmw : m • z = d w) : ∃ c ∈ grading (M := 𝒜 ᵍ⊗[ℤ] ℬ) 1, z = d c := by
  obtain ⟨α, hα, β, hβ, t, ht, rfl⟩ := exists_deg_two hA hB hz
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_deg_one hA hB hw
  -- The outer components.
  have hpα : pr₁ A B (coeff₀ hB) (α ᵍ⊗ₜ[ℤ] (1 : B) + t + (1 : A) ᵍ⊗ₜ[ℤ] β) = α := by
    rw [map_add, map_add, pr₁_tmul_one, pr₁_tensorOneOne hB ht, pr₁_one_tmul hB (Or.inr hβ),
      add_zero, add_zero]
  have hpβ : pr₂ A B (coeff₀ hA) (α ᵍ⊗ₜ[ℤ] (1 : B) + t + (1 : A) ᵍ⊗ₜ[ℤ] β) = β := by
    rw [map_add, map_add, pr₂_tmul_one hA (Or.inr hα), pr₂_tensorOneOne hA ht, pr₂_one_tmul,
      zero_add, zero_add]
  have hpa : pr₁ A B (coeff₀ hB) (a ᵍ⊗ₜ[ℤ] (1 : B) + (1 : A) ᵍ⊗ₜ[ℤ] b) = a := by
    rw [map_add, pr₁_tmul_one, pr₁_one_tmul hB (Or.inl hb), add_zero]
  have hpb : pr₂ A B (coeff₀ hA) (a ᵍ⊗ₜ[ℤ] (1 : B) + (1 : A) ᵍ⊗ₜ[ℤ] b) = b := by
    rw [map_add, pr₂_tmul_one hA (Or.inl ha), pr₂_one_tmul, zero_add]
  obtain ⟨a', ha', hα'⟩ := hA₂ m hm α hα (by rw [← hpα, ← pr₁_d, hdz, map_zero]) a ha (by
    rw [← hpα, ← hpa, ← map_zsmul, hmw, pr₁_d])
  obtain ⟨b', hb', hβ'⟩ := hB₂ m hm β hβ (by rw [← hpβ, ← pr₂_d, hdz, map_zero]) b hb (by
    rw [← hpβ, ← hpb, ← map_zsmul, hmw, pr₂_d])
  -- The middle component vanishes.
  have hdt : d t = 0 := by
    have h := hdz
    rw [d_add, d_add, hα', hβ', ← d_tmul_one, ← d_one_tmul, d_d, d_d, zero_add, add_zero] at h
    exact h
  have ht0 : t = 0 := by
    rw [eq_sum_of_mem_tensorOneOne e ht]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hA₁ _ (pr₁_coord_mem e j ht) (by
      rw [← pr₁_d_of _ (fun b => by rw [coord, AddMonoidHom.comp_apply, comp₁_d hB, map_zero]),
        hdt, map_zero]), GradedTensorProduct.zero_tmul]
  have h₁ := GradedTensorProduct.tmul_mem_grading (R := ℤ) ha' (one_mem_grading (A := B))
  have h₂ := GradedTensorProduct.tmul_mem_grading (R := ℤ) (one_mem_grading (A := A)) hb'
  rw [add_zero] at h₁
  rw [zero_add] at h₂
  refine ⟨a' ᵍ⊗ₜ[ℤ] (1 : B) + (1 : A) ᵍ⊗ₜ[ℤ] b', add_mem h₁ h₂, ?_⟩
  rw [ht0, add_zero, d_add, d_tmul_one, d_one_tmul, hα', hβ']

/-! ### Cohomological form -/

include hA hB in
theorem cohomology_one_eq_zero (hA₁ : ∀ a ∈ grading (M := A) 1, d a = 0 → a = 0)
    (hB₁ : ∀ b ∈ grading (M := B) 1, d b = 0 → b = 0) (x : cohomology (𝒜 ᵍ⊗[ℤ] ℬ) 1) :
    x = 0 := by
  induction x using cohomology.induction_on with
  | h z =>
    rw [show z = 0 from Subtype.ext (cocycle_one_eq_zero hA hB hA₁ hB₁ (cocycles.mem_grading z)
      (cocycles.d_eq_zero z)), map_zero]

include hA hB in
theorem cohomology_two_torsionFree (hA₁ : ∀ a ∈ grading (M := A) 1, d a = 0 → a = 0)
    (hA₂ : ∀ m : ℤ, m ≠ 0 → ∀ α ∈ grading (M := A) 2, d α = 0 → ∀ a ∈ grading (M := A) 1,
      m • α = d a → ∃ a' ∈ grading (M := A) 1, α = d a')
    (hB₂ : ∀ m : ℤ, m ≠ 0 → ∀ β ∈ grading (M := B) 2, d β = 0 → ∀ b ∈ grading (M := B) 1,
      m • β = d b → ∃ b' ∈ grading (M := B) 1, β = d b')
    {ι : Type*} [Fintype ι] (e : Module.Basis ι ℤ (grading (M := B) 1)) (m : ℤ) (hm : m ≠ 0)
    (x : cohomology (𝒜 ᵍ⊗[ℤ] ℬ) 2) (hx : m • x = 0) : x = 0 := by
  induction x using cohomology.induction_on with
  | h z =>
    rw [← map_zsmul, cohomology.mk_eq_zero_iff] at hx
    obtain ⟨w, hw, hdw⟩ := mem_coboundaries.mp hx
    obtain ⟨c, hc, hzc⟩ := exists_eq_d_of_zsmul_eq_d hA hB hA₁ hA₂ hB₂ e hm
      (cocycles.mem_grading z) (cocycles.d_eq_zero z) (w := w) (by simpa using hw)
      (by rw [hdw]; rfl)
    rw [cohomology.mk_eq_zero_iff]
    exact mem_coboundaries.mpr ⟨c, by simpa using hc, hzc.symm⟩

end ConnectedTensor

end DG
