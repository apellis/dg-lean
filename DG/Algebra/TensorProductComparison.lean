import DG.Algebra.TensorProduct
import DG.Algebra.Hom

/-!
# Comparison of tensor products of dg algebras over `ℤ` and over `R`

Let `R` be a commutative ring and `A`, `B` dg `R`-algebras. Both `A ᵍ⊗[ℤ] B` and `A ᵍ⊗[R] B`
are dg rings (with the Koszul sign rule and the differential
`d (a ⊗ b) = d a ⊗ b + (-1)^{|a|} a ⊗ d b`), and the canonical surjection
`a ⊗ b ↦ a ⊗ b` is a morphism of dg rings
(`DG.GradedTensorProduct.intComparison R A B : A ᵍ⊗[ℤ] B →ᵈᵍ+* A ᵍ⊗[R] B`).
-/

open scoped TensorProduct

noncomputable section

namespace DG

namespace GradedTensorProduct

variable (R A B : Type*) [CommRing R]
  [Ring A] [Algebra R A] [DGAddCommGroup A] [DGRing A] [DGAlgebra R A]
  [Ring B] [Algebra R B] [DGAddCommGroup B] [DGRing B] [DGAlgebra R B]

local notation "𝒜" => DGAlgebra.gradingSubmodule ℤ A
local notation "ℬ" => DGAlgebra.gradingSubmodule ℤ B
local notation "𝒜ᵣ" => DGAlgebra.gradingSubmodule R A
local notation "ℬᵣ" => DGAlgebra.gradingSubmodule R B

/-- The canonical map `A ᵍ⊗[ℤ] B → A ᵍ⊗[R] B`, `a ⊗ b ↦ a ⊗ b`, as an additive map. -/
def intComparisonAddHom : (𝒜 ᵍ⊗[ℤ] ℬ) →+ (𝒜ᵣ ᵍ⊗[R] ℬᵣ) :=
  ((_root_.GradedTensorProduct.of R 𝒜ᵣ ℬᵣ).toLinearMap.restrictScalars ℤ ∘ₗ
    TensorProduct.mapOfCompatibleSMul R ℤ ℤ A B ∘ₗ
      (_root_.GradedTensorProduct.of ℤ 𝒜 ℬ).symm.toLinearMap).toAddMonoidHom

variable {R A B}

@[simp]
theorem intComparisonAddHom_tmul (a : A) (b : B) :
    intComparisonAddHom R A B (a ᵍ⊗ₜ[ℤ] b) = (a ᵍ⊗ₜ[R] b : 𝒜ᵣ ᵍ⊗[R] ℬᵣ) := rfl

theorem intComparisonAddHom_mul (x y : 𝒜 ᵍ⊗[ℤ] ℬ) :
    intComparisonAddHom R A B (x * y) =
      intComparisonAddHom R A B x * intComparisonAddHom R A B y := by
  induction x using induction_on_tmul (R := ℤ) with
  | zero => simp
  | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]
  | @tmul i j a ha b hb =>
    induction y using induction_on_tmul (R := ℤ) with
    | zero => simp
    | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
    | @tmul i' j' a' ha' b' hb' =>
      rw [tmul_mul_tmul 𝒜 ℬ a hb ha' b', intComparisonAddHom_tmul,
        intComparisonAddHom_tmul,
        tmul_mul_tmul 𝒜ᵣ ℬᵣ a hb ha' b', Units.smul_def, map_zsmul,
        intComparisonAddHom_tmul, Units.smul_def]

variable (R A B)

/-- **The comparison `A ᵍ⊗[ℤ] B → A ᵍ⊗[R] B`**, `a ⊗ b ↦ a ⊗ b`, a morphism of dg rings. -/
def intComparison : (𝒜 ᵍ⊗[ℤ] ℬ) →ᵈᵍ+* (𝒜ᵣ ᵍ⊗[R] ℬᵣ) where
  toFun := intComparisonAddHom R A B
  map_one' := rfl
  map_mul' := intComparisonAddHom_mul
  map_zero' := map_zero _
  map_add' := map_add _
  map_mem' {n x} hx := by
    refine grading_induction 𝒜 ℬ hx
      (motive := fun x => intComparisonAddHom R A B x ∈ DG.grading n) ?_ ?_ ?_
    · rw [map_zero]; exact zero_mem _
    · intro i j a b hij
      rw [intComparisonAddHom_tmul, ← hij]
      exact tmul_mem_grading (R := R) a.2 b.2
    · intro x y hx hy
      rw [map_add]; exact add_mem hx hy
  map_d' x := by
    induction x using induction_on_tmul (R := ℤ) with
    | zero => simp
    | add x y hx hy => rw [d_add, map_add, hx, hy, map_add, d_add]
    | @tmul i j a ha b hb =>
      change intComparisonAddHom R A B (d (a ᵍ⊗ₜ[ℤ] b)) = d (a ᵍ⊗ₜ[R] b : 𝒜ᵣ ᵍ⊗[R] ℬᵣ)
      rw [d_tmul (R := ℤ) ha, d_tmul (R := R) ha, map_add, Units.smul_def, map_zsmul,
        intComparisonAddHom_tmul, intComparisonAddHom_tmul, Units.smul_def]

@[simp]
theorem intComparison_tmul (a : A) (b : B) :
    intComparison R A B (a ᵍ⊗ₜ[ℤ] b) = (a ᵍ⊗ₜ[R] b : 𝒜ᵣ ᵍ⊗[R] ℬᵣ) := rfl

theorem intComparison_surjective : Function.Surjective (intComparison R A B) := by
  intro y
  induction y using induction_on_tmul (R := R) with
  | zero => exact ⟨0, map_zero _⟩
  | @tmul i j a ha b hb => exact ⟨a ᵍ⊗ₜ[ℤ] b, rfl⟩
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add _ _ _⟩

end GradedTensorProduct

end DG
