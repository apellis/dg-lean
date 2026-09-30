import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal
import DG.Graded.Commutative

/-!
# Graded tensor products of `ℤ`-graded algebras

Mathlib's `GradedTensorProduct R 𝒜 ℬ` (notation `𝒜 ᵍ⊗[R] ℬ`) is the tensor product `A ⊗[R] B`
of two `R`-algebras graded by an index type `ι` with `Module ι (Additive ℤˣ)`, with the signed
product
  `(a ⊗ b) * (a' ⊗ b') = (-1)^(j * i') • ((a * a') ⊗ (b * b'))`
for `b` of degree `j` and `a'` of degree `i'`. The index type `ℤ` satisfies this hypothesis (every
additive group is a `ℤ`-module), and for `ι = ℤ` the sign `(-1 : ℤˣ)^(j * i')` is definitionally
`DG.koszulSign (j * i')`. This file therefore reuses Mathlib's construction for `ℤ`-graded
algebras and adds what Mathlib does not provide:

* the grading `DG.GradedTensorProduct.grading 𝒜 ℬ` on `𝒜 ᵍ⊗[R] ℬ`, whose degree-`n` piece is the
  sum of the images of `𝒜 i ⊗[R] ℬ j` over `i + j = n`, and the `GradedAlgebra` instance;
* the product formula on pure tensors of homogeneous elements with the sign written as
  `koszulSign` (`DG.GradedTensorProduct.tmul_mul_tmul`);
* degree preservation of the inclusions `includeLeft`, `includeRight` and of the symmetry
  `GradedTensorProduct.comm`, restated with `koszulSign`
  (`DG.GradedTensorProduct.comm_tmul`);
* the associativity isomorphism `DG.GradedTensorProduct.assoc` and the unit isomorphism
  `DG.GradedTensorProduct.lid` (with `R` graded in degree `0`, `DG.trivialGrading R R`), both
  algebra isomorphisms preserving degrees.

## Notation

The notation `𝒜 ᵍ⊗[R] ℬ` and `a ᵍ⊗ₜ b` is Mathlib's (`open scoped TensorProduct`).
-/

suppress_compilation

open DirectSum TensorProduct GradedTensorProduct
open scoped TensorProduct

namespace DG

/-! ### The grading concentrated in degree zero -/

section trivialGrading

variable (R A : Type*) [CommRing R] [Ring A] [Algebra R A]

/-- The grading of an `R`-algebra `A` concentrated in degree `0`. -/
def trivialGrading : ℤ → Submodule R A := fun n => if n = 0 then ⊤ else ⊥

theorem trivialGrading_zero : trivialGrading R A 0 = ⊤ := ite_eq_left rfl

theorem trivialGrading_of_ne {n : ℤ} (h : n ≠ 0) : trivialGrading R A n = ⊥ := ite_eq_right h

theorem mem_trivialGrading_zero (a : A) : a ∈ trivialGrading R A 0 := by
  rw [trivialGrading_zero]; exact Submodule.mem_top

theorem eq_zero_of_mem_trivialGrading {n : ℤ} (h : n ≠ 0) {a : A} (ha : a ∈ trivialGrading R A n) :
    a = 0 := by
  rw [trivialGrading_of_ne R A h] at ha
  exact (Submodule.mem_bot R).mp ha

instance : SetLike.GradedMonoid (trivialGrading R A) where
  one_mem := mem_trivialGrading_zero R A 1
  mul_mem {i j} a b ha hb := by
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · subst hi hj
        exact mem_trivialGrading_zero R A _
      · rw [eq_zero_of_mem_trivialGrading R A hj hb, mul_zero]
        exact zero_mem _
    · rw [eq_zero_of_mem_trivialGrading R A hi ha, zero_mul]
      exact zero_mem _

instance : DirectSum.Decomposition (trivialGrading R A) :=
  DirectSum.Decomposition.ofLinearMap _
    (lof R ℤ (trivialGrading R A ·) 0 ∘ₗ
      LinearMap.codRestrict (trivialGrading R A 0) LinearMap.id (mem_trivialGrading_zero R A))
    (LinearMap.ext fun a => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, lof_eq_of, coeLinearMap_of,
        LinearMap.id_apply]
      rfl)
    (DirectSum.linearMap_ext _ fun n => LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, lof_eq_of, coeLinearMap_of, LinearMap.id_apply]
      by_cases hn : n = 0
      · subst hn
        exact congrArg _ (Subtype.ext rfl)
      · have hx : x = 0 := Subtype.ext (eq_zero_of_mem_trivialGrading R A hn x.2)
        subst hx
        simp)

instance : GradedAlgebra (trivialGrading R A) :=
  { (inferInstance : SetLike.GradedMonoid (trivialGrading R A)),
    (inferInstance : DirectSum.Decomposition (trivialGrading R A)) with }

end trivialGrading

variable {R A B C : Type*} [CommRing R] [Ring A] [Ring B] [Ring C]
variable [Algebra R A] [Algebra R B] [Algebra R C]
variable (𝒜 : ℤ → Submodule R A) (ℬ : ℤ → Submodule R B) (𝒞 : ℤ → Submodule R C)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞]

/-- For `ι = ℤ`, the sign `(-1 : ℤˣ)^n` used by Mathlib's graded tensor products is the Koszul
sign `koszulSign n`. -/
theorem uzpow_neg_one_eq_koszulSign (n : ℤ) : ((-1 : ℤˣ) ^ n : ℤˣ) = koszulSign n := rfl

namespace GradedTensorProduct

/-! ### Signs and the product on pure tensors -/

theorem one_def : (1 : 𝒜 ᵍ⊗[R] ℬ) = 1 ᵍ⊗ₜ[R] 1 := rfl

/-- The product of pure tensors, for `b` and `a'` homogeneous:
`(a ⊗ b) * (a' ⊗ b') = (-1)^(j * i') • ((a * a') ⊗ (b * b'))`. -/
theorem tmul_mul_tmul {j i' : ℤ} (a : A) {b : B} (hb : b ∈ ℬ j) {a' : A} (ha' : a' ∈ 𝒜 i')
    (b' : B) :
    (a ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) * (a' ᵍ⊗ₜ[R] b') = koszulSign (j * i') • ((a * a') ᵍ⊗ₜ[R] (b * b')) :=
  tmul_coe_mul_coe_tmul 𝒜 ℬ a ⟨b, hb⟩ ⟨a', ha'⟩ b'

theorem tmul_koszulSign_smul (a : A) (n : ℤ) (b : B) :
    (a ᵍ⊗ₜ[R] (koszulSign n • b) : 𝒜 ᵍ⊗[R] ℬ) = koszulSign n • (a ᵍ⊗ₜ[R] b) := by
  rw [Units.smul_def, Units.smul_def, ← Int.cast_smul_eq_zsmul R, ← Int.cast_smul_eq_zsmul R]
  change of R 𝒜 ℬ (a ⊗ₜ (((koszulSign n : ℤ) : R) • b)) =
    ((koszulSign n : ℤ) : R) • of R 𝒜 ℬ (a ⊗ₜ b)
  rw [TensorProduct.tmul_smul, LinearEquiv.map_smul]

theorem koszulSign_smul_tmul (n : ℤ) (a : A) (b : B) :
    ((koszulSign n • a) ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) = koszulSign n • (a ᵍ⊗ₜ[R] b) := by
  rw [Units.smul_def, Units.smul_def, ← Int.cast_smul_eq_zsmul R, ← Int.cast_smul_eq_zsmul R]
  change of R 𝒜 ℬ ((((koszulSign n : ℤ) : R) • a) ⊗ₜ b) =
    ((koszulSign n : ℤ) : R) • of R 𝒜 ℬ (a ⊗ₜ b)
  rw [← TensorProduct.smul_tmul', LinearEquiv.map_smul]

theorem tmul_zero (a : A) : (a ᵍ⊗ₜ[R] (0 : B) : 𝒜 ᵍ⊗[R] ℬ) = 0 := by
  change of R 𝒜 ℬ (a ⊗ₜ 0) = 0
  rw [TensorProduct.tmul_zero, map_zero]

theorem zero_tmul (b : B) : ((0 : A) ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) = 0 := by
  change of R 𝒜 ℬ (0 ⊗ₜ b) = 0
  rw [TensorProduct.zero_tmul, map_zero]

theorem tmul_add (a : A) (b b' : B) :
    (a ᵍ⊗ₜ[R] (b + b') : 𝒜 ᵍ⊗[R] ℬ) = a ᵍ⊗ₜ[R] b + a ᵍ⊗ₜ[R] b' := by
  change of R 𝒜 ℬ (a ⊗ₜ (b + b')) = of R 𝒜 ℬ (a ⊗ₜ b) + of R 𝒜 ℬ (a ⊗ₜ b')
  rw [TensorProduct.tmul_add, map_add]

theorem add_tmul (a a' : A) (b : B) :
    ((a + a') ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) = a ᵍ⊗ₜ[R] b + a' ᵍ⊗ₜ[R] b := by
  change of R 𝒜 ℬ ((a + a') ⊗ₜ b) = of R 𝒜 ℬ (a ⊗ₜ b) + of R 𝒜 ℬ (a' ⊗ₜ b)
  rw [TensorProduct.add_tmul, map_add]

/-- `(a ⊗ b) * (1 ⊗ b') = a ⊗ (b * b')`, for arbitrary `a`, `b`, `b'`. -/
theorem tmul_mul_one_tmul (a : A) (b b' : B) :
    (a ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) * ((1 : A) ᵍ⊗ₜ[R] b') = a ᵍ⊗ₜ[R] (b * b') := by
  refine DirectSum.Decomposition.inductionOn ℬ
    (motive := fun b => (a ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) * ((1 : A) ᵍ⊗ₜ[R] b') = a ᵍ⊗ₜ[R] (b * b'))
    ?_ ?_ ?_ b
  · show (a ᵍ⊗ₜ[R] (0 : B) : 𝒜 ᵍ⊗[R] ℬ) * ((1 : A) ᵍ⊗ₜ[R] b') = a ᵍ⊗ₜ[R] (0 * b')
    rw [tmul_zero, zero_mul, zero_mul, tmul_zero]
  · intro j b
    exact tmul_coe_mul_one_tmul 𝒜 ℬ a b b'
  · intro b₁ b₂ h₁ h₂
    show (a ᵍ⊗ₜ[R] (b₁ + b₂) : 𝒜 ᵍ⊗[R] ℬ) * ((1 : A) ᵍ⊗ₜ[R] b') = a ᵍ⊗ₜ[R] ((b₁ + b₂) * b')
    rw [tmul_add, add_mul, h₁, h₂, add_mul, tmul_add]

/-- `(a ⊗ 1) * (a' ⊗ b') = (a * a') ⊗ b'`, for arbitrary `a`, `a'`, `b'`. -/
theorem tmul_one_mul_tmul (a a' : A) (b' : B) :
    (a ᵍ⊗ₜ[R] (1 : B) : 𝒜 ᵍ⊗[R] ℬ) * (a' ᵍ⊗ₜ[R] b') = (a * a') ᵍ⊗ₜ[R] b' := by
  refine DirectSum.Decomposition.inductionOn 𝒜
    (motive := fun a' => (a ᵍ⊗ₜ[R] (1 : B) : 𝒜 ᵍ⊗[R] ℬ) * (a' ᵍ⊗ₜ[R] b') = (a * a') ᵍ⊗ₜ[R] b')
    ?_ ?_ ?_ a'
  · show (a ᵍ⊗ₜ[R] (1 : B) : 𝒜 ᵍ⊗[R] ℬ) * ((0 : A) ᵍ⊗ₜ[R] b') = (a * 0) ᵍ⊗ₜ[R] b'
    rw [zero_tmul, mul_zero, mul_zero, zero_tmul]
  · intro i a'
    exact tmul_one_mul_coe_tmul 𝒜 ℬ a a' b'
  · intro a₁ a₂ h₁ h₂
    show (a ᵍ⊗ₜ[R] (1 : B) : 𝒜 ᵍ⊗[R] ℬ) * ((a₁ + a₂) ᵍ⊗ₜ[R] b') = (a * (a₁ + a₂)) ᵍ⊗ₜ[R] b'
    rw [add_tmul, mul_add, h₁, h₂, mul_add, add_tmul]

/-! ### The grading -/

/-- The inclusion `𝒜 i ⊗[R] ℬ j →ₗ[R] 𝒜 ᵍ⊗[R] ℬ`. -/
def tmulIncl (i j : ℤ) : (𝒜 i ⊗[R] ℬ j) →ₗ[R] 𝒜 ᵍ⊗[R] ℬ :=
  (of R 𝒜 ℬ : A ⊗[R] B →ₗ[R] 𝒜 ᵍ⊗[R] ℬ) ∘ₗ TensorProduct.map (𝒜 i).subtype (ℬ j).subtype

@[simp] theorem tmulIncl_tmul {i j : ℤ} (a : 𝒜 i) (b : ℬ j) :
    tmulIncl 𝒜 ℬ i j (a ⊗ₜ b) = (a : A) ᵍ⊗ₜ[R] (b : B) := rfl

/-- The grading on `𝒜 ᵍ⊗[R] ℬ`: the degree-`n` piece is the sum over `i + j = n` of the images
of `𝒜 i ⊗[R] ℬ j`. -/
def grading (n : ℤ) : Submodule R (𝒜 ᵍ⊗[R] ℬ) :=
  ⨆ p : {p : ℤ × ℤ // p.1 + p.2 = n}, LinearMap.range (tmulIncl 𝒜 ℬ p.1.1 p.1.2)

theorem tmulIncl_mem {i j : ℤ} (z : 𝒜 i ⊗[R] ℬ j) : tmulIncl 𝒜 ℬ i j z ∈ grading 𝒜 ℬ (i + j) :=
  Submodule.mem_iSup_of_mem ⟨(i, j), rfl⟩ (LinearMap.mem_range_self _ z)

theorem tmul_mem {i j : ℤ} {a : A} (ha : a ∈ 𝒜 i) {b : B} (hb : b ∈ ℬ j) :
    (a ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) ∈ grading 𝒜 ℬ (i + j) :=
  tmulIncl_mem 𝒜 ℬ (⟨a, ha⟩ ⊗ₜ ⟨b, hb⟩)

theorem tmul_mem_of_eq {i j n : ℤ} (h : i + j = n) {a : A} (ha : a ∈ 𝒜 i) {b : B}
    (hb : b ∈ ℬ j) : (a ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) ∈ grading 𝒜 ℬ n :=
  h ▸ tmul_mem 𝒜 ℬ ha hb

/-- Induction principle for elements of degree `n`: it suffices to consider `0`, pure tensors
`a ⊗ b` with `a`, `b` homogeneous of degrees adding up to `n`, and sums. -/
theorem grading_induction {n : ℤ} {motive : (𝒜 ᵍ⊗[R] ℬ) → Prop} {x : 𝒜 ᵍ⊗[R] ℬ}
    (hx : x ∈ grading 𝒜 ℬ n) (zero : motive 0)
    (tmul : ∀ {i j : ℤ} (a : 𝒜 i) (b : ℬ j), i + j = n → motive ((a : A) ᵍ⊗ₜ[R] (b : B)))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive x := by
  refine Submodule.iSup_induction _ (motive := motive) hx ?_ zero add
  rintro ⟨⟨i, j⟩, hij⟩ x ⟨z, rfl⟩
  induction z using TensorProduct.inductionOn with
  | tmul a b => exact tmul a b hij
  | add z z' hz hz' => rw [map_add]; exact add _ _ hz hz'

set_option backward.isDefEq.respectTransparency false in
instance instGradedMonoid : SetLike.GradedMonoid (grading 𝒜 ℬ) where
  one_mem := by
    rw [one_def]
    exact tmul_mem_of_eq 𝒜 ℬ (add_zero 0) (SetLike.one_mem_graded 𝒜) (SetLike.one_mem_graded ℬ)
  mul_mem {m n} x y hx hy := by
    refine grading_induction 𝒜 ℬ hx (motive := fun x => x * y ∈ grading 𝒜 ℬ (m + n)) ?_ ?_ ?_
    · rw [zero_mul]; exact zero_mem _
    · intro i j a b hij
      refine grading_induction 𝒜 ℬ hy
        (motive := fun y => ((a : A) ᵍ⊗ₜ[R] (b : B)) * y ∈ grading 𝒜 ℬ (m + n)) ?_ ?_ ?_
      · rw [mul_zero]; exact zero_mem _
      · intro i' j' a' b' hij'
        rw [tmul_mul_tmul 𝒜 ℬ _ b.2 a'.2, Units.smul_def]
        refine zsmul_mem ?_ _
        have h : i + i' + (j + j') = m + n := by omega
        rw [← h]
        exact tmul_mem 𝒜 ℬ (SetLike.mul_mem_graded a.2 a'.2) (SetLike.mul_mem_graded b.2 b'.2)
      · intro y y' hy hy'
        rw [mul_add]; exact add_mem hy hy'
    · intro x x' hx hx'
      rw [add_mul]; exact add_mem hx hx'

/-- The linear equivalence of `𝒜 ᵍ⊗[R] ℬ` with the external direct sum of the
`𝒜 i ⊗[R] ℬ j`. -/
def auxEquiv' : (𝒜 ᵍ⊗[R] ℬ) ≃ₗ[R] ⨁ p : ℤ × ℤ, (𝒜 p.1 ⊗[R] ℬ p.2) :=
  auxEquiv R 𝒜 ℬ ≪≫ₗ TensorProduct.directSum R R (𝒜 ·) (ℬ ·)

theorem auxEquiv'_tmul {i j : ℤ} (a : 𝒜 i) (b : ℬ j) :
    auxEquiv' 𝒜 ℬ ((a : A) ᵍ⊗ₜ[R] (b : B)) =
      lof R (ℤ × ℤ) (fun p => 𝒜 p.1 ⊗[R] ℬ p.2) (i, j) (a ⊗ₜ b) := by
  rw [auxEquiv', LinearEquiv.trans_apply, auxEquiv_tmul, decompose_coe, decompose_coe,
    ← lof_eq_of R, ← lof_eq_of R, directSum_lof_tmul_lof]

theorem auxEquiv'_comp_tmulIncl (i j : ℤ) :
    (auxEquiv' 𝒜 ℬ : (𝒜 ᵍ⊗[R] ℬ) →ₗ[R] _) ∘ₗ tmulIncl 𝒜 ℬ i j =
      lof R (ℤ × ℤ) (fun p => 𝒜 p.1 ⊗[R] ℬ p.2) (i, j) :=
  TensorProduct.ext' fun a b => by
    rw [LinearMap.comp_apply, tmulIncl_tmul, LinearEquiv.coe_coe, auxEquiv'_tmul]

theorem auxEquiv'_tmulIncl (i j : ℤ) (z : 𝒜 i ⊗[R] ℬ j) :
    auxEquiv' 𝒜 ℬ (tmulIncl 𝒜 ℬ i j z) = lof R (ℤ × ℤ) (fun p => 𝒜 p.1 ⊗[R] ℬ p.2) (i, j) z :=
  LinearMap.congr_fun (auxEquiv'_comp_tmulIncl 𝒜 ℬ i j) z

theorem auxEquiv'_symm_lof (i j : ℤ) (z : 𝒜 i ⊗[R] ℬ j) :
    (auxEquiv' 𝒜 ℬ).symm (lof R (ℤ × ℤ) (fun p => 𝒜 p.1 ⊗[R] ℬ p.2) (i, j) z) =
      tmulIncl 𝒜 ℬ i j z := by
  rw [LinearEquiv.symm_apply_eq, auxEquiv'_tmulIncl]

/-- The decomposition of the external direct sum of the `𝒜 i ⊗[R] ℬ j` into the graded pieces
of `𝒜 ᵍ⊗[R] ℬ`. -/
def decomposeAux : (⨁ p : ℤ × ℤ, (𝒜 p.1 ⊗[R] ℬ p.2)) →ₗ[R] ⨁ n, grading 𝒜 ℬ n :=
  DirectSum.toModule R _ _ fun p => lof R ℤ (grading 𝒜 ℬ ·) (p.1 + p.2) ∘ₗ
    (tmulIncl 𝒜 ℬ p.1 p.2).codRestrict (grading 𝒜 ℬ (p.1 + p.2)) (tmulIncl_mem 𝒜 ℬ)

theorem decomposeAux_lof (p : ℤ × ℤ) (z : 𝒜 p.1 ⊗[R] ℬ p.2) :
    decomposeAux 𝒜 ℬ (lof R (ℤ × ℤ) (fun p => 𝒜 p.1 ⊗[R] ℬ p.2) p z) =
      lof R ℤ (grading 𝒜 ℬ ·) (p.1 + p.2) ⟨tmulIncl 𝒜 ℬ p.1 p.2 z, tmulIncl_mem 𝒜 ℬ z⟩ := by
  unfold decomposeAux; rw [DirectSum.toModule_lof]; rfl

theorem coeLinearMap_comp_decomposeAux :
    coeLinearMap (grading 𝒜 ℬ) ∘ₗ decomposeAux 𝒜 ℬ = ((auxEquiv' 𝒜 ℬ).symm : _ →ₗ[R] _) := by
  refine DirectSum.linearMap_ext _ fun p => ?_
  obtain ⟨i, j⟩ := p
  refine LinearMap.ext fun z => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, decomposeAux_lof]
  simp only [lof_eq_of, coeLinearMap_of, LinearEquiv.coe_coe]
  exact (auxEquiv'_symm_lof 𝒜 ℬ i j z).symm

instance instDecomposition : DirectSum.Decomposition (grading 𝒜 ℬ) :=
  DirectSum.Decomposition.ofLinearMap _
    (decomposeAux 𝒜 ℬ ∘ₗ (auxEquiv' 𝒜 ℬ : (𝒜 ᵍ⊗[R] ℬ) →ₗ[R] _))
    (by
      rw [← LinearMap.comp_assoc, coeLinearMap_comp_decomposeAux]
      exact LinearMap.ext fun x => by
        rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
          LinearEquiv.symm_apply_apply, LinearMap.id_apply])
    (by
      refine DirectSum.linearMap_ext _ fun n => LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, lof_eq_of, coeLinearMap_of,
        LinearMap.id_apply]
      obtain ⟨x, hx⟩ := x
      refine Submodule.iSup_induction' (motive := fun x hx =>
        decomposeAux 𝒜 ℬ (auxEquiv' 𝒜 ℬ x) = of (fun n => grading 𝒜 ℬ n) n ⟨x, hx⟩) _
        ?_ ?_ ?_ hx
      · rintro ⟨⟨i, j⟩, hij⟩ x ⟨z, rfl⟩
        simp only at hij
        subst hij
        rw [auxEquiv'_tmulIncl, decomposeAux_lof, lof_eq_of]
      · show decomposeAux 𝒜 ℬ (auxEquiv' 𝒜 ℬ 0) = of (fun n => grading 𝒜 ℬ n) n ⟨0, zero_mem _⟩
        rw [map_zero, map_zero]
        exact (map_zero _).symm
      · intro x y hx hy ihx ihy
        show decomposeAux 𝒜 ℬ (auxEquiv' 𝒜 ℬ (x + y)) =
          of (fun n => grading 𝒜 ℬ n) n ⟨x + y, add_mem hx hy⟩
        rw [map_add, map_add, ihx, ihy, ← map_add]
        rfl)

instance instGradedAlgebra : GradedAlgebra (grading 𝒜 ℬ) :=
  { instGradedMonoid 𝒜 ℬ, instDecomposition 𝒜 ℬ with }

/-! ### Degrees of the inclusions and of the symmetry -/

theorem includeLeft_mem {i : ℤ} {a : A} (ha : a ∈ 𝒜 i) : includeLeft 𝒜 ℬ a ∈ grading 𝒜 ℬ i :=
  tmul_mem_of_eq 𝒜 ℬ (add_zero i) ha (SetLike.one_mem_graded ℬ)

theorem includeRight_mem {j : ℤ} {b : B} (hb : b ∈ ℬ j) :
    includeRight 𝒜 ℬ b ∈ grading 𝒜 ℬ j :=
  tmul_mem_of_eq 𝒜 ℬ (zero_add j) (SetLike.one_mem_graded 𝒜) hb

/-- The symmetry `comm 𝒜 ℬ : 𝒜 ᵍ⊗[R] ℬ ≃ₐ[R] ℬ ᵍ⊗[R] 𝒜` on a pure tensor of homogeneous
elements: `a ⊗ b ↦ (-1)^(i * j) • (b ⊗ a)`. -/
theorem comm_tmul {i j : ℤ} {a : A} (ha : a ∈ 𝒜 i) {b : B} (hb : b ∈ ℬ j) :
    comm 𝒜 ℬ (a ᵍ⊗ₜ[R] b) = koszulSign (i * j) • (b ᵍ⊗ₜ[R] a : ℬ ᵍ⊗[R] 𝒜) := by
  have h := comm_coe_tmul_coe 𝒜 ℬ ⟨a, ha⟩ ⟨b, hb⟩
  rw [mul_comm j i] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem comm_mem {n : ℤ} {x : 𝒜 ᵍ⊗[R] ℬ} (hx : x ∈ grading 𝒜 ℬ n) :
    comm 𝒜 ℬ x ∈ grading ℬ 𝒜 n := by
  refine grading_induction 𝒜 ℬ hx (motive := fun x => comm 𝒜 ℬ x ∈ grading ℬ 𝒜 n) ?_ ?_ ?_
  · rw [map_zero]; exact zero_mem _
  · intro i j a b hij
    rw [comm_tmul 𝒜 ℬ a.2 b.2, Units.smul_def]
    exact zsmul_mem (tmul_mem_of_eq ℬ 𝒜 (by rw [add_comm]; exact hij) b.2 a.2) _
  · intro x y hx hy
    rw [map_add]; exact add_mem hx hy

theorem comm_tmul_one (a : A) : comm 𝒜 ℬ (a ᵍ⊗ₜ[R] (1 : B)) = (1 : B) ᵍ⊗ₜ[R] a := by
  refine DirectSum.Decomposition.inductionOn 𝒜
    (motive := fun a => comm 𝒜 ℬ (a ᵍ⊗ₜ[R] (1 : B)) = (1 : B) ᵍ⊗ₜ[R] a) ?_ ?_ ?_ a
  · show comm 𝒜 ℬ ((0 : A) ᵍ⊗ₜ[R] (1 : B)) = (1 : B) ᵍ⊗ₜ[R] (0 : A)
    rw [zero_tmul, map_zero, tmul_zero]
  · intro i a
    rw [comm_tmul 𝒜 ℬ a.2 (SetLike.one_mem_graded ℬ), mul_zero, koszulSign_zero, one_smul]
  · intro a a' h h'
    show comm 𝒜 ℬ ((a + a') ᵍ⊗ₜ[R] (1 : B)) = (1 : B) ᵍ⊗ₜ[R] (a + a')
    rw [add_tmul, map_add, h, h', tmul_add]

theorem comm_one_tmul (b : B) : comm 𝒜 ℬ ((1 : A) ᵍ⊗ₜ[R] b) = b ᵍ⊗ₜ[R] (1 : A) := by
  refine DirectSum.Decomposition.inductionOn ℬ
    (motive := fun b => comm 𝒜 ℬ ((1 : A) ᵍ⊗ₜ[R] b) = b ᵍ⊗ₜ[R] (1 : A)) ?_ ?_ ?_ b
  · show comm 𝒜 ℬ ((1 : A) ᵍ⊗ₜ[R] (0 : B)) = (0 : B) ᵍ⊗ₜ[R] (1 : A)
    rw [tmul_zero, map_zero, zero_tmul]
  · intro j b
    rw [comm_tmul 𝒜 ℬ (SetLike.one_mem_graded 𝒜) b.2, zero_mul, koszulSign_zero, one_smul]
  · intro b b' h h'
    show comm 𝒜 ℬ ((1 : A) ᵍ⊗ₜ[R] (b + b')) = (b + b') ᵍ⊗ₜ[R] (1 : A)
    rw [tmul_add, map_add, h, h', add_tmul]

theorem comm_comp_comm :
    (comm ℬ 𝒜).toAlgHom.comp (comm 𝒜 ℬ).toAlgHom = AlgHom.id R (𝒜 ᵍ⊗[R] ℬ) := by
  refine algHom_ext 𝒜 ℬ (AlgHom.ext fun a => ?_) (AlgHom.ext fun b => ?_)
  · simp only [AlgHom.comp_apply, AlgHom.id_apply, includeLeft_apply, AlgEquiv.coe_toAlgHom,
      comm_tmul_one, comm_one_tmul]
  · simp only [AlgHom.comp_apply, AlgHom.id_apply, includeRight_apply, AlgEquiv.coe_toAlgHom,
      comm_one_tmul, comm_tmul_one]

theorem comm_comm (x : 𝒜 ᵍ⊗[R] ℬ) : comm ℬ 𝒜 (comm 𝒜 ℬ x) = x :=
  AlgHom.congr_fun (comm_comp_comm 𝒜 ℬ) x

theorem comm_symm : (comm 𝒜 ℬ).symm = comm ℬ 𝒜 :=
  AlgEquiv.ext fun x => by
    rw [AlgEquiv.symm_apply_eq, comm_comm]

/-- The symmetry preserves degrees. -/
theorem comm_mem_iff {n : ℤ} {x : 𝒜 ᵍ⊗[R] ℬ} :
    comm 𝒜 ℬ x ∈ grading ℬ 𝒜 n ↔ x ∈ grading 𝒜 ℬ n :=
  ⟨fun h => by simpa only [comm_comm] using comm_mem ℬ 𝒜 h, comm_mem 𝒜 ℬ⟩

/-! ### Associativity -/

/-- The algebra map `𝒜 ᵍ⊗ ℬ →ₐ 𝒜 ᵍ⊗ (ℬ ᵍ⊗ 𝒞)`, `a ⊗ b ↦ a ⊗ (b ⊗ 1)`. -/
def assocAuxLeft : (𝒜 ᵍ⊗[R] ℬ) →ₐ[R] GradedTensorProduct R 𝒜 (grading ℬ 𝒞) :=
  lift 𝒜 ℬ (includeLeft 𝒜 (grading ℬ 𝒞)) ((includeRight 𝒜 (grading ℬ 𝒞)).comp (includeLeft ℬ 𝒞))
    fun i j a b => by
      simp only [AlgHom.comp_apply, includeLeft_apply, includeRight_apply]
      rw [tmul_one_mul_one_tmul,
        tmul_mul_tmul 𝒜 (grading ℬ 𝒞) (1 : A)
          (tmul_mem_of_eq ℬ 𝒞 (add_zero j) b.2 (SetLike.one_mem_graded 𝒞)) a.2,
        one_mul, mul_one, uzpow_neg_one_eq_koszulSign, smul_smul, Int.units_mul_self, one_smul]

theorem assocAuxLeft_tmul (a : A) (b : B) :
    assocAuxLeft 𝒜 ℬ 𝒞 (a ᵍ⊗ₜ[R] b) = a ᵍ⊗ₜ[R] (b ᵍ⊗ₜ[R] (1 : C) : ℬ ᵍ⊗[R] 𝒞) := by
  rw [assocAuxLeft, lift_tmul, AlgHom.comp_apply, includeLeft_apply, includeRight_apply,
    includeLeft_apply, tmul_one_mul_one_tmul]

set_option backward.isDefEq.respectTransparency false in
/-- The algebra map `(𝒜 ᵍ⊗ ℬ) ᵍ⊗ 𝒞 →ₐ 𝒜 ᵍ⊗ (ℬ ᵍ⊗ 𝒞)`, `(a ⊗ b) ⊗ c ↦ a ⊗ (b ⊗ c)`. -/
def assocHom :
    GradedTensorProduct R (grading 𝒜 ℬ) 𝒞 →ₐ[R] GradedTensorProduct R 𝒜 (grading ℬ 𝒞) :=
  lift (grading 𝒜 ℬ) 𝒞 (assocAuxLeft 𝒜 ℬ 𝒞)
    ((includeRight 𝒜 (grading ℬ 𝒞)).comp (includeRight ℬ 𝒞)) fun n k x c => by
      obtain ⟨x, hx⟩ := x
      refine grading_induction 𝒜 ℬ hx (motive := fun x =>
        assocAuxLeft 𝒜 ℬ 𝒞 x * ((includeRight 𝒜 (grading ℬ 𝒞)).comp (includeRight ℬ 𝒞)) c =
          (-1 : ℤˣ) ^ (k * n) •
            (((includeRight 𝒜 (grading ℬ 𝒞)).comp (includeRight ℬ 𝒞)) c *
              assocAuxLeft 𝒜 ℬ 𝒞 x)) ?_ ?_ ?_
      · rw [map_zero, zero_mul, mul_zero, smul_zero]
      · intro i j a b hij
        subst hij
        rw [assocAuxLeft_tmul, AlgHom.comp_apply, includeRight_apply, includeRight_apply,
          tmul_mul_tmul 𝒜 (grading ℬ 𝒞) _
            (tmul_mem_of_eq ℬ 𝒞 (add_zero j) b.2 (SetLike.one_mem_graded 𝒞))
            (SetLike.one_mem_graded 𝒜),
          mul_zero, koszulSign_zero, one_smul, mul_one, tmul_one_mul_one_tmul,
          tmul_mul_tmul 𝒜 (grading ℬ 𝒞) _
            (tmul_mem_of_eq ℬ 𝒞 (zero_add k) (SetLike.one_mem_graded ℬ) c.2) a.2,
          tmul_mul_tmul ℬ 𝒞 _ c.2 b.2, one_mul, one_mul, mul_one, tmul_koszulSign_smul,
          smul_smul, smul_smul, uzpow_neg_one_eq_koszulSign, ← koszulSign_add, ← koszulSign_add,
          show k * (i + j) + k * i + k * j = 2 * (k * (i + j)) by ring,
          koszulSign_even (even_two_mul _), one_smul]
      · intro x y hx hy
        rw [map_add, add_mul, mul_add, hx, hy, smul_add]

set_option backward.isDefEq.respectTransparency false in
theorem assocHom_tmul_tmul (a : A) (b : B) (c : C) :
    assocHom 𝒜 ℬ 𝒞 ((a ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) ᵍ⊗ₜ[R] c) =
      a ᵍ⊗ₜ[R] (b ᵍ⊗ₜ[R] c : ℬ ᵍ⊗[R] 𝒞) := by
  rw [assocHom, lift_tmul, assocAuxLeft_tmul, AlgHom.comp_apply, includeRight_apply,
    includeRight_apply, tmul_mul_one_tmul, tmul_one_mul_one_tmul]

/-- The algebra map `ℬ ᵍ⊗ 𝒞 →ₐ (𝒜 ᵍ⊗ ℬ) ᵍ⊗ 𝒞`, `b ⊗ c ↦ (1 ⊗ b) ⊗ c`. -/
def assocInvAux : (ℬ ᵍ⊗[R] 𝒞) →ₐ[R] GradedTensorProduct R (grading 𝒜 ℬ) 𝒞 :=
  lift ℬ 𝒞 ((includeLeft (grading 𝒜 ℬ) 𝒞).comp (includeRight 𝒜 ℬ))
    (includeRight (grading 𝒜 ℬ) 𝒞) fun j k b c => by
      simp only [AlgHom.comp_apply, includeLeft_apply, includeRight_apply]
      rw [tmul_one_mul_one_tmul,
        tmul_mul_tmul (grading 𝒜 ℬ) 𝒞 (1 : 𝒜 ᵍ⊗[R] ℬ) c.2
          (tmul_mem_of_eq 𝒜 ℬ (zero_add j) (SetLike.one_mem_graded 𝒜) b.2) (1 : C),
        one_mul, mul_one, uzpow_neg_one_eq_koszulSign, smul_smul, Int.units_mul_self, one_smul]

theorem assocInvAux_tmul (b : B) (c : C) :
    assocInvAux 𝒜 ℬ 𝒞 (b ᵍ⊗ₜ[R] c) = ((1 : A) ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) ᵍ⊗ₜ[R] c := by
  rw [assocInvAux, lift_tmul, AlgHom.comp_apply, includeRight_apply, includeLeft_apply,
    includeRight_apply, tmul_one_mul_one_tmul]

set_option backward.isDefEq.respectTransparency false in
/-- The algebra map `𝒜 ᵍ⊗ (ℬ ᵍ⊗ 𝒞) →ₐ (𝒜 ᵍ⊗ ℬ) ᵍ⊗ 𝒞`, `a ⊗ (b ⊗ c) ↦ (a ⊗ b) ⊗ c`. -/
def assocInv :
    GradedTensorProduct R 𝒜 (grading ℬ 𝒞) →ₐ[R] GradedTensorProduct R (grading 𝒜 ℬ) 𝒞 :=
  lift 𝒜 (grading ℬ 𝒞) ((includeLeft (grading 𝒜 ℬ) 𝒞).comp (includeLeft 𝒜 ℬ))
    (assocInvAux 𝒜 ℬ 𝒞) fun i n a y => by
      obtain ⟨y, hy⟩ := y
      refine grading_induction ℬ 𝒞 hy (motive := fun y =>
        ((includeLeft (grading 𝒜 ℬ) 𝒞).comp (includeLeft 𝒜 ℬ)) a * assocInvAux 𝒜 ℬ 𝒞 y =
          (-1 : ℤˣ) ^ (n * i) •
            (assocInvAux 𝒜 ℬ 𝒞 y *
              ((includeLeft (grading 𝒜 ℬ) 𝒞).comp (includeLeft 𝒜 ℬ)) a)) ?_ ?_ ?_
      · rw [map_zero, mul_zero, zero_mul, smul_zero]
      · intro j k b c hjk
        subst hjk
        rw [assocInvAux_tmul, AlgHom.comp_apply, includeLeft_apply, includeLeft_apply,
          tmul_one_mul_tmul, tmul_one_mul_one_tmul,
          tmul_mul_tmul (grading 𝒜 ℬ) 𝒞 _ c.2
            (tmul_mem_of_eq 𝒜 ℬ (add_zero i) a.2 (SetLike.one_mem_graded ℬ)) (1 : C),
          tmul_mul_tmul 𝒜 ℬ _ b.2 a.2, one_mul, mul_one, mul_one, koszulSign_smul_tmul,
          smul_smul, smul_smul, uzpow_neg_one_eq_koszulSign, ← koszulSign_add, ← koszulSign_add,
          show (j + k) * i + k * i + j * i = 2 * ((j + k) * i) by ring,
          koszulSign_even (even_two_mul _), one_smul]
      · intro y y' hy hy'
        rw [map_add, mul_add, add_mul, hy, hy', smul_add]

set_option backward.isDefEq.respectTransparency false in
theorem assocInv_tmul_tmul (a : A) (b : B) (c : C) :
    assocInv 𝒜 ℬ 𝒞 (a ᵍ⊗ₜ[R] (b ᵍ⊗ₜ[R] c : ℬ ᵍ⊗[R] 𝒞)) =
      (a ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) ᵍ⊗ₜ[R] c := by
  rw [assocInv, lift_tmul, assocInvAux_tmul, AlgHom.comp_apply, includeLeft_apply,
    includeLeft_apply, tmul_one_mul_tmul, tmul_one_mul_one_tmul]

theorem assocHom_comp_assocInv :
    (assocHom 𝒜 ℬ 𝒞).comp (assocInv 𝒜 ℬ 𝒞) = AlgHom.id R _ := by
  refine algHom_ext 𝒜 (grading ℬ 𝒞) (AlgHom.ext fun a => ?_) ?_
  · simp only [AlgHom.comp_apply, AlgHom.id_apply]
    rw [includeLeft_apply, one_def ℬ 𝒞, assocInv_tmul_tmul, assocHom_tmul_tmul]
  · refine algHom_ext ℬ 𝒞 (AlgHom.ext fun b => ?_) (AlgHom.ext fun c => ?_)
    · simp only [AlgHom.comp_apply, AlgHom.id_apply]
      rw [includeLeft_apply, includeRight_apply, assocInv_tmul_tmul, assocHom_tmul_tmul]
    · simp only [AlgHom.comp_apply, AlgHom.id_apply]
      rw [includeRight_apply, includeRight_apply, assocInv_tmul_tmul, assocHom_tmul_tmul]

theorem assocInv_comp_assocHom :
    (assocInv 𝒜 ℬ 𝒞).comp (assocHom 𝒜 ℬ 𝒞) = AlgHom.id R _ := by
  refine algHom_ext (grading 𝒜 ℬ) 𝒞 ?_ (AlgHom.ext fun c => ?_)
  · refine algHom_ext 𝒜 ℬ (AlgHom.ext fun a => ?_) (AlgHom.ext fun b => ?_)
    · simp only [AlgHom.comp_apply, AlgHom.id_apply]
      rw [includeLeft_apply, includeLeft_apply, assocHom_tmul_tmul, assocInv_tmul_tmul]
    · simp only [AlgHom.comp_apply, AlgHom.id_apply]
      rw [includeRight_apply, includeLeft_apply, assocHom_tmul_tmul, assocInv_tmul_tmul]
  · simp only [AlgHom.comp_apply, AlgHom.id_apply]
    rw [includeRight_apply, one_def 𝒜 ℬ, assocHom_tmul_tmul, assocInv_tmul_tmul]

/-- The associativity isomorphism `(𝒜 ᵍ⊗ ℬ) ᵍ⊗ 𝒞 ≃ₐ[R] 𝒜 ᵍ⊗ (ℬ ᵍ⊗ 𝒞)` of graded tensor
products, `(a ⊗ b) ⊗ c ↦ a ⊗ (b ⊗ c)`. It preserves degrees (`assoc_mem_iff`). -/
def assoc :
    GradedTensorProduct R (grading 𝒜 ℬ) 𝒞 ≃ₐ[R] GradedTensorProduct R 𝒜 (grading ℬ 𝒞) :=
  AlgEquiv.ofAlgHom (assocHom 𝒜 ℬ 𝒞) (assocInv 𝒜 ℬ 𝒞) (assocHom_comp_assocInv 𝒜 ℬ 𝒞)
    (assocInv_comp_assocHom 𝒜 ℬ 𝒞)

@[simp] theorem assoc_tmul_tmul (a : A) (b : B) (c : C) :
    assoc 𝒜 ℬ 𝒞 ((a ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) ᵍ⊗ₜ[R] c) = a ᵍ⊗ₜ[R] (b ᵍ⊗ₜ[R] c : ℬ ᵍ⊗[R] 𝒞) :=
  assocHom_tmul_tmul 𝒜 ℬ 𝒞 a b c

@[simp] theorem assoc_symm_tmul_tmul (a : A) (b : B) (c : C) :
    (assoc 𝒜 ℬ 𝒞).symm (a ᵍ⊗ₜ[R] (b ᵍ⊗ₜ[R] c : ℬ ᵍ⊗[R] 𝒞)) =
      (a ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) ᵍ⊗ₜ[R] c :=
  assocInv_tmul_tmul 𝒜 ℬ 𝒞 a b c

theorem assoc_mem {n : ℤ} {x : GradedTensorProduct R (grading 𝒜 ℬ) 𝒞}
    (hx : x ∈ grading (grading 𝒜 ℬ) 𝒞 n) : assoc 𝒜 ℬ 𝒞 x ∈ grading 𝒜 (grading ℬ 𝒞) n := by
  refine grading_induction (grading 𝒜 ℬ) 𝒞 hx
    (motive := fun x => assoc 𝒜 ℬ 𝒞 x ∈ grading 𝒜 (grading ℬ 𝒞) n) ?_ ?_ ?_
  · rw [map_zero]; exact zero_mem _
  · intro m k x c hmk
    obtain ⟨x, hx⟩ := x
    refine grading_induction 𝒜 ℬ hx
      (motive := fun x => assoc 𝒜 ℬ 𝒞 (x ᵍ⊗ₜ[R] (c : C)) ∈ grading 𝒜 (grading ℬ 𝒞) n) ?_ ?_ ?_
    · rw [zero_tmul, map_zero]; exact zero_mem _
    · intro i j a b hij
      rw [assoc_tmul_tmul]
      exact tmul_mem_of_eq 𝒜 (grading ℬ 𝒞) (by omega) a.2 (tmul_mem ℬ 𝒞 b.2 c.2)
    · intro x y hx hy
      rw [add_tmul, map_add]; exact add_mem hx hy
  · intro x y hx hy
    rw [map_add]; exact add_mem hx hy

theorem assoc_symm_mem {n : ℤ} {y : GradedTensorProduct R 𝒜 (grading ℬ 𝒞)}
    (hy : y ∈ grading 𝒜 (grading ℬ 𝒞) n) :
    (assoc 𝒜 ℬ 𝒞).symm y ∈ grading (grading 𝒜 ℬ) 𝒞 n := by
  refine grading_induction 𝒜 (grading ℬ 𝒞) hy
    (motive := fun y => (assoc 𝒜 ℬ 𝒞).symm y ∈ grading (grading 𝒜 ℬ) 𝒞 n) ?_ ?_ ?_
  · rw [map_zero]; exact zero_mem _
  · intro i m a y him
    obtain ⟨y, hy⟩ := y
    refine grading_induction ℬ 𝒞 hy
      (motive := fun y => (assoc 𝒜 ℬ 𝒞).symm ((a : A) ᵍ⊗ₜ[R] y) ∈ grading (grading 𝒜 ℬ) 𝒞 n)
      ?_ ?_ ?_
    · rw [tmul_zero, map_zero]; exact zero_mem _
    · intro j k b c hjk
      rw [assoc_symm_tmul_tmul]
      exact tmul_mem_of_eq (grading 𝒜 ℬ) 𝒞 (by omega) (tmul_mem 𝒜 ℬ a.2 b.2) c.2
    · intro y y' hy hy'
      rw [tmul_add, map_add]; exact add_mem hy hy'
  · intro y y' hy hy'
    rw [map_add]; exact add_mem hy hy'

/-- The associativity isomorphism preserves degrees. -/
theorem assoc_mem_iff {n : ℤ} {x : GradedTensorProduct R (grading 𝒜 ℬ) 𝒞} :
    assoc 𝒜 ℬ 𝒞 x ∈ grading 𝒜 (grading ℬ 𝒞) n ↔ x ∈ grading (grading 𝒜 ℬ) 𝒞 n :=
  ⟨fun h => by simpa only [AlgEquiv.symm_apply_apply] using assoc_symm_mem 𝒜 ℬ 𝒞 h,
    assoc_mem 𝒜 ℬ 𝒞⟩

/-! ### The unit -/

/-- The algebra map `R ᵍ⊗ ℬ →ₐ B`, `r ⊗ b ↦ r • b`, for `R` graded in degree `0`. -/
def lidHom : GradedTensorProduct R (trivialGrading R R) ℬ →ₐ[R] B :=
  lift (trivialGrading R R) ℬ (Algebra.ofId R B) (AlgHom.id R B) fun i j r b => by
    rw [Algebra.ofId_apply, AlgHom.id_apply]
    by_cases hi : i = 0
    · subst hi
      rw [mul_zero, uzpow_zero, one_smul, Algebra.commutes]
    · rw [eq_zero_of_mem_trivialGrading R R hi r.2, map_zero, zero_mul, mul_zero, smul_zero]

theorem lidHom_tmul (r : R) (b : B) : lidHom ℬ (r ᵍ⊗ₜ[R] b) = r • b := by
  rw [lidHom, lift_tmul, Algebra.ofId_apply, AlgHom.id_apply, Algebra.smul_def]

/-- The unit isomorphism `R ᵍ⊗ ℬ ≃ₐ[R] B`, `r ⊗ b ↦ r • b`, where `R` is graded in degree `0`
(`trivialGrading R R`). It preserves degrees (`lid_mem_iff`). -/
def lid : GradedTensorProduct R (trivialGrading R R) ℬ ≃ₐ[R] B :=
  AlgEquiv.ofAlgHom (lidHom ℬ) (includeRight (trivialGrading R R) ℬ)
    (AlgHom.ext fun b => by
      rw [AlgHom.comp_apply, AlgHom.id_apply, includeRight_apply, lidHom_tmul, one_smul])
    (by
      refine algHom_ext _ ℬ (AlgHom.ext fun r => ?_) (AlgHom.ext fun b => ?_)
      · rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.id_apply,
          show includeLeft (trivialGrading R R) ℬ r = algebraMap R _ r from
            (includeLeft (trivialGrading R R) ℬ).commutes r,
          AlgHom.commutes, AlgHom.commutes]
      · simp only [AlgHom.comp_apply, AlgHom.id_apply, includeRight_apply, lidHom_tmul,
          one_smul])

@[simp] theorem lid_tmul (r : R) (b : B) : lid ℬ (r ᵍ⊗ₜ[R] b) = r • b := lidHom_tmul ℬ r b

@[simp] theorem lid_symm_apply (b : B) :
    (lid ℬ).symm b = ((1 : R) ᵍ⊗ₜ[R] b : GradedTensorProduct R (trivialGrading R R) ℬ) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem lid_mem {n : ℤ} {x : GradedTensorProduct R (trivialGrading R R) ℬ}
    (hx : x ∈ grading (trivialGrading R R) ℬ n) : lid ℬ x ∈ ℬ n := by
  refine grading_induction _ ℬ hx (motive := fun x => lid ℬ x ∈ ℬ n) ?_ ?_ ?_
  · rw [map_zero]; exact zero_mem _
  · intro i j r b hij
    rw [lid_tmul]
    by_cases hi : i = 0
    · subst hi
      rw [zero_add] at hij
      subst hij
      exact Submodule.smul_mem _ _ b.2
    · rw [eq_zero_of_mem_trivialGrading R R hi r.2, zero_smul]; exact zero_mem _
  · intro x y hx hy
    rw [map_add]; exact add_mem hx hy

theorem lid_symm_mem {n : ℤ} {b : B} (hb : b ∈ ℬ n) :
    (lid ℬ).symm b ∈ grading (trivialGrading R R) ℬ n := by
  rw [lid_symm_apply]
  exact tmul_mem_of_eq _ ℬ (zero_add n) (mem_trivialGrading_zero R R 1) hb

/-- The unit isomorphism preserves degrees. -/
theorem lid_mem_iff {n : ℤ} {x : GradedTensorProduct R (trivialGrading R R) ℬ} :
    lid ℬ x ∈ ℬ n ↔ x ∈ grading (trivialGrading R R) ℬ n :=
  ⟨fun h => by simpa only [AlgEquiv.symm_apply_apply] using lid_symm_mem ℬ h, lid_mem ℬ⟩

end GradedTensorProduct

end DG
