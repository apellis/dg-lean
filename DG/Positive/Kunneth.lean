import DG.Algebra.TensorProduct
import DG.Positive.SplitTensor
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Künneth formula for `K₀` of positive dg algebras

Let `k` be a field and `A`, `B` positive dg `k`-algebras (`DG.IsPositive`). Their tensor product
`A ⊗_k B` (the graded tensor product `DG.GradedTensorProduct`, with the Koszul sign rule) has
degree-`0` part `A⁰ ⊗_k B⁰` (`DG.degreeZeroTensorEquiv`), since `A` and `B` have no components of
negative degree. This file proves Roadmap 6.5 under a splitting hypothesis.

## The hypothesis

We assume that the semisimple `k`-algebras `A⁰` and `B⁰` are *split*
(`DG.IsSplitSemisimple k (DG.DGAlgebra.degreeZeroSubalgebra k A)`): for every simple idempotent
`e` of `A⁰`, `e A⁰ e = k e`, i.e. every simple `A⁰`-module has endomorphism ring `k`. This holds
for instance when `k` is algebraically closed and `A⁰` is finite-dimensional (the endomorphism
ring of a simple module is then a finite-dimensional division algebra over `k`, hence `k`; this
implication is not formalized here).

The hypothesis cannot be dropped:

* *`K₀` is not multiplicative.* For `k = ℝ` and `A = B = ℂ` in degree `0`, `K₀(ℂ) = ℤ` (one simple
  module), so `K₀(A) ⊗ K₀(B) = ℤ`, but `ℂ ⊗_ℝ ℂ ≅ ℂ × ℂ` has two simple modules and
  `K₀(A ⊗ B) = ℤ²`.
* *Positivity is not inherited.* For `k = 𝔽_p(t)` and the purely inseparable extension
  `K = k(t^{1/p})` in degree `0`, `K ⊗_k K ≅ K[x]/(x - t^{1/p})^p` is not semisimple, so `A ⊗ B`
  is not positive although `A` and `B` are.

## Main results

* `DG.IsPositive.tensorProduct`: `A ⊗_k B` is positive, for split `A⁰`, `B⁰`
  (semisimplicity of `A⁰ ⊗ B⁰` is `DG.isSemisimpleRing_tensorProduct`).
* `DG.DGIdempotent.tmul`, `DG.IsPositive.isSimple_tmul`, `DG.IsPositive.equiv_tmul_iff`,
  `DG.IsPositive.exists_equiv_tmul`: the simple idempotents of `(A ⊗ B)⁰` are, up to equivalence,
  exactly the `e ⊗ f` with `e`, `f` simple, and `e ⊗ f ~ e' ⊗ f'` iff `e ~ e'` and `f ~ f'`.
* `DG.kunnethBasis`: `K₀(A ⊗ B)` is free on the classes `[(A ⊗ B)(e ⊗ f)]`, for representatives
  `e`, `f` of the simple idempotents of `A⁰`, `B⁰`; `DG.K0KunnethEquivOfBasis` for given
  representatives.
* `DG.IsPositive.K0KunnethEquiv : K₀(A) ⊗_ℤ K₀(B) ≃ₗ[ℤ] K₀(A ⊗_k B)` with
  `[A e] ⊗ [B f] ↦ [(A ⊗ B)(e ⊗ f)]` (`DG.IsPositive.K0KunnethEquiv_tmul`), from the bases of
  Roadmap 6.3 (`DG.IsPositive.basis`).
-/

open scoped TensorProduct

universe u

namespace DG

/-! ### The degree-`0` subalgebra -/

section DegreeZero

variable (k : Type*) [CommRing k] (A : Type*) [Ring A] [Algebra k A] [DGAddCommGroup A]
  [DGRing A] [DGAlgebra k A]

/-- The degree-`0` part `A⁰` of a dg `k`-algebra, as a `k`-subalgebra. -/
def DGAlgebra.degreeZeroSubalgebra : Subalgebra k A :=
  { degreeZeroSubring A with algebraMap_mem' := algebraMap_mem_grading k }

theorem DGAlgebra.mem_degreeZeroSubalgebra {a : A} :
    a ∈ DGAlgebra.degreeZeroSubalgebra k A ↔ a ∈ grading (M := A) 0 :=
  Iff.rfl

/-- The degree-`0` subring and the degree-`0` subalgebra are the same ring. -/
def DGAlgebra.degreeZeroSubalgebraRingEquiv :
    degreeZeroSubring A ≃+* DGAlgebra.degreeZeroSubalgebra k A where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

end DegreeZero

section Tensor

variable {k : Type*} [Field k]
  {A : Type u} [Ring A] [Algebra k A] [DGAddCommGroup A] [DGRing A] [DGAlgebra k A]
  {B : Type u} [Ring B] [Algebra k B] [DGAddCommGroup B] [DGRing B] [DGAlgebra k B]

local notation "𝒜" => DGAlgebra.gradingSubmodule k A
local notation "ℬ" => DGAlgebra.gradingSubmodule k B
local notation "A₀" => DGAlgebra.degreeZeroSubalgebra k A
local notation "B₀" => DGAlgebra.degreeZeroSubalgebra k B

/-! ### `(A ⊗ B)⁰ = A⁰ ⊗ B⁰` -/

variable (k A B) in
/-- The algebra map `A⁰ ⊗_k B⁰ → A ⊗_k B`, `a ⊗ b ↦ a ⊗ b`. -/
noncomputable def degreeZeroTensorHom : A₀ ⊗[k] B₀ →ₐ[k] 𝒜 ᵍ⊗[k] ℬ :=
  Algebra.TensorProduct.lift ((_root_.GradedTensorProduct.includeLeft 𝒜 ℬ).comp (A₀).val)
    ((_root_.GradedTensorProduct.includeRight 𝒜 ℬ).comp (B₀).val) fun a b => by
      change ((a : A) ᵍ⊗ₜ[k] (1 : B) : 𝒜 ᵍ⊗[k] ℬ) * ((1 : A) ᵍ⊗ₜ[k] (b : B)) =
        ((1 : A) ᵍ⊗ₜ[k] (b : B) : 𝒜 ᵍ⊗[k] ℬ) * ((a : A) ᵍ⊗ₜ[k] (1 : B))
      rw [GradedTensorProduct.tmul_mul_one_tmul, GradedTensorProduct.tmul_mul_tmul 𝒜 ℬ _
        (show (b : B) ∈ ℬ 0 from b.2) (show (a : A) ∈ 𝒜 0 from a.2), zero_mul,
        koszulSign_zero, one_smul, one_mul, one_mul, mul_one]

theorem degreeZeroTensorHom_tmul (a : A₀) (b : B₀) :
    degreeZeroTensorHom k A B (a ⊗ₜ b) = ((a : A) ᵍ⊗ₜ[k] (b : B) : 𝒜 ᵍ⊗[k] ℬ) := by
  rw [degreeZeroTensorHom, Algebra.TensorProduct.lift_tmul]
  change ((a : A) ᵍ⊗ₜ[k] (1 : B) : 𝒜 ᵍ⊗[k] ℬ) * ((1 : A) ᵍ⊗ₜ[k] (b : B)) = _
  rw [GradedTensorProduct.tmul_mul_one_tmul, one_mul]

theorem degreeZeroTensorHom_injective : Function.Injective (degreeZeroTensorHom k A B) := by
  have h : (degreeZeroTensorHom k A B).toLinearMap =
      (_root_.GradedTensorProduct.of k 𝒜 ℬ).toLinearMap ∘ₗ
        TensorProduct.map (A₀).val.toLinearMap (B₀).val.toLinearMap :=
    TensorProduct.ext' fun a b => degreeZeroTensorHom_tmul a b
  have hinj : Function.Injective
      ((_root_.GradedTensorProduct.of k 𝒜 ℬ).toLinearMap ∘ₗ
        TensorProduct.map (A₀).val.toLinearMap (B₀).val.toLinearMap) :=
    (_root_.GradedTensorProduct.of k 𝒜 ℬ).injective.comp
      (TensorProduct.map_injective_of_flat_flat _ _ Subtype.val_injective Subtype.val_injective)
  rw [← h] at hinj
  exact hinj

theorem degreeZeroTensorHom_mem (y : A₀ ⊗[k] B₀) :
    degreeZeroTensorHom k A B y ∈ grading (M := 𝒜 ᵍ⊗[k] ℬ) 0 := by
  induction y using TensorProduct.inductionOn with
  | tmul a b =>
    rw [degreeZeroTensorHom_tmul]
    exact GradedTensorProduct.tmul_mem_of_eq 𝒜 ℬ (add_zero 0) a.2 b.2
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

variable (hA : IsPositive A) (hB : IsPositive B)

include hA hB in
/-- A pure tensor of homogeneous elements of positive dg algebras vanishes unless both degrees
are non-negative. -/
theorem tmul_eq_zero_or {i j : ℤ} {a : A} (ha : a ∈ grading i) {b : B} (hb : b ∈ grading j) :
    (a ᵍ⊗ₜ[k] b : 𝒜 ᵍ⊗[k] ℬ) = 0 ∨ (0 ≤ i ∧ 0 ≤ j) := by
  by_cases hi : i < 0
  · left
    rw [hA.eq_zero_of_mem_grading hi ha, GradedTensorProduct.zero_tmul]
  by_cases hj : j < 0
  · left
    rw [hB.eq_zero_of_mem_grading hj hb, GradedTensorProduct.tmul_zero]
  right
  omega

include hA hB in
theorem exists_degreeZeroTensorHom_eq {x : 𝒜 ᵍ⊗[k] ℬ} (hx : x ∈ grading (M := 𝒜 ᵍ⊗[k] ℬ) 0) :
    ∃ y, degreeZeroTensorHom k A B y = x := by
  refine GradedTensorProduct.grading_induction 𝒜 ℬ hx
    (motive := fun x => ∃ y, degreeZeroTensorHom k A B y = x) ⟨0, map_zero _⟩ ?_ ?_
  · intro i j a b hij
    rcases tmul_eq_zero_or hA hB (k := k) a.2 b.2 with h | ⟨hi, hj⟩
    · exact ⟨0, by rw [map_zero, h]⟩
    · have hi0 : i = 0 := by omega
      have hj0 : j = 0 := by omega
      subst hi0 hj0
      exact ⟨(⟨a, a.2⟩ : A₀) ⊗ₜ[k] (⟨b, b.2⟩ : B₀), degreeZeroTensorHom_tmul _ _⟩
  · rintro x y ⟨x', rfl⟩ ⟨y', rfl⟩
    exact ⟨x' + y', map_add _ _ _⟩

include hA hB in
/-- **`(A ⊗ B)⁰ ≅ A⁰ ⊗ B⁰`** for positive dg algebras `A`, `B`, as rings. -/
noncomputable def degreeZeroTensorEquiv :
    A₀ ⊗[k] B₀ ≃+* degreeZeroSubring (𝒜 ᵍ⊗[k] ℬ) :=
  RingEquiv.ofBijective
    ((degreeZeroTensorHom k A B : A₀ ⊗[k] B₀ →+* 𝒜 ᵍ⊗[k] ℬ).codRestrict
      (degreeZeroSubring (𝒜 ᵍ⊗[k] ℬ)) fun y =>
        mem_degreeZeroSubring.mpr (degreeZeroTensorHom_mem y))
    ⟨fun x y h => degreeZeroTensorHom_injective (congrArg Subtype.val h), fun x => by
      obtain ⟨y, hy⟩ := exists_degreeZeroTensorHom_eq hA hB x.2
      exact ⟨y, Subtype.ext hy⟩⟩

theorem coe_degreeZeroTensorEquiv_apply (y : A₀ ⊗[k] B₀) :
    (degreeZeroTensorEquiv hA hB y : 𝒜 ᵍ⊗[k] ℬ) = degreeZeroTensorHom k A B y :=
  rfl

/-! ### Positivity of the tensor product -/

include hA hB in
theorem grading_tensorProduct_eq_bot {n : ℤ} (hn : n < 0) :
    grading (M := 𝒜 ᵍ⊗[k] ℬ) n = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => (AddSubgroup.mem_bot).mpr ?_
  refine GradedTensorProduct.grading_induction 𝒜 ℬ hx (motive := fun x => x = 0) rfl ?_ ?_
  · intro i j a b hij
    rcases tmul_eq_zero_or hA hB (k := k) a.2 b.2 with h | ⟨hi, hj⟩
    · exact h
    · omega
  · intro x y hx hy
    rw [hx, hy, add_zero]

include hA hB in
theorem d_tensorProduct_eq_zero {x : 𝒜 ᵍ⊗[k] ℬ} (hx : x ∈ grading (M := 𝒜 ᵍ⊗[k] ℬ) 0) :
    d x = 0 := by
  refine GradedTensorProduct.grading_induction 𝒜 ℬ hx (motive := fun x => d x = 0) d_zero ?_ ?_
  · intro i j a b hij
    rcases tmul_eq_zero_or hA hB (k := k) a.2 b.2 with h | ⟨hi, hj⟩
    · rw [h, d_zero]
    · have hi0 : i = 0 := by omega
      have hj0 : j = 0 := by omega
      subst hi0 hj0
      have ha : (a : A) ∈ grading 0 := a.2
      have hb : (b : B) ∈ grading 0 := b.2
      rw [GradedTensorProduct.d_tmul ha, hA.d_eq_zero ha, hB.d_eq_zero hb,
        GradedTensorProduct.zero_tmul, GradedTensorProduct.tmul_zero, smul_zero, add_zero]
  · intro x y hx hy
    rw [d_add, hx, hy, add_zero]

include hA hB in
/-- **The tensor product of positive dg algebras with split degree-`0` parts is positive.** -/
theorem IsPositive.tensorProduct (hsA : IsSplitSemisimple k A₀) (hsB : IsSplitSemisimple k B₀) :
    IsPositive (𝒜 ᵍ⊗[k] ℬ) := by
  have := hA.isSemisimple
  have := hB.isSemisimple
  have : IsSemisimpleRing A₀ := (DGAlgebra.degreeZeroSubalgebraRingEquiv k A).isSemisimpleRing
  have : IsSemisimpleRing B₀ := (DGAlgebra.degreeZeroSubalgebraRingEquiv k B).isSemisimpleRing
  have := isSemisimpleRing_tensorProduct (R₁ := A₀) (R₂ := B₀) k hsA hsB
  refine ⟨fun n hn => grading_tensorProduct_eq_bot hA hB hn, ?_,
    fun x hx => d_tensorProduct_eq_zero hA hB hx⟩
  exact (degreeZeroTensorEquiv hA hB).isSemisimpleRing

/-! ### Simple idempotents of the tensor product -/

variable (e : DGIdempotent A) (f : DGIdempotent B)

/-- The tensor product `e ⊗ f` of degree-`0` idempotent cocycles, an idempotent cocycle of
`A ⊗ B`. -/
noncomputable def DGIdempotent.tmul : DGIdempotent (𝒜 ᵍ⊗[k] ℬ) where
  val := e.val ᵍ⊗ₜ[k] f.val
  mem_zero := GradedTensorProduct.tmul_mem_of_eq 𝒜 ℬ (add_zero 0) e.mem_zero f.mem_zero
  mul_self := by
    rw [GradedTensorProduct.tmul_mul_tmul 𝒜 ℬ _ (show f.val ∈ ℬ 0 from f.mem_zero)
      (show e.val ∈ 𝒜 0 from e.mem_zero), zero_mul, koszulSign_zero, one_smul, e.mul_self,
      f.mul_self]
  d_eq_zero := by
    rw [GradedTensorProduct.d_tmul e.mem_zero, e.d_eq_zero, f.d_eq_zero,
      GradedTensorProduct.zero_tmul, GradedTensorProduct.tmul_zero, smul_zero, add_zero]

theorem DGIdempotent.tmul_val : (e.tmul (k := k) f).val = e.val ᵍ⊗ₜ[k] f.val :=
  rfl

theorem toZero_tmul :
    (e.tmul (k := k) f).toZero = degreeZeroTensorEquiv hA hB
      (DGAlgebra.degreeZeroSubalgebraRingEquiv k A e.toZero ⊗ₜ
        DGAlgebra.degreeZeroSubalgebraRingEquiv k B f.toZero) :=
  Subtype.ext (by rw [coe_degreeZeroTensorEquiv_apply, degreeZeroTensorHom_tmul]; rfl)

theorem isIdempotentElem_toZero_ringEquiv {C : Type*} [Ring C] [DGAddCommGroup C] [DGRing C]
    {R : Type*} [Ring R] (φ : degreeZeroSubring C ≃+* R) (e : DGIdempotent C) :
    IsIdempotentElem (φ e.toZero) := by
  change φ _ * φ _ = φ _
  rw [← map_mul, e.isIdempotentElem_toZero.eq]

theorem isSimpleModule_ringEquiv {C : Type*} [Ring C] [DGAddCommGroup C] [DGRing C]
    {R : Type*} [Ring R] (φ : degreeZeroSubring C ≃+* R) {e : DGIdempotent C}
    (he : e.IsSimple) : IsSimpleModule R (Submodule.span R {φ e.toZero}) :=
  (isSimpleModule_span_singleton_ringEquiv_iff φ _).mpr he

include hA hB in
/-- `e ⊗ f` is simple for simple `e`, `f`, when `A⁰` and `B⁰` are split. -/
theorem IsPositive.isSimple_tmul (hsA : IsSplitSemisimple k A₀) (hsB : IsSplitSemisimple k B₀)
    {e : DGIdempotent A} {f : DGIdempotent B} (he : e.IsSimple) (hf : f.IsSimple) :
    (e.tmul (k := k) f).IsSimple := by
  unfold DGIdempotent.IsSimple
  rw [toZero_tmul hA hB, isSimpleModule_span_singleton_ringEquiv_iff]
  have he' := isSimpleModule_ringEquiv (DGAlgebra.degreeZeroSubalgebraRingEquiv k A) he
  have hf' := isSimpleModule_ringEquiv (DGAlgebra.degreeZeroSubalgebraRingEquiv k B) hf
  have hie := isIdempotentElem_toZero_ringEquiv (DGAlgebra.degreeZeroSubalgebraRingEquiv k A) e
  have hif := isIdempotentElem_toZero_ringEquiv (DGAlgebra.degreeZeroSubalgebraRingEquiv k B) f
  exact isSimpleModule_span_tmul hie hif he' hf' (hsA _ hie he') (hsB _ hif hf')

include hA hB in
/-- For simple `e, e', f, f'`, `e ⊗ f ~ e' ⊗ f'` iff `e ~ e'` and `f ~ f'`. -/
theorem IsPositive.equiv_tmul_iff (hsA : IsSplitSemisimple k A₀) (hsB : IsSplitSemisimple k B₀)
    {e e' : DGIdempotent A} {f f' : DGIdempotent B} (he : e.IsSimple) (he' : e'.IsSimple)
    (hf : f.IsSimple) (hf' : f'.IsSimple) :
    (e.tmul (k := k) f).Equiv (e'.tmul f') ↔ e.Equiv e' ∧ f.Equiv f' := by
  unfold DGIdempotent.Equiv
  rw [toZero_tmul hA hB, toZero_tmul hA hB, idemEquiv_ringEquiv_iff,
    ← idemEquiv_ringEquiv_iff (DGAlgebra.degreeZeroSubalgebraRingEquiv k A) (e := e.toZero),
    ← idemEquiv_ringEquiv_iff (DGAlgebra.degreeZeroSubalgebraRingEquiv k B) (e := f.toZero)]
  have hie := isIdempotentElem_toZero_ringEquiv (DGAlgebra.degreeZeroSubalgebraRingEquiv k A) e
  have hif := isIdempotentElem_toZero_ringEquiv (DGAlgebra.degreeZeroSubalgebraRingEquiv k B) f
  have hse := isSimpleModule_ringEquiv (DGAlgebra.degreeZeroSubalgebraRingEquiv k A) he
  have hsf := isSimpleModule_ringEquiv (DGAlgebra.degreeZeroSubalgebraRingEquiv k B) hf
  exact idemEquiv_tmul_iff hie
    (isIdempotentElem_toZero_ringEquiv (DGAlgebra.degreeZeroSubalgebraRingEquiv k A) e') hif
    (isIdempotentElem_toZero_ringEquiv (DGAlgebra.degreeZeroSubalgebraRingEquiv k B) f') hse
    (isSimpleModule_ringEquiv (DGAlgebra.degreeZeroSubalgebraRingEquiv k A) he') hsf
    (isSimpleModule_ringEquiv (DGAlgebra.degreeZeroSubalgebraRingEquiv k B) hf')
    (hsA _ hie hse) (hsB _ hif hsf)

include hA hB in
/-- Every simple idempotent of `(A ⊗ B)⁰` is equivalent to some `e ⊗ f`, `e` and `f` running over
sets of representatives of the simple idempotents of `A⁰` and `B⁰`. -/
theorem IsPositive.exists_equiv_tmul (hsA : IsSplitSemisimple k A₀) (hsB : IsSplitSemisimple k B₀)
    {ι κ : Type*} (sA : ι → SimpleIdempotent A)
    (hsA' : ∀ e : SimpleIdempotent A, ∃ i, e.1.Equiv (sA i).1) (sB : κ → SimpleIdempotent B)
    (hsB' : ∀ f : SimpleIdempotent B, ∃ j, f.1.Equiv (sB j).1)
    (g : SimpleIdempotent (𝒜 ᵍ⊗[k] ℬ)) :
    ∃ i j, g.1.Equiv ((sA i).1.tmul (sB j).1) := by
  set ζA := DGAlgebra.degreeZeroSubalgebraRingEquiv k A
  set ζB := DGAlgebra.degreeZeroSubalgebraRingEquiv k B
  set Ψ := degreeZeroTensorEquiv (k := k) hA hB
  have := hA.isSemisimple
  have := hB.isSemisimple
  have : IsSemisimpleRing A₀ := ζA.isSemisimpleRing
  have : IsSemisimpleRing B₀ := ζB.isSemisimpleRing
  obtain ⟨l₁, hl₁, hs₁⟩ := exists_list_sum_eq_of_isSemisimpleRing (R := A₀) IsIdempotentElem.one
  obtain ⟨l₂, hl₂, hs₂⟩ := exists_list_sum_eq_of_isSemisimpleRing (R := B₀) IsIdempotentElem.one
  have hg : IsIdempotentElem (Ψ.symm g.1.toZero) := by
    change Ψ.symm _ * Ψ.symm _ = Ψ.symm _
    rw [← map_mul, g.1.isIdempotentElem_toZero.eq]
  have hsg := (isSimpleModule_span_singleton_ringEquiv_iff Ψ.symm g.1.toZero).mpr g.2
  obtain ⟨s, hs, t, ht, hgst⟩ := exists_idemEquiv_tmul hg hsg
    (fun s hs => ⟨(hl₁ s hs).1, (hl₁ s hs).2, hsA s (hl₁ s hs).1 (hl₁ s hs).2⟩)
    (fun t ht => ⟨(hl₂ t ht).1, (hl₂ t ht).2, hsB t (hl₂ t ht).1 (hl₂ t ht).2⟩) hs₁ hs₂
  have hsi : IsIdempotentElem (ζA.symm s) := by
    change ζA.symm s * ζA.symm s = ζA.symm s
    rw [← map_mul, (hl₁ s hs).1.eq]
  have hti : IsIdempotentElem (ζB.symm t) := by
    change ζB.symm t * ζB.symm t = ζB.symm t
    rw [← map_mul, (hl₂ t ht).1.eq]
  let es : DGIdempotent A := hA.dgIdempotent (ζA.symm s) hsi
  let ft : DGIdempotent B := hB.dgIdempotent (ζB.symm t) hti
  have hes : es.IsSimple := (isSimpleModule_span_singleton_ringEquiv_iff ζA.symm s).mpr (hl₁ s hs).2
  have hft : ft.IsSimple := (isSimpleModule_span_singleton_ringEquiv_iff ζB.symm t).mpr (hl₂ t ht).2
  obtain ⟨i, hi⟩ := hsA' ⟨es, hes⟩
  obtain ⟨j, hj⟩ := hsB' ⟨ft, hft⟩
  have hi' : IdemEquiv A₀ s (ζA (sA i).1.toZero) := by
    change IdemEquiv _ (ζA.symm s) _ at hi
    have := IdemEquiv.map ζA.toRingHom hi
    simpa using this
  have hj' : IdemEquiv B₀ t (ζB (sB j).1.toZero) := by
    change IdemEquiv _ (ζB.symm t) _ at hj
    have := IdemEquiv.map ζB.toRingHom hj
    simpa using this
  refine ⟨i, j, ?_⟩
  unfold DGIdempotent.Equiv
  rw [toZero_tmul hA hB]
  have := IdemEquiv.map Ψ.toRingHom (hgst.trans (hi'.tmul hj'))
  simpa using this

/-- Equivalent idempotents of a positive dg ring have the same class in `K₀`. -/
theorem IsPositive.leftCorner_eq_of_equiv {C : Type u} [Ring C] [DGAddCommGroup C] [DGRing C]
    (hC : IsPositive C) [HasDerivedCategory.{u, u} C] {e f : DGIdempotent C} (h : e.Equiv f) :
    DGRing.K0.leftCorner e = DGRing.K0.leftCorner f := by
  rw [← IsPositive.mk_cell_zero, ← IsPositive.mk_cell_zero]
  exact DG.K0.mk_eq_of_iso_obj (hC.nonempty_cell_iso_of_equiv h 0).some

/-! ### The Künneth isomorphism -/

variable (hsA : IsSplitSemisimple k (DGAlgebra.degreeZeroSubalgebra k A))
  (hsB : IsSplitSemisimple k (DGAlgebra.degreeZeroSubalgebra k B)) {ι κ : Type*}
  (sA : ι → SimpleIdempotent A) (hsA₁ : ∀ a b, (sA a).1.Equiv (sA b).1 → a = b)
  (hsA₂ : ∀ e : SimpleIdempotent A, ∃ a, e.1.Equiv (sA a).1)
  (sB : κ → SimpleIdempotent B) (hsB₁ : ∀ a b, (sB a).1.Equiv (sB b).1 → a = b)
  (hsB₂ : ∀ f : SimpleIdempotent B, ∃ b, f.1.Equiv (sB b).1)
  [HasDerivedCategory.{u, u}
    (DGAlgebra.gradingSubmodule k A ᵍ⊗[k] DGAlgebra.gradingSubmodule k B)]

/-- The basis of `K₀(A ⊗ B)` given by the classes `[(A ⊗ B)(e ⊗ f)]`, `e`, `f` running over
representatives of the simple idempotents of `A⁰` and `B⁰`. -/
noncomputable def kunnethBasis : Module.Basis (ι × κ) ℤ (DGRing.K0 (𝒜 ᵍ⊗[k] ℬ)) :=
  letI := HasDerivedCategory.small.{u, u} (hA.tensorProduct hB hsA hsB).degreeZeroDGSubring
  (hA.tensorProduct hB hsA hsB).basis
    (fun p => ⟨(sA p.1).1.tmul (sB p.2).1, hA.isSimple_tmul hB hsA hsB (sA p.1).2 (sB p.2).2⟩)
    (fun p q h => by
      obtain ⟨h1, h2⟩ := (hA.equiv_tmul_iff hB hsA hsB (sA p.1).2 (sA q.1).2 (sB p.2).2
        (sB q.2).2).mp h
      exact Prod.ext (hsA₁ _ _ h1) (hsB₁ _ _ h2))
    (fun g => by
      obtain ⟨i, j, h⟩ := hA.exists_equiv_tmul hB hsA hsB sA hsA₂ sB hsB₂ g
      exact ⟨(i, j), h⟩)

theorem kunnethBasis_apply (p : ι × κ) :
    kunnethBasis hA hB hsA hsB sA hsA₁ hsA₂ sB hsB₁ hsB₂ p =
      DGRing.K0.leftCorner ((sA p.1).1.tmul (sB p.2).1) := by
  let := HasDerivedCategory.small.{u, u} (hA.tensorProduct hB hsA hsB).degreeZeroDGSubring
  exact IsPositive.basis_apply _ _ _ _ p

variable [HasDerivedCategory.{u, u} A] [HasDerivedCategory.{u, u} B]

/-- The Künneth isomorphism `K₀(A) ⊗ K₀(B) ≅ K₀(A ⊗ B)` for given sets of representatives of the
simple idempotents, matching the bases of `DG.IsPositive.basis` and `DG.kunnethBasis`. -/
noncomputable def K0KunnethEquivOfBasis :
    DGRing.K0 A ⊗[ℤ] DGRing.K0 B ≃ₗ[ℤ] DGRing.K0 (𝒜 ᵍ⊗[k] ℬ) :=
  letI := HasDerivedCategory.small.{u, u} hA.degreeZeroDGSubring
  letI := HasDerivedCategory.small.{u, u} hB.degreeZeroDGSubring
  ((hA.basis sA hsA₁ hsA₂).tensorProduct (hB.basis sB hsB₁ hsB₂)).equiv
    (kunnethBasis hA hB hsA hsB sA hsA₁ hsA₂ sB hsB₁ hsB₂) (Equiv.refl _)

theorem K0KunnethEquivOfBasis_tmul (a : ι) (b : κ) :
    K0KunnethEquivOfBasis hA hB hsA hsB sA hsA₁ hsA₂ sB hsB₁ hsB₂
        (DGRing.K0.leftCorner (sA a).1 ⊗ₜ DGRing.K0.leftCorner (sB b).1) =
      DGRing.K0.leftCorner ((sA a).1.tmul (sB b).1) := by
  let := HasDerivedCategory.small.{u, u} hA.degreeZeroDGSubring
  let := HasDerivedCategory.small.{u, u} hB.degreeZeroDGSubring
  rw [← IsPositive.basis_apply hA sA hsA₁ hsA₂ a, ← IsPositive.basis_apply hB sB hsB₁ hsB₂ b,
    ← Module.Basis.tensorProduct_apply, K0KunnethEquivOfBasis]
  exact (Module.Basis.equiv_apply (i := (a, b)) _ _ _).trans
    (kunnethBasis_apply hA hB hsA hsB sA hsA₁ hsA₂ sB hsB₁ hsB₂ (a, b))

end Tensor

/-! ### Canonical representatives -/

section Canonical

variable {C : Type*} [Ring C] [DGAddCommGroup C] [DGRing C]

variable (C) in
/-- Equivalence of simple idempotents, as a setoid. -/
def simpleIdempotentSetoid : Setoid (SimpleIdempotent C) where
  r e f := e.1.Equiv f.1
  iseqv := ⟨fun e => DGIdempotent.Equiv.refl e.1, fun h => h.symm, fun h h' => IdemEquiv.trans h h'⟩

variable (C) in
/-- The isomorphism classes of simple `C⁰`-modules, i.e. the simple idempotents of `C⁰` up to
equivalence. -/
abbrev SimpleClass : Type _ := Quotient (simpleIdempotentSetoid C)

/-- A representative of a class of simple idempotents. -/
noncomputable def SimpleClass.out (x : SimpleClass C) : SimpleIdempotent C :=
  Quotient.out x

theorem SimpleClass.out_injective (a b : SimpleClass C) (h : a.out.1.Equiv b.out.1) : a = b := by
  rw [← Quotient.out_eq a, ← Quotient.out_eq b]
  exact Quotient.sound h

theorem SimpleClass.equiv_out (e : SimpleIdempotent C) :
    e.1.Equiv (SimpleClass.out (Quotient.mk (simpleIdempotentSetoid C) e)).1 :=
  (Quotient.mk_out (s := simpleIdempotentSetoid C) e).symm

end Canonical

section Kunneth

variable {k : Type*} [Field k]
  {A : Type u} [Ring A] [Algebra k A] [DGAddCommGroup A] [DGRing A] [DGAlgebra k A]
  {B : Type u} [Ring B] [Algebra k B] [DGAddCommGroup B] [DGRing B] [DGAlgebra k B]
  (hA : IsPositive A) (hB : IsPositive B)
  [HasDerivedCategory.{u, u} A] [HasDerivedCategory.{u, u} B]
  [HasDerivedCategory.{u, u} (DGAlgebra.gradingSubmodule k A ᵍ⊗[k] DGAlgebra.gradingSubmodule k B)]

/-- **Künneth formula for `K₀`** (Roadmap 6.5): for positive dg algebras `A`, `B` over a field `k`
whose degree-`0` parts are split semisimple, `K₀(A) ⊗_ℤ K₀(B) ≅ K₀(A ⊗_k B)`, with
`[A e] ⊗ [B f] ↦ [(A ⊗ B)(e ⊗ f)]` (`DG.IsPositive.K0KunnethEquiv_tmul`). See the module docstring
for why the splitting hypothesis is needed. -/
noncomputable def IsPositive.K0KunnethEquiv
    (hsA : IsSplitSemisimple k (DGAlgebra.degreeZeroSubalgebra k A))
    (hsB : IsSplitSemisimple k (DGAlgebra.degreeZeroSubalgebra k B)) :
    DGRing.K0 A ⊗[ℤ] DGRing.K0 B ≃ₗ[ℤ]
      DGRing.K0 (DGAlgebra.gradingSubmodule k A ᵍ⊗[k] DGAlgebra.gradingSubmodule k B) :=
  K0KunnethEquivOfBasis hA hB hsA hsB (SimpleClass.out (C := A)) SimpleClass.out_injective
    (fun e => ⟨_, SimpleClass.equiv_out e⟩) (SimpleClass.out (C := B)) SimpleClass.out_injective
    (fun f => ⟨_, SimpleClass.equiv_out f⟩)

theorem IsPositive.K0KunnethEquiv_tmul
    (hsA : IsSplitSemisimple k (DGAlgebra.degreeZeroSubalgebra k A))
    (hsB : IsSplitSemisimple k (DGAlgebra.degreeZeroSubalgebra k B))
    (e : SimpleIdempotent A) (f : SimpleIdempotent B) :
    hA.K0KunnethEquiv hB hsA hsB (DGRing.K0.leftCorner e.1 ⊗ₜ DGRing.K0.leftCorner f.1) =
      DGRing.K0.leftCorner (e.1.tmul (k := k) f.1) := by
  have he := SimpleClass.equiv_out e
  have hf := SimpleClass.equiv_out f
  rw [hA.leftCorner_eq_of_equiv he, hB.leftCorner_eq_of_equiv hf, IsPositive.K0KunnethEquiv,
    K0KunnethEquivOfBasis_tmul]
  exact (hA.tensorProduct hB hsA hsB).leftCorner_eq_of_equiv
    ((hA.equiv_tmul_iff hB hsA hsB (SimpleClass.out _).2 e.2 (SimpleClass.out _).2 f.2).mpr
      ⟨he.symm, hf.symm⟩)

end Kunneth

end DG
