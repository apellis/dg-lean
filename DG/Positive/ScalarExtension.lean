import DG.Positive.Kunneth
import DG.Positive.K0Basis

/-!
# Extension of scalars of connected dg rings

Let `K` be a commutative ring and `A` a dg ring. Regard `K` as a dg ring concentrated in degree
`0` with zero differential (`DG.DegreeZeroRing K`); the dg ring `K ⊗ A` is the graded tensor
product `K ᵍ⊗[ℤ] A` of dg `ℤ`-algebras (`DG.ExtendScalars K A`), a dg `K`-algebra
(`DG.ExtendScalars.dgAlgebra`) with the dg ring map `A → K ⊗ A`, `a ↦ 1 ⊗ a`
(`DG.ExtendScalars.unitHom`).

The degree-`0` part of `K ⊗ A` is `K ⊗_ℤ A⁰` (`DG.ExtendScalars.degreeZeroEquiv`, a ring
isomorphism `k ⊗ a ↦ k ⊗ a`; it uses no hypothesis on `A`). Hence if `Aⁿ = 0` for `n < 0`, `d`
vanishes on `A⁰` and the ring `K ⊗_ℤ A⁰` is semisimple, then `K ⊗ A` is positive in Schnürer's
sense (`DG.ExtendScalars.isPositive_of_isSemisimpleRing`), and `K₀(K ⊗ A)` is computed by
`DG.IsPositive.K0DegreeZeroEquiv` and `DG.IsPositive.basis`. The ring `A⁰` itself need not be
semisimple: e.g. `A⁰ = ℤ`.

Suppose `A` is *connected over `ℤ`*: `Aⁿ = 0` for `n < 0` and `A⁰ = ℤ · 1` (every element of
degree `0` is an integer multiple of `1`). Then `A` itself is not positive (`ℤ` is not
semisimple), but `K ⊗ A` is for every semisimple commutative ring `K`: its degree-`0` part is the
image of `K` (`DG.ExtendScalars.exists_eq_tmul_one`) and `d` vanishes on it
(`DG.ExtendScalars.isPositive`). If moreover `K` is a field and `1` has infinite additive order in
`A`, then `K ⊗ A` is nonzero, and `K₀(K ⊗ A) ≃ ℤ` with `[K ⊗ A] ↦ 1`
(`DG.ExtendScalars.K0EquivInt`).
-/

open scoped TensorProduct
open DirectSum

universe u

noncomputable section

namespace DG

/-- A ring regarded as a dg ring concentrated in degree `0`, with zero differential. -/
def DegreeZeroRing (R : Type*) : Type _ := R

namespace DegreeZeroRing

variable (K : Type*) [CommRing K]

instance : CommRing (DegreeZeroRing K) := inferInstanceAs (CommRing K)

instance {K : Type*} [Field K] : Field (DegreeZeroRing K) := inferInstanceAs (Field K)

instance : DGAddCommGroup (DegreeZeroRing K) := DGAddCommGroup.degreeZero (DegreeZeroRing K)

instance : DGRing (DegreeZeroRing K) := DGRing.degreeZero (DegreeZeroRing K)

/-- The identity `K → DegreeZeroRing K`. -/
def of : K ≃+* DegreeZeroRing K := RingEquiv.refl K

theorem eq_zero_of_mem_grading {i : ℤ} (hi : i ≠ 0) {a : DegreeZeroRing K}
    (ha : a ∈ grading (M := DegreeZeroRing K) i) : a = 0 := by
  have : grading (M := DegreeZeroRing K) i = ⊥ := degreeZeroGrading_of_ne _ hi
  rw [this] at ha
  exact ha

theorem d_eq_zero (a : DegreeZeroRing K) : d a = 0 := rfl

theorem mem_grading_zero (a : DegreeZeroRing K) : a ∈ grading (M := DegreeZeroRing K) 0 :=
  mem_degreeZeroGrading_zero (DegreeZeroRing K) a

end DegreeZeroRing

/-- Extension of scalars `K ⊗ A` of a dg ring `A` along `ℤ → K`, with `K` in degree `0`: the
graded tensor product of dg `ℤ`-algebras. -/
abbrev ExtendScalars (K : Type*) [CommRing K] (A : Type*) [Ring A] [DGAddCommGroup A] [DGRing A] :=
  DGAlgebra.gradingSubmodule ℤ (DegreeZeroRing K) ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ A

namespace ExtendScalars

variable (K : Type*) [CommRing K] (A : Type*) [Ring A] [DGAddCommGroup A] [DGRing A]

local notation "𝒦" => DGAlgebra.gradingSubmodule ℤ (DegreeZeroRing K)
local notation "𝒜" => DGAlgebra.gradingSubmodule ℤ A

variable {K A}

/-- `(m • k) ⊗ 1 = k ⊗ m`, for an integer `m`. -/
theorem tmul_intCast (k : DegreeZeroRing K) (m : ℤ) :
    (k ᵍ⊗ₜ[ℤ] (m : A) : ExtendScalars K A) = (m • k) ᵍ⊗ₜ[ℤ] (1 : A) := by
  rw [← zsmul_one]
  exact congrArg (_root_.GradedTensorProduct.of ℤ 𝒦 𝒜) (TensorProduct.smul_tmul m k 1).symm

variable (hneg : ∀ n < 0, grading (M := A) n = ⊥)
  (h0 : ∀ a ∈ grading (M := A) 0, ∃ m : ℤ, (m : A) = a)

include hneg in
theorem tmul_eq_zero_or {i j : ℤ} {a : DegreeZeroRing K} (ha : a ∈ grading i) {b : A}
    (hb : b ∈ grading j) : (a ᵍ⊗ₜ[ℤ] b : ExtendScalars K A) = 0 ∨ (i = 0 ∧ 0 ≤ j) := by
  by_cases hi : i = 0
  · by_cases hj : j < 0
    · left
      rw [hneg j hj] at hb
      rw [(AddSubgroup.mem_bot).mp hb, GradedTensorProduct.tmul_zero]
    · right
      omega
  · left
    rw [DegreeZeroRing.eq_zero_of_mem_grading K hi ha, GradedTensorProduct.zero_tmul]

include hneg in
theorem grading_eq_bot {n : ℤ} (hn : n < 0) : grading (M := ExtendScalars K A) n = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => (AddSubgroup.mem_bot).mpr ?_
  refine GradedTensorProduct.grading_induction 𝒦 𝒜 hx (motive := fun x => x = 0) rfl ?_ ?_
  · intro i j a b hij
    rcases tmul_eq_zero_or hneg a.2 b.2 with h | ⟨hi, hj⟩
    · exact h
    · omega
  · intro x y hx hy
    rw [hx, hy, add_zero]

include hneg h0 in
/-- The degree-`0` part of `K ⊗ A` is the image of `K`. -/
theorem exists_eq_tmul_one {x : ExtendScalars K A} (hx : x ∈ grading (M := ExtendScalars K A) 0) :
    ∃ k : DegreeZeroRing K, x = k ᵍ⊗ₜ[ℤ] (1 : A) := by
  refine GradedTensorProduct.grading_induction 𝒦 𝒜 hx
    (motive := fun x => ∃ k : DegreeZeroRing K, x = k ᵍ⊗ₜ[ℤ] (1 : A)) ⟨0, by
      rw [GradedTensorProduct.zero_tmul]⟩ ?_ ?_
  · intro i j a b hij
    rcases tmul_eq_zero_or hneg a.2 b.2 with h | ⟨hi, hj⟩
    · exact ⟨0, by rw [h, GradedTensorProduct.zero_tmul]⟩
    · have hj0 : j = 0 := by omega
      subst hj0
      obtain ⟨m, hm⟩ := h0 b b.2
      exact ⟨m • (a : DegreeZeroRing K), by rw [← hm, tmul_intCast]⟩
  · rintro x y ⟨k, rfl⟩ ⟨k', rfl⟩
    exact ⟨k + k', (GradedTensorProduct.add_tmul 𝒦 𝒜 k k' (1 : A)).symm⟩

theorem tmul_one_mem (k : DegreeZeroRing K) :
    (k ᵍ⊗ₜ[ℤ] (1 : A) : ExtendScalars K A) ∈ grading (M := ExtendScalars K A) 0 := by
  have h := GradedTensorProduct.tmul_mem_grading (R := ℤ) (i := 0) (j := 0)
    (DegreeZeroRing.mem_grading_zero K k) (one_mem_grading (A := A))
  rwa [add_zero] at h

theorem d_tmul_one (k : DegreeZeroRing K) : d (k ᵍ⊗ₜ[ℤ] (1 : A) : ExtendScalars K A) = 0 := by
  rw [GradedTensorProduct.d_tmul', DegreeZeroRing.d_eq_zero, d_one,
    GradedTensorProduct.zero_tmul, GradedTensorProduct.tmul_zero, add_zero]

/-- `k ⊗ 1` is central in `K ⊗ A`, since `K` sits in degree `0` and is commutative. -/
theorem tmul_one_mul_comm (k : DegreeZeroRing K) (x : ExtendScalars K A) :
    (k ᵍ⊗ₜ[ℤ] (1 : A) : ExtendScalars K A) * x = x * (k ᵍ⊗ₜ[ℤ] (1 : A)) := by
  induction x using GradedTensorProduct.induction_on_tmul (R := ℤ) with
  | zero => rw [mul_zero, zero_mul]
  | @tmul i j a ha b hb =>
    rw [GradedTensorProduct.tmul_mul_tmul 𝒦 𝒜 k (one_mem_grading (A := A)) ha b,
      GradedTensorProduct.tmul_mul_tmul 𝒦 𝒜 (i' := 0) a hb (DegreeZeroRing.mem_grading_zero K k) 1,
      zero_mul, mul_zero, koszulSign_zero, one_smul, one_smul, one_mul, mul_one, mul_comm]
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]

variable (K A) in
/-- `K ⊗ A` is a `K`-algebra, `k ↦ k ⊗ 1`. -/
instance algebra : Algebra K (ExtendScalars K A) :=
  RingHom.toAlgebra' ((_root_.GradedTensorProduct.includeLeft 𝒦 𝒜).toRingHom.comp
    (DegreeZeroRing.of K).toRingHom) fun k x => tmul_one_mul_comm (DegreeZeroRing.of K k) x

theorem algebraMap_apply (k : K) :
    algebraMap K (ExtendScalars K A) k = (DegreeZeroRing.of K k) ᵍ⊗ₜ[ℤ] (1 : A) := rfl

variable (K A) in
/-- `K ⊗ A` is a dg `K`-algebra. -/
instance dgAlgebra : DGAlgebra K (ExtendScalars K A) where
  algebraMap_mem' k := tmul_one_mem (DegreeZeroRing.of K k)
  d_algebraMap' k := d_tmul_one (DegreeZeroRing.of K k)

variable (K A) in
/-- The dg ring map `A → K ⊗ A`, `a ↦ 1 ⊗ a`. -/
def unitHom : A →ᵈᵍ+* ExtendScalars K A :=
  (GradedTensorProduct.includeRightDGAlgHom ℤ (DegreeZeroRing K) A).toDGRingHom

theorem unitHom_apply (a : A) :
    unitHom K A a = ((1 : DegreeZeroRing K) ᵍ⊗ₜ[ℤ] a : ExtendScalars K A) := rfl

variable (K A) in
/-- `K → (K ⊗ A)⁰`, `k ↦ k ⊗ 1`. -/
def toDegreeZero : DegreeZeroRing K →+* degreeZeroSubring (ExtendScalars K A) :=
  (_root_.GradedTensorProduct.includeLeft 𝒦 𝒜).toRingHom.codRestrict _ fun k =>
    mem_degreeZeroSubring.mpr (tmul_one_mem k)

include hneg h0 in
theorem toDegreeZero_surjective : Function.Surjective (toDegreeZero K A) := by
  rintro ⟨x, hx⟩
  obtain ⟨k, rfl⟩ := exists_eq_tmul_one hneg h0 (mem_degreeZeroSubring.mp hx)
  exact ⟨k, rfl⟩

/-! ### The degree-`0` part of `K ⊗ A` -/

variable (K A) in
/-- `K ⊗_ℤ A⁰ → K ⊗ A`, `k ⊗ a ↦ k ⊗ a`, as a `ℤ`-linear map. -/
def degreeZeroLinearMap : K ⊗[ℤ] degreeZeroSubring A →ₗ[ℤ] ExtendScalars K A :=
  (_root_.GradedTensorProduct.of ℤ 𝒦 𝒜).toLinearMap ∘ₗ
    TensorProduct.map (DegreeZeroRing.of K).toRingHom.toAddMonoidHom.toIntLinearMap
      (degreeZeroSubring A).subtype.toAddMonoidHom.toIntLinearMap

theorem degreeZeroLinearMap_tmul (k : K) (a : degreeZeroSubring A) :
    degreeZeroLinearMap K A (k ⊗ₜ a) =
      ((DegreeZeroRing.of K k) ᵍ⊗ₜ[ℤ] (a : A) : ExtendScalars K A) := rfl

theorem degreeZeroLinearMap_mul_tmul (k k' : K) (a a' : degreeZeroSubring A) :
    degreeZeroLinearMap K A ((k ⊗ₜ a) * (k' ⊗ₜ a')) =
      degreeZeroLinearMap K A (k ⊗ₜ a) * degreeZeroLinearMap K A (k' ⊗ₜ a') := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, degreeZeroLinearMap_tmul, degreeZeroLinearMap_tmul,
    degreeZeroLinearMap_tmul,
    GradedTensorProduct.tmul_mul_tmul 𝒦 𝒜 (j := 0) (i' := 0) (DegreeZeroRing.of K k)
      (mem_degreeZeroSubring.mp a.2)
      (DegreeZeroRing.mem_grading_zero K (DegreeZeroRing.of K k')) (a' : A), zero_mul,
    koszulSign_zero, one_smul]
  rfl

variable (K A) in
/-- `K ⊗_ℤ A⁰ → K ⊗ A`, `k ⊗ a ↦ k ⊗ a`, as a ring homomorphism. -/
def degreeZeroRingHom : K ⊗[ℤ] degreeZeroSubring A →+* ExtendScalars K A where
  toFun := degreeZeroLinearMap K A
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    rw [Algebra.TensorProduct.one_def, degreeZeroLinearMap_tmul]
    rfl
  map_mul' x y := by
    induction x using TensorProduct.inductionOn with
    | tmul k a =>
      induction y using TensorProduct.inductionOn with
      | tmul k' a' => exact degreeZeroLinearMap_mul_tmul k k' a a'
      | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
    | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]

theorem degreeZeroRingHom_tmul (k : K) (a : degreeZeroSubring A) :
    degreeZeroRingHom K A (k ⊗ₜ a) =
      ((DegreeZeroRing.of K k) ᵍ⊗ₜ[ℤ] (a : A) : ExtendScalars K A) := rfl

theorem degreeZeroRingHom_mem (x : K ⊗[ℤ] degreeZeroSubring A) :
    degreeZeroRingHom K A x ∈ grading (M := ExtendScalars K A) 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul k a =>
    rw [degreeZeroRingHom_tmul]
    have h := GradedTensorProduct.tmul_mem_grading (R := ℤ) (i := 0) (j := 0)
      (DegreeZeroRing.mem_grading_zero K (DegreeZeroRing.of K k)) (mem_degreeZeroSubring.mp a.2)
    rwa [add_zero] at h
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

variable (K A) in
/-- `K ⊗_ℤ A⁰ → (K ⊗ A)⁰`, `k ⊗ a ↦ k ⊗ a`; a ring isomorphism (`degreeZeroEquiv`). -/
def degreeZeroHom : K ⊗[ℤ] degreeZeroSubring A →+* degreeZeroSubring (ExtendScalars K A) :=
  (degreeZeroRingHom K A).codRestrict _ fun x =>
    mem_degreeZeroSubring.mpr (degreeZeroRingHom_mem x)

theorem degreeZeroHom_surjective : Function.Surjective (degreeZeroHom K A) := by
  rintro ⟨x, hx⟩
  suffices h : ∃ y, degreeZeroRingHom K A y = x from
    h.imp fun y hy => Subtype.ext hy
  refine GradedTensorProduct.grading_induction 𝒦 𝒜 (mem_degreeZeroSubring.mp hx)
    (motive := fun x => ∃ y, degreeZeroRingHom K A y = x) ⟨0, map_zero _⟩ ?_ ?_
  · intro i j a b hij
    by_cases hi : i = 0
    · subst hi
      have hj : j = 0 := by omega
      subst hj
      exact ⟨(DegreeZeroRing.of K).symm (a : DegreeZeroRing K) ⊗ₜ
        ⟨(b : A), mem_degreeZeroSubring.mpr b.2⟩, degreeZeroRingHom_tmul _ _⟩
    · refine ⟨0, ?_⟩
      rw [map_zero, DegreeZeroRing.eq_zero_of_mem_grading K hi a.2, GradedTensorProduct.zero_tmul]
  · rintro x y ⟨x', rfl⟩ ⟨y', rfl⟩
    exact ⟨x' + y', map_add _ _ _⟩

variable (A) in
/-- The projection `A → A⁰` onto the degree-`0` component. -/
def degreeZeroProj : A →+ degreeZeroSubring A :=
  { toFun := fun a => ⟨decompose (grading (M := A)) a 0,
      mem_degreeZeroSubring.mpr (decompose (grading (M := A)) a 0).2⟩
    map_zero' := Subtype.ext (by simp)
    map_add' := fun a b => Subtype.ext (by simp) }

theorem degreeZeroProj_coe (a : degreeZeroSubring A) : degreeZeroProj A (a : A) = a :=
  Subtype.ext (decompose_of_mem_same _ (mem_degreeZeroSubring.mp a.2))

theorem degreeZeroHom_injective : Function.Injective (degreeZeroHom K A) := by
  let Φ : ExtendScalars K A →ₗ[ℤ] K ⊗[ℤ] degreeZeroSubring A :=
    (LinearMap.rTensor _ (DegreeZeroRing.of K).symm.toAddMonoidHom.toIntLinearMap) ∘ₗ
      (LinearMap.lTensor (DegreeZeroRing K) (degreeZeroProj A).toIntLinearMap) ∘ₗ
        (_root_.GradedTensorProduct.of ℤ 𝒦 𝒜).symm.toLinearMap
  have hΦ : Φ ∘ₗ degreeZeroLinearMap K A = LinearMap.id := by
    refine TensorProduct.ext' fun k a => ?_
    change Φ (degreeZeroLinearMap K A (k ⊗ₜ a)) = k ⊗ₜ a
    rw [degreeZeroLinearMap_tmul]
    change (DegreeZeroRing.of K).symm (DegreeZeroRing.of K k) ⊗ₜ degreeZeroProj A (a : A) = k ⊗ₜ a
    rw [degreeZeroProj_coe]
    rfl
  intro x y h
  have hx : Φ (degreeZeroRingHom K A x) = x := LinearMap.congr_fun hΦ x
  have hy : Φ (degreeZeroRingHom K A y) = y := LinearMap.congr_fun hΦ y
  have h' : degreeZeroRingHom K A x = degreeZeroRingHom K A y := congrArg Subtype.val h
  rw [← hx, ← hy, h']

variable (K A) in
/-- **The degree-`0` part of `K ⊗ A` is `K ⊗_ℤ A⁰`**: `k ⊗ a ↦ k ⊗ a` is a ring isomorphism. -/
def degreeZeroEquiv : K ⊗[ℤ] degreeZeroSubring A ≃+* degreeZeroSubring (ExtendScalars K A) :=
  RingEquiv.ofBijective (degreeZeroHom K A) ⟨degreeZeroHom_injective, degreeZeroHom_surjective⟩

@[simp]
theorem degreeZeroEquiv_tmul (k : K) (a : degreeZeroSubring A) :
    (degreeZeroEquiv K A (k ⊗ₜ a) : ExtendScalars K A) =
      (DegreeZeroRing.of K k) ᵍ⊗ₜ[ℤ] (a : A) :=
  degreeZeroRingHom_tmul k a

theorem d_degreeZeroRingHom (hd0 : ∀ a ∈ grading (M := A) 0, d a = 0)
    (x : K ⊗[ℤ] degreeZeroSubring A) : d (degreeZeroRingHom K A x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul k a =>
    rw [degreeZeroRingHom_tmul, GradedTensorProduct.d_tmul', DegreeZeroRing.d_eq_zero,
      hd0 _ (mem_degreeZeroSubring.mp a.2), GradedTensorProduct.zero_tmul,
      GradedTensorProduct.tmul_zero, add_zero]
  | add x y hx hy => rw [map_add, d_add, hx, hy, add_zero]

include hneg in
/-- **Positivity of `K ⊗ A`**: if `Aⁿ = 0` for `n < 0`, `d` vanishes on `A⁰`, and the ring
`K ⊗_ℤ A⁰` is semisimple, then `K ⊗ A` is positive, with degree-`0` part `K ⊗_ℤ A⁰`
(`degreeZeroEquiv`). Hence (`DG.IsPositive.K0DegreeZeroEquiv`, `DG.IsPositive.basis`) `K₀(K ⊗ A)`
is `K₀` of `(K ⊗ A)⁰ ≅ K ⊗_ℤ A⁰`, free on the classes of the simple idempotents. -/
theorem isPositive_of_isSemisimpleRing (hd0 : ∀ a ∈ grading (M := A) 0, d a = 0)
    [IsSemisimpleRing (K ⊗[ℤ] degreeZeroSubring A)] : IsPositive (ExtendScalars K A) where
  grading_eq_bot n hn := grading_eq_bot hneg hn
  isSemisimple := (degreeZeroHom K A).isSemisimpleRing_of_surjective degreeZeroHom_surjective
  d_eq_zero_of_mem_zero a ha := by
    obtain ⟨x, hx⟩ := degreeZeroHom_surjective (K := K) (A := A) ⟨a, mem_degreeZeroSubring.mpr ha⟩
    have hax : a = degreeZeroRingHom K A x := (congrArg Subtype.val hx).symm
    rw [hax]
    exact d_degreeZeroRingHom hd0 x

include hneg h0 in
/-- **Positivity of `K ⊗ A`** for `A` connected over `ℤ` and `K` a semisimple commutative ring
(e.g. a field). -/
theorem isPositive [IsSemisimpleRing K] : IsPositive (ExtendScalars K A) where
  grading_eq_bot n hn := grading_eq_bot hneg hn
  isSemisimple :=
    haveI : IsSemisimpleRing (DegreeZeroRing K) := inferInstanceAs (IsSemisimpleRing K)
    (toDegreeZero K A).isSemisimpleRing_of_surjective (toDegreeZero_surjective hneg h0)
  d_eq_zero_of_mem_zero a ha := by
    obtain ⟨k, rfl⟩ := exists_eq_tmul_one hneg h0 ha
    exact d_tmul_one k

include hneg h0 in
/-- Every nonzero element of `(K ⊗ A)⁰` is a unit, for `K` a field. -/
theorem isUnit_of_ne_zero {K : Type*} [Field K] (a : degreeZeroSubring (ExtendScalars K A))
    (ha : a ≠ 0) : IsUnit a := by
  obtain ⟨k, rfl⟩ := toDegreeZero_surjective hneg h0 a
  have hk : k ≠ 0 := fun h => ha (by rw [h, map_zero])
  exact (isUnit_iff_ne_zero.mpr hk).map _

/-! ### Nontriviality -/

variable (hchar : ∀ m : ℤ, (m : A) = 0 → m = 0)

include h0 hchar in
/-- If `A⁰ = ℤ · 1` freely, the degree-`0` component is a retraction `A → ℤ` of `ℤ → A`. -/
theorem exists_retraction : ∃ r : A →+ ℤ, r 1 = 1 := by
  let e : ℤ →+ grading (M := A) 0 :=
    { toFun := fun m => ⟨(m : A), by
        rw [← zsmul_one]; exact zsmul_mem (one_mem_grading (A := A)) m⟩
      map_zero' := Subtype.ext Int.cast_zero
      map_add' := fun m n => Subtype.ext (Int.cast_add m n) }
  have he : Function.Bijective e := by
    refine ⟨fun m n h => ?_, fun a => ?_⟩
    · have h' : ((m - n : ℤ) : A) = 0 := by
        rw [Int.cast_sub]; exact sub_eq_zero.mpr (congrArg Subtype.val h)
      exact sub_eq_zero.mp (hchar _ h')
    · obtain ⟨m, hm⟩ := h0 a a.2
      exact ⟨m, Subtype.ext hm⟩
  let E := AddEquiv.ofBijective e he
  let p : A →+ grading (M := A) 0 :=
    (DFinsupp.evalAddMonoidHom 0).comp (decomposeAddEquiv (grading (M := A))).toAddMonoidHom
  refine ⟨E.symm.toAddMonoidHom.comp p, ?_⟩
  have hp : p 1 = ⟨1, one_mem_grading (A := A)⟩ := by
    change decompose (grading (M := A)) (1 : A) 0 = _
    exact Subtype.ext (decompose_of_mem_same _ (one_mem_grading (A := A)))
  change E.symm (p 1) = 1
  rw [hp, AddEquiv.symm_apply_eq]
  exact Subtype.ext Int.cast_one.symm

include h0 hchar in
theorem nontrivial [Nontrivial K] : Nontrivial (ExtendScalars K A) := by
  have : Nontrivial (DegreeZeroRing K) := inferInstanceAs (Nontrivial K)
  obtain ⟨r, hr⟩ := exists_retraction h0 hchar
  let Φ : ExtendScalars K A →ₗ[ℤ] DegreeZeroRing K :=
    (TensorProduct.rid ℤ (DegreeZeroRing K)).toLinearMap ∘ₗ
      (LinearMap.lTensor (DegreeZeroRing K) r.toIntLinearMap) ∘ₗ
        (_root_.GradedTensorProduct.of ℤ 𝒦 𝒜).symm.toLinearMap
  have h1 : Φ 1 = 1 := by
    change TensorProduct.rid ℤ (DegreeZeroRing K) ((1 : DegreeZeroRing K) ⊗ₜ r 1) = 1
    rw [hr, TensorProduct.rid_tmul, one_smul]
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have := congrArg Φ h
  rw [h1, map_zero] at this
  exact one_ne_zero this

/-! ### `K₀(K ⊗ A) ≃ ℤ` -/

variable {K A : Type u} [Field K] [Ring A] [DGAddCommGroup A] [DGRing A]
  (hneg : ∀ n < 0, grading (M := A) n = ⊥)
  (h0 : ∀ a ∈ grading (M := A) 0, ∃ m : ℤ, (m : A) = a)
  (hchar : ∀ m : ℤ, (m : A) = 0 → m = 0)
  [HasDerivedCategory.{u, u} (ExtendScalars K A)]
  [HasDerivedCategory.{u, u} (isPositive (K := K) hneg h0).degreeZeroDGSubring]

/-- **`K₀(K ⊗ A) ≃ ℤ`**, `[K ⊗ A] ↦ 1`, for `A` connected over `ℤ` with `1` of infinite order
and `K` a field. -/
noncomputable def K0EquivInt : DGRing.K0 (ExtendScalars K A) ≃+ ℤ :=
  haveI := nontrivial (K := K) h0 hchar
  (isPositive hneg h0).K0EquivIntOfDivisionRing (isUnit_of_ne_zero hneg h0)

theorem K0EquivInt_self :
    K0EquivInt hneg h0 hchar (DGRing.K0.self (ExtendScalars K A)) = 1 :=
  haveI := nontrivial (K := K) h0 hchar
  (isPositive hneg h0).K0EquivIntOfDivisionRing_self _

end ExtendScalars

end DG

end
