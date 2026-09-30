import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import DG.Algebra.Commutative
import DG.Module.Cohomology

/-!
# The Koszul complex as a commutative dg algebra

Let `R` be a commutative ring, `M` an `R`-module and `φ : M →ₗ[R] R` a linear form. The Koszul
complex `K(φ)` is the exterior algebra `⋀ M`, with `⋀ᵏ M` placed in cohomological degree `-k`,
and with differential the contraction (interior product) with `φ`,
  `d (m₁ ∧ ⋯ ∧ mₖ) = ∑ᵢ (-1)^(i-1) φ(mᵢ) m₁ ∧ ⋯ ∧ m̂ᵢ ∧ ⋯ ∧ mₖ`,
which is Mathlib's `CliffordAlgebra.contractLeft φ` for the zero quadratic form. It is the
unique derivation (for the graded Leibniz rule `d (a * b) = d a * b + (-1)^{|a|} a * d b`)
extending `m ↦ φ m` on `M = ⋀¹ M`. For `M = R^ι` and `φ = ∑ᵢ xᵢ eᵢ*`, this is the Koszul
complex `K(x₁, …, xₙ)` of the elements `xᵢ ∈ R` (`DG.KoszulComplex.ofElements`), with
`d eᵢ = xᵢ`.

## Main definitions and results

* `DG.koszulGrading R M`: the `ℤ`-grading of `ExteriorAlgebra R M` with `⋀ᵏ M` in degree `-k`,
  a `GradedAlgebra` (`DG.koszulGrading.gradedAlgebra`), which is strictly graded commutative
  (`DG.koszulGrading.isGradedCommStrict`).
* `DG.KoszulComplex φ`: a type synonym for `ExteriorAlgebra R M` carrying the dg structure,
  with instances `DGAddCommGroup`, `DGRing`, `DGAlgebra R`, and
  `DG.KoszulComplex.isGradedCommStrict` (strict graded commutativity of the dg algebra), so that
  it is a commutative dg algebra (`DG.KoszulComplex.isCDGA`).
* `DG.KoszulComplex.cohomologyZeroAddEquiv`: `H⁰(K(φ)) ≅ R ⧸ φ(M)`; for the Koszul complex of
  elements, `H⁰(K(x₁, …, xₙ)) ≅ R ⧸ (x₁, …, xₙ)`
  (`DG.KoszulComplex.ofElements.cohomologyZeroAddEquiv`).

## Conventions

Gradings are cohomological (`d` has degree `+1`), so the exterior degree is negated; the Koszul
sign of `⋀ᵏ M` is `(-1)^(-k) = (-1)^k`.
-/

open DirectSum

namespace DG

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-! ### Contraction on the exterior algebra -/

namespace ExteriorAlgebra

open _root_.ExteriorAlgebra

/-- The contraction with a linear form `φ`, as an `R`-linear endomorphism of the exterior
algebra (Mathlib's `CliffordAlgebra.contractLeft` for the zero quadratic form). -/
abbrev contract (φ : Module.Dual R M) : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) φ

variable (φ : Module.Dual R M)

theorem contract_ι_mul (m : M) (b : ExteriorAlgebra R M) :
    contract φ (ι R m * b) = φ m • b - ι R m * contract φ b :=
  CliffordAlgebra.contractLeft_ι_mul φ m b

theorem contract_ι (m : M) : contract φ (ι R m) = algebraMap R _ (φ m) :=
  CliffordAlgebra.contractLeft_ι _ φ m

theorem contract_algebraMap (r : R) : contract φ (algebraMap R (ExteriorAlgebra R M) r) = 0 :=
  CliffordAlgebra.contractLeft_algebraMap _ φ r

theorem contract_algebraMap_mul (r : R) (b : ExteriorAlgebra R M) :
    contract φ (algebraMap R _ r * b) = algebraMap R _ r * contract φ b :=
  CliffordAlgebra.contractLeft_algebraMap_mul φ r b

@[simp]
theorem contract_contract (a : ExteriorAlgebra R M) : contract φ (contract φ a) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft φ a

theorem ι_mem_exteriorPower_one (m : M) : ι R m ∈ ⋀[R]^1 M := by
  simp

/-- The contraction lowers the exterior degree by one, and kills `⋀⁰ M = R`. -/
theorem contract_mem_aux {k : ℕ} {a : ExteriorAlgebra R M} (ha : a ∈ ⋀[R]^k M) :
    contract φ a ∈ ⋀[R]^(k - 1) M ∧ (k = 0 → contract φ a = 0) := by
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y i _ _ ihx ihy =>
    exact ⟨by rw [map_add]; exact add_mem ihx.1 ihy.1,
      fun h => by rw [map_add, ihx.2 h, ihy.2 h, add_zero]⟩
  | mem_mul m hm i x hx ih =>
    obtain ⟨m, rfl⟩ := hm
    refine ⟨?_, fun h => absurd h (Nat.succ_ne_zero i)⟩
    rw [contract_ι_mul]
    refine sub_mem (Submodule.smul_mem _ _ (by simpa using hx)) ?_
    rcases i with _ | i
    · rw [ih.2 rfl, mul_zero]
      exact zero_mem _
    · have := Submodule.mul_mem_mul (LinearMap.mem_range_self (ι R) m) ih.1
      simpa [pow_succ'] using this

theorem contract_mem {k : ℕ} {a : ExteriorAlgebra R M} (ha : a ∈ ⋀[R]^(k + 1) M) :
    contract φ a ∈ ⋀[R]^k M :=
  (contract_mem_aux φ ha).1

theorem contract_eq_zero_of_mem_zero {a : ExteriorAlgebra R M} (ha : a ∈ ⋀[R]^0 M) :
    contract φ a = 0 :=
  (contract_mem_aux φ ha).2 rfl

/-- The contraction is an antiderivation: for `a ∈ ⋀ᵏ M`,
`φ ⌋ (a * b) = (φ ⌋ a) * b + (-1)^k a * (φ ⌋ b)`. -/
theorem contract_mul {k : ℕ} {a : ExteriorAlgebra R M} (ha : a ∈ ⋀[R]^k M)
    (b : ExteriorAlgebra R M) :
    contract φ (a * b) = contract φ a * b + koszulSign k • (a * contract φ b) := by
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r => simp [contract_algebraMap_mul]
  | add x y i _ _ ihx ihy =>
    rw [add_mul, map_add, ihx, ihy, map_add, add_mul, add_mul, smul_add]
    abel
  | mem_mul m hm i x hx ih =>
    obtain ⟨m, rfl⟩ := hm
    rw [mul_assoc, contract_ι_mul, ih, contract_ι_mul, Nat.cast_succ, koszulSign_add,
      show koszulSign 1 = -1 from Int.negOnePow_one, mul_neg_one, Units.neg_smul]
    simp only [mul_add, sub_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
    abel

/-! ### Graded commutativity of the exterior algebra -/

theorem ι_mul_ι_comm (m n : M) : ι R m * ι R n = -(ι R n * ι R m) :=
  eq_neg_of_add_eq_zero_left (ι_add_mul_swap m n)

theorem ι_mul_comm (m : M) {j : ℕ} {b : ExteriorAlgebra R M} (hb : b ∈ ⋀[R]^j M) :
    ι R m * b = koszulSign j • (b * ι R m) := by
  induction hb using Submodule.pow_induction_on_left' with
  | algebraMap r => simp [Algebra.commutes]
  | add x y i _ _ ihx ihy => rw [mul_add, ihx, ihy, add_mul, smul_add]
  | mem_mul n hn i x hx ih =>
    obtain ⟨n, rfl⟩ := hn
    rw [← mul_assoc, ι_mul_ι_comm, neg_mul, mul_assoc, ih, Nat.cast_succ, koszulSign_add,
      mul_smul_comm, mul_smul, mul_assoc]
    simp

theorem mul_comm_of_mem {i j : ℕ} {a b : ExteriorAlgebra R M} (ha : a ∈ ⋀[R]^i M)
    (hb : b ∈ ⋀[R]^j M) : a * b = koszulSign (i * j) • (b * a) := by
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r => simp [Algebra.commutes]
  | add x y i _ _ ihx ihy => rw [add_mul, ihx, ihy, mul_add, smul_add]
  | mem_mul m hm i x hx ih =>
    obtain ⟨m, rfl⟩ := hm
    rw [mul_assoc, ih, mul_smul_comm, ← mul_assoc, ι_mul_comm m hb, smul_mul_assoc, smul_smul,
      mul_assoc, ← koszulSign_add, Nat.cast_succ]
    congr 2
    ring

theorem mul_self_of_odd {i : ℕ} {a : ExteriorAlgebra R M} (ha : a ∈ ⋀[R]^i M) (hi : Odd i) :
    a * a = 0 := by
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r => exact absurd hi (by decide)
  | add x y i hx hy ihx ihy =>
    have hxy := mul_comm_of_mem hx hy
    rw [koszulSign, Int.negOnePow_odd _ (by exact_mod_cast hi.mul hi), Units.neg_smul,
      one_smul] at hxy
    rw [add_mul, mul_add, mul_add, ihx hi, ihy hi, hxy]
    abel
  | mem_mul m hm i x hx _ =>
    obtain ⟨m, rfl⟩ := hm
    rw [mul_assoc, ← mul_assoc x, mul_comm_of_mem hx (ι_mem_exteriorPower_one m), smul_mul_assoc,
      mul_smul_comm, ← mul_assoc, ← mul_assoc, ι_sq_zero, zero_mul, zero_mul, smul_zero]

end ExteriorAlgebra

/-! ### The cohomological grading -/

open _root_.ExteriorAlgebra

variable (R M) in
/-- The cohomological grading of the Koszul complex: `⋀ᵏ M` in degree `-k`, and `0` in positive
degrees. -/
def koszulGrading (n : ℤ) : Submodule R (ExteriorAlgebra R M) :=
  if n ≤ 0 then ⋀[R]^((-n).toNat) M else ⊥

namespace koszulGrading

theorem neg_natCast (k : ℕ) : koszulGrading R M (-(k : ℤ)) = ⋀[R]^k M := by
  rw [koszulGrading, ite_eq_left (by omega), neg_neg, Int.toNat_natCast]

theorem zero : koszulGrading R M 0 = ⋀[R]^0 M := by
  simpa using neg_natCast (R := R) (M := M) 0

theorem of_pos {n : ℤ} (hn : 0 < n) : koszulGrading R M n = ⊥ := by
  rw [koszulGrading, ite_eq_right (by omega)]

theorem mem_neg_natCast {k : ℕ} {a : ExteriorAlgebra R M} (ha : a ∈ ⋀[R]^k M) :
    a ∈ koszulGrading R M (-k) := by
  rwa [neg_natCast]

/-- Case analysis on an element of `koszulGrading R M n`: either `n = -k` and the element lies
in `⋀ᵏ M`, or the element is zero. -/
@[elab_as_elim]
theorem cases {P : ∀ (n : ℤ) (a : ExteriorAlgebra R M), a ∈ koszulGrading R M n → Prop}
    (h_neg : ∀ (k : ℕ) (a : ExteriorAlgebra R M) (ha : a ∈ ⋀[R]^k M),
      P (-k) a (mem_neg_natCast ha))
    (h_zero : ∀ n, P n 0 (zero_mem _)) {n : ℤ} {a : ExteriorAlgebra R M}
    (ha : a ∈ koszulGrading R M n) : P n a ha := by
  by_cases hn : n ≤ 0
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -k := ⟨(-n).toNat, by omega⟩
    have ha' : a ∈ ⋀[R]^k M := by rwa [neg_natCast] at ha
    exact h_neg k a ha'
  · rw [of_pos (by omega), Submodule.mem_bot] at ha
    subst ha
    exact h_zero n

instance gradedMonoid : SetLike.GradedMonoid (koszulGrading R M) where
  one_mem := by
    rw [zero]
    exact SetLike.GradedOne.one_mem
  mul_mem i j a b ha hb := by
    induction ha using cases with
    | h_zero => simp
    | h_neg k a ha =>
      induction hb using cases with
      | h_zero => simp
      | h_neg l b hb =>
        rw [show -(k : ℤ) + -(l : ℤ) = -((k + l : ℕ) : ℤ) by push_cast; ring]
        exact mem_neg_natCast (SetLike.GradedMul.mul_mem ha hb)

theorem ι_mem (m : M) : ι R m ∈ koszulGrading R M (-1) := by
  simpa using mem_neg_natCast (ExteriorAlgebra.ι_mem_exteriorPower_one (R := R) m)

/-- `ι` into the direct sum of the `koszulGrading R M n`, in degree `-1`. -/
def gradedι : M →ₗ[R] ⨁ n : ℤ, koszulGrading R M n :=
  DirectSum.lof R ℤ (fun n => koszulGrading R M n) (-1) ∘ₗ
    (ι R).codRestrict _ ι_mem

theorem gradedι_apply (m : M) :
    gradedι m = DirectSum.of (fun n => koszulGrading R M n) (-1) ⟨ι R m, ι_mem m⟩ := rfl

theorem gradedι_sq_zero (m : M) : gradedι (R := R) m * gradedι m = 0 := by
  rw [gradedι_apply, DirectSum.of_mul_of]
  exact DFinsupp.single_eq_zero.mpr (Subtype.ext <| ExteriorAlgebra.ι_sq_zero _)

/-- The decomposition of the exterior algebra into the pieces of `koszulGrading R M`, as an
algebra homomorphism. -/
def liftι : ExteriorAlgebra R M →ₐ[R] ⨁ n : ℤ, koszulGrading R M n :=
  lift R ⟨gradedι, gradedι_sq_zero⟩

theorem liftι_eq (n : ℤ) (x : koszulGrading R M n) :
    liftι (x : ExteriorAlgebra R M) = DirectSum.of (fun n => koszulGrading R M n) n x := by
  obtain ⟨x, hx⟩ := x
  induction hx using cases with
  | h_zero n =>
    change liftι 0 = DirectSum.of (fun n => koszulGrading R M n) n 0
    rw [map_zero, map_zero]
  | h_neg k x hx =>
    induction hx using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      rw [AlgHom.commutes, DirectSum.algebraMap_apply]
      refine DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext ?_ rfl)
      show (0 : ℤ) = -((0 : ℕ) : ℤ)
      simp
    | add x y i hx hy ihx ihy =>
      rw [map_add, ihx, ihy, ← map_add]
      rfl
    | mem_mul m hm i x hx ih =>
      obtain ⟨m, rfl⟩ := hm
      rw [map_mul, ih, liftι, lift_ι_apply, gradedι_apply, DirectSum.of_mul_of]
      refine DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext ?_ rfl)
      show -1 + -(i : ℤ) = -((i + 1 : ℕ) : ℤ)
      push_cast
      ring

/-- The exterior algebra with `⋀ᵏ M` in degree `-k` is a `ℤ`-graded algebra. -/
instance gradedAlgebra : GradedAlgebra (koszulGrading R M) :=
  GradedAlgebra.ofAlgHom _ liftι
    (by
      ext m
      dsimp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        AlgHom.id_apply, liftι]
      rw [lift_ι_apply, gradedι_apply, DirectSum.coeAlgHom_of, Subtype.coe_mk])
    liftι_eq

/-- The exterior algebra, graded with `⋀ᵏ M` in degree `-k`, is strictly graded commutative. -/
instance isGradedCommStrict : IsGradedCommStrict (koszulGrading R M) where
  mul_comm_of_mem {i j a b} ha hb := by
    induction ha using cases with
    | h_zero => simp
    | h_neg k a ha =>
      induction hb using cases with
      | h_zero => simp
      | h_neg l b hb =>
        rw [ExteriorAlgebra.mul_comm_of_mem ha hb, neg_mul_neg]
  mul_self_of_odd {i a} ha hi := by
    induction ha using cases with
    | h_zero => simp
    | h_neg k a ha =>
      exact ExteriorAlgebra.mul_self_of_odd ha (by simpa using hi)

/-- The decomposition of the exterior algebra into the additive subgroups underlying
`koszulGrading R M`. -/
@[instance_reducible]
def decompositionAddSubgroup : Decomposition fun n => (koszulGrading R M n).toAddSubgroup where
  decompose' := DirectSum.decompose (koszulGrading R M)
  left_inv x := DirectSum.Decomposition.left_inv (ℳ := koszulGrading R M) x
  right_inv x := DirectSum.Decomposition.right_inv (ℳ := koszulGrading R M) x

end koszulGrading

/-! ### The Koszul complex -/

/-- The Koszul complex of a linear form `φ : M →ₗ[R] R`: the exterior algebra `⋀ M`, with `⋀ᵏ M`
in cohomological degree `-k` and differential the contraction with `φ`. A type synonym for
`ExteriorAlgebra R M`, carrying the dg algebra structure. -/
@[nolint unusedArguments]
def KoszulComplex (_φ : Module.Dual R M) : Type _ := ExteriorAlgebra R M

namespace KoszulComplex

variable (φ : Module.Dual R M)

instance instRing : Ring (KoszulComplex φ) := inferInstanceAs (Ring (ExteriorAlgebra R M))

instance instAlgebra : Algebra R (KoszulComplex φ) :=
  inferInstanceAs (Algebra R (ExteriorAlgebra R M))

/-- The identification of the Koszul complex with the exterior algebra. -/
def toExterior : KoszulComplex φ ≃ₐ[R] ExteriorAlgebra R M := AlgEquiv.refl

/-- The Koszul complex is a dg abelian group: `⋀ᵏ M` in degree `-k`, with differential the
contraction with `φ`. -/
noncomputable instance instDGAddCommGroup : DGAddCommGroup (KoszulComplex φ) where
  grading n := (koszulGrading R M n).toAddSubgroup
  decomposition := koszulGrading.decompositionAddSubgroup
  d := (ExteriorAlgebra.contract φ).toAddMonoidHom
  d_mem' {n a} ha := by
    change ExteriorAlgebra.contract φ a ∈ koszulGrading R M (n + 1)
    change a ∈ koszulGrading R M n at ha
    induction ha using koszulGrading.cases with
    | h_zero => simp
    | h_neg k a ha =>
      rcases k with _ | k
      · rw [ExteriorAlgebra.contract_eq_zero_of_mem_zero φ ha]
        exact zero_mem _
      · rw [show -((k + 1 : ℕ) : ℤ) + 1 = -(k : ℤ) by push_cast; ring]
        exact koszulGrading.mem_neg_natCast (ExteriorAlgebra.contract_mem φ ha)
  d_d' a := ExteriorAlgebra.contract_contract φ a

variable {φ}

theorem mem_grading_iff {n : ℤ} {a : KoszulComplex φ} :
    a ∈ grading n ↔ (toExterior φ a) ∈ koszulGrading R M n :=
  Iff.rfl

theorem d_apply (a : KoszulComplex φ) :
    toExterior φ (d a) = ExteriorAlgebra.contract φ (toExterior φ a) :=
  rfl

theorem d_ι (m : M) :
    d ((toExterior φ).symm (ι R m)) = algebraMap R (KoszulComplex φ) (φ m) :=
  ExteriorAlgebra.contract_ι φ m

variable (φ)

set_option backward.isDefEq.respectTransparency false in
/-- The Koszul complex is a dg ring: the contraction with `φ` is an antiderivation. -/
instance instDGRing : DGRing (KoszulComplex φ) where
  one_mem := by
    change (1 : ExteriorAlgebra R M) ∈ koszulGrading R M 0
    exact SetLike.GradedOne.one_mem
  mul_mem i j a b ha hb := by
    change toExterior φ a * toExterior φ b ∈ koszulGrading R M (i + j)
    exact SetLike.GradedMul.mul_mem (A := koszulGrading R M) ha hb
  d_mul' {n a} ha b := by
    change a ∈ koszulGrading R M n at ha
    induction ha using koszulGrading.cases with
    | h_zero => simp
    | h_neg k a ha =>
      rw [koszulSign, Int.negOnePow_neg]
      exact ExteriorAlgebra.contract_mul φ ha b

/-- The Koszul complex is a dg `R`-algebra. -/
instance instDGAlgebra : DGAlgebra R (KoszulComplex φ) where
  algebraMap_mem' r := SetLike.algebraMap_mem_graded (koszulGrading R M) r
  d_algebraMap' r := ExteriorAlgebra.contract_algebraMap φ r

/-- The Koszul complex is a strictly graded commutative dg algebra. -/
instance isGradedCommStrict :
    IsGradedCommStrict (DGAlgebra.gradingSubmodule R (KoszulComplex φ)) where
  mul_comm_of_mem ha hb := IsGradedComm.mul_comm_of_mem (𝒜 := koszulGrading R M) ha hb
  mul_self_of_odd ha hi := IsGradedCommStrict.mul_self_of_odd (𝒜 := koszulGrading R M) ha hi

/-- The Koszul complex is a commutative dg algebra. -/
instance isCDGA : IsCDGA (KoszulComplex φ) :=
  IsCDGA.of_isGradedCommStrict R

/-- The Koszul differential is the unique additive map satisfying the graded Leibniz rule, killing
the scalars and sending `m ∈ M = ⋀¹ M` to `φ m`. -/
theorem eq_d_of_leibniz (D : KoszulComplex φ →+ KoszulComplex φ)
    (hD : ∀ {n : ℤ} {a : KoszulComplex φ}, a ∈ grading n → ∀ b : KoszulComplex φ,
      D (a * b) = D a * b + koszulSign n • (a * D b))
    (hι : ∀ m : M, D ((toExterior φ).symm (ι R m)) = algebraMap R (KoszulComplex φ) (φ m))
    (halg : ∀ r : R, D (algebraMap R (KoszulComplex φ) r) = 0) (a : KoszulComplex φ) :
    D a = d a := by
  induction a using induction_on with
  | h_zero => rw [map_zero, d_zero]
  | h_add a b ha hb => rw [map_add, map_add, ha, hb]
  | h_homogeneous a =>
    obtain ⟨a, ha⟩ := a
    have key : ∀ (n : ℤ) (a : ExteriorAlgebra R M), a ∈ koszulGrading R M n →
        D ((toExterior φ).symm a) = d ((toExterior φ).symm a) := by
      intro n a ha
      induction ha using koszulGrading.cases with
      | h_zero => simp
      | h_neg k a ha =>
        induction ha using Submodule.pow_induction_on_left' with
        | algebraMap r => exact (halg r).trans (d_algebraMap R _).symm
        | add x y i _ _ ihx ihy =>
          rw [map_add, map_add, map_add, ihx, ihy]
        | mem_mul m hm i x hx ih =>
          obtain ⟨m, rfl⟩ := hm
          have hm : (toExterior φ).symm (ι R m) ∈ grading (M := KoszulComplex φ) (-1) :=
            koszulGrading.ι_mem m
          refine (hD hm ((toExterior φ).symm x)).trans ?_
          rw [hι, ih, map_mul, d_mul hm, d_ι]
    exact key _ a ha

/-! ### `H⁰` of the Koszul complex -/

theorem mem_grading_zero_iff {a : KoszulComplex φ} :
    a ∈ grading 0 ↔ ∃ r : R, algebraMap R (KoszulComplex φ) r = a := by
  rw [mem_grading_iff, koszulGrading.zero]
  change _ ∈ LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M) ^ 0 ↔ _
  rw [pow_zero, Submodule.mem_one]
  rfl

theorem mem_grading_neg_one_iff {a : KoszulComplex φ} :
    a ∈ grading (-1) ↔ ∃ m : M, (toExterior φ).symm (ι R m) = a := by
  rw [mem_grading_iff, show (-1 : ℤ) = -((1 : ℕ) : ℤ) by norm_num, koszulGrading.neg_natCast]
  change _ ∈ LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M) ^ 1 ↔ _
  rw [pow_one]
  rfl

/-- The algebra map `ExteriorAlgebra R M → R` (killing `⋀^{≥1}`), on the Koszul complex. -/
def augmentation : KoszulComplex φ →ₐ[R] R := algebraMapInv

@[simp]
theorem augmentation_algebraMap (r : R) : augmentation φ (algebraMap R _ r) = r :=
  algebraMap_leftInverse M r

theorem mem_cocycles_zero_iff {a : KoszulComplex φ} :
    a ∈ cocycles (KoszulComplex φ) 0 ↔ a ∈ grading 0 := by
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  have h1 : d a ∈ grading (M := KoszulComplex φ) (0 + 1) := d_mem h
  rw [mem_grading_iff, koszulGrading.of_pos (by norm_num)] at h1
  exact h1

theorem mem_coboundaries_zero_iff {a : KoszulComplex φ} :
    a ∈ coboundaries (KoszulComplex φ) 0 ↔
      ∃ r ∈ LinearMap.range φ, algebraMap R (KoszulComplex φ) r = a := by
  rw [mem_coboundaries, zero_sub]
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨m, rfl⟩ := (mem_grading_neg_one_iff φ).mp hb
    exact ⟨φ m, LinearMap.mem_range_self φ m, (d_ι m).symm⟩
  · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
    exact ⟨_, (mem_grading_neg_one_iff φ).mpr ⟨m, rfl⟩, d_ι m⟩

/-- The map from degree-`0` cocycles of the Koszul complex to `R ⧸ φ(M)`. -/
noncomputable def cocyclesZeroToQuotient :
    cocycles (KoszulComplex φ) 0 →+ R ⧸ LinearMap.range φ :=
  (Submodule.mkQ (LinearMap.range φ)).toAddMonoidHom.comp
    ((augmentation φ).toRingHom.toAddMonoidHom.comp (cocycles (KoszulComplex φ) 0).subtype)

/-- The map `H⁰(K(φ)) → R ⧸ φ(M)`. -/
noncomputable def cohomologyZeroToQuotient :
    cohomology (KoszulComplex φ) 0 →+ R ⧸ LinearMap.range φ :=
  cohomology.lift (cocyclesZeroToQuotient φ) fun z hz => by
    obtain ⟨r, hr, hz⟩ := (mem_coboundaries_zero_iff φ).mp hz
    simp only [cocyclesZeroToQuotient, AddMonoidHom.coe_comp, Function.comp_apply,
      AddSubgroup.coe_subtype, ← hz, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, augmentation_algebraMap,
      LinearMap.toAddMonoidHom_coe, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hr]

theorem cohomologyZeroToQuotient_mk (z : cocycles (KoszulComplex φ) 0) :
    cohomologyZeroToQuotient φ (cohomology.mk _ 0 z) =
      Submodule.Quotient.mk (augmentation φ z) :=
  cohomology.lift_mk _ _ z

theorem cohomologyZeroToQuotient_bijective :
    Function.Bijective (cohomologyZeroToQuotient φ) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using cohomology.induction_on with
    | h z =>
    rw [cohomologyZeroToQuotient_mk, Submodule.Quotient.mk_eq_zero] at hx
    rw [cohomology.mk_eq_zero_iff, mem_coboundaries_zero_iff]
    obtain ⟨r, hr⟩ := (mem_grading_zero_iff φ).mp (cocycles_le_grading 0 z.2)
    refine ⟨r, ?_, hr⟩
    rwa [← hr, augmentation_algebraMap] at hx
  · intro q
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hr : algebraMap R (KoszulComplex φ) r ∈ cocycles (KoszulComplex φ) 0 :=
      (mem_cocycles_zero_iff φ).mpr ((mem_grading_zero_iff φ).mpr ⟨r, rfl⟩)
    refine ⟨cohomology.mk _ 0 ⟨_, hr⟩, ?_⟩
    rw [cohomologyZeroToQuotient_mk, augmentation_algebraMap]

/-- `H⁰(K(φ)) ≅ R ⧸ φ(M)`: the degree-`0` cohomology of the Koszul complex of `φ` is the
quotient of `R` by the image of `φ`. -/
noncomputable def cohomologyZeroAddEquiv :
    cohomology (KoszulComplex φ) 0 ≃+ R ⧸ LinearMap.range φ :=
  AddEquiv.ofBijective (cohomologyZeroToQuotient φ) (cohomologyZeroToQuotient_bijective φ)

@[simp]
theorem cohomologyZeroAddEquiv_mkOf (r : R) (hr : algebraMap R (KoszulComplex φ) r ∈ grading 0)
    (hd : d (algebraMap R (KoszulComplex φ) r) = 0) :
    cohomologyZeroAddEquiv φ (cohomology.mkOf hr hd) = Submodule.Quotient.mk r := by
  rw [cohomologyZeroAddEquiv, AddEquiv.ofBijective_apply, cohomology.mkOf,
    cohomologyZeroToQuotient_mk, augmentation_algebraMap]

/-! ### The Koszul complex of a family of elements -/

variable {κ : Type*} [Fintype κ]

/-- The Koszul complex `K(x₁, …, xₙ)` of a finite family of elements `x : ι → R`: the Koszul
complex of the linear form `R^ι → R`, `v ↦ ∑ᵢ vᵢ xᵢ`, which sends the `i`-th basis vector
`eᵢ` to `xᵢ`. -/
abbrev ofElements (x : κ → R) : Type _ := KoszulComplex (Fintype.linearCombination R x)

namespace ofElements

variable (x : κ → R)

theorem d_ι_single [DecidableEq κ] (i : κ) :
    d ((toExterior _).symm (ι R (Pi.single i 1)) : ofElements x) =
      algebraMap R (ofElements x) (x i) := by
  rw [d_ι, Fintype.linearCombination_apply_single, one_smul]

theorem range_eq : LinearMap.range (Fintype.linearCombination R x) = Ideal.span (Set.range x) :=
  Fintype.range_linearCombination R x

/-- `H⁰(K(x₁, …, xₙ)) ≅ R ⧸ (x₁, …, xₙ)`. -/
noncomputable def cohomologyZeroAddEquiv :
    cohomology (ofElements x) 0 ≃+ R ⧸ Ideal.span (Set.range x) :=
  (KoszulComplex.cohomologyZeroAddEquiv _).trans
    (Submodule.quotEquivOfEq _ _ (range_eq x)).toAddEquiv

end ofElements

end KoszulComplex

end DG
