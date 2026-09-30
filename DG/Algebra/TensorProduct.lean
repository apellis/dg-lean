import DG.Algebra.Constructions
import DG.Algebra.Equiv
import DG.Graded.Opposite
import DG.Graded.TensorProduct

/-!
# Tensor products of dg algebras

For dg `R`-algebras `A` and `B` with gradings `𝒜 = DGAlgebra.gradingSubmodule R A` and
`ℬ = DGAlgebra.gradingSubmodule R B`, the graded tensor product `𝒜 ᵍ⊗[R] ℬ` (Mathlib's graded
tensor product, with product `(a ⊗ b) * (a' ⊗ b') = (-1)^{|b||a'|} • (a a' ⊗ b b')`, see
`DG.Graded.TensorProduct`) is a dg `R`-algebra with the grading `DG.GradedTensorProduct.grading`
and the differential

  `d (a ⊗ b) = d a ⊗ b + (-1)^{|a|} • a ⊗ d b`.

## Main definitions and results

* `DG.DGAlgebra.parity`: the parity operator `a ↦ (-1)^{|a|} • a` of a dg algebra, an `R`-linear
  map anticommuting with `d` (`DG.DGAlgebra.parity_d`).
* `DG.GradedTensorProduct.dLinear`: the differential, defined as the `R`-linear map
  `d ⊗ id + parity ⊗ d`; `DG.GradedTensorProduct.dLinear_dLinear`: it squares to zero.
* `DG.GradedTensorProduct.instDGAddCommGroup`, `DG.GradedTensorProduct.instDGRing` (the Leibniz
  rule for the signed product, `DG.GradedTensorProduct.d_tmul_mul_tmul`),
  `DG.GradedTensorProduct.instDGAlgebra`: the dg algebra structure.
* `DG.GradedTensorProduct.includeLeftDGAlgHom`, `DG.GradedTensorProduct.includeRightDGAlgHom`:
  the inclusions `a ↦ a ⊗ 1` and `b ↦ 1 ⊗ b` as morphisms of dg algebras.
* `DG.GradedTensorProduct.map`: the tensor product `f ⊗ g` of morphisms of dg algebras, with
  `map_id` and `map_comp`.
* `DG.GradedTensorProduct.commDGAlgEquiv`, `DG.GradedTensorProduct.assocDGAlgEquiv`,
  `DG.GradedTensorProduct.lidDGAlgEquiv`: the symmetry, associativity and unit isomorphisms of
  `DG.Graded.TensorProduct` commute with the differentials, hence are isomorphisms of dg algebras.
  For the unit, `R` is the dg algebra concentrated in degree `0` with zero differential
  (`DG.DGAddCommGroup.degreeZero`).
-/

suppress_compilation

open DirectSum GradedTensorProduct
open scoped TensorProduct

namespace DG

private theorem ks_eq {m n : ℤ} (h : Even (m - n)) : koszulSign m = koszulSign n :=
  (Int.negOnePow_eq_iff m n).mpr h

private theorem mul_units_smul {T : Type*} [Ring T] (x y : T) (u : ℤˣ) :
    x * (u • y) = u • (x * y) := by
  rw [Units.smul_def, Units.smul_def, mul_smul_comm]

/-! ### The parity operator -/

section Parity

variable (R A : Type*) [CommRing R] [Ring A] [Algebra R A] [DGAddCommGroup A] [DGRing A]
  [DGAlgebra R A]

/-- The parity operator of a dg `R`-algebra, the `R`-linear map `a ↦ (-1)^{|a|} • a` on
homogeneous elements. -/
def DGAlgebra.parity : A →ₗ[R] A :=
  DirectSum.toModule R ℤ A
      (fun i => (koszulSign i : ℤ) • (DGAlgebra.gradingSubmodule R A i).subtype) ∘ₗ
    (decomposeLinearEquiv (DGAlgebra.gradingSubmodule R A)).toLinearMap

variable {R A}

theorem DGAlgebra.parity_of_mem {i : ℤ} {a : A} (ha : a ∈ grading i) :
    DGAlgebra.parity R A a = koszulSign i • a := by
  rw [DGAlgebra.parity, LinearMap.comp_apply, LinearEquiv.coe_coe, decomposeLinearEquiv_apply,
    decompose_of_mem (DGAlgebra.gradingSubmodule R A) (i := i) ha, ← lof_eq_of R,
    toModule_lof, LinearMap.smul_apply, Submodule.subtype_apply, Units.smul_def]

@[simp]
theorem DGAlgebra.parity_one : DGAlgebra.parity R A 1 = 1 := by
  rw [DGAlgebra.parity_of_mem one_mem_grading, koszulSign_zero, one_smul]

theorem DGAlgebra.parity_d (a : A) : DGAlgebra.parity R A (d a) = -d (DGAlgebra.parity R A a) := by
  induction a using induction_on with
  | h_zero => simp
  | h_homogeneous a =>
    rw [DGAlgebra.parity_of_mem (d_mem a.2), DGAlgebra.parity_of_mem a.2, d_units_smul,
      koszulSign_add, koszulSign, koszulSign, Int.negOnePow_one, mul_neg_one, Units.neg_smul]
  | h_add a a' ha ha' => rw [d_add, map_add, map_add, ha, ha', d_add, neg_add]

end Parity

/-! ### The differential of a tensor product -/

variable {R A B C : Type*} [CommRing R]
  [Ring A] [Algebra R A] [DGAddCommGroup A] [DGRing A] [DGAlgebra R A]
  [Ring B] [Algebra R B] [DGAddCommGroup B] [DGRing B] [DGAlgebra R B]
  [Ring C] [Algebra R C] [DGAddCommGroup C] [DGRing C] [DGAlgebra R C]

local notation "𝒜" => DGAlgebra.gradingSubmodule R A
local notation "ℬ" => DGAlgebra.gradingSubmodule R B
local notation "𝒞" => DGAlgebra.gradingSubmodule R C

namespace GradedTensorProduct

variable (R A B) in
/-- The differential of the tensor product of two dg algebras, the `R`-linear map
`a ⊗ b ↦ d a ⊗ b + (-1)^{|a|} • a ⊗ d b`, written as `d ⊗ id + parity ⊗ d`. -/
def dLinear :
    GradedTensorProduct R (DGAlgebra.gradingSubmodule R A) (DGAlgebra.gradingSubmodule R B) →ₗ[R]
      GradedTensorProduct R (DGAlgebra.gradingSubmodule R A) (DGAlgebra.gradingSubmodule R B) :=
  (_root_.GradedTensorProduct.of R (DGAlgebra.gradingSubmodule R A)
      (DGAlgebra.gradingSubmodule R B)).toLinearMap ∘ₗ
    (TensorProduct.map (DGAlgebra.dLinear R A) LinearMap.id +
      TensorProduct.map (DGAlgebra.parity R A) (DGAlgebra.dLinear R B)) ∘ₗ
    (_root_.GradedTensorProduct.of R (DGAlgebra.gradingSubmodule R A)
      (DGAlgebra.gradingSubmodule R B)).symm.toLinearMap

theorem dLinear_tmul (a : A) (b : B) :
    dLinear R A B (a ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) = d a ᵍ⊗ₜ[R] b + DGAlgebra.parity R A a ᵍ⊗ₜ[R] d b := by
  rw [dLinear, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, _root_.GradedTensorProduct.of_symm_of, LinearMap.add_apply,
    TensorProduct.map_tmul,
    TensorProduct.map_tmul, map_add]
  rfl

theorem dLinear_tmul_of_mem {i : ℤ} {a : A} (ha : a ∈ DG.grading i) (b : B) :
    dLinear R A B (a ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) = d a ᵍ⊗ₜ[R] b + koszulSign i • (a ᵍ⊗ₜ[R] d b) := by
  rw [dLinear_tmul, DGAlgebra.parity_of_mem ha, koszulSign_smul_tmul]

theorem dLinear_dLinear (x : 𝒜 ᵍ⊗[R] ℬ) : dLinear R A B (dLinear R A B x) = 0 := by
  suffices h : dLinear R A B ∘ₗ dLinear R A B = 0 from LinearMap.congr_fun h x
  apply _root_.GradedTensorProduct.hom_ext
  refine TensorProduct.ext' fun a b => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.zero_comp, LinearMap.zero_apply]
  change dLinear R A B (dLinear R A B (a ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ)) = 0
  rw [dLinear_tmul, map_add, dLinear_tmul, dLinear_tmul, d_d, d_d, zero_tmul 𝒜 ℬ,
    tmul_zero 𝒜 ℬ, zero_add, add_zero, DGAlgebra.parity_d, ← add_tmul 𝒜 ℬ, neg_add_cancel,
    zero_tmul 𝒜 ℬ]

theorem dLinear_mem {n : ℤ} {x : 𝒜 ᵍ⊗[R] ℬ} (hx : x ∈ GradedTensorProduct.grading 𝒜 ℬ n) :
    dLinear R A B x ∈ GradedTensorProduct.grading 𝒜 ℬ (n + 1) := by
  refine grading_induction 𝒜 ℬ hx (motive := fun x =>
    dLinear R A B x ∈ GradedTensorProduct.grading 𝒜 ℬ (n + 1)) ?_ ?_ ?_
  · rw [map_zero]; exact zero_mem _
  · intro i j a b hij
    rw [dLinear_tmul_of_mem a.2, Units.smul_def]
    exact add_mem (tmul_mem_of_eq 𝒜 ℬ (by omega) (d_mem a.2) b.2)
      (zsmul_mem (tmul_mem_of_eq 𝒜 ℬ (by omega) a.2 (d_mem b.2)) _)
  · intro x y hx hy
    rw [map_add]; exact add_mem hx hy

/-- The tensor product of two dg algebras is a dg abelian group, with the grading of the graded
tensor product and the differential `d (a ⊗ b) = d a ⊗ b + (-1)^{|a|} • a ⊗ d b`. -/
instance instDGAddCommGroup : DGAddCommGroup (𝒜 ᵍ⊗[R] ℬ) where
  grading n := (GradedTensorProduct.grading 𝒜 ℬ n).toAddSubgroup
  decomposition :=
    { decompose' := DirectSum.decompose (GradedTensorProduct.grading 𝒜 ℬ)
      left_inv := DirectSum.Decomposition.left_inv (ℳ := GradedTensorProduct.grading 𝒜 ℬ)
      right_inv := DirectSum.Decomposition.right_inv (ℳ := GradedTensorProduct.grading 𝒜 ℬ) }
  d := (dLinear R A B).toAddMonoidHom
  d_mem' hx := dLinear_mem hx
  d_d' := dLinear_dLinear

theorem d_def (x : 𝒜 ᵍ⊗[R] ℬ) : d x = dLinear R A B x := rfl

theorem mem_grading_iff {n : ℤ} {x : 𝒜 ᵍ⊗[R] ℬ} :
    x ∈ DG.grading n ↔ x ∈ GradedTensorProduct.grading 𝒜 ℬ n := Iff.rfl

/-- The differential on pure tensors: `d (a ⊗ b) = d a ⊗ b + (-1)^{|a|} • a ⊗ d b` for `a`
homogeneous of degree `i`. -/
theorem d_tmul {i : ℤ} {a : A} (ha : a ∈ DG.grading i) (b : B) :
    d (a ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) = d a ᵍ⊗ₜ[R] b + koszulSign i • (a ᵍ⊗ₜ[R] d b) :=
  dLinear_tmul_of_mem ha b

theorem d_tmul' (a : A) (b : B) :
    d (a ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) = d a ᵍ⊗ₜ[R] b + DGAlgebra.parity R A a ᵍ⊗ₜ[R] d b :=
  dLinear_tmul a b

theorem tmul_mem_grading {i j : ℤ} {a : A} (ha : a ∈ DG.grading i) {b : B} (hb : b ∈ DG.grading j) :
    (a ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) ∈ DG.grading (i + j) :=
  tmul_mem 𝒜 ℬ ha hb

/-- Induction principle for the tensor product of two dg algebras: a predicate holding for `0`
and for pure tensors of homogeneous elements, and closed under addition, holds everywhere. -/
@[elab_as_elim]
theorem induction_on_tmul {motive : (𝒜 ᵍ⊗[R] ℬ) → Prop} (zero : motive 0)
    (tmul : ∀ {i j : ℤ} {a : A} (_ : a ∈ DG.grading i) {b : B} (_ : b ∈ DG.grading j),
      motive (a ᵍ⊗ₜ[R] b))
    (add : ∀ x y, motive x → motive y → motive (x + y)) (x : 𝒜 ᵍ⊗[R] ℬ) : motive x := by
  induction x using induction_on with
  | h_zero => exact zero
  | h_homogeneous x =>
    exact grading_induction 𝒜 ℬ x.2 zero (fun a b _ => tmul a.2 b.2) add
  | h_add x y hx hy => exact add x y hx hy

/-- The Leibniz rule on products of pure tensors of homogeneous elements. -/
theorem d_tmul_mul_tmul {i j i' : ℤ} {a : A} (ha : a ∈ DG.grading i) {b : B}
    (hb : b ∈ DG.grading j) {a' : A} (ha' : a' ∈ DG.grading i') (b' : B) :
    d ((a ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) * (a' ᵍ⊗ₜ[R] b')) =
      d (a ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) * (a' ᵍ⊗ₜ[R] b') +
        koszulSign (i + j) • ((a ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) * d (a' ᵍ⊗ₜ[R] b')) := by
  rw [tmul_mul_tmul 𝒜 ℬ a hb ha' b', d_units_smul, d_tmul (mul_mem_grading ha ha'), d_mul ha,
    d_mul hb, d_tmul ha, d_tmul ha', add_mul, mul_add, smul_mul_assoc, mul_units_smul,
    tmul_mul_tmul 𝒜 ℬ (d a) hb ha' b', tmul_mul_tmul 𝒜 ℬ a (d_mem hb) ha' b',
    tmul_mul_tmul 𝒜 ℬ a hb (d_mem ha') b', tmul_mul_tmul 𝒜 ℬ a hb ha' (d b')]
  simp only [add_tmul 𝒜 ℬ, tmul_add 𝒜 ℬ, koszulSign_smul_tmul 𝒜 ℬ, tmul_koszulSign_smul 𝒜 ℬ,
    smul_add, smul_smul, ← koszulSign_add]
  rw [ks_eq (m := i + (j + 1) * i') (n := j * i' + (i + i')) ⟨0, by ring⟩,
    ks_eq (m := i + j + j * (i' + 1)) (n := j * i' + i) ⟨j, by ring⟩,
    ks_eq (m := i + j + (i' + j * i')) (n := j * i' + (i + i' + j)) ⟨0, by ring⟩]
  abel

/-- The tensor product of two dg algebras is a dg ring. -/
instance instDGRing : DGRing (𝒜 ᵍ⊗[R] ℬ) where
  one_mem := (instGradedMonoid 𝒜 ℬ).one_mem
  mul_mem := (instGradedMonoid 𝒜 ℬ).mul_mem
  d_mul' {n x} hx y := by
    refine induction_on_tmul ?_ ?_ ?_ y
    · simp only [mul_zero, d_zero, smul_zero, add_zero]
    · intro i' j' a' ha' b' _
      refine grading_induction 𝒜 ℬ hx (motive := fun x => d (x * (a' ᵍ⊗ₜ[R] b')) =
        d x * (a' ᵍ⊗ₜ[R] b') + koszulSign n • (x * d (a' ᵍ⊗ₜ[R] b'))) ?_ ?_ ?_
      · simp only [zero_mul, d_zero, smul_zero, add_zero]
      · intro i j a b hij
        subst hij
        exact d_tmul_mul_tmul a.2 b.2 ha' b'
      · intro x x' hx hx'
        simp only [add_mul, d_add, hx, hx', smul_add]
        abel
    · intro y y' hy hy'
      simp only [mul_add, d_add, hy, hy', smul_add]
      abel

/-- The tensor product of two dg `R`-algebras is a dg `R`-algebra. -/
instance instDGAlgebra : DGAlgebra R (𝒜 ᵍ⊗[R] ℬ) where
  algebraMap_mem' r := by
    rw [_root_.GradedTensorProduct.algebraMap_def]
    exact tmul_mem_of_eq 𝒜 ℬ (add_zero 0) (algebraMap_mem_grading R r) (one_mem_grading (A := B))
  d_algebraMap' r := by
    rw [_root_.GradedTensorProduct.algebraMap_def, d_tmul (algebraMap_mem_grading R r),
      d_algebraMap, d_one, zero_tmul 𝒜 ℬ,
      tmul_zero 𝒜 ℬ, smul_zero, add_zero]

theorem gradingSubmodule_eq :
    DGAlgebra.gradingSubmodule R (𝒜 ᵍ⊗[R] ℬ) = GradedTensorProduct.grading 𝒜 ℬ := rfl

/-! ### The inclusions -/

variable (R A B) in
/-- The inclusion `a ↦ a ⊗ 1` as a morphism of dg algebras. -/
def includeLeftDGAlgHom :
    A →ᵈᵍₐ[R]
      GradedTensorProduct R (DGAlgebra.gradingSubmodule R A) (DGAlgebra.gradingSubmodule R B) where
  __ := _root_.GradedTensorProduct.includeLeft (DGAlgebra.gradingSubmodule R A)
    (DGAlgebra.gradingSubmodule R B)
  map_mem' ha := includeLeft_mem _ _ ha
  map_d' a := by
    change d a ᵍ⊗ₜ[R] (1 : B) = d (a ᵍ⊗ₜ[R] (1 : B) : 𝒜 ᵍ⊗[R] ℬ)
    rw [d_tmul', d_one, tmul_zero 𝒜 ℬ, add_zero]

@[simp]
theorem includeLeftDGAlgHom_apply (a : A) :
    includeLeftDGAlgHom R A B a = (a ᵍ⊗ₜ[R] (1 : B) : 𝒜 ᵍ⊗[R] ℬ) := rfl

variable (R A B) in
/-- The inclusion `b ↦ 1 ⊗ b` as a morphism of dg algebras. -/
def includeRightDGAlgHom :
    B →ᵈᵍₐ[R]
      GradedTensorProduct R (DGAlgebra.gradingSubmodule R A) (DGAlgebra.gradingSubmodule R B) where
  __ := _root_.GradedTensorProduct.includeRight (DGAlgebra.gradingSubmodule R A)
    (DGAlgebra.gradingSubmodule R B)
  map_mem' hb := includeRight_mem _ _ hb
  map_d' b := by
    change (1 : A) ᵍ⊗ₜ[R] d b = d ((1 : A) ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ)
    rw [d_tmul', d_one, zero_tmul 𝒜 ℬ, zero_add, DGAlgebra.parity_one]

@[simp]
theorem includeRightDGAlgHom_apply (b : B) :
    includeRightDGAlgHom R A B b = ((1 : A) ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) := rfl

/-! ### Functoriality -/

section Map

variable {A' B' : Type*} [Ring A'] [Algebra R A'] [DGAddCommGroup A'] [DGRing A']
  [DGAlgebra R A'] [Ring B'] [Algebra R B'] [DGAddCommGroup B'] [DGRing B'] [DGAlgebra R B']

local notation "𝒜'" => DGAlgebra.gradingSubmodule R A'
local notation "ℬ'" => DGAlgebra.gradingSubmodule R B'

/-- The tensor product of two morphisms of dg algebras, as an algebra homomorphism. -/
def mapAlgHom (f : A →ᵈᵍₐ[R] A') (g : B →ᵈᵍₐ[R] B') : (𝒜 ᵍ⊗[R] ℬ) →ₐ[R] (𝒜' ᵍ⊗[R] ℬ') :=
  lift 𝒜 ℬ ((includeLeft 𝒜' ℬ').comp f.toAlgHom) ((includeRight 𝒜' ℬ').comp g.toAlgHom)
    fun i j a b => by
      simp only [AlgHom.comp_apply, includeLeft_apply, includeRight_apply, DGAlgHom.toAlgHom_apply]
      rw [tmul_one_mul_one_tmul, tmul_mul_tmul 𝒜' ℬ' (1 : A') (g.map_mem b.2) (f.map_mem a.2),
        one_mul, mul_one, uzpow_neg_one_eq_koszulSign, smul_smul, Int.units_mul_self, one_smul]

theorem mapAlgHom_tmul (f : A →ᵈᵍₐ[R] A') (g : B →ᵈᵍₐ[R] B') (a : A) (b : B) :
    mapAlgHom f g (a ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) = (f a ᵍ⊗ₜ[R] g b : 𝒜' ᵍ⊗[R] ℬ') := by
  rw [mapAlgHom, lift_tmul, AlgHom.comp_apply, AlgHom.comp_apply, includeLeft_apply,
    includeRight_apply, tmul_one_mul_one_tmul]
  rfl

/-- The tensor product of two morphisms of dg algebras, `a ⊗ b ↦ f a ⊗ g b`. -/
def map (f : A →ᵈᵍₐ[R] A') (g : B →ᵈᵍₐ[R] B') : (𝒜 ᵍ⊗[R] ℬ) →ᵈᵍₐ[R] (𝒜' ᵍ⊗[R] ℬ') where
  __ := mapAlgHom f g
  map_mem' {n x} hx := by
    change mapAlgHom f g x ∈ DG.grading n
    refine grading_induction 𝒜 ℬ hx (motive := fun x => mapAlgHom f g x ∈ DG.grading n)
      ?_ ?_ ?_
    · rw [map_zero]; exact zero_mem _
    · intro i j a b hij
      rw [mapAlgHom_tmul, ← hij]
      exact tmul_mem_grading (f.map_mem a.2) (g.map_mem b.2)
    · intro x y hx hy
      rw [map_add]; exact add_mem hx hy
  map_d' x := by
    change mapAlgHom f g (d x) = d (mapAlgHom f g x)
    refine induction_on_tmul ?_ ?_ ?_ x
    · rw [d_zero, map_zero, d_zero]
    · intro i j a ha b _
      rw [d_tmul ha, map_add, map_koszulSign_smul, mapAlgHom_tmul, mapAlgHom_tmul,
        mapAlgHom_tmul, d_tmul (f.map_mem ha), DGAlgHom.map_d, DGAlgHom.map_d]
    · intro x y hx hy
      rw [d_add, map_add, map_add, hx, hy, d_add]

@[simp]
theorem map_tmul (f : A →ᵈᵍₐ[R] A') (g : B →ᵈᵍₐ[R] B') (a : A) (b : B) :
    map f g (a ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) = (f a ᵍ⊗ₜ[R] g b : 𝒜' ᵍ⊗[R] ℬ') :=
  mapAlgHom_tmul f g a b

@[simp]
theorem map_id : map (DGAlgHom.id : A →ᵈᵍₐ[R] A) (DGAlgHom.id : B →ᵈᵍₐ[R] B) = DGAlgHom.id := by
  ext x
  refine induction_on_tmul ?_ ?_ ?_ x
  · rw [map_zero, map_zero]
  · intro i j a _ b _
    rw [map_tmul]
    rfl
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]

theorem map_comp {A'' B'' : Type*} [Ring A''] [Algebra R A''] [DGAddCommGroup A''] [DGRing A'']
    [DGAlgebra R A''] [Ring B''] [Algebra R B''] [DGAddCommGroup B''] [DGRing B'']
    [DGAlgebra R B''] (f : A →ᵈᵍₐ[R] A') (g : B →ᵈᵍₐ[R] B') (f' : A' →ᵈᵍₐ[R] A'')
    (g' : B' →ᵈᵍₐ[R] B'') : map (f'.comp f) (g'.comp g) = (map f' g').comp (map f g) := by
  ext x
  refine induction_on_tmul ?_ ?_ ?_ x
  · rw [map_zero, map_zero]
  · intro i j a _ b _
    rw [DGAlgHom.comp_apply, map_tmul, map_tmul, map_tmul]
    rfl
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]

end Map

/-! ### Symmetry, associativity and unit -/

variable (R A B) in
/-- The symmetry `A ⊗ B ≅ B ⊗ A`, `a ⊗ b ↦ (-1)^{|a||b|} • b ⊗ a`, is an isomorphism of dg
algebras. -/
def commDGAlgEquiv :
    GradedTensorProduct R (DGAlgebra.gradingSubmodule R A) (DGAlgebra.gradingSubmodule R B)
      ≃ᵈᵍₐ[R]
    GradedTensorProduct R (DGAlgebra.gradingSubmodule R B) (DGAlgebra.gradingSubmodule R A) :=
  DGAlgEquiv.ofAlgEquiv (_root_.GradedTensorProduct.comm _ _) (fun hx => comm_mem _ _ hx)
    fun x => by
      refine induction_on_tmul ?_ ?_ ?_ x
      · rw [d_zero, map_zero, map_zero]
      · intro i j a ha b hb
        rw [d_tmul ha, map_add, map_koszulSign_smul, comm_tmul 𝒜 ℬ (d_mem ha) hb,
          comm_tmul 𝒜 ℬ ha (d_mem hb), comm_tmul 𝒜 ℬ ha hb, d_units_smul, d_tmul hb, smul_add,
          smul_smul, smul_smul, ← koszulSign_add, ← koszulSign_add, add_comm,
          ks_eq (m := i + i * (j + 1)) (n := i * j) ⟨i, by ring⟩,
          ks_eq (m := (i + 1) * j) (n := i * j + j) ⟨0, by ring⟩]
      · intro x y hx hy
        rw [d_add, map_add, map_add, hx, hy, d_add]

@[simp]
theorem commDGAlgEquiv_apply (x : 𝒜 ᵍ⊗[R] ℬ) :
    commDGAlgEquiv R A B x = _root_.GradedTensorProduct.comm 𝒜 ℬ x := rfl

set_option backward.isDefEq.respectTransparency false in
variable (R A B C) in
/-- The associativity isomorphism `(A ⊗ B) ⊗ C ≅ A ⊗ (B ⊗ C)`, `(a ⊗ b) ⊗ c ↦ a ⊗ (b ⊗ c)`, is an
isomorphism of dg algebras. -/
def assocDGAlgEquiv :
    GradedTensorProduct R
        (DGAlgebra.gradingSubmodule R
          (GradedTensorProduct R (DGAlgebra.gradingSubmodule R A) (DGAlgebra.gradingSubmodule R B)))
        (DGAlgebra.gradingSubmodule R C)
      ≃ᵈᵍₐ[R]
    GradedTensorProduct R (DGAlgebra.gradingSubmodule R A)
        (DGAlgebra.gradingSubmodule R
          (GradedTensorProduct R (DGAlgebra.gradingSubmodule R B)
            (DGAlgebra.gradingSubmodule R C))) :=
  DGAlgEquiv.ofAlgEquiv (assoc 𝒜 ℬ 𝒞) (fun hx => assoc_mem 𝒜 ℬ 𝒞 hx) fun x => by
    refine induction_on_tmul ?_ ?_ ?_ x
    · rw [d_zero, map_zero, map_zero]
    · intro m k y hy c hc
      refine grading_induction 𝒜 ℬ hy (motive := fun y =>
        assoc 𝒜 ℬ 𝒞 (show DGAlgebra.gradingSubmodule R (𝒜 ᵍ⊗[R] ℬ) ᵍ⊗[R] 𝒞 from
          d (y ᵍ⊗ₜ[R] c)) =
          d (show 𝒜 ᵍ⊗[R] DGAlgebra.gradingSubmodule R (ℬ ᵍ⊗[R] 𝒞) from
            assoc 𝒜 ℬ 𝒞 (show DGAlgebra.gradingSubmodule R (𝒜 ᵍ⊗[R] ℬ) ᵍ⊗[R] 𝒞 from
              y ᵍ⊗ₜ[R] c)))
        ?_ ?_ ?_
      · dsimp only
        rw [zero_tmul, d_zero, map_zero, d_zero]
      · intro i j a b hij
        dsimp only
        subst hij
        rw [d_tmul (tmul_mem_grading a.2 b.2), d_tmul a.2, add_tmul, koszulSign_smul_tmul,
          map_add, map_add, map_koszulSign_smul, map_koszulSign_smul, assoc_tmul_tmul,
          assoc_tmul_tmul, assoc_tmul_tmul, assoc_tmul_tmul, d_tmul a.2, d_tmul b.2, tmul_add,
          tmul_koszulSign_smul, smul_add, smul_smul, ← koszulSign_add, add_assoc]
        rfl
      · intro y y' hy hy'
        dsimp only
        rw [add_tmul, d_add, map_add, map_add, hy, hy', d_add]
    · intro x y hx hy
      rw [d_add, map_add, map_add, hx, hy, d_add]

@[simp]
theorem assocDGAlgEquiv_tmul_tmul (a : A) (b : B) (c : C) :
    assocDGAlgEquiv R A B C ((a ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) ᵍ⊗ₜ[R] c) =
      a ᵍ⊗ₜ[R] (b ᵍ⊗ₜ[R] c : ℬ ᵍ⊗[R] 𝒞) :=
  assoc_tmul_tmul 𝒜 ℬ 𝒞 a b c

section Lid

variable (R B)

/-- The algebra homomorphism `R ⊗ B → B`, `r ⊗ b ↦ r • b`, where `R` is concentrated in degree
`0` (`DGAddCommGroup.degreeZero`). -/
def lidDegreeZeroHom :
    letI := DGAddCommGroup.degreeZero R
    haveI := DGRing.degreeZero R
    haveI := DGAlgebra.degreeZero R
    GradedTensorProduct R (DGAlgebra.gradingSubmodule R R) ℬ →ₐ[R] B :=
  letI := DGAddCommGroup.degreeZero R
  haveI := DGRing.degreeZero R
  haveI := DGAlgebra.degreeZero R
  lift _ ℬ (Algebra.ofId R B) (AlgHom.id R B) fun i j r b => by
    rw [Algebra.ofId_apply, AlgHom.id_apply]
    rcases (mem_degreeZeroGrading_iff R).mp r.2 with h | h
    · subst h
      rw [mul_zero, uzpow_zero, one_smul, Algebra.commutes]
    · rw [h, map_zero, zero_mul, mul_zero, smul_zero]

theorem lidDegreeZeroHom_tmul (r : R) (b : B) :
    letI := DGAddCommGroup.degreeZero R
    haveI := DGRing.degreeZero R
    haveI := DGAlgebra.degreeZero R
    lidDegreeZeroHom R B (r ᵍ⊗ₜ[R] b : GradedTensorProduct R (DGAlgebra.gradingSubmodule R R) ℬ) =
      r • b := by
  let := DGAddCommGroup.degreeZero R
  have := DGRing.degreeZero R
  have := DGAlgebra.degreeZero R
  rw [lidDegreeZeroHom, lift_tmul, Algebra.ofId_apply, AlgHom.id_apply, Algebra.smul_def]

/-- The unit isomorphism `R ⊗ B ≅ B`, `r ⊗ b ↦ r • b`, where `R` is the dg algebra concentrated
in degree `0` with zero differential (`DGAddCommGroup.degreeZero`), is an isomorphism of dg
algebras. -/
def lidDGAlgEquiv :
    letI := DGAddCommGroup.degreeZero R
    haveI := DGRing.degreeZero R
    haveI := DGAlgebra.degreeZero R
    GradedTensorProduct R (DGAlgebra.gradingSubmodule R R) ℬ ≃ᵈᵍₐ[R] B :=
  letI := DGAddCommGroup.degreeZero R
  haveI := DGRing.degreeZero R
  haveI := DGAlgebra.degreeZero R
  DGAlgEquiv.ofAlgEquiv
    (AlgEquiv.ofAlgHom (lidDegreeZeroHom R B) (includeRight (DGAlgebra.gradingSubmodule R R) ℬ)
      (AlgHom.ext fun b => by
        rw [AlgHom.comp_apply, AlgHom.id_apply, includeRight_apply, lidDegreeZeroHom_tmul,
          one_smul])
      (by
        refine algHom_ext _ ℬ (AlgHom.ext fun r => ?_) (AlgHom.ext fun b => ?_)
        · rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.id_apply,
            show includeLeft (DGAlgebra.gradingSubmodule R R) ℬ r = algebraMap R _ r from
              (includeLeft (DGAlgebra.gradingSubmodule R R) ℬ).commutes r,
            AlgHom.commutes, AlgHom.commutes]
        · simp only [AlgHom.comp_apply, AlgHom.id_apply, includeRight_apply, lidDegreeZeroHom_tmul,
            one_smul]))
    (fun {n x} hx => by
      refine grading_induction _ ℬ hx (motive := fun x => lidDegreeZeroHom R B x ∈ DG.grading n)
        ?_ ?_ ?_
      · rw [map_zero]; exact zero_mem _
      · intro i j r b hij
        rw [lidDegreeZeroHom_tmul]
        rcases (mem_degreeZeroGrading_iff R).mp r.2 with h | h
        · subst h
          rw [zero_add] at hij
          subst hij
          exact DGAlgebra.smul_mem _ b.2
        · rw [h, zero_smul]; exact zero_mem _
      · intro x y hx hy
        rw [map_add]; exact add_mem hx hy)
    fun x => by
      change lidDegreeZeroHom R B (d x) = d (lidDegreeZeroHom R B x)
      refine induction_on_tmul ?_ ?_ ?_ x
      · rw [d_zero, map_zero, map_zero]
      · intro i j r hr b _
        rw [d_tmul hr, lidDegreeZeroHom_tmul, map_add, map_koszulSign_smul, lidDegreeZeroHom_tmul,
          lidDegreeZeroHom_tmul,
          d_smul_algebra]
        rcases (mem_degreeZeroGrading_iff R).mp hr with h | h
        · subst h
          rw [koszulSign_zero, one_smul, show d r = 0 from rfl, zero_smul, zero_add]
        · rw [h, d_zero, zero_smul, zero_smul, smul_zero, zero_add]
      · intro x y hx hy
        rw [d_add, map_add, map_add, hx, hy, d_add]

end Lid

end GradedTensorProduct

end DG
