import Mathlib.Algebra.FreeAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import DG.Algebra.Hom

/-!
# Free dg algebras on graded sets (semi-free dg algebras)

Let `R` be a commutative ring, `X` a set of generators with degrees `deg : X → ℤ`, and
`δ : X → FreeAlgebra R X` a prescribed differential on the generators, with `δ x` homogeneous
of degree `deg x + 1`.

* `DG.freeGrading R deg`: the `ℤ`-grading of the free algebra `FreeAlgebra R X` in which a
  monomial `x₁ ⋯ xₖ` has degree `deg x₁ + ⋯ + deg xₖ`; it is a `GradedAlgebra`
  (`DG.freeGrading.gradedAlgebra`).
* `DG.freeDeriv deg δ`: the unique `R`-linear map satisfying the graded Leibniz rule
  `d (a * b) = d a * b + (-1)^{|a|} a * d b` and extending `x ↦ δ x`
  (`DG.freeDeriv_mul_of_mem`, `DG.freeDeriv_ι`, `DG.eq_freeDeriv_of_leibniz`). It has degree
  `+1` (`DG.freeDeriv_mem`), and `d ∘ d = 0` if and only if `d (δ x) = 0` for every generator
  (`DG.freeDeriv_freeDeriv_eq_zero_iff`).
* `DG.SemiFreeData R X`: degrees and a differential on generators satisfying these conditions;
  `DG.SemiFree S`: the free algebra, as a dg `R`-algebra (instances `DGAddCommGroup`, `DGRing`,
  `DGAlgebra R`).
* `DG.SemiFree.liftEquiv`: the universal property. Morphisms of dg `R`-algebras
  `SemiFree S → B` correspond to maps `f : X → B` with `f x ∈ B^{deg x}` and
  `d (f x) = f̃ (δ x)`, where `f̃ : FreeAlgebra R X → B` is the algebra map extending `f`.

## Implementation notes

The derivation is constructed from the algebra homomorphism
`FreeAlgebra R X → Mat₂(FreeAlgebra R X)`, `x ↦ [[(-1)^{deg x} x, δ x], [0, x]]`, whose value on
`a` is `[[ε a, d a], [0, a]]` with `ε` the grading automorphism `a ↦ (-1)^{|a|} a`; multiplicativity
of this map is exactly the Leibniz rule `d (a * b) = d a * b + ε a * d b`.
-/

open DirectSum

namespace DG

variable {R : Type*} [CommRing R] {X : Type*}

/-! ### The grading of the free algebra -/

section Grading

variable (R) (deg : X → ℤ)

/-- The grading of the free algebra `FreeAlgebra R X` in which the monomial `x₁ ⋯ xₖ` has
degree `deg x₁ + ⋯ + deg xₖ`: the degree-`n` part is spanned by the monomials of degree `n`. -/
def freeGrading (n : ℤ) : Submodule R (FreeAlgebra R X) :=
  Submodule.span R
    {a | ∃ l : List X, (l.map deg).sum = n ∧ (l.map (FreeAlgebra.ι R)).prod = a}

variable {R deg}

theorem prod_mem_freeGrading (l : List X) :
    (l.map (FreeAlgebra.ι R)).prod ∈ freeGrading R deg (l.map deg).sum :=
  Submodule.subset_span ⟨l, rfl, rfl⟩

theorem ι_mem_freeGrading (x : X) : FreeAlgebra.ι R x ∈ freeGrading R deg (deg x) := by
  simpa using prod_mem_freeGrading (R := R) (deg := deg) [x]

instance freeGrading.gradedMonoid : SetLike.GradedMonoid (freeGrading R deg) where
  one_mem := by simpa using prod_mem_freeGrading (R := R) (deg := deg) []
  mul_mem i j a b ha hb := by
    have hab := Submodule.mul_mem_mul ha hb
    rw [freeGrading, freeGrading, Submodule.span_mul_span] at hab
    refine Submodule.span_mono ?_ hab
    rintro _ ⟨_, ⟨l₁, rfl, rfl⟩, _, ⟨l₂, rfl, rfl⟩, rfl⟩
    exact ⟨l₁ ++ l₂, by simp, by simp⟩

namespace freeGrading

/-- The generators, in the direct sum of the graded pieces. -/
def gradedι (x : X) : ⨁ n, freeGrading R deg n :=
  DirectSum.of (fun n => freeGrading R deg n) (deg x) ⟨FreeAlgebra.ι R x, ι_mem_freeGrading x⟩

variable (R deg) in
/-- The decomposition of the free algebra into its graded pieces, as an algebra
homomorphism. -/
def decomposeAlgHom : FreeAlgebra R X →ₐ[R] ⨁ n, freeGrading R deg n :=
  FreeAlgebra.lift R gradedι

theorem decomposeAlgHom_prod (l : List X) :
    decomposeAlgHom R deg (l.map (FreeAlgebra.ι R)).prod =
      DirectSum.of (fun n => freeGrading R deg n) (l.map deg).sum
        ⟨_, prod_mem_freeGrading l⟩ := by
  induction l with
  | nil =>
    show decomposeAlgHom R deg 1 = _
    rw [map_one]
    rfl
  | cons x l ih =>
    show decomposeAlgHom R deg (FreeAlgebra.ι R x * (l.map (FreeAlgebra.ι R)).prod) = _
    rw [map_mul, ih, decomposeAlgHom, FreeAlgebra.lift_ι_apply, gradedι, DirectSum.of_mul_of]
    exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext rfl rfl)

theorem decomposeAlgHom_coe (n : ℤ) (a : freeGrading R deg n) :
    decomposeAlgHom R deg (a : FreeAlgebra R X) =
      DirectSum.of (fun n => freeGrading R deg n) n a := by
  obtain ⟨a, ha⟩ := a
  induction ha using Submodule.span_induction with
  | mem a h =>
    obtain ⟨l, rfl, rfl⟩ := h
    exact decomposeAlgHom_prod l
  | zero =>
    show decomposeAlgHom R deg 0 = DirectSum.of (fun n => freeGrading R deg n) _ 0
    rw [map_zero, map_zero]
  | add x y hx hy ihx ihy =>
    show decomposeAlgHom R deg (x + y) =
      DirectSum.of (fun n => freeGrading R deg n) _ (⟨x, hx⟩ + ⟨y, hy⟩)
    rw [map_add, ihx, ihy, map_add]
  | smul r x hx ih =>
    show decomposeAlgHom R deg (r • x) =
      DirectSum.of (fun n => freeGrading R deg n) _ (r • ⟨x, hx⟩)
    rw [map_smul, ih, ← DirectSum.lof_eq_of R, ← DirectSum.lof_eq_of R, map_smul]

/-- The free algebra, graded by the degrees of the generators, is a `ℤ`-graded algebra. -/
instance gradedAlgebra : GradedAlgebra (freeGrading R deg) :=
  GradedAlgebra.ofAlgHom _ (decomposeAlgHom R deg)
    (by
      ext x
      simp [decomposeAlgHom, gradedι])
    decomposeAlgHom_coe

/-- The decomposition of the free algebra into the additive subgroups underlying the
grading. -/
@[instance_reducible]
def decompositionAddSubgroup : Decomposition fun n => (freeGrading R deg n).toAddSubgroup where
  decompose' := DirectSum.decompose (freeGrading R deg)
  left_inv x := DirectSum.Decomposition.left_inv (ℳ := freeGrading R deg) x
  right_inv x := DirectSum.Decomposition.right_inv (ℳ := freeGrading R deg) x

end freeGrading

/-- Induction over the homogeneous elements of degree `n` of the free algebra: monomials,
sums and scalar multiples. -/
@[elab_as_elim]
theorem freeGrading.induction_on {n : ℤ}
    {P : ∀ a : FreeAlgebra R X, a ∈ freeGrading R deg n → Prop}
    (h_prod : ∀ (l : List X) (hl : (l.map deg).sum = n),
      P (l.map (FreeAlgebra.ι R)).prod (hl ▸ prod_mem_freeGrading l))
    (h_zero : P 0 (zero_mem _))
    (h_add : ∀ a b ha hb, P a ha → P b hb → P (a + b) (add_mem ha hb))
    (h_smul : ∀ (r : R) a ha, P a ha → P (r • a) (Submodule.smul_mem _ r ha))
    {a : FreeAlgebra R X} (ha : a ∈ freeGrading R deg n) : P a ha := by
  induction ha using Submodule.span_induction with
  | mem a h =>
    obtain ⟨l, hl, rfl⟩ := h
    exact h_prod l hl
  | zero => exact h_zero
  | add x y _ _ hx hy => exact h_add x y _ _ hx hy
  | smul r x _ hx => exact h_smul r x _ hx

end Grading

/-! ### The derivation -/

section Derivation

variable (deg : X → ℤ) (δ : X → FreeAlgebra R X)

/-- The grading automorphism `a ↦ (-1)^{|a|} a` of the free algebra. -/
def freeSignAut : FreeAlgebra R X →ₐ[R] FreeAlgebra R X :=
  FreeAlgebra.lift R fun x => koszulSign (deg x) • FreeAlgebra.ι R x

/-- The algebra homomorphism `a ↦ [[ε a, d a], [0, a]]` into `2 × 2` matrices from which the
derivation `d` extending `δ` is read off. -/
def freeDerivMatrix : FreeAlgebra R X →ₐ[R] Matrix (Fin 2) (Fin 2) (FreeAlgebra R X) :=
  FreeAlgebra.lift R fun x =>
    !![koszulSign (deg x) • FreeAlgebra.ι R x, δ x; 0, FreeAlgebra.ι R x]

@[simp]
theorem freeSignAut_ι (x : X) :
    freeSignAut deg (FreeAlgebra.ι R x) = koszulSign (deg x) • FreeAlgebra.ι R x :=
  FreeAlgebra.lift_ι_apply _ x

theorem freeDerivMatrix_apply (a : FreeAlgebra R X) :
    freeDerivMatrix deg δ a 1 0 = 0 ∧ freeDerivMatrix deg δ a 1 1 = a ∧
      freeDerivMatrix deg δ a 0 0 = freeSignAut deg a := by
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    rw [AlgHom.commutes, AlgHom.commutes]
    simp [Matrix.algebraMap_matrix_apply]
  | grade1 x => simp [freeDerivMatrix, freeSignAut]
  | mul a b ha hb =>
    simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_two, ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1,
      hb.2.2, zero_mul, mul_zero, add_zero, zero_add, true_and]
  | add a b ha hb =>
    simp only [map_add, Matrix.add_apply, ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1, hb.2.2, add_zero,
      true_and]

/-- The derivation of the free algebra extending `δ`: the unique `R`-linear map with
`d x = δ x` on generators satisfying the graded Leibniz rule. -/
def freeDeriv : FreeAlgebra R X →ₗ[R] FreeAlgebra R X where
  toFun a := freeDerivMatrix deg δ a 0 1
  map_add' a b := by simp [Matrix.add_apply]
  map_smul' r a := by simp [Matrix.smul_apply]

theorem freeDeriv_apply (a : FreeAlgebra R X) : freeDeriv deg δ a = freeDerivMatrix deg δ a 0 1 :=
  rfl

@[simp]
theorem freeDeriv_ι (x : X) : freeDeriv deg δ (FreeAlgebra.ι R x) = δ x := by
  simp [freeDeriv_apply, freeDerivMatrix]

@[simp]
theorem freeDeriv_algebraMap (r : R) :
    freeDeriv deg δ (algebraMap R (FreeAlgebra R X) r) = 0 := by
  rw [freeDeriv_apply, AlgHom.commutes]
  simp [Matrix.algebraMap_matrix_apply]

@[simp]
theorem freeDeriv_one : freeDeriv deg δ (1 : FreeAlgebra R X) = 0 := by
  simpa using freeDeriv_algebraMap deg δ (1 : R)

/-- The Leibniz rule in terms of the grading automorphism: `d (a * b) = d a * b + ε a * d b`. -/
theorem freeDeriv_mul (a b : FreeAlgebra R X) :
    freeDeriv deg δ (a * b) = freeDeriv deg δ a * b + freeSignAut deg a * freeDeriv deg δ b := by
  rw [freeDeriv_apply, map_mul, Matrix.mul_apply, Fin.sum_univ_two,
    (freeDerivMatrix_apply deg δ a).2.2, (freeDerivMatrix_apply deg δ b).2.1, add_comm]
  rfl

theorem freeDeriv_units_smul (u : ℤˣ) (a : FreeAlgebra R X) :
    freeDeriv deg δ (u • a) = u • freeDeriv deg δ a := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

variable {deg} in
theorem freeSignAut_of_mem {n : ℤ} {a : FreeAlgebra R X} (ha : a ∈ freeGrading R deg n) :
    freeSignAut deg a = koszulSign n • a := by
  induction ha using freeGrading.induction_on with
  | h_prod l hl =>
    subst hl
    induction l with
    | nil => simp
    | cons x l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [map_mul, ih, freeSignAut_ι, smul_mul_assoc, mul_smul_comm, smul_smul, koszulSign_add,
        mul_comm]
  | h_zero => rw [map_zero, smul_zero]
  | h_add a b _ _ ha hb => rw [map_add, ha, hb, smul_add]
  | h_smul r a _ ha =>
    rw [map_smul, ha, Units.smul_def, Units.smul_def, smul_comm r]

variable {deg} in
/-- The graded Leibniz rule: `d (a * b) = d a * b + (-1)^n a * d b` for `a` of degree `n`. -/
theorem freeDeriv_mul_of_mem {n : ℤ} {a : FreeAlgebra R X} (ha : a ∈ freeGrading R deg n)
    (b : FreeAlgebra R X) :
    freeDeriv deg δ (a * b) = freeDeriv deg δ a * b + koszulSign n • (a * freeDeriv deg δ b) := by
  rw [freeDeriv_mul, freeSignAut_of_mem ha, smul_mul_assoc]

variable {deg δ} in
/-- If `δ x` has degree `deg x + 1` for every generator, the derivation has degree `+1`. -/
theorem freeDeriv_mem (hδ : ∀ x, δ x ∈ freeGrading R deg (deg x + 1)) {n : ℤ}
    {a : FreeAlgebra R X} (ha : a ∈ freeGrading R deg n) :
    freeDeriv deg δ a ∈ freeGrading R deg (n + 1) := by
  induction ha using freeGrading.induction_on with
  | h_prod l hl =>
    subst hl
    induction l with
    | nil => simp
    | cons x l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [freeDeriv_mul_of_mem δ (ι_mem_freeGrading x), freeDeriv_ι]
      refine add_mem ?_ ?_
      · have := SetLike.GradedMul.mul_mem (hδ x) (prod_mem_freeGrading (R := R) (deg := deg) l)
        rwa [show deg x + 1 + (l.map deg).sum = deg x + (l.map deg).sum + 1 by ring] at this
      · have := SetLike.GradedMul.mul_mem (ι_mem_freeGrading (R := R) (deg := deg) x) ih
        rw [show deg x + ((l.map deg).sum + 1) = deg x + (l.map deg).sum + 1 by ring] at this
        rw [Units.smul_def]
        exact zsmul_mem this _
  | h_zero => rw [map_zero]; exact zero_mem _
  | h_add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | h_smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ r ha

variable {deg δ} in
/-- `d ∘ d` is an (ungraded) derivation: `d² (a * b) = d² a * b + a * d² b`. -/
theorem freeDeriv_freeDeriv_mul (hδ : ∀ x, δ x ∈ freeGrading R deg (deg x + 1))
    (a b : FreeAlgebra R X) :
    freeDeriv deg δ (freeDeriv deg δ (a * b)) =
      freeDeriv deg δ (freeDeriv deg δ a) * b + a * freeDeriv deg δ (freeDeriv deg δ b) := by
  induction a using DirectSum.Decomposition.inductionOn (freeGrading R deg) with
  | zero => simp
  | add a a' ha ha' =>
    rw [add_mul, map_add, map_add, ha, ha', map_add, map_add, add_mul, add_mul]
    abel
  | homogeneous a =>
    obtain ⟨a, ha⟩ := a
    rename_i n
    simp only
    rw [freeDeriv_mul_of_mem δ ha, map_add, freeDeriv_mul_of_mem δ (freeDeriv_mem hδ ha),
      freeDeriv_units_smul, freeDeriv_mul_of_mem δ ha, smul_add, smul_smul, Int.units_mul_self,
      one_smul, koszulSign_add, show koszulSign 1 = -1 from Int.negOnePow_one, mul_neg_one,
      Units.neg_smul]
    abel

variable {deg δ} in
/-- `d ∘ d = 0` if and only if `d (δ x) = 0` for every generator `x`. -/
theorem freeDeriv_freeDeriv_eq_zero_iff (hδ : ∀ x, δ x ∈ freeGrading R deg (deg x + 1)) :
    (∀ a, freeDeriv deg δ (freeDeriv deg δ a) = 0) ↔ ∀ x, freeDeriv deg δ (δ x) = 0 := by
  refine ⟨fun h x => by simpa using h (FreeAlgebra.ι R x), fun h a => ?_⟩
  induction a using FreeAlgebra.induction with
  | grade0 r => simp
  | grade1 x => rw [freeDeriv_ι, h]
  | mul a b ha hb => rw [freeDeriv_freeDeriv_mul hδ, ha, hb, zero_mul, mul_zero, add_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]

variable {deg δ} in
/-- Uniqueness of the derivation: an additive map satisfying the graded Leibniz rule, killing
the scalars and extending `δ` is `freeDeriv deg δ`. -/
theorem eq_freeDeriv_of_leibniz (D : FreeAlgebra R X →+ FreeAlgebra R X)
    (hD : ∀ {n : ℤ} {a : FreeAlgebra R X}, a ∈ freeGrading R deg n → ∀ b,
      D (a * b) = D a * b + koszulSign n • (a * D b))
    (hι : ∀ x, D (FreeAlgebra.ι R x) = δ x) (halg : ∀ r, D (algebraMap R _ r) = 0)
    (a : FreeAlgebra R X) : D a = freeDeriv deg δ a := by
  have hD' : ∀ a b, D (a * b) = D a * b + freeSignAut deg a * D b := by
    intro a b
    induction a using DirectSum.Decomposition.inductionOn (freeGrading R deg) with
    | zero => simp
    | add a a' ha ha' => rw [add_mul, map_add, ha, ha', map_add, map_add, add_mul, add_mul]; abel
    | homogeneous a =>
      obtain ⟨a, ha⟩ := a
      rw [hD ha, freeSignAut_of_mem ha, smul_mul_assoc]
  induction a using FreeAlgebra.induction with
  | grade0 r => rw [halg, freeDeriv_algebraMap]
  | grade1 x => rw [hι, freeDeriv_ι]
  | mul a b ha hb => rw [hD', ha, hb, freeDeriv_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

end Derivation

/-! ### Semi-free dg algebras -/

variable (R X) in
/-- The data of a free dg algebra on a graded set of generators `X`: the degrees of the
generators, and their differentials `δ x`, homogeneous of degree `deg x + 1`, such that the
derivation extending `δ` squares to zero on the generators (equivalently, everywhere). -/
structure SemiFreeData where
  /-- The degrees of the generators. -/
  deg : X → ℤ
  /-- The differential of the generators. -/
  δ : X → FreeAlgebra R X
  δ_mem : ∀ x, δ x ∈ freeGrading R deg (deg x + 1)
  freeDeriv_δ : ∀ x, freeDeriv deg δ (δ x) = 0

/-- The free (semi-free) dg algebra on a graded set of generators with prescribed differential:
the free algebra `FreeAlgebra R X`, graded by the degrees of the generators, with the
derivation extending the differential of the generators. -/
@[nolint unusedArguments]
def SemiFree (_S : SemiFreeData R X) : Type _ := FreeAlgebra R X

namespace SemiFree

variable (S : SemiFreeData R X)

instance instRing : Ring (SemiFree S) := inferInstanceAs (Ring (FreeAlgebra R X))

instance instAlgebra : Algebra R (SemiFree S) := inferInstanceAs (Algebra R (FreeAlgebra R X))

/-- The identification of `SemiFree S` with the free algebra. -/
def toFree : SemiFree S ≃ₐ[R] FreeAlgebra R X := AlgEquiv.refl

/-- A generator, as an element of `SemiFree S`. -/
def ι (x : X) : SemiFree S := FreeAlgebra.ι R x

theorem freeDeriv_freeDeriv (a : FreeAlgebra R X) :
    freeDeriv S.deg S.δ (freeDeriv S.deg S.δ a) = 0 :=
  (freeDeriv_freeDeriv_eq_zero_iff S.δ_mem).mpr S.freeDeriv_δ a

/-- The semi-free dg algebra as a dg abelian group. -/
instance instDGAddCommGroup : DGAddCommGroup (SemiFree S) where
  grading n := (freeGrading R S.deg n).toAddSubgroup
  decomposition := freeGrading.decompositionAddSubgroup
  d := (freeDeriv S.deg S.δ).toAddMonoidHom
  d_mem' ha := freeDeriv_mem S.δ_mem ha
  d_d' a := freeDeriv_freeDeriv S a

variable {S}

theorem mem_grading_iff {n : ℤ} {a : SemiFree S} :
    a ∈ grading n ↔ toFree S a ∈ freeGrading R S.deg n :=
  Iff.rfl

theorem d_apply (a : SemiFree S) : toFree S (d a) = freeDeriv S.deg S.δ (toFree S a) :=
  rfl

theorem ι_mem (x : X) : ι S x ∈ grading (S.deg x) :=
  ι_mem_freeGrading x

@[simp]
theorem d_ι (x : X) : d (ι S x) = (toFree S).symm (S.δ x) :=
  freeDeriv_ι S.deg S.δ x

variable (S)

/-- The semi-free dg algebra is a dg ring. -/
instance instDGRing : DGRing (SemiFree S) where
  one_mem := by
    change (1 : FreeAlgebra R X) ∈ freeGrading R S.deg 0
    exact SetLike.GradedOne.one_mem
  mul_mem i j a b ha hb := by
    change toFree S a * toFree S b ∈ freeGrading R S.deg (i + j)
    exact SetLike.GradedMul.mul_mem (A := freeGrading R S.deg) ha hb
  d_mul' ha b := freeDeriv_mul_of_mem S.δ ha b

/-- The semi-free dg algebra is a dg `R`-algebra. -/
instance instDGAlgebra : DGAlgebra R (SemiFree S) where
  algebraMap_mem' r := SetLike.algebraMap_mem_graded (freeGrading R S.deg) r
  d_algebraMap' r := freeDeriv_algebraMap S.deg S.δ r

/-! ### The universal property -/

variable {B : Type*} [Ring B] [Algebra R B] [DGAddCommGroup B] [DGRing B] [DGAlgebra R B]

/-- The maps on generators inducing morphisms of dg algebras out of `SemiFree S`: maps
`f : X → B` sending each generator to an element of the same degree, with
`d (f x) = f̃ (δ x)` for the algebra map `f̃` extending `f`. -/
def GeneratorMap (B : Type*) [Ring B] [Algebra R B] [DGAddCommGroup B] : Type _ :=
  {f : X → B // (∀ x, f x ∈ grading (S.deg x)) ∧ ∀ x, d (f x) = FreeAlgebra.lift R f (S.δ x)}

variable {S}

theorem lift_mem (f : X → B) (hf : ∀ x, f x ∈ grading (S.deg x)) {n : ℤ}
    {a : FreeAlgebra R X} (ha : a ∈ freeGrading R S.deg n) :
    FreeAlgebra.lift R f a ∈ grading n := by
  induction ha using freeGrading.induction_on with
  | h_prod l hl =>
    subst hl
    induction l with
    | nil => simpa using one_mem_grading (A := B)
    | cons x l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [map_mul, FreeAlgebra.lift_ι_apply]
      exact mul_mem_grading (hf x) ih
  | h_zero => rw [map_zero]; exact zero_mem _
  | h_add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | h_smul r a _ ha => rw [map_smul]; exact DGAlgebra.smul_mem r ha

theorem lift_freeDeriv (f : GeneratorMap S B) (a : FreeAlgebra R X) :
    FreeAlgebra.lift R f.1 (freeDeriv S.deg S.δ a) = d (FreeAlgebra.lift R f.1 a) := by
  induction a using DirectSum.Decomposition.inductionOn (freeGrading R S.deg) with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, d_add]
  | homogeneous a =>
    obtain ⟨a, ha⟩ := a
    show FreeAlgebra.lift R f.1 (freeDeriv S.deg S.δ a) = d (FreeAlgebra.lift R f.1 a)
    induction ha using freeGrading.induction_on with
    | h_prod l hl =>
      clear hl
      induction l with
      | nil => simp
      | cons x l ih =>
        rw [List.map_cons, List.prod_cons, freeDeriv_mul_of_mem S.δ (ι_mem_freeGrading x),
          map_add, map_mul, map_mul, Units.smul_def, map_zsmul, map_mul, ih, freeDeriv_ι,
          FreeAlgebra.lift_ι_apply, ← f.2.2 x, d_mul (f.2.1 x), Units.smul_def]
    | h_zero => simp
    | h_add a b _ _ ha hb => rw [map_add, map_add, ha, hb, map_add, d_add]
    | h_smul r a _ ha => rw [map_smul, map_smul, ha, map_smul, d_smul_algebra]

variable (S B)

/-- The universal property of the semi-free dg algebra: morphisms of dg `R`-algebras
`SemiFree S → B` are the maps on generators preserving degrees and compatible with the
differentials. -/
noncomputable def liftEquiv : GeneratorMap S B ≃ (SemiFree S →ᵈᵍₐ[R] B) where
  toFun f :=
    { toAlgHom := FreeAlgebra.lift R f.1
      map_mem' := fun ha => lift_mem f.1 f.2.1 ha
      map_d' := fun a => lift_freeDeriv f a }
  invFun G := ⟨fun x => G (ι S x), fun x => G.map_mem (ι_mem x), fun x => by
    rw [← G.map_d, d_ι]
    have : FreeAlgebra.lift R (fun x => G (ι S x)) = G.toAlgHom :=
      FreeAlgebra.lift_comp_ι G.toAlgHom
    rw [this]
    rfl⟩
  left_inv f := Subtype.ext (funext fun x => FreeAlgebra.lift_ι_apply f.1 x)
  right_inv G := DGAlgHom.ext fun a => by
    change FreeAlgebra.lift R (fun x => G (ι S x)) a = G a
    rw [show FreeAlgebra.lift R (fun x => G (ι S x)) = G.toAlgHom from
      FreeAlgebra.lift_comp_ι G.toAlgHom]
    rfl

variable {S B}

@[simp]
theorem liftEquiv_apply_ι (f : GeneratorMap S B) (x : X) : liftEquiv S B f (ι S x) = f.1 x :=
  FreeAlgebra.lift_ι_apply f.1 x

/-- Two morphisms of dg algebras out of `SemiFree S` agreeing on the generators are equal. -/
theorem hom_ext {G G' : SemiFree S →ᵈᵍₐ[R] B} (h : ∀ x, G (ι S x) = G' (ι S x)) : G = G' :=
  (liftEquiv S B).symm.injective (Subtype.ext (funext h))

end SemiFree

end DG
