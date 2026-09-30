import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.CategoryTheory.Monoidal.Mon
import DG.Monoidal.Complex
import DG.Monoidal.ComplexSum

/-!
# The dg algebra of a monoid object in cochain complexes

Let `M` be a monoid object in the monoidal category `CochainComplex (ModuleCat R) ℤ`, with
multiplication `μ : M ⊗ M ⟶ M` and unit `η : 𝟙_ ⟶ M`. The components `Mⁿ` form a graded
`R`-algebra (`DirectSum.GRing`, `DirectSum.GAlgebra`) with product
`Mⁱ × Mʲ → Mⁱ⁺ʲ, (x, y) ↦ μ (x ⊗ y)` and unit `η 1 ∈ M⁰`, so that `DG.ComplexSum M.X = ⨁ n, Mⁿ`
is an `R`-algebra. Together with its dg abelian group structure (`DG.ComplexSum`), it is a dg
`R`-algebra: the Leibniz rule is the statement that `μ` is a morphism of complexes, for the
differential `d (x ⊗ y) = d x ⊗ y + (-1)^|x| x ⊗ d y` of the tensor product
(`DG.ComplexTensor.d_tmul`).

## Main definitions

* `DG.MonObj.gRing M`, `DG.MonObj.gAlgebra M`: the graded `R`-algebra structure on the
  components of `M`;
* the instances `Ring (ComplexSum M.X)`, `Algebra R (ComplexSum M.X)`, `DGRing (ComplexSum M.X)`,
  `DGAlgebra R (ComplexSum M.X)`;
* `DG.MonObj.one_mul_apply`, `DG.MonObj.mul_one_apply`, `DG.MonObj.mul_assoc_apply`: the
  axioms of a monoid object, evaluated on elements.
-/

open CategoryTheory MonoidalCategory HomologicalComplex DirectSum
open scoped CategoryTheory.MonObj

universe u

noncomputable section

namespace DG

/-! ### From monoid objects to dg algebras -/

namespace ComplexTensor

variable {R : Type u} [CommRing R] {K L N : CochainComplex (ModuleCat.{u} R) ℤ}

/-- The value of a morphism out of a tensor product on `x ⊗ y`, as an element of the graded
monoid `Σ n, Nⁿ`, does not depend on the choice of the degree `n = p + q`. -/
theorem mk_f_tmul (φ : K ⊗ L ⟶ N) {p q n n' : ℤ} (h : p + q = n) (h' : p + q = n')
    (x : K.X p) (y : L.X q) :
    GradedMonoid.mk (A := fun n => N.X n) n (φ.f n (tmul K L h x y)) =
      GradedMonoid.mk n' (φ.f n' (tmul K L h' x y)) := by
  subst h h'
  rfl

/-- The value of a morphism out of a tensor product on `x ⊗ y`, as an element of
`ComplexSum N`, does not depend on the choice of the degree `n = p + q`. -/
theorem of_f_tmul (φ : K ⊗ L ⟶ N) {p q n n' : ℤ} (h : p + q = n) (h' : p + q = n')
    (x : K.X p) (y : L.X q) :
    ComplexSum.of N n (φ.f n (tmul K L h x y)) = ComplexSum.of N n' (φ.f n' (tmul K L h' x y)) := by
  subst h h'
  rfl

end ComplexTensor

namespace MonObj

variable {R : Type u} [CommRing R] (M : Mon (CochainComplex (ModuleCat.{u} R) ℤ))

open ComplexTensor

/-- The unit `1 ∈ M⁰` of a monoid object `M` in cochain complexes. -/
def one : M.X.X 0 := (η[M.X]).f 0 (unitOne R)

/-- The multiplication `Mⁱ × Mʲ → Mⁱ⁺ʲ` of a monoid object `M` in cochain complexes. -/
def mul {i j : ℤ} (x : M.X.X i) (y : M.X.X j) : M.X.X (i + j) :=
  (μ[M.X]).f (i + j) (tmul M.X M.X rfl x y)

/-- The left unit axiom of a monoid object on elements: `μ (1 ⊗ x) = x`. -/
theorem one_mul_apply {n : ℤ} (x : M.X.X n) :
    (μ[M.X]).f n (tmul M.X M.X (zero_add n) (one M) x) = x := by
  have := congrArg (fun φ => φ.f n (tmul _ M.X (zero_add n) (unitOne R) x))
    (CategoryTheory.MonObj.one_mul M.X)
  simp only [comp_f, ModuleCat.comp_apply, whiskerRight_f_tmul, leftUnitor_hom_f_tmul] at this
  exact this

/-- The right unit axiom of a monoid object on elements: `μ (x ⊗ 1) = x`. -/
theorem mul_one_apply {n : ℤ} (x : M.X.X n) :
    (μ[M.X]).f n (tmul M.X M.X (add_zero n) x (one M)) = x := by
  have := congrArg (fun φ => φ.f n (tmul M.X _ (add_zero n) x (unitOne R)))
    (CategoryTheory.MonObj.mul_one M.X)
  simp only [comp_f, ModuleCat.comp_apply, whiskerLeft_f_tmul, rightUnitor_hom_f_tmul] at this
  exact this

/-- The associativity axiom of a monoid object on elements:
`μ (μ (x ⊗ y) ⊗ z) = μ (x ⊗ μ (y ⊗ z))`. -/
theorem mul_assoc_apply {p q r n : ℤ} (h : p + q + r = n) (x : M.X.X p) (y : M.X.X q)
    (z : M.X.X r) :
    (μ[M.X]).f n (tmul M.X M.X h ((μ[M.X]).f (p + q) (tmul M.X M.X rfl x y)) z) =
      (μ[M.X]).f n (tmul M.X M.X (show p + (q + r) = n by omega) x
        ((μ[M.X]).f (q + r) (tmul M.X M.X rfl y z))) := by
  have := congrArg (fun φ => φ.f n (tmul _ M.X h (tmul M.X M.X rfl x y) z))
    (CategoryTheory.MonObj.mul_assoc M.X)
  simpa only [comp_f, ModuleCat.comp_apply, whiskerRight_f_tmul, whiskerLeft_f_tmul,
    associator_hom_f_tmul] using this

/-- The unit `1 ∈ M⁰`. -/
instance gOne : GradedMonoid.GOne (fun n : ℤ => (M.X.X n : Type u)) := ⟨one M⟩

/-- The product `Mⁱ × Mʲ → Mⁱ⁺ʲ`. -/
instance gMul : GradedMonoid.GMul (fun n : ℤ => (M.X.X n : Type u)) := ⟨mul M⟩

/-- The graded ring structure on the components of a monoid object in cochain complexes. -/
instance gRing : DirectSum.GRing (fun n : ℤ => (M.X.X n : Type u)) where
  mul x y := mul M x y
  one := one M
  one_mul := by
    rintro ⟨i, x⟩
    exact (mk_f_tmul μ[M.X] rfl (zero_add i) _ _).trans (congrArg _ (one_mul_apply M x))
  mul_one := by
    rintro ⟨i, x⟩
    exact (mk_f_tmul μ[M.X] rfl (add_zero i) _ _).trans (congrArg _ (mul_one_apply M x))
  mul_assoc := by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩
    exact (mk_f_tmul μ[M.X] rfl rfl _ _).trans ((congrArg _ (mul_assoc_apply M rfl x y z)).trans
      (mk_f_tmul μ[M.X] _ rfl _ _))
  mul_zero x := by simp [mul]
  zero_mul x := by simp [mul]
  mul_add x y y' := by simp [mul]
  add_mul x x' y := by simp [mul]
  natCast n := n • one M
  natCast_zero := zero_smul ℕ _
  natCast_succ n := succ_nsmul (one M) n
  intCast n := n • one M
  intCast_ofNat n := natCast_zsmul (one M) n
  intCast_negSucc_ofNat n := negSucc_zsmul (one M) n

theorem mk_smul_one_mul (r : R) {i : ℤ} (x : M.X.X i) :
    GradedMonoid.mk (A := fun n => M.X.X n) (0 + i) (mul M (r • one M) x) =
      GradedMonoid.mk i (r • x) :=
  (mk_f_tmul μ[M.X] rfl (zero_add i) _ _).trans (by
    rw [tmul_smul_left, map_smul, one_mul_apply])

theorem mk_mul_smul_one (r : R) {i : ℤ} (x : M.X.X i) :
    GradedMonoid.mk (A := fun n => M.X.X n) (i + 0) (mul M x (r • one M)) =
      GradedMonoid.mk i (r • x) :=
  (mk_f_tmul μ[M.X] rfl (add_zero i) _ _).trans (by
    rw [tmul_smul_right, map_smul, mul_one_apply])

/-- The `R`-algebra structure on the graded ring of components of a monoid object: `R` maps to
`M⁰` by `r ↦ r • 1`. -/
instance gAlgebra : DirectSum.GAlgebra R (fun n : ℤ => (M.X.X n : Type u)) where
  toFun := (LinearMap.toSpanSingleton R _ (one M)).toAddMonoidHom
  map_one := one_smul R (one M)
  map_mul r s := by
    refine Eq.trans ?_ (mk_smul_one_mul M r (s • one M)).symm
    exact congrArg (GradedMonoid.mk 0) (mul_smul r s (one M))
  commutes r := by
    rintro ⟨i, x⟩
    exact (mk_smul_one_mul M r x).trans (mk_mul_smul_one M r x).symm
  smul_def r := by
    rintro ⟨i, x⟩
    exact (mk_smul_one_mul M r x).symm

/-- The ring `⨁ n, Mⁿ` of a monoid object `M`. -/
instance : Ring (ComplexSum M.X) :=
  inferInstanceAs (Ring (⨁ n, M.X.X n))

/-- The `R`-algebra `⨁ n, Mⁿ` of a monoid object `M`. -/
instance : Algebra R (ComplexSum M.X) :=
  inferInstanceAs (Algebra R (⨁ n, M.X.X n))

/-- The product of `⨁ n, Mⁿ` on summands. -/
theorem of_mul_of {i j : ℤ} (x : M.X.X i) (y : M.X.X j) :
    ComplexSum.of M.X i x * ComplexSum.of M.X j y =
      ComplexSum.of M.X (i + j) ((μ[M.X]).f (i + j) (tmul M.X M.X rfl x y)) :=
  DirectSum.of_mul_of (A := fun n => M.X.X n) x y

theorem one_def : (1 : ComplexSum M.X) = ComplexSum.of M.X 0 (one M) :=
  rfl

theorem algebraMap_apply (r : R) :
    algebraMap R (ComplexSum M.X) r = ComplexSum.of M.X 0 (r • one M) :=
  rfl

/-- The Leibniz rule for `⨁ n, Mⁿ` on summands. -/
theorem d_of_mul_of {n j : ℤ} (x : M.X.X n) (y : M.X.X j) :
    d (ComplexSum.of M.X n x * ComplexSum.of M.X j y) =
      d (ComplexSum.of M.X n x) * ComplexSum.of M.X j y +
        koszulSign n • (ComplexSum.of M.X n x * d (ComplexSum.of M.X j y)) := by
  rw [of_mul_of, ComplexSum.d_of, ComplexSum.d_of, ComplexSum.d_of, of_mul_of, of_mul_of,
    ← Hom.comm_apply, d_tmul, map_add, map_add, Units.smul_def, Units.smul_def, map_zsmul,
    map_zsmul, of_f_tmul μ[M.X] _ (rfl : n + 1 + j = _), of_f_tmul μ[M.X] _ (rfl : n + (j + 1) = _)]

theorem d_of_mul_add {n : ℤ} (x : M.X.X n) (b b' : ComplexSum M.X)
    (hb : d (ComplexSum.of M.X n x * b) =
      d (ComplexSum.of M.X n x) * b + koszulSign n • (ComplexSum.of M.X n x * d b))
    (hb' : d (ComplexSum.of M.X n x * b') =
      d (ComplexSum.of M.X n x) * b' + koszulSign n • (ComplexSum.of M.X n x * d b')) :
    d (ComplexSum.of M.X n x * (b + b')) =
      d (ComplexSum.of M.X n x) * (b + b') +
        koszulSign n • (ComplexSum.of M.X n x * d (b + b')) := by
  rw [mul_add, d_add, hb, hb', d_add, mul_add (d _) b b',
    mul_add (ComplexSum.of M.X n x) (d b) (d b'), smul_add, add_add_add_comm]

/-- `⨁ n, Mⁿ` is a dg ring; the Leibniz rule is the statement that the multiplication of `M`
is a morphism of complexes. -/
instance : DGRing (ComplexSum M.X) where
  one_mem := ComplexSum.of_mem_grading 0 (one M)
  mul_mem := by
    rintro i j _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨_, (of_mul_of M x y).symm⟩
  d_mul' := by
    intro n a ha b
    obtain ⟨x, rfl⟩ := ComplexSum.mem_grading_iff.mp ha
    induction b using ComplexSum.induction_on with
    | zero => simp
    | of j y => exact d_of_mul_of M x y
    | add b b' hb hb' => exact d_of_mul_add M x b b' hb hb'

/-- `⨁ n, Mⁿ` is a dg `R`-algebra. -/
instance : DGAlgebra R (ComplexSum M.X) where
  algebraMap_mem' r := ComplexSum.of_mem_grading 0 (r • one M)
  d_algebraMap' r := by
    have h : (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)).d 0 (0 + 1) = 0 := rfl
    rw [algebraMap_apply, ComplexSum.d_of, map_smul, one, ← Hom.comm_apply, h]
    simp

end MonObj

end DG

end
