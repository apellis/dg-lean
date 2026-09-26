import Mathlib.LinearAlgebra.TensorProduct.Graded.External
import Mathlib.RingTheory.GradedAlgebra.Basic
import DG.Graded.Commutative

/-!
# The graded opposite algebra

For a `ℤ`-graded `R`-algebra `A` with grading `𝒜 : ℤ → Submodule R A`, the graded opposite
algebra `DG.GradedOpposite 𝒜` is `A` with the same addition and `R`-action and with the signed
opposite product: for homogeneous `a ∈ 𝒜 i` and `b ∈ 𝒜 j`,

  `op a * op b = koszulSign (i * j) • op (b * a)`,

extended bilinearly to all elements. It carries the same grading (`GradedOpposite.grading 𝒜`,
whose degree-`i` piece is the image of `𝒜 i` under `op`), for which it is again a graded algebra.

## Main definitions and results

* `DG.GradedOpposite 𝒜`: the type synonym, with `Ring`, `Algebra R` and `GradedAlgebra`
  instances.
* `DG.GradedOpposite.op`, `DG.GradedOpposite.unop`: the `R`-linear equivalences with `A`.
* `DG.GradedOpposite.op_mul_op`: the product formula on homogeneous elements.
* `DG.GradedOpposite.opOpAlgEquiv`: the graded algebra isomorphism `(𝒜ᵒᵖ)ᵒᵖ ≃ₐ[R] A`, which
  preserves degrees (`DG.GradedOpposite.opOpAlgEquiv_mem_iff`).
* `DG.isGradedComm_iff_op_mul`: `𝒜` is graded commutative iff `op` is multiplicative, and
  `DG.GradedOpposite.opAlgEquiv`: for graded commutative `𝒜`, `op` as an algebra isomorphism.

## Implementation notes

`GradedOpposite 𝒜` is a type synonym of `A` rather than of `Aᵐᵒᵖ`: the identity of `A` is then
the linear equivalence `op`, the grading is (the image under `op` of) the same family of
submodules, and the sign twist lives entirely in the multiplication. (The alternative, `Aᵐᵒᵖ`
with the product twisted by the signs `(-1)^(i * (i - 1) / 2)`, hides the Koszul sign inside
`op` instead, which makes every homogeneous formula carry that twist.)

The product on general elements is defined through the decomposition into homogeneous
components, following the construction of `GradedTensorProduct` in Mathlib: on the external
direct sum `⨁ i, 𝒜 i` the signed opposite product is `mul' ∘ gradedComm`, where
`TensorProduct.gradedComm` is Mathlib's Koszul-signed braiding, and this bilinear map is
transported to `A` along `DirectSum.decomposeLinearEquiv 𝒜` (`GradedOpposite.mulHom`, a
bilinear map on `A`). The `Ring` instance on the synonym is then a single structure, so that
every algebraic instance on `GradedOpposite 𝒜` is a projection of one term; this keeps the
iterated opposite `GradedOpposite (grading 𝒜)` cheap to work with.
-/

suppress_compilation

open DirectSum TensorProduct

namespace DG

/-- Additive maps commute with the Koszul sign action. -/
theorem map_koszulSign_smul {F M N : Type*} [AddCommGroup M] [AddCommGroup N] [FunLike F M N]
    [AddMonoidHomClass F M N] (f : F) (n : ℤ) (x : M) :
    f (koszulSign n • x) = koszulSign n • f x := by
  rw [Units.smul_def, map_zsmul, Units.smul_def]

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]

namespace GradedOpposite

/-! ### The signed opposite product on the external direct sum -/

/-- Auxiliary construction: the signed opposite product on the external direct sum
`⨁ i, 𝒜 i`, sending `lof i a ⊗ lof j b` to `koszulSign (i * j) • (lof j b * lof i a)`. -/
def mulAux : (⨁ i, 𝒜 i) →ₗ[R] (⨁ i, 𝒜 i) →ₗ[R] (⨁ i, 𝒜 i) :=
  TensorProduct.curry
    (LinearMap.mul' R (⨁ i, 𝒜 i) ∘ₗ (gradedComm R (𝒜 ·) (𝒜 ·)).toLinearMap)

theorem mulAux_lof_lof (i j : ℤ) (a : 𝒜 i) (b : 𝒜 j) :
    mulAux 𝒜 (lof R ℤ (𝒜 ·) i a) (lof R ℤ (𝒜 ·) j b) =
      koszulSign (i * j) • (lof R ℤ (𝒜 ·) j b * lof R ℤ (𝒜 ·) i a) := by
  rw [mulAux, curry_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, gradedComm_of_tmul_of,
    mul_comm j i, Units.smul_def, map_zsmul, LinearMap.mul'_apply]
  rfl

theorem mulAux_of_of (i j : ℤ) (a : 𝒜 i) (b : 𝒜 j) :
    mulAux 𝒜 (of (𝒜 ·) i a) (of (𝒜 ·) j b) =
      koszulSign (i * j) • (of (𝒜 ·) j b * of (𝒜 ·) i a) :=
  mulAux_lof_lof 𝒜 i j a b

theorem mulAux_smul_left (s : ℤ) (x y : ⨁ i, 𝒜 i) :
    mulAux 𝒜 (koszulSign s • x) y = koszulSign s • mulAux 𝒜 x y := by
  rw [Units.smul_def, map_zsmul, LinearMap.smul_apply, Units.smul_def]

theorem mulAux_smul_right (s : ℤ) (x y : ⨁ i, 𝒜 i) :
    mulAux 𝒜 x (koszulSign s • y) = koszulSign s • mulAux 𝒜 x y := by
  rw [Units.smul_def, map_zsmul, Units.smul_def]

theorem mulAux_one (x : ⨁ i, 𝒜 i) : mulAux 𝒜 x 1 = x := by
  suffices (mulAux 𝒜).flip 1 = LinearMap.id from DFunLike.congr_fun this x
  refine DirectSum.linearMap_ext _ fun i => LinearMap.ext fun a => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply, LinearMap.id_coe,
    id_eq]
  rw [DirectSum.one_def, lof_eq_of, mulAux_of_of, mul_zero, koszulSign_zero, one_smul,
    ← DirectSum.one_def, one_mul]

theorem one_mulAux (x : ⨁ i, 𝒜 i) : mulAux 𝒜 1 x = x := by
  suffices mulAux 𝒜 1 = LinearMap.id from DFunLike.congr_fun this x
  refine DirectSum.linearMap_ext _ fun i => LinearMap.ext fun a => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
  rw [DirectSum.one_def, lof_eq_of, mulAux_of_of, zero_mul, koszulSign_zero, one_smul,
    ← DirectSum.one_def, mul_one]

theorem mulAux_assoc (x y z : ⨁ i, 𝒜 i) :
    mulAux 𝒜 (mulAux 𝒜 x y) z = mulAux 𝒜 x (mulAux 𝒜 y z) := by
  let m := mulAux 𝒜
  suffices LinearMap.llcomp R _ _ _ m ∘ₗ m =
      (LinearMap.llcomp R _ _ _ LinearMap.lflip <| LinearMap.llcomp R _ _ _ m.flip ∘ₗ m).flip by
    exact DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun this x) y) z
  ext i a j b k c : 6
  simp only [m, LinearMap.coe_comp, Function.comp_apply, LinearMap.llcomp_apply,
    LinearMap.flip_apply, LinearMap.lflip_apply, lof_eq_of, mulAux_of_of, mulAux_smul_left,
    mulAux_smul_right, DirectSum.of_mul_of]
  simp only [← DirectSum.of_mul_of, smul_smul, ← koszulSign_add, mul_assoc]
  rw [show i * j + (j + i) * k = j * k + i * (k + j) by ring]

/-! ### The signed opposite product on `A` -/

/-- The signed opposite product, as a bilinear map on `A`: the product `mulAux` transported
along the decomposition `A ≃ₗ[R] ⨁ i, 𝒜 i`. This is the multiplication of
`GradedOpposite 𝒜`. -/
def mulHom : A →ₗ[R] A →ₗ[R] A :=
  ((mulAux 𝒜).compl₁₂ (decomposeLinearEquiv 𝒜 : A →ₗ[R] ⨁ i, 𝒜 i)
    (decomposeLinearEquiv 𝒜 : A →ₗ[R] ⨁ i, 𝒜 i)).compr₂
    ((decomposeLinearEquiv 𝒜).symm : (⨁ i, 𝒜 i) →ₗ[R] A)

theorem mulHom_apply (a b : A) :
    mulHom 𝒜 a b = (decompose 𝒜).symm (mulAux 𝒜 (decompose 𝒜 a) (decompose 𝒜 b)) := rfl

theorem decompose_mulHom (a b : A) :
    decompose 𝒜 (mulHom 𝒜 a b) = mulAux 𝒜 (decompose 𝒜 a) (decompose 𝒜 b) := by
  rw [mulHom_apply, Equiv.apply_symm_apply]

theorem mulHom_one (a : A) : mulHom 𝒜 a 1 = a := by
  rw [mulHom_apply, decompose_one, mulAux_one, Equiv.symm_apply_apply]

theorem one_mulHom (a : A) : mulHom 𝒜 1 a = a := by
  rw [mulHom_apply, decompose_one, one_mulAux, Equiv.symm_apply_apply]

theorem mulHom_assoc (a b c : A) :
    mulHom 𝒜 (mulHom 𝒜 a b) c = mulHom 𝒜 a (mulHom 𝒜 b c) := by
  simp only [mulHom_apply, Equiv.apply_symm_apply]
  rw [mulAux_assoc]

/-- The signed opposite product of two homogeneous elements. -/
theorem mulHom_of_mem {i j : ℤ} {a b : A} (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 j) :
    mulHom 𝒜 a b = koszulSign (i * j) • (b * a) := by
  rw [mulHom_apply, decompose_of_mem 𝒜 ha, decompose_of_mem 𝒜 hb, mulAux_of_of, Units.smul_def,
    ← decomposeLinearEquiv_symm_apply, map_zsmul, decomposeLinearEquiv_symm_apply,
    decompose_symm_mul, decompose_symm_of, decompose_symm_of, Units.smul_def]

end GradedOpposite

/-- The graded opposite algebra of a `ℤ`-graded algebra: a type synonym of `A` with the product
`op a * op b = koszulSign (i * j) • op (b * a)` on homogeneous elements of degrees `i` and `j`. -/
@[nolint unusedArguments]
def GradedOpposite (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] : Type _ := A

namespace GradedOpposite

instance instRing : Ring (GradedOpposite 𝒜) where
  __ := inferInstanceAs (AddCommGroupWithOne A)
  mul x y := mulHom 𝒜 x y
  mul_assoc := mulHom_assoc 𝒜
  one_mul := one_mulHom 𝒜
  mul_one := mulHom_one 𝒜
  left_distrib x y z := LinearMap.map_add (mulHom 𝒜 x) y z
  right_distrib x y z := LinearMap.map_add₂ (mulHom 𝒜) x y z
  zero_mul x := LinearMap.map_zero₂ (mulHom 𝒜) x
  mul_zero x := LinearMap.map_zero (mulHom 𝒜 x)

/-- The `R`-algebra structure of `GradedOpposite 𝒜`. The `R`-module structure is that of `A`;
it is only available through this instance (as `Algebra.toModule`), so that there is a single
`Module R (GradedOpposite 𝒜)` instance. -/
instance instAlgebra : Algebra R (GradedOpposite 𝒜) :=
  @Algebra.ofModule R (GradedOpposite 𝒜) _ _ (inferInstanceAs (Module R A))
    (fun r x y => LinearMap.map_smul₂ (mulHom 𝒜) r x y)
    (fun r x y => LinearMap.map_smul (mulHom 𝒜 x) r y)

/-- The canonical `R`-linear equivalence `A ≃ₗ[R] GradedOpposite 𝒜`. -/
def op : A ≃ₗ[R] GradedOpposite 𝒜 := LinearEquiv.refl R A

/-- The canonical `R`-linear equivalence `GradedOpposite 𝒜 ≃ₗ[R] A`. -/
def unop : GradedOpposite 𝒜 ≃ₗ[R] A := LinearEquiv.refl R A

@[simp] theorem op_symm : (op 𝒜).symm = unop 𝒜 := rfl
@[simp] theorem unop_symm : (unop 𝒜).symm = op 𝒜 := rfl
@[simp] theorem unop_op (a : A) : unop 𝒜 (op 𝒜 a) = a := rfl
@[simp] theorem op_unop (x : GradedOpposite 𝒜) : op 𝒜 (unop 𝒜 x) = x := rfl
@[simp] theorem op_one : op 𝒜 (1 : A) = 1 := rfl
@[simp] theorem unop_one : unop 𝒜 (1 : GradedOpposite 𝒜) = 1 := rfl

theorem op_injective : Function.Injective (op 𝒜) := (op 𝒜).injective
theorem unop_injective : Function.Injective (unop 𝒜) := (unop 𝒜).injective

/-- Two linear maps out of `GradedOpposite 𝒜` agree if they agree after composing with `op`. -/
@[ext]
theorem hom_ext {M : Type*} [AddCommMonoid M] [Module R M] ⦃f g : GradedOpposite 𝒜 →ₗ[R] M⦄
    (h : f ∘ₗ (op 𝒜).toLinearMap = g ∘ₗ (op 𝒜).toLinearMap) : f = g :=
  h

theorem mul_def (x y : GradedOpposite 𝒜) : x * y = op 𝒜 (mulHom 𝒜 (unop 𝒜 x) (unop 𝒜 y)) := rfl

theorem unop_mul' (x y : GradedOpposite 𝒜) : unop 𝒜 (x * y) = mulHom 𝒜 (unop 𝒜 x) (unop 𝒜 y) :=
  rfl

theorem op_mul' (a b : A) : op 𝒜 a * op 𝒜 b = op 𝒜 (mulHom 𝒜 a b) := rfl

theorem algebraMap_def (r : R) :
    algebraMap R (GradedOpposite 𝒜) r = op 𝒜 (algebraMap R A r) := by
  change r • (1 : GradedOpposite 𝒜) = op 𝒜 (algebraMap R A r)
  rw [Algebra.algebraMap_eq_smul_one, map_smul, op_one]

@[simp] theorem op_algebraMap (r : R) :
    op 𝒜 (algebraMap R A r) = algebraMap R (GradedOpposite 𝒜) r := (algebraMap_def 𝒜 r).symm

@[simp] theorem unop_algebraMap (r : R) :
    unop 𝒜 (algebraMap R (GradedOpposite 𝒜) r) = algebraMap R A r := by
  rw [algebraMap_def, unop_op]

/-- The product of two homogeneous elements of the graded opposite algebra. -/
theorem op_mul_op {i j : ℤ} {a b : A} (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 j) :
    op 𝒜 a * op 𝒜 b = koszulSign (i * j) • op 𝒜 (b * a) := by
  rw [op_mul', mulHom_of_mem 𝒜 ha hb, Units.smul_def, map_zsmul, Units.smul_def]

/-! ### The grading -/

/-- The grading of the graded opposite algebra: the degree-`i` piece is the image of `𝒜 i`
under `op`. -/
def grading (i : ℤ) : Submodule R (GradedOpposite 𝒜) :=
  (𝒜 i).map (op 𝒜 : A →ₗ[R] GradedOpposite 𝒜)

theorem mem_grading_iff {i : ℤ} {x : GradedOpposite 𝒜} : x ∈ grading 𝒜 i ↔ unop 𝒜 x ∈ 𝒜 i :=
  Submodule.mem_map_equiv (𝒜 i)

theorem op_mem_grading_iff {i : ℤ} {a : A} : op 𝒜 a ∈ grading 𝒜 i ↔ a ∈ 𝒜 i :=
  mem_grading_iff 𝒜

theorem op_mem_grading {i : ℤ} {a : A} (ha : a ∈ 𝒜 i) : op 𝒜 a ∈ grading 𝒜 i :=
  (op_mem_grading_iff 𝒜).mpr ha

/-- The product of two homogeneous elements of the graded opposite algebra, in terms of
`unop`. -/
theorem unop_mul {i j : ℤ} {x y : GradedOpposite 𝒜} (hx : x ∈ grading 𝒜 i)
    (hy : y ∈ grading 𝒜 j) :
    unop 𝒜 (x * y) = koszulSign (i * j) • (unop 𝒜 y * unop 𝒜 x) := by
  rw [unop_mul', mulHom_of_mem 𝒜 ((mem_grading_iff 𝒜).mp hx) ((mem_grading_iff 𝒜).mp hy)]

instance instGradedMonoid : SetLike.GradedMonoid (grading 𝒜) where
  one_mem := op_mem_grading 𝒜 (SetLike.one_mem_graded 𝒜)
  mul_mem {i j} x y hx hy := by
    rw [mem_grading_iff, unop_mul 𝒜 hx hy, Units.smul_def, add_comm]
    exact zsmul_mem
      (SetLike.mul_mem_graded ((mem_grading_iff 𝒜).mp hy) ((mem_grading_iff 𝒜).mp hx)) _

/-- The degree-`i` piece of the opposite grading is `𝒜 i`, via `op`. -/
def gradingEquiv (i : ℤ) : 𝒜 i ≃ₗ[R] grading 𝒜 i := (op 𝒜).submoduleMap (𝒜 i)

@[simp] theorem coe_gradingEquiv {i : ℤ} (a : 𝒜 i) :
    (gradingEquiv 𝒜 i a : GradedOpposite 𝒜) = op 𝒜 a := rfl

@[simp] theorem coe_gradingEquiv_symm {i : ℤ} (x : grading 𝒜 i) :
    ((gradingEquiv 𝒜 i).symm x : A) = unop 𝒜 x := rfl

/-- The direct sum of the `gradingEquiv 𝒜 i`. -/
def toGrading : (⨁ i, 𝒜 i) →ₗ[R] ⨁ i, grading 𝒜 i :=
  DirectSum.toModule R ℤ _ fun i => lof R ℤ (grading 𝒜 ·) i ∘ₗ (gradingEquiv 𝒜 i).toLinearMap

/-- The direct sum of the `(gradingEquiv 𝒜 i).symm`. -/
def ofGrading : (⨁ i, grading 𝒜 i) →ₗ[R] ⨁ i, 𝒜 i :=
  DirectSum.toModule R ℤ _ fun i => lof R ℤ (𝒜 ·) i ∘ₗ (gradingEquiv 𝒜 i).symm.toLinearMap

@[simp] theorem toGrading_lof (i : ℤ) (a : 𝒜 i) :
    toGrading 𝒜 (lof R ℤ (𝒜 ·) i a) = lof R ℤ (grading 𝒜 ·) i (gradingEquiv 𝒜 i a) := by
  unfold toGrading; rw [DirectSum.toModule_lof]; rfl

@[simp] theorem ofGrading_lof (i : ℤ) (x : grading 𝒜 i) :
    ofGrading 𝒜 (lof R ℤ (grading 𝒜 ·) i x) = lof R ℤ (𝒜 ·) i ((gradingEquiv 𝒜 i).symm x) := by
  unfold ofGrading; rw [DirectSum.toModule_lof]; rfl

theorem coeLinearMap_comp_toGrading :
    coeLinearMap (grading 𝒜) ∘ₗ toGrading 𝒜 =
      (op 𝒜 : A →ₗ[R] GradedOpposite 𝒜) ∘ₗ coeLinearMap 𝒜 := by
  refine DirectSum.linearMap_ext _ fun i => LinearMap.ext fun a => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    toGrading_lof, lof_eq_of, lof_eq_of, coeLinearMap_of, coeLinearMap_of, coe_gradingEquiv,
    LinearEquiv.coe_coe]

theorem coeLinearMap_comp_ofGrading :
    coeLinearMap 𝒜 ∘ₗ ofGrading 𝒜 =
      (unop 𝒜 : GradedOpposite 𝒜 →ₗ[R] A) ∘ₗ coeLinearMap (grading 𝒜) := by
  refine DirectSum.linearMap_ext _ fun i => LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    ofGrading_lof, lof_eq_of, lof_eq_of, coeLinearMap_of, coeLinearMap_of, coe_gradingEquiv_symm,
    LinearEquiv.coe_coe]

theorem toGrading_comp_ofGrading : toGrading 𝒜 ∘ₗ ofGrading 𝒜 = LinearMap.id := by
  refine DirectSum.linearMap_ext _ fun i => LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, ofGrading_lof,
    toGrading_lof, LinearEquiv.apply_symm_apply, LinearMap.id_apply]

theorem coeLinearMap_toGrading (y : ⨁ i, 𝒜 i) :
    coeLinearMap (grading 𝒜) (toGrading 𝒜 y) = op 𝒜 (coeLinearMap 𝒜 y) :=
  LinearMap.congr_fun (coeLinearMap_comp_toGrading 𝒜) y

theorem unop_coeLinearMap (z : ⨁ i, grading 𝒜 i) :
    unop 𝒜 (coeLinearMap (grading 𝒜) z) = coeLinearMap 𝒜 (ofGrading 𝒜 z) :=
  (LinearMap.congr_fun (coeLinearMap_comp_ofGrading 𝒜) z).symm

theorem toGrading_ofGrading (z : ⨁ i, grading 𝒜 i) : toGrading 𝒜 (ofGrading 𝒜 z) = z :=
  LinearMap.congr_fun (toGrading_comp_ofGrading 𝒜) z

/-- `DirectSum.coeLinearMap` is the inverse of the decomposition. -/
theorem _root_.DirectSum.coeLinearMap_eq_decomposeLinearEquiv_symm :
    coeLinearMap 𝒜 = ((decomposeLinearEquiv 𝒜).symm : (⨁ i, 𝒜 i) →ₗ[R] A) :=
  DirectSum.linearMap_ext _ fun i => by
    rw [decomposeLinearEquiv_symm_comp_lof]
    exact LinearMap.ext fun a => by
      rw [LinearMap.comp_apply, lof_eq_of, coeLinearMap_of, Submodule.subtype_apply]

theorem _root_.DirectSum.coeLinearMap_decompose (a : A) :
    coeLinearMap 𝒜 (decompose 𝒜 a) = a := by
  rw [DirectSum.coeLinearMap_eq_decomposeLinearEquiv_symm, LinearEquiv.coe_coe,
    decomposeLinearEquiv_symm_apply, Equiv.symm_apply_apply]

theorem _root_.DirectSum.decompose_coeLinearMap (y : ⨁ i, 𝒜 i) :
    decompose 𝒜 (coeLinearMap 𝒜 y) = y := by
  rw [DirectSum.coeLinearMap_eq_decomposeLinearEquiv_symm, LinearEquiv.coe_coe,
    decomposeLinearEquiv_symm_apply, Equiv.apply_symm_apply]

instance instDecomposition : DirectSum.Decomposition (grading 𝒜) :=
  DirectSum.Decomposition.ofLinearMap (grading 𝒜)
    (toGrading 𝒜 ∘ₗ (decomposeLinearEquiv 𝒜 : A →ₗ[R] ⨁ i, 𝒜 i) ∘ₗ
      (unop 𝒜 : GradedOpposite 𝒜 →ₗ[R] A))
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.coe_coe, coeLinearMap_toGrading, decomposeLinearEquiv_apply,
        DirectSum.coeLinearMap_decompose, op_unop, LinearMap.id_apply])
    (LinearMap.ext fun z => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.coe_coe, unop_coeLinearMap, decomposeLinearEquiv_apply,
        DirectSum.decompose_coeLinearMap, toGrading_ofGrading, LinearMap.id_apply])

instance instGradedAlgebra : GradedAlgebra (grading 𝒜) :=
  { instGradedMonoid 𝒜, instDecomposition 𝒜 with }

theorem decompose_grading (x : GradedOpposite 𝒜) :
    decompose (grading 𝒜) x = toGrading 𝒜 (decompose 𝒜 (unop 𝒜 x)) := rfl

/-- The graded opposite of the graded opposite is the original algebra: the algebra isomorphism
`(𝒜ᵒᵖ)ᵒᵖ ≃ₐ[R] A` given by `unop ∘ unop`. -/
def opOpAlgEquiv : GradedOpposite (grading 𝒜) ≃ₐ[R] A :=
  AlgEquiv.ofLinearEquiv (unop (grading 𝒜) ≪≫ₗ unop 𝒜)
    (by rw [LinearEquiv.trans_apply, unop_one, unop_one])
    (map_mul_of_homogeneous (grading (grading 𝒜)) _ fun {i j} x y => by
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
        unop_mul (grading 𝒜) x.2 y.2, Units.smul_def, map_zsmul, ← Units.smul_def,
        unop_mul 𝒜 ((mem_grading_iff (grading 𝒜)).mp y.2) ((mem_grading_iff (grading 𝒜)).mp x.2),
        smul_smul, mul_comm j i, Int.units_mul_self, one_smul])

@[simp] theorem opOpAlgEquiv_apply (x : GradedOpposite (grading 𝒜)) :
    opOpAlgEquiv 𝒜 x = unop 𝒜 (unop (grading 𝒜) x) := rfl

@[simp] theorem opOpAlgEquiv_symm_apply (a : A) :
    (opOpAlgEquiv 𝒜).symm a = op (grading 𝒜) (op 𝒜 a) := rfl

/-- `opOpAlgEquiv` preserves degrees. -/
theorem opOpAlgEquiv_mem_iff {i : ℤ} {x : GradedOpposite (grading 𝒜)} :
    opOpAlgEquiv 𝒜 x ∈ 𝒜 i ↔ x ∈ grading (grading 𝒜) i :=
  ((mem_grading_iff (grading 𝒜)).trans (mem_grading_iff 𝒜)).symm

/-- `opOpAlgEquiv` preserves degrees, in terms of submodules. -/
theorem map_opOpAlgEquiv_grading (i : ℤ) :
    (grading (grading 𝒜) i).map (opOpAlgEquiv 𝒜).toLinearMap = 𝒜 i := by
  ext a
  refine ⟨?_, fun ha => ⟨(opOpAlgEquiv 𝒜).symm a, ?_, (opOpAlgEquiv 𝒜).apply_symm_apply a⟩⟩
  · rintro ⟨x, hx, rfl⟩
    exact (opOpAlgEquiv_mem_iff 𝒜).mpr hx
  · rw [SetLike.mem_coe, ← opOpAlgEquiv_mem_iff, AlgEquiv.apply_symm_apply]
    exact ha

/-! ### Graded commutativity and the opposite algebra -/

/-- `op` is multiplicative on homogeneous elements iff they commute up to the Koszul sign. -/
theorem op_mul_eq_iff {i j : ℤ} {a b : A} (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 j) :
    op 𝒜 (a * b) = op 𝒜 a * op 𝒜 b ↔ a * b = koszulSign (i * j) • (b * a) := by
  rw [op_mul_op 𝒜 ha hb, ← map_koszulSign_smul]
  exact (op 𝒜).injective.eq_iff

/-- A graded algebra is graded commutative iff the identity map `op : A → GradedOpposite 𝒜` is
multiplicative. -/
theorem _root_.DG.isGradedComm_iff_op_mul :
    IsGradedComm 𝒜 ↔ ∀ a b : A, op 𝒜 (a * b) = op 𝒜 a * op 𝒜 b := by
  constructor
  · intro h
    exact map_mul_of_homogeneous 𝒜 (op 𝒜) fun a b =>
      (op_mul_eq_iff 𝒜 a.2 b.2).mpr (h.mul_comm_of_mem a.2 b.2)
  · intro h
    exact ⟨fun ha hb => (op_mul_eq_iff 𝒜 ha hb).mp (h _ _)⟩

/-- For a graded commutative algebra, `op` is an algebra isomorphism
`A ≃ₐ[R] GradedOpposite 𝒜`. -/
def opAlgEquiv [IsGradedComm 𝒜] : A ≃ₐ[R] GradedOpposite 𝒜 :=
  AlgEquiv.ofLinearEquiv (op 𝒜) rfl ((isGradedComm_iff_op_mul 𝒜).mp inferInstance)

@[simp] theorem opAlgEquiv_apply [IsGradedComm 𝒜] (a : A) : opAlgEquiv 𝒜 a = op 𝒜 a := rfl

/-- The graded opposite of a graded commutative algebra is graded commutative. -/
instance [IsGradedComm 𝒜] : IsGradedComm (grading 𝒜) where
  mul_comm_of_mem {i j x y} hx hy := by
    apply (unop 𝒜).injective
    rw [unop_mul 𝒜 hx hy, Units.smul_def (koszulSign (i * j)) (y * x), map_zsmul,
      unop_mul 𝒜 hy hx,
      IsGradedComm.mul_comm_of_mem ((mem_grading_iff 𝒜).mp hy) ((mem_grading_iff 𝒜).mp hx),
      ← Units.smul_def]

end GradedOpposite

end DG
