import Mathlib.Algebra.DirectSum.Algebra
import DG.Algebra.Cohomology

/-!
# Cohomology over a dg `R`-algebra

Let `A` be a dg `R`-algebra and `M` a dg `A`-module with a compatible `R`-module structure
(`IsScalarTower R A M`). The differential of `M` is `R`-linear and the graded pieces are
`R`-submodules, so the cohomology groups `Hⁿ(M)` are `R`-modules and the maps induced by
morphisms of dg modules are `R`-linear. For `M = A`, the cohomology ring `H(A)` is a graded
`R`-algebra and a dg `R`-algebra with zero differential.

## Main definitions and results

* `DG.DGModule.ground_smul_mem_cocycles`, `DG.DGModule.ground_smul_mem_coboundaries`: the
  cocycles and coboundaries are stable under `R`; as submodules,
  `DG.DGModule.cocyclesSubmodule` and `DG.DGModule.coboundariesSubmodule`.
* `DG.cohomology.groundModule R A M n : Module R (cohomology M n)`, with `r • [z] = [r • z]`
  (`DG.cohomology.groundModule_smul_mk`).
* `DG.cohomology.map_groundSMul`, `DG.cohomology.mapLinear`: `Hⁿ(f)` is `R`-linear.
* `DG.cohomology.instModuleOfAlgebra`: the instance `Module R (cohomology A n)` for a dg
  `R`-algebra `A`.
* `DG.Cohomology.galgebra`: `H(A) = ⨁ n, Hⁿ(A)` is a graded `R`-algebra
  (`DirectSum.GAlgebra`), with structure map `r ↦ r • 1 ∈ H⁰(A)`
  (`DG.Cohomology.algebraMapZero`). Hence `Algebra R (Cohomology A)` (Mathlib's
  `DirectSum.instAlgebra`), and `DG.Cohomology.dgAlgebra : DGAlgebra R (Cohomology A)`.
* `DG.DGAlgHom.cohomologyAlgHom`: a morphism of dg `R`-algebras induces a morphism of
  `R`-algebras on cohomology.

## Implementation notes

`DG.cohomology.groundModule R A M n` is a definition, not an instance: the dg algebra `A` does
not occur in `Module R (cohomology M n)`, so it cannot be found by instance search. It is made
an instance for `M = A` (`DG.cohomology.instModuleOfAlgebra`) and, in
`DG.Homotopy.CohomologyLinear`, for the objects of `DG.DGModuleCat A` (scoped, like the
`R`-module structure on their carriers).

The action is defined through `Quotient.map'`, exactly as the `ℤ`-action of the quotient
group. Consequently, for `R = ℤ` with its canonical actions,
`DG.cohomology.groundModule ℤ A M n` is equal to `AddCommGroup.toIntModule` at reducible and
instance transparency, so the instance for `M = A` creates no diamond. With this action, the
structure map `r ↦ r • 1` makes the `ℤ`-algebra structure of `H(A)` from
`DG.Cohomology.galgebra` definitionally equal (by `rfl`) to `Ring.toIntAlgebra`, and its
underlying module structure equal to `AddCommGroup.toIntModule` at instance transparency.
-/

open DirectSum

namespace DG

section Stable

variable (R : Type*) (A : Type*) (M : Type*) [CommRing R] [Ring A] [Algebra R A]
  [DGAddCommGroup A] [DGRing A] [DGAlgebra R A] [AddCommGroup M] [DGAddCommGroup M]
  [Module A M] [DGModule A M] [Module R M] [IsScalarTower R A M]

include A

variable {R M} in
theorem DGModule.ground_smul_mem_cocycles {n : ℤ} (r : R) {m : M} (hm : m ∈ cocycles M n) :
    r • m ∈ cocycles M n := by
  rw [mem_cocycles] at hm ⊢
  exact ⟨DGModule.ground_smul_mem A r hm.1, by rw [d_ground_smul A, hm.2, smul_zero]⟩

variable {R M} in
theorem DGModule.ground_smul_mem_coboundaries {n : ℤ} (r : R) {m : M}
    (hm : m ∈ coboundaries M n) : r • m ∈ coboundaries M n := by
  obtain ⟨m', hm', rfl⟩ := hm
  exact ⟨r • m', DGModule.ground_smul_mem A r hm', d_ground_smul A r m'⟩

/-- The cocycles `Zⁿ(M)` of a dg module over a dg `R`-algebra, as an `R`-submodule. -/
def DGModule.cocyclesSubmodule (n : ℤ) : Submodule R M where
  __ := cocycles M n
  smul_mem' r _ hm := DGModule.ground_smul_mem_cocycles A r hm

/-- The coboundaries `Bⁿ(M)` of a dg module over a dg `R`-algebra, as an `R`-submodule. -/
def DGModule.coboundariesSubmodule (n : ℤ) : Submodule R M where
  __ := coboundaries M n
  smul_mem' r _ hm := DGModule.ground_smul_mem_coboundaries A r hm

@[simp]
theorem DGModule.cocyclesSubmodule_toAddSubgroup (n : ℤ) :
    (DGModule.cocyclesSubmodule R A M n).toAddSubgroup = cocycles M n := rfl

@[simp]
theorem DGModule.coboundariesSubmodule_toAddSubgroup (n : ℤ) :
    (DGModule.coboundariesSubmodule R A M n).toAddSubgroup = coboundaries M n := rfl

namespace cohomology

variable {R M} in
/-- The action of `r : R` on the cocycles `Zⁿ(M)`, as an additive map. -/
def groundSMulCocycles (n : ℤ) (r : R) : cocycles M n →+ cocycles M n where
  toFun z := ⟨r • (z : M), DGModule.ground_smul_mem_cocycles A r z.2⟩
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [smul_add]

variable {R M} in
@[simp]
theorem coe_groundSMulCocycles_apply (n : ℤ) (r : R) (z : cocycles M n) :
    (groundSMulCocycles A n r z : M) = r • (z : M) := rfl

/-- The `R`-module structure on `Hⁿ(M)`, `r • [z] = [r • z]`, for a dg module `M` over a dg
`R`-algebra `A` with `IsScalarTower R A M`. Not an instance, since `A` is not determined by
`Module R (cohomology M n)`; see the module docstring. -/
abbrev groundModule (n : ℤ) : Module R (cohomology M n) :=
  letI : SMul R (cohomology M n) := ⟨fun r => Quotient.map' (groundSMulCocycles A n r)
    fun x y h => QuotientAddGroup.leftRel_apply.mpr <| by
      have h := QuotientAddGroup.leftRel_apply.mp h
      rw [AddSubgroup.mem_addSubgroupOf] at h ⊢
      rw [← _root_.map_neg, ← _root_.map_add]
      exact DGModule.ground_smul_mem_coboundaries A r h⟩
  { one_smul := fun x => by
      induction x using cohomology.induction_on with
      | h z => exact congrArg (mk M n) (Subtype.ext (one_smul R (z : M)))
    mul_smul := fun r s x => by
      induction x using cohomology.induction_on with
      | h z => exact congrArg (mk M n) (Subtype.ext (mul_smul r s (z : M)))
    smul_zero := fun r => congrArg (mk M n) (Subtype.ext (smul_zero r))
    smul_add := fun r x y => by
      induction x using cohomology.induction_on with
      | h z =>
      induction y using cohomology.induction_on with
      | h w => exact congrArg (mk M n) (Subtype.ext (smul_add r (z : M) w))
    add_smul := fun r s x => by
      induction x using cohomology.induction_on with
      | h z => exact congrArg (mk M n) (Subtype.ext (add_smul r s (z : M)))
    zero_smul := fun x => by
      induction x using cohomology.induction_on with
      | h z => exact congrArg (mk M n) (Subtype.ext (zero_smul R (z : M))) }

variable {R M}

theorem groundModule_smul_mk {n : ℤ} (r : R) (z : cocycles M n) :
    letI := groundModule R A M n
    r • mk M n z = mk M n (groundSMulCocycles A n r z) := rfl

theorem groundModule_smul_mkOf {n : ℤ} (r : R) {m : M} (hm : m ∈ grading n) (hd : d m = 0) :
    letI := groundModule R A M n
    r • mkOf hm hd = mkOf (DGModule.ground_smul_mem A r hm)
      (by rw [d_ground_smul A, hd, smul_zero]) := rfl

variable {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]
  [Module R N] [IsScalarTower R A N]

/-- The map induced on cohomology by a morphism of dg modules is `R`-linear. -/
theorem map_groundSMul (f : M →ᵈᵍ[A] N) (n : ℤ) (r : R) (x : cohomology M n) :
    letI := groundModule R A M n
    letI := groundModule R A N n
    map f n (r • x) = r • map f n x := by
  induction x using cohomology.induction_on with
  | h z =>
    rw [groundModule_smul_mk, map_mk, map_mk, groundModule_smul_mk]
    refine congrArg (mk N n) (Subtype.ext ?_)
    change f (r • (z : M)) = r • f z
    rw [← algebraMap_smul A r (z : M), map_smul, algebraMap_smul]

variable (R) in
/-- `Hⁿ(f)` as an `R`-linear map, for a morphism `f` of dg modules over a dg `R`-algebra. -/
def mapLinear (f : M →ᵈᵍ[A] N) (n : ℤ) :
    letI := groundModule R A M n
    letI := groundModule R A N n
    cohomology M n →ₗ[R] cohomology N n :=
  letI := groundModule R A M n
  letI := groundModule R A N n
  { map f n with map_smul' := map_groundSMul A f n }

end cohomology

end Stable

section Algebra

variable (R : Type*) (A : Type*) [CommRing R] [Ring A] [Algebra R A] [DGAddCommGroup A]
  [DGRing A] [DGAlgebra R A]

namespace cohomology

/-- For a dg `R`-algebra `A`, `Hⁿ(A)` is an `R`-module, `r • [a] = [r • a]`. -/
instance instModuleOfAlgebra (n : ℤ) : Module R (cohomology A n) :=
  groundModule R A A n

variable {R A}

theorem smul_mk {n : ℤ} (r : R) (z : cocycles A n) :
    r • mk A n z = mk A n (groundSMulCocycles A n r z) := rfl

theorem smul_mkOf {n : ℤ} (r : R) {a : A} (ha : a ∈ grading n) (hd : d a = 0) :
    r • mkOf ha hd = mkOf (DGModule.ground_smul_mem A r ha)
      (by rw [d_ground_smul A, hd, smul_zero]) := rfl

end cohomology

namespace Cohomology

open GradedMonoid

variable {R A}

theorem smul_mul_mk {i j : ℤ} (r : R) (a : cocycles A i) (b : cocycles A j) :
    GMul.mul (r • cohomology.mk A i a) (cohomology.mk A j b) =
      r • GMul.mul (cohomology.mk A i a) (cohomology.mk A j b) := by
  rw [cohomology.smul_mk, mk_mul_mk, mk_mul_mk, cohomology.smul_mk]
  exact congrArg (cohomology.mk A (i + j)) (Subtype.ext (smul_mul_assoc r (a : A) b))

variable (R A)

/-- The structure map `R → H⁰(A)`, `r ↦ r • 1`. -/
def algebraMapZero : R →+ cohomology A 0 :=
  (smulAddHom R (cohomology A 0)).flip GOne.one

variable {R A}

theorem algebraMapZero_apply (r : R) : algebraMapZero R A r = r • GOne.one := rfl

/-- The structure map `R → H⁰(A)` sends `r` to the class of `algebraMap R A r`. -/
theorem algebraMapZero_eq_mk (r : R) :
    algebraMapZero R A r = cohomology.mk A 0 ⟨algebraMap R A r,
      mem_cocycles.mpr ⟨algebraMap_mem_grading R r, d_algebraMap R r⟩⟩ :=
  congrArg (cohomology.mk A 0) (Subtype.ext (Algebra.algebraMap_eq_smul_one r).symm)

variable (R A)

/-- The cohomology `H(A) = ⨁ n, Hⁿ(A)` of a dg `R`-algebra is a graded `R`-algebra. -/
instance galgebra : DirectSum.GAlgebra R (fun n => cohomology A n) where
  toFun := algebraMapZero R A
  map_one := one_smul R (GOne.one : cohomology A 0)
  map_mul r s := by
    refine Sigma.ext (add_zero 0).symm ?_
    change HEq ((r * s) • (GOne.one : cohomology A 0))
      (GMul.mul (r • (GOne.one : cohomology A 0)) (s • (GOne.one : cohomology A 0)))
    rw [one_def, cohomology.smul_mk, cohomology.smul_mk, cohomology.smul_mk, mk_mul_mk]
    refine cohomology.mk_heq_mk (add_zero 0).symm ?_
    simp only [cohomology.coe_groundSMulCocycles_apply, cocycles.coe_smulHom_apply,
      smul_eq_mul, smul_mul_assoc, one_mul, mul_smul]
  commutes r x := by
    obtain ⟨i, x⟩ := x
    obtain ⟨a, rfl⟩ := cohomology.mk_surjective A i x
    refine Sigma.ext (by simp [add_comm]) ?_
    change HEq (GMul.mul (r • (GOne.one : cohomology A 0)) (cohomology.mk A i a))
      (GMul.mul (cohomology.mk A i a) (r • (GOne.one : cohomology A 0)))
    rw [one_def, cohomology.smul_mk, mk_mul_mk, mk_mul_mk]
    refine cohomology.mk_heq_mk (by simp [add_comm]) ?_
    simp only [cohomology.coe_groundSMulCocycles_apply, cocycles.coe_smulHom_apply,
      smul_eq_mul, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  smul_def r x := by
    obtain ⟨i, x⟩ := x
    obtain ⟨a, rfl⟩ := cohomology.mk_surjective A i x
    refine Sigma.ext (zero_add i).symm ?_
    change HEq (r • cohomology.mk A i a)
      (GMul.mul (r • (GOne.one : cohomology A 0)) (cohomology.mk A i a))
    rw [one_def, cohomology.smul_mk, cohomology.smul_mk, mk_mul_mk]
    refine cohomology.mk_heq_mk (zero_add i).symm ?_
    simp only [cohomology.coe_groundSMulCocycles_apply, cocycles.coe_smulHom_apply,
      smul_eq_mul, smul_mul_assoc, one_mul]

variable {R A}

theorem algebraMap_apply (r : R) :
    algebraMap R (Cohomology A) r =
      DirectSum.of (fun n => cohomology A n) 0 (algebraMapZero R A r) := rfl

variable (R A)

/-- The cohomology `H(A)` of a dg `R`-algebra is a dg `R`-algebra with zero differential. -/
instance dgAlgebra : DGAlgebra R (Cohomology A) where
  algebraMap_mem' r := ⟨algebraMapZero R A r, rfl⟩
  d_algebraMap' _ := rfl

end Cohomology

end Algebra

namespace DGAlgHom

variable {R A B : Type*} [CommRing R] [Ring A] [Algebra R A] [DGAddCommGroup A] [DGRing A]
  [DGAlgebra R A] [Ring B] [Algebra R B] [DGAddCommGroup B] [DGRing B] [DGAlgebra R B]
  (f : A →ᵈᵍₐ[R] B)

/-- The map `Hⁿ(A) → Hⁿ(B)` induced by a morphism of dg `R`-algebras is `R`-linear. -/
theorem cohomologyMap_smul (n : ℤ) (r : R) (x : cohomology A n) :
    f.toDGRingHom.cohomologyMap n (r • x) = r • f.toDGRingHom.cohomologyMap n x := by
  induction x using cohomology.induction_on with
  | h z =>
    rw [cohomology.smul_mk, DGRingHom.cohomologyMap_mk, DGRingHom.cohomologyMap_mk,
      cohomology.smul_mk]
    exact congrArg (cohomology.mk B n) (Subtype.ext (map_smul f r (z : A)))

/-- The morphism of `R`-algebras `H(A) →ₐ[R] H(B)` induced by a morphism of dg `R`-algebras
`A → B`; its underlying ring homomorphism is `DG.DGRingHom.cohomologyRingHom`. -/
def cohomologyAlgHom : Cohomology A →ₐ[R] Cohomology B :=
  { f.toDGRingHom.cohomologyRingHom with
    commutes' := fun r => by
      change f.toDGRingHom.cohomologyRingHom
          (DirectSum.of _ 0 (r • GradedMonoid.GOne.one)) =
        DirectSum.of _ 0 (r • GradedMonoid.GOne.one)
      rw [DGRingHom.cohomologyRingHom_of, cohomologyMap_smul, DGRingHom.cohomologyMap_one] }

@[simp]
theorem cohomologyAlgHom_of (n : ℤ) (x : cohomology A n) :
    f.cohomologyAlgHom (DirectSum.of (fun n => cohomology A n) n x) =
      DirectSum.of (fun n => cohomology B n) n (f.toDGRingHom.cohomologyMap n x) :=
  DGRingHom.cohomologyRingHom_of _ n x

@[simp]
theorem toRingHom_cohomologyAlgHom :
    (f.cohomologyAlgHom : Cohomology A →+* Cohomology B) = f.toDGRingHom.cohomologyRingHom :=
  rfl

end DGAlgHom

end DG
