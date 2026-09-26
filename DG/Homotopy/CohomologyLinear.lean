import DG.Homotopy.CohomologyComparison
import DG.Module.CohomologyLinear

/-!
# The `R`-linear comparison of cohomology with Mathlib's homology

For a dg `R`-algebra `A` and a dg `A`-module `M`, the cohomology groups `DG.cohomology M n` are
`R`-modules (`DG.cohomology.groundModule`), and the comparison
`DG.DGModuleCat.cohomologyAddEquiv R M n` with the homology of the underlying cochain complex
of `R`-modules is `R`-linear:

* `DG.DGModuleCat.Algebra.instModuleCohomology`: the (scoped) instance `Module R (cohomology M n)`
  for `M : DGModuleCat A`, compatible with the scoped `R`-module structure
  `r • m = algebraMap R A r • m` on the carrier of `M`;
* `DG.DGModuleCat.cohomologyLinearEquiv R M n :
    cohomology M n ≃ₗ[R] ((forget R A).obj M).homology n`.

The instance is scoped in `DG.DGModuleCat.Algebra`, like the `R`-module structure on the
carriers: for `R = ℤ` it agrees with the `ℤ`-module structure of the abelian group
`cohomology M n` only propositionally.
-/

open CategoryTheory

universe v u w

noncomputable section

namespace DG

namespace DGModuleCat

variable (R : Type w) {A : Type u} [CommRing R] [Ring A] [DGAddCommGroup A] [Algebra R A]
  [DGRing A] [DGAlgebra R A]

namespace Algebra

/-- The `R`-module structure on the cohomology of a dg `A`-module, `r • [z] = [r • z]`, where
`r • z = algebraMap R A r • z`. -/
scoped instance instModuleCohomology (M : DGModuleCat.{v} A) (n : ℤ) :
    Module R (cohomology M n) :=
  cohomology.groundModule R A M n

end Algebra

open Algebra

variable (M : DGModuleCat.{v} A)

/-- The comparison `Hⁿ(M) ≃ₗ[R] Hⁿ(toComplex R M)` between the cohomology of a dg module and
the homology of its underlying cochain complex of `R`-modules, as an `R`-linear equivalence;
the underlying additive equivalence is `DG.DGModuleCat.cohomologyAddEquiv`. -/
def cohomologyLinearEquiv (n : ℤ) : cohomology M n ≃ₗ[R] ((forget R A).obj M).homology n :=
  { cohomologyAddEquiv R M n with
    map_smul' := fun r x => by
      induction x using cohomology.induction_on with
      | h z =>
        change ((toComplex R M).sc n).moduleCatHomologyIso.symm.toLinearEquiv _ =
          r • ((toComplex R M).sc n).moduleCatHomologyIso.symm.toLinearEquiv _
        rw [← LinearEquiv.map_smul]
        rfl }

@[simp]
theorem toAddEquiv_cohomologyLinearEquiv (n : ℤ) :
    (cohomologyLinearEquiv R M n).toAddEquiv = cohomologyAddEquiv R M n :=
  rfl

theorem cohomologyLinearEquiv_apply (n : ℤ) (x : cohomology M n) :
    cohomologyLinearEquiv R M n x = cohomologyAddEquiv R M n x :=
  rfl

variable {M} in
/-- The map induced on cohomology by a morphism in `DGModuleCat A` is `R`-linear. -/
theorem cohomology_map_smul {N : DGModuleCat.{v} A} (f : M ⟶ N) (n : ℤ) (r : R)
    (x : cohomology M n) : cohomology.map f.hom n (r • x) = r • cohomology.map f.hom n x :=
  cohomology.map_groundSMul A f.hom n r x

end DGModuleCat

end DG
