import DG.Algebra.Constructions
import DG.Homotopy.Homotopy
import DG.Module.HomLinear

/-!
# The endomorphism dg algebra of a cochain complex

A cochain complex `C` of `R`-modules is a dg module over `R` concentrated in degree `0`
(`DG.DGAlgebra.degreeZero R`); conversely a dg abelian group with a compatible `R`-module
structure is such a dg module (`DG.DGModule.ofGround`). Its endomorphism complex
`END_R(C) = DG.DGModule.END R C` is then a dg `R`-algebra (`DG.DGModule.END.instDGAlgebra`),
with product `f * g = (-1)^{|f||g|} g ∘ f`.

For any dg ring `A` and dg `A`-module `M`, in particular for `END_R(C)`:

* `DG.DGModule.END.cocyclesZeroAddEquiv`: the degree-`0` cocycles of `END_A(M)` are the
  morphisms of dg modules `M → M` (chain maps, when `A = R`), with `1 ↦ id`
  (`cocyclesZeroAddEquiv_id`) and composition corresponding to the (opposite) product
  (`cocyclesZeroAddEquiv_comp`);
* `DG.DGModule.END.cohomologyZeroAddEquiv`: `H⁰(END_A(M))` is the group of morphisms modulo
  null-homotopic ones (chain maps up to homotopy).

The ring `R` is given its degree-`0` dg structure through local instances in this file.
-/

open DirectSum

namespace DG

namespace DGModule.END

variable {A M : Type*} [Ring A] [DGAddCommGroup A] [AddCommGroup M] [DGAddCommGroup M]
  [Module A M] [DGModule A M]

variable (A M) in
/-- The degree-`0` cocycles of `END_A(M)` are the endomorphisms of the dg module `M`. -/
noncomputable def cocyclesZeroAddEquiv : (M →ᵈᵍ[A] M) ≃+ cocycles (END A M) 0 :=
  (Cocycle.equivHom A M M).trans (HOM.cocyclesAddEquiv A M M 0)

theorem coe_cocyclesZeroAddEquiv (f : M →ᵈᵍ[A] M) :
    (cocyclesZeroAddEquiv A M f : END A M) =
      DirectSum.of (fun n => Cochain A M M n) 0 (Cochain.ofHom f) :=
  rfl

theorem cocyclesZeroAddEquiv_id :
    (cocyclesZeroAddEquiv A M DGModuleHom.id : END A M) = 1 :=
  rfl

/-- Composition of endomorphisms is the opposite of the product of `END_A(M)` (which is
`f * g = g ∘ f` in degree `0`). -/
theorem cocyclesZeroAddEquiv_comp (f g : M →ᵈᵍ[A] M) :
    (cocyclesZeroAddEquiv A M (g.comp f) : END A M) =
      cocyclesZeroAddEquiv A M f * cocyclesZeroAddEquiv A M g := by
  rw [coe_cocyclesZeroAddEquiv, coe_cocyclesZeroAddEquiv, coe_cocyclesZeroAddEquiv, of_mul_of]
  exact HOM.of_congr (add_zero 0).symm fun x => by
    rw [Cochain.units_smul_apply, mul_zero, koszulSign_zero, one_smul]
    rfl

variable (A M) in
/-- `H⁰(END_A(M))` is the group of endomorphisms of the dg module `M` modulo the
null-homotopic ones. -/
noncomputable def cohomologyZeroAddEquiv :
    ((M →ᵈᵍ[A] M) ⧸ nullHomotopic A M M) ≃+ cohomology (END A M) 0 :=
  quotientNullHomotopicAddEquivCohomology A M M

theorem cohomologyZeroAddEquiv_mk (f : M →ᵈᵍ[A] M) :
    cohomologyZeroAddEquiv A M (QuotientAddGroup.mk f) =
      cohomology.mk _ 0 (cocyclesZeroAddEquiv A M f) :=
  quotientNullHomotopicAddEquivCohomology_mk f

/-- Two endomorphisms of `M` have the same class in `H⁰(END_A(M))` if and only if they are
homotopic. -/
theorem cohomology_mk_eq_iff (f g : M →ᵈᵍ[A] M) :
    cohomology.mk _ 0 (cocyclesZeroAddEquiv A M f) =
      cohomology.mk _ 0 (cocyclesZeroAddEquiv A M g) ↔ Homotopic f g := by
  rw [← cohomologyZeroAddEquiv_mk, ← cohomologyZeroAddEquiv_mk,
    (cohomologyZeroAddEquiv A M).injective.eq_iff, QuotientAddGroup.eq_iff_sub_mem,
    homotopic_iff_sub_mem, ← neg_mem_iff, neg_sub]

end DGModule.END

/-! ### Cochain complexes of `R`-modules -/

section Ground

variable (R : Type*) [CommRing R]

/-- `R` concentrated in degree `0` (local instance). -/
local instance instDGAddCommGroupGround : DGAddCommGroup R := DGAddCommGroup.degreeZero R

/-- `R` concentrated in degree `0`, as a dg ring (local instance). -/
local instance instDGRingGround : DGRing R := DGRing.degreeZero R

/-- `R` concentrated in degree `0`, as a dg `R`-algebra (local instance). -/
local instance instDGAlgebraGround : DGAlgebra R R := DGAlgebra.degreeZero R

variable {R} (C : Type*) [AddCommGroup C] [DGAddCommGroup C] [Module R C]

/-- A dg abelian group with an `R`-module structure for which the graded pieces are
`R`-submodules and the differential is `R`-linear (a cochain complex of `R`-modules) is a dg
module over `R` concentrated in degree `0`. -/
theorem DGModule.ofGround
    (hmem : ∀ (r : R) {n : ℤ} {c : C}, c ∈ grading n → r • c ∈ grading n)
    (hd : ∀ (r : R) (c : C), d (r • c) = r • d c) : DGModule R C where
  smul_mem i j r c hr hc := by
    rcases (mem_degreeZeroGrading_iff R).mp hr with rfl | rfl
    · simpa using hmem r hc
    · simpa using zero_mem (grading (M := C) (i + j))
  d_smul' {n r} hr c := by
    change d (r • c) = (0 : R →+ R) r • c + koszulSign n • (r • d c)
    rcases (mem_degreeZeroGrading_iff R).mp hr with rfl | rfl
    · simp [hd]
    · simp

variable [DGModule R C]

/-- The endomorphism complex `END_R(C)` of a cochain complex of `R`-modules is a dg
`R`-algebra. -/
example : DGAlgebra R (DGModule.END R C) := inferInstance

theorem DGModule.END.algebraMap_ground_apply (r : R) :
    algebraMap R (DGModule.END R C) r =
      DirectSum.of (fun n => Cochain R C C n) 0 (r • Cochain.id R C) :=
  rfl

end Ground

end DG
