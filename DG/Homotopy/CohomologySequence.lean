import Mathlib.Algebra.Homology.ConcreteCategory
import DG.Homotopy.Abelian
import DG.Homotopy.CohomologyComparison

/-!
# The long exact cohomology sequence

For a short exact sequence `0 → X₁ → X₂ → X₃ → 0` of dg modules over a dg ring `A`
(`hS : S.ShortExact` for `S : ShortComplex (DGModuleCat A)`), there are connecting morphisms
`DG.DGModuleCat.δ hS n : Hⁿ(X₃) →+ Hⁿ⁺¹(X₁)` and the sequence

  `⋯ → Hⁿ(X₁) → Hⁿ(X₂) → Hⁿ(X₃) → Hⁿ⁺¹(X₁) → Hⁿ⁺¹(X₂) → ⋯`

of cohomology groups (`DG.cohomology`, with the maps `DG.cohomology.map`) is exact:
`DG.DGModuleCat.cohomology_exact₁`, `DG.DGModuleCat.cohomology_exact₂`,
`DG.DGModuleCat.cohomology_exact₃`.

The connecting morphism is transported from Mathlib's
(`CategoryTheory.ShortComplex.ShortExact.δ`) for the short exact sequence of underlying cochain
complexes, along `DG.DGModuleCat.cohomologyAddEquiv`, and exactness is deduced from
`HomologicalComplex.HomologySequence`. The connecting morphism has the usual description
`δ [z₃] = [x₁]` where `g x₂ = z₃` and `f x₁ = d x₂` (`DG.DGModuleCat.δ_mk`); in particular it
has no sign. It agrees with Mathlib's connecting morphism over any ground ring `R`
(`DG.DGModuleCat.cohomologyAddEquiv_δ`).
-/

open CategoryTheory

universe v u w

noncomputable section

namespace DG

namespace DGModuleCat

open DGModuleCat.Algebra

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]
  {S : ShortComplex (DGModuleCat.{v} A)} (hS : S.ShortExact)

/-- The connecting morphism of the long exact cohomology sequence of a short exact sequence
`0 → X₁ → X₂ → X₃ → 0` of dg modules, `δ : Hⁿ(X₃) → Hⁿ⁺¹(X₁)`, obtained from Mathlib's
connecting morphism (`CategoryTheory.ShortComplex.ShortExact.δ`) of the underlying short exact
sequence of cochain complexes of abelian groups. It is described explicitly by
`DG.DGModuleCat.δ_mk`. -/
def δ (n : ℤ) : cohomology S.X₃ n →+ cohomology S.X₁ (n + 1) :=
  (cohomologyAddEquiv ℤ S.X₁ (n + 1)).symm.toAddMonoidHom.comp
    ((AddMonoidHomClass.toAddMonoidHom ((shortExact_map_forget ℤ hS).δ n (n + 1) rfl).hom).comp
      (cohomologyAddEquiv ℤ S.X₃ n).toAddMonoidHom)

variable (R : Type w) [CommRing R] [Algebra R A] [DGAlgebra R A]

include hS in
/-- If `f x₁ = d x₂`, then `x₁` is a cocycle, since `f` is injective. -/
theorem d_eq_zero_of_f_eq_d {x₂ : S.X₂} {x₁ : S.X₁} (h₁ : S.f x₁ = d x₂) : d x₁ = 0 :=
  ((shortExact_iff S).1 hS).1 (by
    change S.f.hom (d x₁) = S.f.hom 0
    rw [map_zero, DGModuleHom.map_d]
    exact (congrArg d h₁).trans (d_d x₂))

/-- The connecting morphism of the underlying short exact sequence of cochain complexes of
`R`-modules, on the class of a cocycle. -/
theorem δ_forget_apply (n : ℤ) (z₃ : cocycles S.X₃ n) (x₂ : S.X₂) (hx₂ : x₂ ∈ grading n)
    (h₂ : S.g x₂ = z₃) (x₁ : S.X₁) (hx₁ : x₁ ∈ grading (n + 1)) (h₁ : S.f x₁ = d x₂) :
    (shortExact_map_forget R hS).δ n (n + 1) rfl
        (cohomologyAddEquiv R S.X₃ n (cohomology.mk _ n z₃)) =
      cohomologyAddEquiv R S.X₁ (n + 1) (cohomology.mk _ (n + 1)
        ⟨x₁, hx₁, d_eq_zero_of_f_eq_d hS h₁⟩) := by
  rw [cohomologyAddEquiv_mk, cohomologyAddEquiv_mk]
  exact (shortExact_map_forget R hS).δ_apply n (n + 1) rfl
    (⟨z₃, cocycles.mem_grading z₃⟩ : DGModule.gradingSubmodule R A S.X₃ n) _
    (⟨x₂, hx₂⟩ : DGModule.gradingSubmodule R A S.X₂ n) (Subtype.ext h₂)
    (⟨x₁, hx₁⟩ : DGModule.gradingSubmodule R A S.X₁ (n + 1))
    (Subtype.ext (h₁.trans (toComplex_d_apply R S.X₂ rfl ⟨x₂, hx₂⟩).symm)) _ _

/-- Explicit description of the connecting morphism: for a cocycle `z₃ ∈ X₃ⁿ`, choose
`x₂ ∈ X₂ⁿ` with `g x₂ = z₃` and `x₁ ∈ X₁ⁿ⁺¹` with `f x₁ = d x₂`; then `δ [z₃] = [x₁]`. -/
theorem δ_mk (n : ℤ) (z₃ : cocycles S.X₃ n) (x₂ : S.X₂) (hx₂ : x₂ ∈ grading n)
    (h₂ : S.g x₂ = z₃) (x₁ : S.X₁) (hx₁ : x₁ ∈ grading (n + 1)) (h₁ : S.f x₁ = d x₂) :
    δ hS n (cohomology.mk _ n z₃) =
      cohomology.mk _ (n + 1) ⟨x₁, hx₁, d_eq_zero_of_f_eq_d hS h₁⟩ := by
  change (cohomologyAddEquiv ℤ S.X₁ (n + 1)).symm ((shortExact_map_forget ℤ hS).δ n (n + 1) rfl
    (cohomologyAddEquiv ℤ S.X₃ n (cohomology.mk _ n z₃))) = _
  rw [δ_forget_apply hS ℤ n z₃ x₂ hx₂ h₂ x₁ hx₁ h₁, AddEquiv.symm_apply_apply]

include hS in
/-- The elements used in the description `DG.DGModuleCat.δ_mk` of the connecting morphism
exist. -/
theorem exists_δ_data (n : ℤ) (z₃ : cocycles S.X₃ n) :
    ∃ x₂ : S.X₂, x₂ ∈ grading n ∧ S.g x₂ = z₃ ∧
      ∃ x₁ : S.X₁, x₁ ∈ grading (n + 1) ∧ S.f x₁ = d x₂ := by
  obtain ⟨hf, hfg, hg⟩ := (shortExact_iff S).1 hS
  obtain ⟨y, hy⟩ := hg (z₃ : S.X₃)
  let x₂ : S.X₂ := DirectSum.decompose (grading (M := S.X₂)) y n
  have h₂ : S.g x₂ = z₃ := by
    rw [← decompose_apply, hy, DirectSum.decompose_of_mem_same _ (cocycles.mem_grading z₃)]
  obtain ⟨x, hx⟩ := (hfg (d x₂)).mp (by
    change S.g.hom (d x₂) = 0
    rw [DGModuleHom.map_d]
    exact (congrArg d h₂).trans (cocycles.d_eq_zero z₃))
  refine ⟨x₂, SetLike.coe_mem _, h₂, DirectSum.decompose (grading (M := S.X₁)) x (n + 1),
    SetLike.coe_mem _, ?_⟩
  rw [← decompose_apply, hx, DirectSum.decompose_of_mem_same _ (d_mem (SetLike.coe_mem _))]

/-- The connecting morphism `DG.DGModuleCat.δ` agrees, under the comparison isomorphisms
`DG.DGModuleCat.cohomologyAddEquiv`, with Mathlib's connecting morphism of the underlying short
exact sequence of cochain complexes of `R`-modules. -/
theorem cohomologyAddEquiv_δ (n : ℤ) (x : cohomology S.X₃ n) :
    cohomologyAddEquiv R S.X₁ (n + 1) (δ hS n x) =
      (shortExact_map_forget R hS).δ n (n + 1) rfl (cohomologyAddEquiv R S.X₃ n x) := by
  induction x using cohomology.induction_on with
  | h z₃ =>
    obtain ⟨x₂, hx₂, h₂, x₁, hx₁, h₁⟩ := exists_δ_data hS n z₃
    rw [δ_mk hS n z₃ x₂ hx₂ h₂ x₁ hx₁ h₁, δ_forget_apply hS R n z₃ x₂ hx₂ h₂ x₁ hx₁ h₁]

/-! ### Exactness -/

include hS in
/-- Exactness of the long exact cohomology sequence at `Hⁿ(X₂)`:
`Hⁿ(X₁) → Hⁿ(X₂) → Hⁿ(X₃)`. -/
theorem cohomology_exact₂ (n : ℤ) :
    Function.Exact (cohomology.map S.f.hom n) (cohomology.map S.g.hom n) :=
  (Function.Exact.iff_of_ladder_addEquiv (cohomologyAddEquiv ℤ S.X₁ n)
    (cohomologyAddEquiv ℤ S.X₂ n) (cohomologyAddEquiv ℤ S.X₃ n)
    (g₁₂ := AddMonoidHomClass.toAddMonoidHom
      (HomologicalComplex.homologyMap ((forget ℤ A).map S.f) n).hom)
    (g₂₃ := AddMonoidHomClass.toAddMonoidHom
      (HomologicalComplex.homologyMap ((forget ℤ A).map S.g) n).hom)
    (AddMonoidHom.ext fun x => (cohomologyAddEquiv_naturality ℤ S.f n x).symm)
    (AddMonoidHom.ext fun x => (cohomologyAddEquiv_naturality ℤ S.g n x).symm)).1
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      ((shortExact_map_forget ℤ hS).homology_exact₂ n))

/-- Exactness of the long exact cohomology sequence at `Hⁿ(X₃)`:
`Hⁿ(X₂) → Hⁿ(X₃) → Hⁿ⁺¹(X₁)`. -/
theorem cohomology_exact₃ (n : ℤ) :
    Function.Exact (cohomology.map S.g.hom n) (δ hS n) :=
  (Function.Exact.iff_of_ladder_addEquiv (cohomologyAddEquiv ℤ S.X₂ n)
    (cohomologyAddEquiv ℤ S.X₃ n) (cohomologyAddEquiv ℤ S.X₁ (n + 1))
    (g₁₂ := AddMonoidHomClass.toAddMonoidHom
      (HomologicalComplex.homologyMap ((forget ℤ A).map S.g) n).hom)
    (g₂₃ := AddMonoidHomClass.toAddMonoidHom ((shortExact_map_forget ℤ hS).δ n (n + 1) rfl).hom)
    (AddMonoidHom.ext fun x => (cohomologyAddEquiv_naturality ℤ S.g n x).symm)
    (AddMonoidHom.ext fun x => (cohomologyAddEquiv_δ hS ℤ n x).symm)).1
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      ((shortExact_map_forget ℤ hS).homology_exact₃ n (n + 1) rfl))

/-- Exactness of the long exact cohomology sequence at `Hⁿ⁺¹(X₁)`:
`Hⁿ(X₃) → Hⁿ⁺¹(X₁) → Hⁿ⁺¹(X₂)`. -/
theorem cohomology_exact₁ (n : ℤ) :
    Function.Exact (δ hS n) (cohomology.map S.f.hom (n + 1)) :=
  (Function.Exact.iff_of_ladder_addEquiv (cohomologyAddEquiv ℤ S.X₃ n)
    (cohomologyAddEquiv ℤ S.X₁ (n + 1)) (cohomologyAddEquiv ℤ S.X₂ (n + 1))
    (g₁₂ := AddMonoidHomClass.toAddMonoidHom ((shortExact_map_forget ℤ hS).δ n (n + 1) rfl).hom)
    (g₂₃ := AddMonoidHomClass.toAddMonoidHom
      (HomologicalComplex.homologyMap ((forget ℤ A).map S.f) (n + 1)).hom)
    (AddMonoidHom.ext fun x => (cohomologyAddEquiv_δ hS ℤ n x).symm)
    (AddMonoidHom.ext fun x => (cohomologyAddEquiv_naturality ℤ S.f (n + 1) x).symm)).1
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      ((shortExact_map_forget ℤ hS).homology_exact₁ n (n + 1) rfl))

end DGModuleCat

end DG
