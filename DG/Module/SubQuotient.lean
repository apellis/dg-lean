import DG.Module.Sub
import DG.Module.Quotient
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Quotients of dg modules by dg submodules

For a dg submodule `S` of a dg `A`-module `M`, the quotient module `M ⧸ S.toSubmodule` is a dg
`A`-module: its homogeneous components are the images of those of `M` and its differential is
induced by `d` (`DG.DGAddCommGroup.quotient`, since `S` is a dg subgroup). The quotient map
`DG.DGSubmodule.mkQ S : M →ᵈᵍ[A] M ⧸ S.toSubmodule` is a morphism of dg modules, and a morphism
of dg modules vanishing on `S` factors through it (`DG.DGSubmodule.liftQ`).
-/

namespace DG

variable {A : Type*} {M : Type*} [Ring A] [DGAddCommGroup A] [AddCommGroup M]
  [DGAddCommGroup M] [Module A M]

namespace DGSubmodule

variable (S : DGSubmodule A M)

/-- A dg submodule is a dg subgroup. -/
instance isDGAddSubgroup : IsDGAddSubgroup S.toSubmodule.toAddSubgroup where
  decompose_mem hx n := S.decompose_mem n hx
  d_mem hx := S.d_mem hx

/-- The quotient of a dg module by a dg submodule is a dg abelian group, with
`(M ⧸ S)ⁿ` the image of `Mⁿ` and the induced differential. -/
noncomputable instance quotientDGAddCommGroup : DGAddCommGroup (M ⧸ S.toSubmodule) :=
  DGAddCommGroup.quotient S.toSubmodule.toAddSubgroup

theorem mem_grading_quotient_iff {n : ℤ} {y : M ⧸ S.toSubmodule} :
    y ∈ DGAddCommGroup.grading n ↔
      ∃ x ∈ DGAddCommGroup.grading (M := M) n, Submodule.Quotient.mk x = y :=
  Iff.rfl

theorem mk_mem_grading {n : ℤ} {x : M} (hx : x ∈ DGAddCommGroup.grading n) :
    (Submodule.Quotient.mk x : M ⧸ S.toSubmodule) ∈ DGAddCommGroup.grading n :=
  ⟨x, hx, rfl⟩

@[simp]
theorem d_mk (x : M) :
    DGAddCommGroup.d (Submodule.Quotient.mk x : M ⧸ S.toSubmodule) =
      Submodule.Quotient.mk (DGAddCommGroup.d x) :=
  rfl

variable [DGModule A M]

/-- The quotient of a dg module by a dg submodule is a dg module. -/
instance quotientDGModule : DGModule A (M ⧸ S.toSubmodule) where
  smul_mem _ _ a _ ha hy := by
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨a • x, smul_mem_grading ha hx, rfl⟩
  d_smul' {n a} ha y := by
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      rw [← Submodule.Quotient.mk_smul, d_mk, d_smul ha, d_mk, Submodule.Quotient.mk_add,
        Units.smul_def, Units.smul_def, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_smul]

omit [DGModule A M]

/-- The quotient map `M → M ⧸ S` as a morphism of dg modules. -/
def mkQ : M →ᵈᵍ[A] M ⧸ S.toSubmodule where
  __ := S.toSubmodule.mkQ
  map_mem' hx := S.mk_mem_grading hx
  map_d' _ := rfl

@[simp]
theorem mkQ_apply (x : M) : S.mkQ x = Submodule.Quotient.mk x := rfl

theorem mkQ_surjective : Function.Surjective S.mkQ :=
  Submodule.mkQ_surjective _

theorem mkQ_eq_zero_iff {x : M} : S.mkQ x = 0 ↔ x ∈ S :=
  Submodule.Quotient.mk_eq_zero _

@[simp]
theorem ker_mkQ : S.mkQ.ker = S :=
  ext fun _ => S.mkQ_eq_zero_iff

variable {S} {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module A N]

/-- A morphism of dg modules vanishing on `S` factors through the quotient `M ⧸ S`. -/
def liftQ (f : M →ᵈᵍ[A] N) (h : ∀ x ∈ S, f x = 0) : (M ⧸ S.toSubmodule) →ᵈᵍ[A] N where
  __ := S.toSubmodule.liftQ f.toLinearMap fun x hx => h x hx
  map_mem' := by
    rintro n _ ⟨x, hx, rfl⟩
    exact f.map_mem hx
  map_d' y := by
    induction y using Submodule.Quotient.induction_on with
    | H x => exact f.map_d x

@[simp]
theorem liftQ_mk (f : M →ᵈᵍ[A] N) (h : ∀ x ∈ S, f x = 0) (x : M) :
    liftQ f h (Submodule.Quotient.mk x) = f x := rfl

@[simp]
theorem liftQ_mkQ (f : M →ᵈᵍ[A] N) (h : ∀ x ∈ S, f x = 0) (x : M) :
    liftQ f h (S.mkQ x) = f x := rfl

@[simp]
theorem liftQ_comp_mkQ (f : M →ᵈᵍ[A] N) (h : ∀ x ∈ S, f x = 0) : (liftQ f h).comp S.mkQ = f :=
  rfl

/-- Two morphisms out of `M ⧸ S` agreeing after composition with the quotient map are equal. -/
theorem quotient_ext {f g : (M ⧸ S.toSubmodule) →ᵈᵍ[A] N} (h : f.comp S.mkQ = g.comp S.mkQ) :
    f = g :=
  DGModuleHom.ext fun y => by
    obtain ⟨x, rfl⟩ := S.mkQ_surjective y
    exact congrArg (fun φ : M →ᵈᵍ[A] N => φ x) h

end DGSubmodule

end DG
