import DG.Algebra.Decompose
import DG.Module.Basic

/-!
# dg submodules

A dg submodule of a dg `A`-module `M` is an `A`-submodule which is stable under the
differential and homogeneous (it contains the homogeneous components of each of its elements).
Such a submodule is itself a dg `A`-module, graded by `Sⁿ = S ∩ Mⁿ`, and the inclusion
`S →ᵈᵍ[A] M` is a morphism of dg modules.

* `DG.DGSubmodule A M`: the structure, extending `Submodule A M`.
* `DG.DGSubmodule.subtype`, `DG.DGSubmodule.codRestrict`: the inclusion and corestriction.
* `DG.DGModuleHom.ker`, `DG.DGModuleHom.range`: kernel and image of a morphism.

The decomposition of `S` into homogeneous components is obtained noncomputably from
`DirectSum.IsInternal`, which is proved using that the inclusion is injective of degree `0`
(`DG.coeAddMonoidHom_injective_of_injective`).
-/

open DirectSum

namespace DG

variable {A : Type*} {M : Type*} [Ring A] [DGAddCommGroup A] [AddCommGroup M]
  [DGAddCommGroup M] [Module A M]

/-- A dg submodule of a dg module: an `A`-submodule stable under `d` and containing the
homogeneous components of its elements. -/
structure DGSubmodule (A : Type*) (M : Type*) [Ring A] [DGAddCommGroup A] [AddCommGroup M]
    [DGAddCommGroup M] [Module A M] extends Submodule A M where
  d_mem' : ∀ {m : M}, m ∈ carrier → d m ∈ carrier
  decompose_mem' : ∀ (n : ℤ) {m : M}, m ∈ carrier →
    (decompose (grading (M := M)) m n : M) ∈ carrier

namespace DGSubmodule

instance : SetLike (DGSubmodule A M) M where
  coe S := S.carrier
  coe_injective S T h := by
    obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _, _⟩ := S
    obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _, _⟩ := T
    congr

instance : PartialOrder (DGSubmodule A M) := .ofSetLike (DGSubmodule A M) M

@[simp]
theorem mem_toSubmodule {S : DGSubmodule A M} {m : M} : m ∈ S.toSubmodule ↔ m ∈ S :=
  Iff.rfl

@[simp]
theorem mem_mk {p : Submodule A M} {h₁ h₂} {m : M} : m ∈ mk p h₁ h₂ ↔ m ∈ p :=
  Iff.rfl

@[ext]
theorem ext {S T : DGSubmodule A M} (h : ∀ m, m ∈ S ↔ m ∈ T) : S = T :=
  SetLike.ext h

theorem toSubmodule_injective :
    Function.Injective (DGSubmodule.toSubmodule : DGSubmodule A M → Submodule A M) :=
  fun _ _ h => ext fun m => by rw [← mem_toSubmodule, h, mem_toSubmodule]

variable (S : DGSubmodule A M)

theorem d_mem {m : M} (hm : m ∈ S) : d m ∈ S :=
  S.d_mem' hm

theorem decompose_mem (n : ℤ) {m : M} (hm : m ∈ S) :
    (decompose (grading (M := M)) m n : M) ∈ S :=
  S.decompose_mem' n hm

instance : AddSubgroupClass (DGSubmodule A M) M where
  add_mem := fun {S} => S.toSubmodule.add_mem
  zero_mem S := S.toSubmodule.zero_mem
  neg_mem := fun {S} => S.toSubmodule.neg_mem

instance : SMulMemClass (DGSubmodule A M) A M where
  smul_mem := fun {S} a => S.toSubmodule.smul_mem a

@[simp, norm_cast]
theorem coe_add (x y : S) : ((x + y : S) : M) = x + y := rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : S) : M) = 0 := rfl

@[simp, norm_cast]
theorem coe_smul (a : A) (x : S) : ((a • x : S) : M) = a • (x : M) := rfl

/-- The homogeneous components `Sⁿ = S ∩ Mⁿ` of a dg submodule. -/
def grading (n : ℤ) : AddSubgroup S :=
  (DGAddCommGroup.grading n).comap (AddSubgroupClass.subtype S)

theorem mem_grading_iff {n : ℤ} {x : S} : x ∈ S.grading n ↔ (x : M) ∈ DGAddCommGroup.grading n :=
  Iff.rfl

theorem isInternal_grading : DirectSum.IsInternal S.grading := by
  classical
  refine ⟨coeAddMonoidHom_injective_of_injective S.grading (AddSubgroupClass.subtype S)
    (fun _ _ hx => hx) Subtype.val_injective, fun x => ?_⟩
  refine ⟨∑ n ∈ (decompose (DGAddCommGroup.grading (M := M)) (x : M)).support,
    DirectSum.of (fun n => S.grading n) n
      ⟨⟨decompose (DGAddCommGroup.grading (M := M)) (x : M) n, S.decompose_mem n x.2⟩,
        (decompose (DGAddCommGroup.grading (M := M)) (x : M) n).2⟩, ?_⟩
  apply Subtype.ext
  rw [map_sum]
  simp only [DirectSum.coeAddMonoidHom_of]
  rw [AddSubmonoidClass.coe_finsetSum]
  exact DirectSum.sum_support_decompose (DGAddCommGroup.grading (M := M)) (x : M)

/-- The differential of a dg submodule. -/
def d : S →+ S :=
  AddMonoidHom.codRestrict ((DGAddCommGroup.d : M →+ M).comp (AddSubgroupClass.subtype S)) S
    fun x => S.d_mem x.2

@[simp]
theorem coe_d_apply (x : S) : (S.d x : M) = DGAddCommGroup.d (x : M) := rfl

noncomputable instance instDGAddCommGroup : DGAddCommGroup S where
  grading := S.grading
  decomposition := S.isInternal_grading.chooseDecomposition
  d := S.d
  d_mem' hx := DG.d_mem hx
  d_d' x := Subtype.ext (by simp)

@[simp]
theorem coe_d (x : S) : ((DGAddCommGroup.d x : S) : M) = DGAddCommGroup.d (x : M) := rfl

@[simp]
theorem mem_grading {n : ℤ} {x : S} :
    x ∈ DGAddCommGroup.grading n ↔ (x : M) ∈ DGAddCommGroup.grading n :=
  Iff.rfl

variable [DGModule A M]

instance instDGModule : DGModule A S where
  smul_mem _ _ _ _ ha hx := smul_mem_grading (M := M) ha hx
  d_smul' ha x := Subtype.ext (by
    rw [coe_d, coe_smul, d_smul ha (x : M)]
    simp only [coe_add, coe_smul]
    rfl)

/-- The inclusion of a dg submodule as a morphism of dg modules. -/
def subtype : S →ᵈᵍ[A] M where
  __ := S.toSubmodule.subtype
  map_mem' hx := hx
  map_d' _ := rfl

omit [DGModule A M] in
@[simp]
theorem subtype_apply (x : S) : S.subtype x = x := rfl

omit [DGModule A M] in
theorem subtype_injective : Function.Injective S.subtype :=
  Subtype.val_injective

variable {S} {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module A N]

omit [DGModule A M]

/-- Corestriction of a morphism of dg modules to a dg submodule containing its image. -/
def codRestrict (f : N →ᵈᵍ[A] M) (h : ∀ x, f x ∈ S) : N →ᵈᵍ[A] S where
  __ := LinearMap.codRestrict S.toSubmodule f.toLinearMap h
  map_mem' hx := f.map_mem hx
  map_d' x := Subtype.ext (f.map_d x)

@[simp]
theorem coe_codRestrict_apply (f : N →ᵈᵍ[A] M) (h : ∀ x, f x ∈ S) (x : N) :
    (codRestrict f h x : M) = f x := rfl

@[simp]
theorem subtype_comp_codRestrict (f : N →ᵈᵍ[A] M) (h : ∀ x, f x ∈ S) :
    S.subtype.comp (codRestrict f h) = f := rfl

/-- The decomposition of `S` is the restriction of that of `M`. -/
theorem coe_decompose_apply (x : S) (n : ℤ) :
    ((decompose (DGAddCommGroup.grading (M := S)) x n : S) : M) =
      decompose (DGAddCommGroup.grading (M := M)) (x : M) n :=
  (coe_decompose_map_of_map_mem S.subtype.toLinearMap.toAddMonoidHom
    (fun hx => S.subtype.map_mem hx) x n).symm

end DGSubmodule

namespace DGModuleHom

variable {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module A N] (f : M →ᵈᵍ[A] N)

/-- The kernel of a morphism of dg modules, as a dg submodule. -/
def ker : DGSubmodule A M where
  __ := LinearMap.ker f.toLinearMap
  d_mem' := fun {m} hm => by
    have hm' : f m = 0 := hm
    show f (d m) = 0
    rw [map_d, hm', d_zero]
  decompose_mem' := fun n {m} hm => by
    have hm' : f m = 0 := hm
    show f _ = 0
    refine (coe_decompose_map_of_map_mem f.toLinearMap.toAddMonoidHom
      (fun hx => f.map_mem hx) m n).symm.trans ?_
    change (decompose (grading (M := N)) (f m) n : N) = 0
    rw [hm', decompose_zero,
      DirectSum.zero_apply, ZeroMemClass.coe_zero]

@[simp]
theorem mem_ker {m : M} : m ∈ f.ker ↔ f m = 0 :=
  Iff.rfl

/-- The image of a morphism of dg modules, as a dg submodule. -/
def range : DGSubmodule A N where
  __ := LinearMap.range f.toLinearMap
  d_mem' := fun {x} hx => by
    obtain ⟨m, rfl⟩ : ∃ m, f m = x := hx
    exact ⟨d m, by simp⟩
  decompose_mem' := fun n {x} hx => by
    obtain ⟨m, rfl⟩ : ∃ m, f m = x := hx
    exact ⟨decompose (grading (M := M)) m n,
      (coe_decompose_map_of_map_mem f.toLinearMap.toAddMonoidHom (fun hx => f.map_mem hx) m n).symm⟩

@[simp]
theorem mem_range {n : N} : n ∈ f.range ↔ ∃ m, f m = n :=
  Iff.rfl

theorem apply_mem_range (m : M) : f m ∈ f.range :=
  ⟨m, rfl⟩

/-- A morphism of dg modules corestricted to its image. -/
def rangeRestrict : M →ᵈᵍ[A] f.range :=
  DGSubmodule.codRestrict f f.apply_mem_range

@[simp]
theorem coe_rangeRestrict_apply (m : M) : (f.rangeRestrict m : N) = f m := rfl

end DGModuleHom

end DG
