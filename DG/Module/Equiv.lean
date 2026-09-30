import DG.Module.Basic

/-!
# Isomorphisms of dg modules

* `DGModuleEquiv A M N` (notation `M ≃ᵈᵍ[A] N`): an `A`-linear equivalence of degree `0`
  commuting with the differentials. Its inverse is automatically a morphism of dg modules
  (`DGModuleEquiv.symm`): a bijective graded map of degree `0` has a graded inverse, which is
  proved through the uniqueness of homogeneous decompositions
  (`DGModuleHom.mem_grading_of_injective`).

The API is deliberately small: `refl`, `symm`, `trans`, `toDGModuleHom` and the evaluation
lemmas.
-/

open DirectSum

namespace DG

section Decompose

variable {A : Type*} {M N : Type*} [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N]

/-- A morphism of dg modules commutes with the homogeneous decompositions. -/
theorem DGModuleHom.coe_decompose_apply (f : M →ᵈᵍ[A] N) (m : M) (j : ℤ) :
    (decompose (grading (M := N)) (f m) j : N) = f (decompose (grading (M := M)) m j) := by
  induction m using induction_on with
  | h_zero => simp
  | h_homogeneous x =>
    rename_i i
    rw [decompose_of_mem _ (f.map_mem x.2), decompose_coe]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [of_eq_of_ne _ _ _ (Ne.symm hij)]
  | h_add m m' hm hm' => simp [decompose_add, hm, hm']

/-- An injective morphism of dg modules reflects the grading: if `f m` is homogeneous of
degree `k`, so is `m`. -/
theorem DGModuleHom.mem_grading_of_injective (f : M →ᵈᵍ[A] N) (hf : Function.Injective f)
    {k : ℤ} {m : M} (hm : f m ∈ grading k) : m ∈ grading k := by
  set ℳ := grading (M := M)
  have key : ∀ j, j ≠ k → decompose ℳ m j = 0 := fun j hj => by
    refine Subtype.ext (hf ?_)
    rw [← f.coe_decompose_apply, decompose_of_mem_ne _ hm (Ne.symm hj), ZeroMemClass.coe_zero,
      map_zero]
  have h : decompose ℳ m = DirectSum.of (fun i => ℳ i) k (decompose ℳ m k) := by
    refine DirectSum.ext fun j => ?_
    by_cases hjk : j = k
    · subst hjk
      rw [of_eq_same]
    · rw [of_eq_of_ne _ _ _ hjk, key j hjk]
  have h' := congrArg (decompose ℳ).symm h
  rw [Equiv.symm_apply_apply, decompose_symm_of] at h'
  rw [h']
  exact (decompose ℳ m k).2

end Decompose

/-- An isomorphism of dg `A`-modules: an `A`-linear equivalence of degree `0` commuting with
the differentials. -/
structure DGModuleEquiv (A : Type*) (M : Type*) (N : Type*) [Ring A] [DGAddCommGroup A]
    [AddCommGroup M] [DGAddCommGroup M] [Module A M]
    [AddCommGroup N] [DGAddCommGroup N] [Module A N] extends M ≃ₗ[A] N where
  map_mem' : ∀ {n : ℤ} {m : M}, m ∈ grading n → toFun m ∈ grading n
  map_d' : ∀ m : M, toFun (d m) = d (toFun m)

@[inherit_doc]
notation:25 M " ≃ᵈᵍ[" A "] " N => DGModuleEquiv A M N

namespace DGModuleEquiv

variable {A : Type*} {M N P : Type*} [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N]
  [AddCommGroup P] [DGAddCommGroup P] [Module A P]

instance : EquivLike (M ≃ᵈᵍ[A] N) M N where
  coe e := e.toFun
  inv e := e.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' e e' h _ := by
    rcases e with ⟨e, _, _⟩
    rcases e' with ⟨e', _, _⟩
    obtain rfl : e = e' := LinearEquiv.ext (congrFun h)
    rfl

instance : LinearEquivClass (M ≃ᵈᵍ[A] N) A M N where
  map_add e := e.map_add'
  map_smulₛₗ e := e.map_smul'

@[simp]
theorem coe_toLinearEquiv (e : M ≃ᵈᵍ[A] N) : ⇑e.toLinearEquiv = e := rfl

@[ext]
theorem ext {e e' : M ≃ᵈᵍ[A] N} (h : ∀ m, e m = e' m) : e = e' :=
  DFunLike.ext e e' h

theorem map_mem (e : M ≃ᵈᵍ[A] N) {n : ℤ} {m : M} (hm : m ∈ grading n) : e m ∈ grading n :=
  e.map_mem' hm

@[simp]
theorem map_d (e : M ≃ᵈᵍ[A] N) (m : M) : e (d m) = d (e m) :=
  e.map_d' m

/-- The underlying morphism of dg modules of an isomorphism. -/
def toDGModuleHom (e : M ≃ᵈᵍ[A] N) : M →ᵈᵍ[A] N where
  __ := e.toLinearEquiv.toLinearMap
  map_mem' := e.map_mem'
  map_d' := e.map_d'

@[simp]
theorem coe_toDGModuleHom (e : M ≃ᵈᵍ[A] N) : ⇑e.toDGModuleHom = e := rfl

theorem injective (e : M ≃ᵈᵍ[A] N) : Function.Injective e :=
  EquivLike.injective e

theorem surjective (e : M ≃ᵈᵍ[A] N) : Function.Surjective e :=
  EquivLike.surjective e

/-- The identity isomorphism. -/
def refl : M ≃ᵈᵍ[A] M where
  __ := LinearEquiv.refl A M
  map_mem' hm := hm
  map_d' _ := rfl

@[simp]
theorem refl_apply (m : M) : (refl : M ≃ᵈᵍ[A] M) m = m := rfl

/-- The inverse of an isomorphism of dg modules. -/
def symm (e : M ≃ᵈᵍ[A] N) : N ≃ᵈᵍ[A] M where
  __ := e.toLinearEquiv.symm
  map_mem' {_ y} hy := by
    refine e.toDGModuleHom.mem_grading_of_injective e.injective ?_
    change e (e.toLinearEquiv.symm y) ∈ grading _
    rwa [← coe_toLinearEquiv, LinearEquiv.apply_symm_apply]
  map_d' y := by
    apply e.injective
    change e (e.toLinearEquiv.symm (d y)) = e (d (e.toLinearEquiv.symm y))
    rw [map_d, ← coe_toLinearEquiv, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

@[simp]
theorem apply_symm_apply (e : M ≃ᵈᵍ[A] N) (y : N) : e (e.symm y) = y :=
  e.right_inv y

@[simp]
theorem symm_apply_apply (e : M ≃ᵈᵍ[A] N) (m : M) : e.symm (e m) = m :=
  e.left_inv m

@[simp]
theorem symm_symm (e : M ≃ᵈᵍ[A] N) : e.symm.symm = e := rfl

/-- Composition of isomorphisms of dg modules. -/
def trans (e : M ≃ᵈᵍ[A] N) (e' : N ≃ᵈᵍ[A] P) : M ≃ᵈᵍ[A] P where
  __ := e.toLinearEquiv.trans e'.toLinearEquiv
  map_mem' hm := e'.map_mem (e.map_mem hm)
  map_d' m := by
    change e' (e (d m)) = d (e' (e m))
    rw [map_d, map_d]

@[simp]
theorem trans_apply (e : M ≃ᵈᵍ[A] N) (e' : N ≃ᵈᵍ[A] P) (m : M) : e.trans e' m = e' (e m) := rfl

end DGModuleEquiv

end DG
