import DG.Derived.TStructure
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The heart of the standard t-structure

Let `A` be a dg ring concentrated in non-positive degrees (`DG.IsNonposGraded A`), and let
`H⁰A := A ⧸ (A^{< 0} ⊕ d(A⁻¹))` be the quotient dg ring of `DG/Examples/Truncation.lean`
(`DG.truncGEZeroIdeal`): it is concentrated in degree `0` with zero differential, and its
underlying group is `H⁰(A) = A⁰ ⧸ d(A⁻¹)` (`DG.cohomologyZeroAddEquivTruncGEZero`). This file
shows that the heart of the standard t-structure on `D(A)` (`DG.DerivedCategory.tStructure`) is
the category of (left) `H⁰A`-modules.

## Main definitions and results

* `DG.DegreeZeroModule hA N`: an `H⁰A`-module `N` regarded as a dg `A`-module concentrated in
  degree `0`, with zero differential and `A` acting through `A → H⁰A`;
  `DG.degreeZeroModuleFunctor hA : ModuleCat H⁰A ⥤ DGModuleCat A`.
* `DG.DerivedCategory.heartFunctor hA : ModuleCat H⁰A ⥤ D(A)`, the composite with `Q`. It is
  fully faithful (`heartFunctor_full`, `heartFunctor_faithful`) and its essential image is the
  heart (`essImage_heartFunctor`); `DG.DerivedCategory.tStructureHeart hA` packages this as
  Mathlib's `TStructure.Heart` structure: the heart of the standard t-structure is
  `ModuleCat H⁰A`.

## Proofs

Full faithfulness: a semi-free resolution `P → N` concentrated in non-positive degrees
(`DG/Derived/ConnectiveResolution.lean`) is surjective, and a morphism of dg modules `P → N'`
to a module concentrated in degree `0` kills the kernel of `P → N` (a degree-`0` element of the
kernel is a coboundary, since `P¹ = 0` and `P → N` is a quasi-isomorphism), so it factors
uniquely through `N`; homotopies `P → N'` vanish for degree reasons.

Essential image: an object of the heart is `Q P` with `P` semi-free concentrated in
non-positive degrees and cohomology concentrated in degree `0`. The elements of `P` whose
degree-`0` component is a coboundary form an acyclic dg submodule `T`, and
`P → P ⧸ T = H⁰(P)` is a quasi-isomorphism onto a module concentrated in degree `0` killed by
`A^{< 0} ⊕ d(A⁻¹)`, i.e. an `H⁰A`-module.

## References

* [A. Beilinson, J. Bernstein, P. Deligne, *Faisceaux pervers*, Astérisque 100 (1982), §1.3]
* [B. Keller, *Deriving DG categories*, Ann. Sci. ÉNS 27 (1994)]
-/

open CategoryTheory Limits DirectSum

universe w v u

set_option backward.isDefEq.respectTransparency false

namespace DG

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] (hA : IsNonposGraded A)

/-! ### Elements of `A` acting trivially on `H⁰A`-modules -/

section Ideal

include hA in
theorem mkRingHom_truncGEZeroIdeal_eq_zero_of_ne {i : ℤ} (hi : i ≠ 0) {a : A}
    (ha : a ∈ grading i) : DGIdeal.Quotient.mkRingHom (truncGEZeroIdeal hA) a = 0 := by
  rw [DGIdeal.Quotient.mkRingHom_eq_zero_iff_mem, mem_truncGEZeroIdeal_iff_of_mem_grading hA ha]
  exact fun h => absurd h hi

include hA in
theorem mkRingHom_truncGEZeroIdeal_d (a : A) :
    DGIdeal.Quotient.mkRingHom (truncGEZeroIdeal hA) (d a) = 0 :=
  (DGIdeal.Quotient.mkRingHom_eq_zero_iff_mem _).mpr (truncGEZero_d_mem a)

end Ideal

/-! ### Modules over `H⁰A` as dg modules -/

/-- An `H⁰A`-module, for `H⁰A = A ⧸ truncGEZeroIdeal hA`, regarded as a dg `A`-module
concentrated in degree `0` with zero differential (a type synonym). -/
@[nolint unusedArguments]
def DegreeZeroModule (_hA : IsNonposGraded A) (N : Type*) : Type _ := N

namespace DegreeZeroModule

variable (N : Type*) [AddCommGroup N] [Module (A ⧸ truncGEZeroIdeal hA) N]

instance : AddCommGroup (DegreeZeroModule hA N) := inferInstanceAs (AddCommGroup N)

instance : Module (A ⧸ truncGEZeroIdeal hA) (DegreeZeroModule hA N) :=
  inferInstanceAs (Module (A ⧸ truncGEZeroIdeal hA) N)

/-- `A` acts through `A → H⁰A`. -/
instance : Module A (DegreeZeroModule hA N) :=
  Module.compHom N (DGIdeal.Quotient.mkRingHom (truncGEZeroIdeal hA))

/-- The grading concentrated in degree `0`, with zero differential. -/
noncomputable instance : DGAddCommGroup (DegreeZeroModule hA N) := DGAddCommGroup.degreeZero N

variable {hA N}

/-- The identity `N → DegreeZeroModule hA N`. -/
def mk : N ≃+ DegreeZeroModule hA N := AddEquiv.refl N

theorem smul_def (a : A) (x : DegreeZeroModule hA N) :
    a • x = (DGIdeal.Quotient.mkRingHom (truncGEZeroIdeal hA) a • x : DegreeZeroModule hA N) := rfl

omit [DGRing A] [Module (A ⧸ truncGEZeroIdeal hA) N] in
theorem mem_grading_iff {n : ℤ} {x : DegreeZeroModule hA N} :
    x ∈ grading n ↔ n = 0 ∨ x = 0 :=
  mem_degreeZeroGrading_iff N

omit [DGRing A] [Module (A ⧸ truncGEZeroIdeal hA) N] in
theorem mem_grading_zero (x : DegreeZeroModule hA N) : x ∈ grading 0 :=
  mem_grading_iff.mpr (Or.inl rfl)

omit [DGRing A] [Module (A ⧸ truncGEZeroIdeal hA) N] in
theorem eq_zero_of_mem_grading {n : ℤ} (hn : n ≠ 0) {x : DegreeZeroModule hA N}
    (hx : x ∈ grading n) : x = 0 :=
  (mem_grading_iff.mp hx).resolve_left hn

omit [DGRing A] [Module (A ⧸ truncGEZeroIdeal hA) N] in
@[simp]
theorem d_apply (x : DegreeZeroModule hA N) : d x = 0 := rfl

instance : DGModule A (DegreeZeroModule hA N) where
  smul_mem {i j} a x ha hx := by
    rcases mem_grading_iff.mp hx with rfl | rfl
    · by_cases hi : i = 0
      · subst hi
        exact mem_grading_zero _
      · rw [smul_def, mkRingHom_truncGEZeroIdeal_eq_zero_of_ne hA hi ha, zero_smul]
        exact zero_mem _
    · rw [smul_zero]
      exact zero_mem _
  d_smul' {_ a} _ x := by
    rw [d_apply, d_apply, smul_zero, smul_zero, add_zero, smul_def,
      mkRingHom_truncGEZeroIdeal_d hA, zero_smul]

/-- An `H⁰A`-linear map as a morphism of dg modules. -/
def map {N' : Type*} [AddCommGroup N'] [Module (A ⧸ truncGEZeroIdeal hA) N']
    (f : N →ₗ[A ⧸ truncGEZeroIdeal hA] N') :
    DegreeZeroModule hA N →ᵈᵍ[A] DegreeZeroModule hA N' where
  toFun := f
  map_add' := f.map_add
  map_smul' a x := f.map_smul (DGIdeal.Quotient.mkRingHom (truncGEZeroIdeal hA) a) x
  map_mem' {n x} hx := by
    rcases mem_grading_iff.mp hx with rfl | rfl
    · exact mem_grading_zero _
    · exact (map_zero f).symm ▸ zero_mem _
  map_d' x := by
    change f 0 = 0
    exact map_zero f

@[simp]
theorem map_apply {N' : Type*} [AddCommGroup N'] [Module (A ⧸ truncGEZeroIdeal hA) N']
    (f : N →ₗ[A ⧸ truncGEZeroIdeal hA] N') (x : DegreeZeroModule hA N) : map f x = f x := rfl

omit [DGRing A] [Module (A ⧸ truncGEZeroIdeal hA) N] in
/-- `Hⁿ(DegreeZeroModule hA N) = 0` for `n ≠ 0`. -/
theorem subsingleton_cohomology {n : ℤ} (hn : n ≠ 0) :
    Subsingleton (cohomology (DegreeZeroModule hA N) n) :=
  subsingleton_cohomology_iff.mpr fun m hm _ => by
    rw [eq_zero_of_mem_grading hn hm]
    exact zero_mem _

end DegreeZeroModule

variable (A) in
/-- `H⁰A`-modules as dg `A`-modules concentrated in degree `0`. -/
@[simps]
noncomputable def degreeZeroModuleFunctor :
    ModuleCat.{v} (A ⧸ truncGEZeroIdeal hA) ⥤ DGModuleCat.{v} A where
  obj N := DGModuleCat.of A (DegreeZeroModule hA N)
  map f := DGModuleCat.ofHom (DegreeZeroModule.map f.hom)

/-! ### Morphisms from modules concentrated in non-positive degrees -/

section Factor

variable {hA} {P : Type*} [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]
  {N N' : Type*} [AddCommGroup N] [Module (A ⧸ truncGEZeroIdeal hA) N]
  [AddCommGroup N'] [Module (A ⧸ truncGEZeroIdeal hA) N']

omit [DGModule A P] in
/-- A morphism into a module concentrated in degree `0` only sees degree-`0` components. -/
theorem DegreeZeroModule.apply_eq_apply_decompose_zero (g : P →ᵈᵍ[A] DegreeZeroModule hA N')
    (x : P) : g x = g (decompose (grading (M := P)) x 0) := by
  rw [← g.coe_decompose_apply, decompose_of_mem_same _ (DegreeZeroModule.mem_grading_zero _)]

omit [DGModule A P] in
/-- Let `π : P → N` be a quasi-isomorphism with `P` concentrated in non-positive degrees and `N`
concentrated in degree `0`. Every morphism `P → N'` to a module concentrated in degree `0`
vanishes on the kernel of `π`. -/
theorem DegreeZeroModule.apply_eq_zero_of_isQuasiIso (hP : IsNonposGraded P)
    (π : P →ᵈᵍ[A] DegreeZeroModule hA N) (hπ : π.IsQuasiIso)
    (g : P →ᵈᵍ[A] DegreeZeroModule hA N') {x : P} (hx : π x = 0) : g x = 0 := by
  rw [apply_eq_apply_decompose_zero]
  set x₀ := (decompose (grading (M := P)) x 0 : P)
  have hx₀ : x₀ ∈ grading 0 := SetLike.coe_mem _
  have hdx₀ : d x₀ = 0 := hP.eq_zero one_pos (by simpa using d_mem hx₀)
  have hπx₀ : π x₀ = 0 := by
    rw [← π.coe_decompose_apply, hx, decompose_zero, DirectSum.zero_apply,
      ZeroMemClass.coe_zero]
  obtain ⟨y, -, hy⟩ := mem_coboundaries.mp
    ((cohomology.map_injective_iff π 0).mp (hπ 0).1 x₀ hx₀ hdx₀
      (by rw [hπx₀]; exact zero_mem _))
  rw [← hy, DGModuleHom.map_d, DegreeZeroModule.d_apply]

/-- Homotopic morphisms from a module concentrated in non-positive degrees to a module
concentrated in degree `0` are equal. -/
theorem DegreeZeroModule.eq_of_homotopic (hP : IsNonposGraded P)
    {g₁ g₂ : P →ᵈᵍ[A] DegreeZeroModule hA N'} (h : Homotopic g₁ g₂) : g₁ = g₂ := by
  ext x
  rw [apply_eq_apply_decompose_zero g₁, apply_eq_apply_decompose_zero g₂]
  set x₀ := (decompose (grading (M := P)) x 0 : P)
  have hx₀ : x₀ ∈ grading 0 := SetLike.coe_mem _
  have hdx₀ : d x₀ = 0 := hP.eq_zero one_pos (by simpa using d_mem hx₀)
  have := congrArg (fun φ => φ (cohomology.mkOf hx₀ hdx₀)) (h.cohomology_map_eq 0)
  rw [cohomology.mkOf_eq_mk, cohomology.map_mk, cohomology.map_mk, cohomology.mk_eq_mk_iff]
    at this
  obtain ⟨y, -, hy⟩ := mem_coboundaries.mp this
  rw [← sub_eq_zero, ← hy, DegreeZeroModule.d_apply]

variable (π : P →ᵈᵍ[A] DegreeZeroModule hA N) (hπ : Function.Surjective π)
  (g : P →ᵈᵍ[A] DegreeZeroModule hA N') (hg : ∀ x, π x = 0 → g x = 0)

include hg in
omit [DGModule A P] in
theorem DegreeZeroModule.apply_eq_apply_of_eq {x y : P} (h : π x = π y) : g x = g y := by
  rw [← sub_eq_zero, ← map_sub]
  exact hg _ (by rw [map_sub, h, sub_self])

/-- A morphism `g : P → N'` vanishing on the kernel of a surjection `π : P → N`, between modules
concentrated in degree `0`, factors through an `H⁰A`-linear map `N → N'`. -/
noncomputable def DegreeZeroModule.factor : N →ₗ[A ⧸ truncGEZeroIdeal hA] N' where
  toFun n := mk.symm (g (Function.surjInv hπ (mk n)))
  map_add' n n' := by
    change (g _ : DegreeZeroModule hA N') = g _ + g _
    rw [← map_add]
    refine apply_eq_apply_of_eq π g hg ?_
    rw [Function.surjInv_eq hπ, map_add π, Function.surjInv_eq hπ, Function.surjInv_eq hπ]
    rfl
  map_smul' r n := by
    obtain ⟨a, rfl⟩ := DGIdeal.Quotient.mkRingHom_surjective (truncGEZeroIdeal hA) r
    have h1 : g (Function.surjInv hπ (mk (DGIdeal.Quotient.mkRingHom _ a • n))) =
        g (a • Function.surjInv hπ (mk n)) :=
      apply_eq_apply_of_eq π g hg (by
        rw [map_smul π, Function.surjInv_eq hπ, Function.surjInv_eq hπ]
        rfl)
    rw [RingHom.id_apply]
    exact h1.trans (map_smul g a _)

omit [DGModule A P] in
theorem DegreeZeroModule.factor_apply (x : P) :
    DegreeZeroModule.factor π hπ g hg (π x) = g x :=
  apply_eq_apply_of_eq π g hg (Function.surjInv_eq hπ _)

end Factor

/-! ### The degree-`0` quotient of a module concentrated in non-positive degrees -/

section Quotient

variable {P : Type*} [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]

variable (P) in
/-- The components of the submodule `P^{< 0} ⊕ d(P⁻¹)`: the coboundaries in degree `0`, and
everything in the other degrees. -/
def degreeZeroQuotientComponents (n : ℤ) : AddSubgroup P :=
  if n = 0 then coboundaries P 0 else ⊤

omit [DGModule A P] in
theorem mem_degreeZeroQuotientComponents_iff {k : ℤ} {x : P} (hx : x ∈ grading k) :
    x ∈ ofComponents (degreeZeroQuotientComponents P) ↔ (k = 0 → x ∈ coboundaries P 0) := by
  rw [mem_ofComponents_of_mem_grading hx, degreeZeroQuotientComponents]
  by_cases h : k = 0 <;> simp [h]

variable (hP : IsNonposGraded P)

omit [DGRing A] in
include hA hP in
theorem degreeZeroQuotient_smul_mem (a : A) {x : P}
    (hx : x ∈ ofComponents (degreeZeroQuotientComponents P)) :
    a • x ∈ ofComponents (degreeZeroQuotientComponents P) := by
  refine induction_on_of_isHomogeneous (isHomogeneous_ofComponents _)
    (P := fun x => a • x ∈ ofComponents (degreeZeroQuotientComponents P)) (by simp [zero_mem]) ?_
    (fun x x' h h' => by simpa only [smul_add] using add_mem h h') hx
  intro k x hxk hxS
  induction a using induction_on with
  | h_zero => simp [zero_mem]
  | h_add a a' ha ha' => rw [add_smul]; exact add_mem ha ha'
  | h_homogeneous a =>
    obtain ⟨a, ha⟩ := a
    rename_i i
    change a • x ∈ _
    rw [mem_degreeZeroQuotientComponents_iff hxk] at hxS
    rw [mem_degreeZeroQuotientComponents_iff (smul_mem_grading ha hxk)]
    intro hik
    by_cases hi : 0 < i
    · rw [hA.eq_zero hi ha, zero_smul]
      exact zero_mem _
    by_cases hk : 0 < k
    · rw [hP.eq_zero hk hxk, smul_zero]
      exact zero_mem _
    obtain rfl : i = 0 := by omega
    obtain rfl : k = 0 := by omega
    obtain ⟨y, hy, rfl⟩ := hxS rfl
    refine ⟨a • y, by simpa using smul_mem_grading ha hy, ?_⟩
    rw [d_smul_of_mem_zero ha, hA.eq_zero one_pos (d_mem ha), zero_smul, zero_add]

omit [DGModule A P] in
theorem degreeZeroQuotient_d_mem (x : P) :
    d x ∈ ofComponents (degreeZeroQuotientComponents P) := by
  induction x using induction_on with
  | h_zero => rw [d_zero]; exact zero_mem _
  | h_add x y hx hy => rw [d_add]; exact add_mem hx hy
  | h_homogeneous x =>
    obtain ⟨x, hx⟩ := x
    rename_i i
    rw [mem_degreeZeroQuotientComponents_iff (d_mem hx)]
    intro h
    obtain rfl : i = 0 - 1 := by omega
    exact ⟨x, hx, rfl⟩

variable (P) in
/-- The submodule `P^{< 0} ⊕ d(P⁻¹)` (together with `P^{> 0} = 0`) of a dg module concentrated in
non-positive degrees over a dg ring concentrated in non-positive degrees. The quotient is
`H⁰(P)`, concentrated in degree `0`. -/
def degreeZeroQuotientSubmodule : Submodule A P where
  carrier := ofComponents (degreeZeroQuotientComponents P)
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' a _ hx := degreeZeroQuotient_smul_mem hA hP a hx

omit [DGRing A] in
theorem mem_degreeZeroQuotientSubmodule_of_ne {k : ℤ} (hk : k ≠ 0) {x : P}
    (hx : x ∈ grading k) : x ∈ degreeZeroQuotientSubmodule hA P hP :=
  (mem_degreeZeroQuotientComponents_iff hx).mpr fun h => absurd h hk

omit [DGRing A] in
theorem mem_degreeZeroQuotientSubmodule_iff {x : P} (hx : x ∈ grading 0) :
    x ∈ degreeZeroQuotientSubmodule hA P hP ↔ x ∈ coboundaries P 0 :=
  (mem_degreeZeroQuotientComponents_iff hx).trans ⟨fun h => h rfl, fun h _ => h⟩

/-- The ideal `A^{< 0} ⊕ d(A⁻¹)` annihilates `P ⧸ (P^{< 0} ⊕ d(P⁻¹))`. -/
theorem isTorsionBySet_degreeZeroQuotient :
    Module.IsTorsionBySet A (P ⧸ degreeZeroQuotientSubmodule hA P hP)
      (truncGEZeroIdeal hA).toIdeal := by
  rintro y ⟨a, ha⟩
  induction y using Submodule.Quotient.induction_on with
  | H x =>
  change Submodule.Quotient.mk (a • x) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  refine induction_on_of_isHomogeneous (truncGEZeroIdeal hA).isHomogeneous
    (P := fun a => a • x ∈ degreeZeroQuotientSubmodule hA P hP) (by simp [zero_mem]) ?_
    (fun a a' h h' => by simpa only [add_smul] using add_mem h h') ha
  intro i a hai haI
  induction x using induction_on with
  | h_zero => simp [zero_mem]
  | h_add x x' hx hx' => rw [smul_add]; exact add_mem hx hx'
  | h_homogeneous x =>
    obtain ⟨x, hx⟩ := x
    rename_i k
    change a • x ∈ _
    by_cases hik : i + k = 0
    · by_cases hi : 0 < i
      · rw [hA.eq_zero hi hai, zero_smul]
        exact zero_mem _
      by_cases hk : 0 < k
      · rw [hP.eq_zero hk hx, smul_zero]
        exact zero_mem _
      obtain rfl : i = 0 := by omega
      obtain rfl : k = 0 := by omega
      rw [mem_degreeZeroQuotientSubmodule_iff hA hP (by simpa using smul_mem_grading hai hx)]
      obtain ⟨b, hb, rfl⟩ := (mem_truncGEZeroIdeal_iff_of_mem_grading hA hai).mp
        (show a ∈ truncGEZeroIdeal hA from haI) rfl
      refine ⟨b • x, by simpa using smul_mem_grading hb hx, ?_⟩
      rw [d_smul hb, hP.eq_zero (x := d x) one_pos (by simpa using d_mem hx), smul_zero,
        smul_zero, add_zero]
    · exact mem_degreeZeroQuotientSubmodule_of_ne hA hP hik (smul_mem_grading hai hx)

/-- `H⁰(P) = P ⧸ (P^{< 0} ⊕ d(P⁻¹))` as an `H⁰A`-module. -/
@[instance_reducible]
noncomputable def degreeZeroQuotientModule :
    Module (A ⧸ truncGEZeroIdeal hA) (P ⧸ degreeZeroQuotientSubmodule hA P hP) :=
  (isTorsionBySet_degreeZeroQuotient hA hP).module

/-- The projection `P → H⁰(P)`, as a morphism of dg modules to a module concentrated in
degree `0`. -/
noncomputable def degreeZeroQuotientπ :
    letI := degreeZeroQuotientModule hA hP
    P →ᵈᵍ[A] DegreeZeroModule hA (P ⧸ degreeZeroQuotientSubmodule hA P hP) :=
  letI := degreeZeroQuotientModule hA hP
  { toFun := fun x => DegreeZeroModule.mk (Submodule.Quotient.mk x)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    map_mem' := fun {n x} hx => by
      by_cases hn : n = 0
      · subst hn
        exact DegreeZeroModule.mem_grading_zero _
      · rw [(Submodule.Quotient.mk_eq_zero _).mpr
          (mem_degreeZeroQuotientSubmodule_of_ne hA hP hn hx)]
        exact zero_mem _
    map_d' := fun x => (Submodule.Quotient.mk_eq_zero _).mpr (degreeZeroQuotient_d_mem x) }

/-- If the cohomology of `P` is concentrated in degree `0`, the projection `P → H⁰(P)` is a
quasi-isomorphism. -/
theorem isQuasiIso_degreeZeroQuotientπ (hH : ∀ k, k ≠ 0 → Subsingleton (cohomology P k)) :
    letI := degreeZeroQuotientModule hA hP
    (degreeZeroQuotientπ hA hP).IsQuasiIso := by
  let := degreeZeroQuotientModule hA hP
  intro k
  by_cases hk : k = 0
  · subst hk
    constructor
    · rw [cohomology.map_injective_iff]
      intro x hx _ hπx
      obtain ⟨y, -, hy⟩ := mem_coboundaries.mp hπx
      rw [DegreeZeroModule.d_apply] at hy
      exact (mem_degreeZeroQuotientSubmodule_iff hA hP hx).mp
        ((Submodule.Quotient.mk_eq_zero _).mp hy.symm)
    · rw [cohomology.map_surjective_iff]
      intro y _ _
      obtain ⟨x, hxy⟩ := Submodule.Quotient.mk_surjective _ (DegreeZeroModule.mk.symm y)
      have hy : degreeZeroQuotientπ hA hP x = y := by
        rw [← DegreeZeroModule.mk.apply_symm_apply y, ← hxy]
        rfl
      set x₀ := (decompose (grading (M := P)) x 0 : P)
      have hx₀ : x₀ ∈ grading 0 := SetLike.coe_mem _
      refine ⟨x₀, hx₀, hP.eq_zero one_pos (by simpa using d_mem hx₀), ?_⟩
      have : degreeZeroQuotientπ hA hP x₀ = degreeZeroQuotientπ hA hP x := by
        rw [DegreeZeroModule.apply_eq_apply_decompose_zero (degreeZeroQuotientπ hA hP) x]
      rw [this, hy, sub_self]
      exact zero_mem _
  · have := hH k hk
    have := DegreeZeroModule.subsingleton_cohomology (hA := hA)
      (N := P ⧸ degreeZeroQuotientSubmodule hA P hP) hk
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

end Quotient

/-! ### The heart -/

instance : (degreeZeroModuleFunctor.{v} A hA).Additive where
  map_add {_ _ f g} := DGModuleCat.hom_ext_apply fun x => LinearMap.add_apply f.hom g.hom x

namespace DerivedCategory

variable [HasDerivedCategory.{w, max u v} A]

/-- The functor `ModuleCat H⁰A ⥤ D(A)`, `N ↦ N` concentrated in degree `0`. -/
noncomputable def heartFunctor :
    ModuleCat.{max u v} (A ⧸ truncGEZeroIdeal hA) ⥤ DerivedCategory.{w, max u v} A :=
  degreeZeroModuleFunctor.{max u v} A hA ⋙ Q

instance : (heartFunctor.{w, v} hA).Additive := by
  dsimp only [heartFunctor]
  infer_instance

section Resolution

variable (N : Type (max u v)) [AddCommGroup N] [Module (A ⧸ truncGEZeroIdeal hA) N]

omit [DGRing A] [HasDerivedCategory A] [Module (A ⧸ truncGEZeroIdeal hA) N] in
theorem isNonposGraded_degreeZeroModule : IsNonposGraded (DegreeZeroModule hA N) :=
  isNonposGraded_iff.mpr fun _ hn _ hx => DegreeZeroModule.eq_zero_of_mem_grading hn.ne' hx

omit [HasDerivedCategory A] in
theorem surjective_resolution_π :
    Function.Surjective (ConnectiveResolution.π A (DegreeZeroModule hA N)) := fun y => by
  obtain ⟨e, -, -, he⟩ := ConnectiveResolution.exists_stage_one (A := A) le_rfl
    (DegreeZeroModule.mem_grading_zero y) (DegreeZeroModule.d_apply y)
  exact ⟨SeqColimit.of _ _ 1 e, by rw [ConnectiveResolution.π_of, he]⟩

end Resolution

instance heartFunctor_full : (heartFunctor.{w, v} hA).Full where
  map_surjective {N N'} φ := by
    let M := DegreeZeroModule hA N
    have hP := ConnectiveResolution.isNonposGraded_colim A M hA
    have hπ := ConnectiveResolution.isQuasiIso_π A M hA (isNonposGraded_degreeZeroModule hA N)
    have hK := (ConnectiveResolution.semiFreeFiltration A M).isKProjective
    let πc : DGModuleCat.of A (ConnectiveResolution.Colim A M) ⟶
        (degreeZeroModuleFunctor A hA).obj N :=
      DGModuleCat.ofHom (ConnectiveResolution.π A M)
    have : IsIso (Q.map πc) := (isIso_Q_map_iff _).mpr hπ
    obtain ⟨g, hg⟩ := exists_Q_map_eq hK (Q.map πc ≫ φ)
    let g' : ConnectiveResolution.Colim A M →ᵈᵍ[A] DegreeZeroModule hA N' := g.hom
    let f := DegreeZeroModule.factor (ConnectiveResolution.π A M)
      (surjective_resolution_π hA N) g'
      (fun _ hx => DegreeZeroModule.apply_eq_zero_of_isQuasiIso hP _ hπ g' hx)
    refine ⟨ModuleCat.ofHom f, ?_⟩
    have h : πc ≫ (degreeZeroModuleFunctor A hA).map (ModuleCat.ofHom f) = g :=
      DGModuleCat.hom_ext_apply fun x =>
        show f (ConnectiveResolution.π A M x) = g' x from
          DegreeZeroModule.factor_apply (ConnectiveResolution.π A M)
            (surjective_resolution_π hA N) g' _ x
    rw [← cancel_epi (Q.map πc), ← hg, ← h, Functor.map_comp]
    rfl

instance heartFunctor_faithful : (heartFunctor.{w, v} hA).Faithful where
  map_injective {N N'} {f₁ f₂} h := by
    let M := DegreeZeroModule hA N
    have hP := ConnectiveResolution.isNonposGraded_colim A M hA
    have hK := (ConnectiveResolution.semiFreeFiltration A M).isKProjective
    let πc : DGModuleCat.of A (ConnectiveResolution.Colim A M) ⟶
        (degreeZeroModuleFunctor A hA).obj N :=
      DGModuleCat.ofHom (ConnectiveResolution.π A M)
    have h' : Q.map (πc ≫ (degreeZeroModuleFunctor A hA).map f₁) =
        Q.map (πc ≫ (degreeZeroModuleFunctor A hA).map f₂) := by
      rw [Functor.map_comp, Functor.map_comp]
      exact congrArg (Q.map πc ≫ ·) h
    let g₁ : ConnectiveResolution.Colim A M →ᵈᵍ[A] DegreeZeroModule hA N' :=
      (πc ≫ (degreeZeroModuleFunctor A hA).map f₁).hom
    let g₂ : ConnectiveResolution.Colim A M →ᵈᵍ[A] DegreeZeroModule hA N' :=
      (πc ≫ (degreeZeroModuleFunctor A hA).map f₂).hom
    have h'' : g₁ = g₂ := DegreeZeroModule.eq_of_homotopic hP ((Q_map_eq_iff hK _ _).mp h')
    ext n
    obtain ⟨x, rfl⟩ := surjective_resolution_π hA N n
    exact congrArg (fun φ => φ x) h''

/-- The essential image of `ModuleCat H⁰A ⥤ D(A)` is the heart of the standard t-structure. -/
theorem essImage_heartFunctor : (heartFunctor.{w, v} hA).essImage = (tStructure hA).heart := by
  ext X
  constructor
  · rintro ⟨N, ⟨e⟩⟩
    refine (tStructure hA).heart.prop_of_iso e ((mem_heart_tStructure_iff hA _).mpr fun k hk => ?_)
    exact (isZero_homologyFunctor_Q_obj_iff _ k).mpr (DegreeZeroModule.subsingleton_cohomology hk)
  · intro hX
    rw [mem_heart_tStructure_iff] at hX
    obtain ⟨M, ⟨eM⟩⟩ := exists_iso_Q_obj X
    have hM : ∀ k, k ≠ 0 → Subsingleton (cohomology M k) := fun k hk =>
      (isZero_homologyFunctor_Q_obj_iff M k).mp
        ((isZero_homologyFunctor_iff_of_iso eM k).mp (hX k hk))
    -- resolve `τ^{≤ 0} M` by a semi-free module in non-positive degrees
    obtain ⟨P, _, _, _, _, π, hπ, -, hP⟩ :=
      exists_semiFreeResolution_of_isNonposGraded A (truncLE hA M 0) hA
        (isNonposGraded_truncLE_zero hA)
    have hι := isQuasiIso_truncLE_subtype hA (M := M) fun k hk => hM k hk.ne'
    let ι₁ : DGModuleCat.of A (truncLE hA M 0) ⟶ M := DGModuleCat.ofHom (truncLE hA M 0).subtype
    let π₁ : DGModuleCat.of A P ⟶ DGModuleCat.of A (truncLE hA M 0) := DGModuleCat.ofHom π
    have : IsIso (Q.map ι₁) := (isIso_Q_map_iff _).mpr hι
    have : IsIso (Q.map π₁) := (isIso_Q_map_iff _).mpr hπ
    have hPH : ∀ k, k ≠ 0 → Subsingleton (cohomology P k) := fun k hk => by
      have := hM k hk
      exact (Equiv.ofBijective _ ((DGModuleHom.IsQuasiIso.comp hι hπ) k)).subsingleton
    let := degreeZeroQuotientModule hA hP
    let ρ : DGModuleCat.of A P ⟶
        (degreeZeroModuleFunctor A hA).obj
          (ModuleCat.of _ (P ⧸ degreeZeroQuotientSubmodule hA P hP)) :=
      DGModuleCat.ofHom (degreeZeroQuotientπ hA hP)
    have : IsIso (Q.map ρ) := (isIso_Q_map_iff _).mpr (isQuasiIso_degreeZeroQuotientπ hA hP hPH)
    exact ⟨ModuleCat.of _ (P ⧸ degreeZeroQuotientSubmodule hA P hP),
      ⟨(asIso (Q.map ρ)).symm ≪≫ asIso (Q.map π₁) ≪≫ asIso (Q.map ι₁) ≪≫ eM.symm⟩⟩

/-- The heart of the standard t-structure on `D(A)`, for `A` concentrated in non-positive
degrees, is the category of modules over `H⁰A = A ⧸ (A^{< 0} ⊕ d(A⁻¹))`: the functor
`ModuleCat H⁰A ⥤ D(A)` regarding a module as a dg module concentrated in degree `0` is fully
faithful with essential image the heart. -/
@[instance_reducible]
noncomputable def tStructureHeart :
    (tStructure.{w, v} hA).Heart (ModuleCat.{max u v} (A ⧸ truncGEZeroIdeal hA)) where
  ι := heartFunctor hA
  essImage_eq_heart := essImage_heartFunctor hA

end DerivedCategory

end DG
