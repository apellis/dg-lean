import DG.Derived.Minimal
import DG.Derived.ConnectiveResolution
import DG.Positive.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Finset.Sum

/-!
# Minimal semi-free resolutions over connective dg rings

Let `A` be a dg ring concentrated in non-positive degrees (`DG.IsNonposGraded A`), with
`d(A⁻¹) = 0` and every nonzero element of `A⁰` a unit, and let `M` be a dg `A`-module with
`Hⁱ(M) = 0` for `i > N`. This file constructs a **minimal** semi-free resolution of `M`: a
quasi-isomorphism `P → M` from a semi-free dg module `P` concentrated in degrees `≤ N` whose
differential takes values in the decomposables `A^{<0} P` (`DG.IsMinimal`)
(`DG.exists_minimal_semiFreeResolution`). By `DG.IsKProjective.exists_bijective_of_isBoundedMinimal`
such a resolution is unique up to isomorphism of dg modules.

## The construction

The resolution is the colimit of stages `P₀ = 0 → P₁ → ⋯`; the stage `Pₙ₊₁` attaches
generators of degree `g = N - n` to `Pₙ` (`DG.MinimalResolution.nextStage`, a cone of the
attaching map of a family of cells, `DG.MinimalResolution.step`). The cohomology groups are
modules over the division ring `A⁰` (`DG.MinimalResolution.HK`), and the cells are chosen
minimally (`DG.MinimalResolution.cells`):

* for a basis of `ker (H^{g+1}(Pₙ) → H^{g+1}(M))`, a generator killing a representing cocycle;
* for a basis of a complement of `im (H^g(Pₙ) → H^g(M))`, a cocycle generator over a
  representing cocycle of `M`.

Then `H^i(Pₙ) → H^i(M)` is injective for `i ≥ N - n + 2` and surjective for `i ≥ N - n + 1`
(`DG.MinimalResolution.injAt_nextStage`, `DG.MinimalResolution.surjAt_nextStage`). Minimality
rests on `DG.MinimalResolution.mem_decomposables_of_cocycle`: a cocycle of `Pₙ₊₁` of degree `g`
whose image in `M` is a coboundary is decomposable, since its coefficients along the new
generators vanish by the linear independence of the two chosen bases. With `d(A⁻¹) = 0`, the
free modules on the cells are minimal (`DG.isMinimal_directSum_shift`), and a cone of a map with
decomposable values between minimal modules is minimal (`DG.IsMinimal.cone`).
-/

open DirectSum

universe u v

set_option backward.isDefEq.respectTransparency false

namespace DG

section General

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  {M N : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N]

omit [DGRing A] [DGAddCommGroup M] [DGAddCommGroup N] in
/-- `A`-linear maps preserve decomposable elements. -/
theorem LinearMap.map_mem_decomposables (f : M →ₗ[A] N) {y : M}
    (hy : y ∈ decomposables A M) : f y ∈ decomposables A N := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, hi, a, ha, x, rfl⟩ := hy
    rw [map_smul]
    exact smul_mem_decomposables hi ha _
  | zero => rw [map_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [map_add]; exact add_mem h h'
  | neg y _ h => rw [map_neg]; exact neg_mem h

omit [DGAddCommGroup M] [DGAddCommGroup N] [Module A N] in
/-- Shifting preserves decomposable elements. -/
theorem Shift.mk_mem_decomposables (n : ℤ) {y : M} (hy : y ∈ decomposables A M) :
    Shift.mk n y ∈ decomposables A (Shift n M) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, hi, a, ha, x, rfl⟩ := hy
    rw [Shift.mk_smul ha, Units.smul_def]
    exact zsmul_mem (smul_mem_decomposables hi ha _) _
  | zero => rw [Shift.mk_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [Shift.mk_add]; exact add_mem h h'
  | neg y _ h => rw [Shift.mk_neg]; exact neg_mem h

omit [DGAddCommGroup M] [DGAddCommGroup N] [Module A N] in
theorem Shift.unmk_mem_decomposables (n : ℤ) {y : Shift n M}
    (hy : y ∈ decomposables A (Shift n M)) : Shift.unmk n y ∈ decomposables A M := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, hi, a, ha, x, rfl⟩ := hy
    rw [Shift.unmk_smul ha, Units.smul_def]
    exact zsmul_mem (smul_mem_decomposables hi ha _) _
  | zero => rw [Shift.unmk_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [Shift.unmk_add]; exact add_mem h h'
  | neg y _ h => rw [Shift.unmk_neg]; exact neg_mem h

omit [DGAddCommGroup N] [Module A N] in
/-- A shift of a minimal dg module is minimal. -/
theorem IsMinimal.shift {n : ℤ} (hM : IsMinimal A M) : IsMinimal A (Shift n M) := fun x => by
  obtain ⟨x, rfl⟩ := Shift.mk_surjective (n := n) (M := M) x
  rw [Shift.d_mk, Shift.mk_units_smul, Units.smul_def]
  exact zsmul_mem (Shift.mk_mem_decomposables n (hM x)) _

end General

section Cone

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  {S N : Type*} [AddCommGroup S] [DGAddCommGroup S] [Module A S] [DGModule A S]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]

omit [DGModule A S] [DGModule A N] in
/-- **The mapping cone of a morphism with decomposable values between minimal dg modules is
minimal**: `d (x, y) = (-d x, f x + d y)`. -/
theorem IsMinimal.cone {f : S →ᵈᵍ[A] N} (hS : IsMinimal A S) (hN : IsMinimal A N)
    (hf : ∀ x, f x ∈ decomposables A N) : IsMinimal A (Cone f) := fun p => by
  rw [← Cone.inlLinear_fstHom_add_inr_sndLinear p, Cone.d_inlLinear_add_inr]
  refine add_mem (LinearMap.map_mem_decomposables _ ((hS.shift (n := 1)) _))
    (DGModuleHom.map_mem_decomposables _ (add_mem (hf _) (hN _)))

end Cone

section Connective

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  {M : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]

omit [DGAddCommGroup M] [DGModule A M] in
/-- Over a dg ring concentrated in non-positive degrees, the decomposable elements form an
`A`-stable subgroup. -/
theorem smul_mem_decomposables_of_isNonposGraded (hA : IsNonposGraded A) (a : A) {y : M}
    (hy : y ∈ decomposables A M) : a • y ∈ decomposables A M := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, hi, b, hb, x, rfl⟩ := hy
    by_cases hi' : 0 < i
    · rw [hA.eq_zero hi' hb, zero_smul, smul_zero]
      exact zero_mem _
    induction a using DG.induction_on with
    | h_zero => rw [zero_smul]; exact zero_mem _
    | h_add a a' h h' => rw [add_smul]; exact add_mem h h'
    | @h_homogeneous j a =>
      by_cases hj : 0 < j
      · rw [hA.eq_zero hj a.2, zero_smul]
        exact zero_mem _
      rw [← mul_smul]
      exact smul_mem_decomposables (i := j + i) (by omega) (mul_mem_grading a.2 hb) _
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg y _ h => rw [smul_neg]; exact neg_mem h

omit [DGRing A] in
/-- A dg ring concentrated in non-positive degrees with `d(A⁻¹) = 0` is minimal as a dg module
over itself. -/
theorem isMinimal_self (hA : IsNonposGraded A) (hdA : ∀ a ∈ grading (M := A) (-1), d a = 0) :
    IsMinimal A A := fun a => by
  induction a using DG.induction_on with
  | h_zero => rw [d_zero]; exact zero_mem _
  | h_add a a' h h' => rw [d_add]; exact add_mem h h'
  | @h_homogeneous j a =>
    by_cases hj : j = -1
    · subst hj
      rw [hdA _ a.2]
      exact zero_mem _
    by_cases hj' : 0 ≤ j
    · rw [hA.eq_zero (by omega) (d_mem a.2)]
      exact zero_mem _
    rw [← mul_one (d (a : A))]
    exact smul_mem_decomposables (i := j + 1) (by omega) (d_mem a.2) (1 : A)

omit [DGRing A] in
/-- Decomposable elements of the summands of a direct sum are decomposable. -/
theorem DirectSum.of_mem_decomposables {ι : Type*} [DecidableEq ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, DGAddCommGroup (M i)] [∀ i, Module A (M i)] (i : ι)
    {y : M i} (hy : y ∈ decomposables A (M i)) :
    DirectSum.of M i y ∈ decomposables A (⨁ i, M i) :=
  LinearMap.map_mem_decomposables (DirectSum.lof A ι M i) hy

/-- The free dg modules `⨁ᵢ A⟦kᵢ⟧` are minimal over a dg ring concentrated in non-positive
degrees with `d(A⁻¹) = 0`. -/
theorem isMinimal_directSum_shift (hA : IsNonposGraded A)
    (hdA : ∀ a ∈ grading (M := A) (-1), d a = 0) {ι : Type*} [DecidableEq ι] (k : ι → ℤ) :
    IsMinimal A (⨁ i, Shift (k i) A) := fun x => by
  induction x using DirectSum.induction_on with
  | zero => rw [d_zero]; exact zero_mem _
  | add x y hx hy => rw [d_add]; exact add_mem hx hy
  | of i y =>
    rw [DirectSum.d_of]
    exact DirectSum.of_mem_decomposables i ((isMinimal_self hA hdA).shift y)

end Connective

/-! ### Linear algebra over a ring whose nonzero elements are units -/

section LinearAlgebra

variable {k : Type*} [Ring k] (hk : ∀ a : k, IsUnit a ∨ a = 0) {V : Type v} [AddCommGroup V]
  [Module k V]
include hk

/-- Every submodule has a linearly independent spanning family (a basis). -/
theorem exists_linearIndependent_span_eq (W : Submodule k V) :
    ∃ (ι : Type v) (w : ι → V), LinearIndependent k w ∧ Submodule.span k (Set.range w) = W := by
  rcases subsingleton_or_nontrivial k with hk' | hk'
  · have : Subsingleton V := Module.subsingleton k V
    refine ⟨PEmpty, PEmpty.elim, linearIndependent_empty_type, ?_⟩
    rw [Set.range_eq_empty, Submodule.span_empty]
    exact Subsingleton.elim _ _
  · let _ : DivisionRing k := DivisionRing.ofIsUnitOrEqZero hk
    let b := Module.Basis.ofVectorSpace k W
    refine ⟨_, fun i => (b i : V), b.linearIndependent.map' W.subtype W.ker_subtype, ?_⟩
    rw [Set.range_comp' (f := b) (g := Subtype.val), ← Submodule.coe_subtype,
      ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

/-- Every submodule has a complement with a linearly independent spanning family. -/
theorem exists_linearIndependent_isCompl (W : Submodule k V) :
    ∃ (ι : Type v) (w : ι → V), LinearIndependent k w ∧
      IsCompl W (Submodule.span k (Set.range w)) := by
  rcases subsingleton_or_nontrivial k with hk' | hk'
  · have : Subsingleton V := Module.subsingleton k V
    refine ⟨PEmpty, PEmpty.elim, linearIndependent_empty_type, ?_⟩
    rw [Set.range_eq_empty, Submodule.span_empty, Subsingleton.elim W ⊤]
    exact isCompl_top_bot
  · let _ : DivisionRing k := DivisionRing.ofIsUnitOrEqZero hk
    obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
    obtain ⟨ι, w, hw, hspan⟩ := exists_linearIndependent_span_eq hk C
    exact ⟨ι, w, hw, hspan ▸ hC⟩

end LinearAlgebra

/-! ### Cohomology as a module over the degree-zero ring -/

section KCohomology

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] (hA : IsNonposGraded A)
  (P : Type*) [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]

omit [DGRing A] in
include hA in
theorem d_smul_of_mem_zero' {a : A} (ha : a ∈ grading (M := A) 0) (x : P) :
    d (a • x) = a • d x := by
  rw [DG.d_smul ha, hA.eq_zero (by norm_num) (d_mem ha), zero_smul, zero_add, koszulSign_zero,
    one_smul]

/-- The cocycles of degree `j`, a module over the degree-zero ring. -/
def cocyclesK (j : ℤ) : Submodule (degreeZeroSubring A) P where
  carrier := {x | x ∈ grading j ∧ d x = 0}
  add_mem' hx hy := ⟨add_mem hx.1 hy.1, by rw [d_add, hx.2, hy.2, add_zero]⟩
  zero_mem' := ⟨zero_mem _, d_zero⟩
  smul_mem' a x hx := ⟨by
    change (a : A) • x ∈ grading j
    simpa using smul_mem_grading (mem_degreeZeroSubring.mp a.2) hx.1, by
    change d ((a : A) • x) = 0
    rw [d_smul_of_mem_zero' hA P (mem_degreeZeroSubring.mp a.2), hx.2, smul_zero]⟩

/-- The coboundaries of degree `j`, a module over the degree-zero ring. -/
def coboundariesK (j : ℤ) : Submodule (degreeZeroSubring A) P where
  carrier := {x | x ∈ grading j ∧ ∃ y ∈ grading (j - 1), d y = x}
  add_mem' := by
    rintro x x' ⟨hx, y, hy, rfl⟩ ⟨hx', y', hy', rfl⟩
    exact ⟨add_mem hx hx', y + y', add_mem hy hy', d_add _ _⟩
  zero_mem' := ⟨zero_mem _, 0, zero_mem _, d_zero⟩
  smul_mem' := by
    rintro a x ⟨hx, y, hy, rfl⟩
    refine ⟨by
      change (a : A) • d y ∈ grading j
      simpa using smul_mem_grading (mem_degreeZeroSubring.mp a.2) hx, (a : A) • y,
      by simpa using smul_mem_grading (mem_degreeZeroSubring.mp a.2) hy, ?_⟩
    exact d_smul_of_mem_zero' hA P (mem_degreeZeroSubring.mp a.2) y

/-- The cohomology in degree `j`, a module over the degree-zero ring. -/
abbrev HK (j : ℤ) : Type _ :=
  cocyclesK hA P j ⧸ (coboundariesK hA P j).comap (cocyclesK hA P j).subtype

variable {P}

theorem mkK_eq_zero_iff {j : ℤ} (z : cocyclesK hA P j) :
    (Submodule.Quotient.mk z : HK hA P j) = 0 ↔ (z : P) ∈ coboundariesK hA P j :=
  Submodule.Quotient.mk_eq_zero _

variable {Q : Type*} [AddCommGroup Q] [DGAddCommGroup Q] [Module A Q] [DGModule A Q]

/-- A morphism of dg modules on cocycles, as a map of modules over the degree-zero ring. -/
def cocyclesKMap (f : P →ᵈᵍ[A] Q) (j : ℤ) : cocyclesK hA P j →ₗ[degreeZeroSubring A] cocyclesK hA Q j where
  toFun z := ⟨f z, f.map_mem z.2.1, by rw [← f.map_d, z.2.2, map_zero]⟩
  map_add' z z' := Subtype.ext (map_add f _ _)
  map_smul' a z := Subtype.ext (f.map_smul (a : A) z)

/-- A morphism of dg modules on cohomology, as a map of modules over the degree-zero ring. -/
def mapK (f : P →ᵈᵍ[A] Q) (j : ℤ) : HK hA P j →ₗ[degreeZeroSubring A] HK hA Q j :=
  Submodule.mapQ _ _ (cocyclesKMap hA f j) (by
    rintro z ⟨hz, y, hy, hdy⟩
    exact ⟨f.map_mem hz, f y, f.map_mem hy, by rw [← f.map_d, hdy]; rfl⟩)

theorem mapK_mk (f : P →ᵈᵍ[A] Q) {j : ℤ} (z : cocyclesK hA P j) :
    mapK hA f j (Submodule.Quotient.mk z) = Submodule.Quotient.mk (cocyclesKMap hA f j z) :=
  rfl

end KCohomology

/-! ### Attaching a family of cells -/

namespace MinimalResolution

open Resolution

section Cells

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  {M : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  {S : Type*} [AddCommGroup S] [DGAddCommGroup S] [Module A S] [DGModule A S]
  {p : S →ᵈᵍ[A] M} {ι : Type*} (c : ι → Cell p)

/-- The free dg module `⨁ᵢ A⟦-deg cᵢ⟧` on a family of cells. -/
abbrev Cells : Type _ := ⨁ i : ι, Shift (-(c i).deg) A

noncomputable instance : DecidableEq ι := Classical.decEq _

/-- The generator of `Cells c` attached to the cell `c i`. -/
noncomputable def gen (i : ι) : Cells c :=
  DirectSum.of _ i (Shift.mk (-(c i).deg) 1)

omit [DGModule A M] [DGModule A S] in
theorem gen_mem (i : ι) : gen c i ∈ grading (c i).deg :=
  DirectSum.of_mem_grading _ i
    (by simpa using Shift.mk_mem_grading (n := -(c i).deg) (one_mem_grading (A := A)))

omit [DGModule A M] [DGModule A S] in
theorem d_gen (i : ι) : d (gen c i) = 0 := by
  rw [gen, DirectSum.d_of, Shift.d_mk, d_one, smul_zero, Shift.mk_zero, map_zero]

/-- The attaching map `Cells c → S`, sending the generator of `c i` to its cocycle. -/
noncomputable def attach : Cells c →ᵈᵍ[A] S :=
  DGModuleHom.toModule fun i =>
    DGModuleHom.shiftGen (-(c i).deg) (c i).z (by rw [neg_neg]; exact (c i).z_mem) (c i).d_z

/-- The null-homotopy of `p ∘ attach c` sending the generator of `c i` to its element of `M`. -/
noncomputable def homotopy : Cochain A (Cells c) M (-1) :=
  (Cochain.directSumDesc fun i =>
    Cochain.shiftGen (-(c i).deg) (Shift.mk (-1) (c i).m) (mk_m_mem p (c i))).rightUnshift (-1)
      (zero_add _)

omit [DGModule A M] in
@[simp]
theorem attach_gen (i : ι) : attach c (gen c i) = (c i).z := by
  rw [gen, attach, DGModuleHom.toModule_lof, DGModuleHom.shiftGen_mk_one]

omit [DGModule A M] in
theorem attach_of (i : ι) (a : Shift (-(c i).deg) A) :
    attach c (DirectSum.of _ i a) =
      Shift.twist A (-(c i).deg) (Shift.unmk _ a) • (c i).z := by
  rw [attach, DGModuleHom.toModule_lof, DGModuleHom.shiftGen_apply]

omit [DGModule A S] in
@[simp]
theorem homotopy_gen (i : ι) : homotopy c (gen c i) = (c i).m := by
  rw [homotopy, Cochain.rightUnshift_apply, gen, Cochain.directSumDesc_of,
    Cochain.shiftGen_mk_one, Shift.unmk_mk]

theorem δ_homotopy : δ (-1) 0 (homotopy c) = Cochain.ofHom (p.comp (attach c)) :=
  Cochain.ext_directSum_shift fun i => by
    change δ (-1) 0 (homotopy c) (gen c i) = Cochain.ofHom (p.comp (attach c)) (gen c i)
    rw [δ_neg_one_apply, d_gen, map_zero, add_zero, homotopy_gen, Cochain.ofHom_apply,
      DGModuleHom.comp_apply, attach_gen, (c i).p_z]

omit [DGModule A M] in
/-- If every cocycle of the family is decomposable, the attaching map takes values in the
decomposables. -/
theorem attach_mem_decomposables (hA : IsNonposGraded A)
    (hc : ∀ i, (c i).z ∈ decomposables A S) (x : Cells c) :
    attach c x ∈ decomposables A S := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
  | of i a =>
    rw [attach_of]
    exact smul_mem_decomposables_of_isNonposGraded hA _ (hc i)

end Cells

/-! ### The next stage -/

section Step

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]
  {M : Type v} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]

/-- The next stage, attaching a family of cells: the cone of the attaching map, mapped to `M` by
`π` and the null-homotopy of `π ∘ attach`. -/
noncomputable def step (s : Stage A M) {ι : Type (max u v)} (c : ι → Cell s.π) : Stage A M where
  obj := DGModuleCat.of A (Cone (attach c))
  π := Cone.desc (attach c) (homotopy c) s.π (δ_homotopy c)

variable (s : Stage A M) {ι : Type (max u v)} (c : ι → Cell s.π)

/-- The inclusion of a stage into the next one. -/
noncomputable def incl : s.obj →ᵈᵍ[A] (step s c).obj := Cone.inr (attach c)

theorem incl_injective : Function.Injective (incl s c) := fun _ _ h =>
  congrArg (Cone.sndLinear (attach c)) h

theorem step_π_comp_incl : (step s c).π.comp (incl s c) = s.π :=
  Cone.inr_desc _ _ _ (δ_homotopy c)

theorem step_π_incl (x : s.obj) : (step s c).π (incl s c x) = s.π x :=
  DFunLike.congr_fun (step_π_comp_incl s c) x

/-- The new generator attached to the cell `c i`. -/
noncomputable def newGen (i : ι) : (step s c).obj := Cone.inl (attach c) (gen c i)

theorem newGen_mem (i : ι) : newGen s c i ∈ grading ((c i).deg - 1) := by
  have h := (Cone.inl (attach c)).map_mem (gen_mem c i)
  rwa [← sub_eq_add_neg] at h

theorem d_newGen (i : ι) : d (newGen s c i) = incl s c (c i).z := by
  have h := Cone.inl_d_apply (f := attach c) (gen c i)
  rw [d_gen, map_zero, sub_zero, attach_gen] at h
  exact h

theorem step_π_newGen (i : ι) : (step s c).π (newGen s c i) = (c i).m :=
  (Cone.inl_desc_apply _ _ _ (δ_homotopy c) _).trans (homotopy_gen c i)

/-- Attaching cells whose cocycles are decomposable preserves minimality. -/
theorem isMinimal_step (hA : IsNonposGraded A) (hdA : ∀ a ∈ grading (M := A) (-1), d a = 0)
    (hs : IsMinimal A s.obj) (hc : ∀ i, (c i).z ∈ decomposables A s.obj) :
    IsMinimal A (step s c).obj :=
  IsMinimal.cone (isMinimal_directSum_shift hA hdA _) hs (attach_mem_decomposables c hA hc)

/-! ### Degrees of the new stage -/

section Degrees

variable (hA : IsNonposGraded A) {g : ℤ} (hdeg : ∀ i, (c i).deg = g + 1)
include hA hdeg

omit [DGRing A] [DGModule A M] in
/-- When all cells have degree `g + 1`, the free module on the cells vanishes in degrees
`> g + 1`. -/
theorem cells_eq_zero {k : ℤ} (hk : g + 1 < k) {x : Cells c} (hx : x ∈ grading k) : x = 0 := by
  ext i
  have hc : x i ∈ grading k := hx i
  rw [DirectSum.zero_apply]
  exact (Shift.unmk _).injective (by
    rw [hA.eq_zero (by rw [hdeg i]; omega) (Shift.unmk_mem_grading hc)]; rfl)

/-- When all cells have degree `g + 1`, the new stage agrees with the old one in degrees `> g`. -/
theorem incl_sndLinear {j : ℤ} (hj : g < j) {x : (step s c).obj} (hx : x ∈ grading j) :
    incl s c (Cone.sndLinear (A := A) (attach c) x) = x := by
  obtain ⟨hx₁, -⟩ := Cone.mem_grading_iff.mp hx
  have h0 : Cone.fstHom (attach c) x = 0 :=
    (Shift.unmk 1).injective (cells_eq_zero s c hA hdeg (k := j + 1) (by omega)
      (Shift.unmk_mem_grading hx₁))
  have h := Cone.inlLinear_fstHom_add_inr_sndLinear (A := A) (f := attach c) x
  rw [h0, map_zero, zero_add] at h
  exact h

theorem exists_eq_incl {j : ℤ} (hj : g < j) {x : (step s c).obj} (hx : x ∈ grading j) :
    ∃ y ∈ grading j, incl s c y = x :=
  ⟨_, Cone.sndLinear_mem (A := A) hx, incl_sndLinear s c hA hdeg hj hx⟩

omit hA [DGModule A M] in
/-- Elements of the free module on the cells in degrees `≤ g` are decomposable. -/
theorem cells_mem_decomposables {k : ℤ} (hk : k ≤ g) {x : Cells c} (hx : x ∈ grading k) :
    x ∈ decomposables A (Cells c) := by
  classical
  rw [← DirectSum.sum_support_of x]
  refine sum_mem fun i _ => DirectSum.of_mem_decomposables i ?_
  obtain ⟨b, hb⟩ := Shift.mk_surjective (n := -(c i).deg) (M := A) (x i)
  have hb' : b ∈ grading (k - (g + 1)) := by
    have := Shift.unmk_mem_grading (hx i)
    rw [← hb, Shift.unmk_mk] at this
    convert this using 2
    rw [hdeg i]
    ring
  rw [← hb, ← mul_one b, ← smul_eq_mul, Shift.mk_smul hb', Units.smul_def]
  exact zsmul_mem (smul_mem_decomposables (by omega) hb' _) _

omit hA in
/-- If the old stage is decomposable in degrees `≤ g`, the new stage (with generators of degree
`g`) is decomposable in degrees `≤ g - 1`. -/
theorem mem_decomposables_of_le
    (hs : ∀ j ≤ g, ∀ y ∈ grading (M := s.obj) j, y ∈ decomposables A s.obj) {j : ℤ}
    (hj : j ≤ g - 1) {x : (step s c).obj} (hx : x ∈ grading j) :
    x ∈ decomposables A (step s c).obj := by
  obtain ⟨hx₁, hx₂⟩ := Cone.mem_grading_iff.mp hx
  rw [← Cone.inlLinear_fstHom_add_inr_sndLinear (A := A) (f := attach c) x]
  refine add_mem (LinearMap.map_mem_decomposables _ ?_)
    (DGModuleHom.map_mem_decomposables _ (hs j (by omega) _ hx₂))
  obtain ⟨w, hw⟩ := Shift.mk_surjective (n := 1) (M := Cells c) (Cone.fstHom (attach c) x)
  rw [← hw]
  refine Shift.mk_mem_decomposables 1 (cells_mem_decomposables s c hdeg (k := j + 1)
    (by omega) ?_)
  have := Shift.unmk_mem_grading hx₁
  rwa [← hw, Shift.unmk_mk] at this

omit hA in
/-- An element of the new stage in the degree `g` of the new generators is a combination of the
new generators with coefficients in `A⁰`, plus an element of the old stage. -/
theorem exists_eq_sum {x : (step s c).obj} (hx : x ∈ grading g) :
    ∃ (t : Finset ι) (l : ι → A), (∀ i, l i ∈ grading (M := A) 0) ∧ ∃ y ∈ grading g,
      x = ∑ i ∈ t, l i • newGen s c i + incl s c y := by
  classical
  obtain ⟨hx₁, hx₂⟩ := Cone.mem_grading_iff.mp hx
  obtain ⟨w, hw⟩ := Shift.mk_surjective (n := 1) (M := Cells c) (Cone.fstHom (attach c) x)
  have hw' : w ∈ grading (g + 1) := by
    have := Shift.unmk_mem_grading hx₁
    rwa [← hw, Shift.unmk_mk] at this
  have hl : ∀ i, Shift.unmk _ (w i) ∈ grading (M := A) 0 := fun i => by
    have := Shift.unmk_mem_grading (hw' i)
    convert this using 2
    rw [hdeg i]
    ring
  refine ⟨w.support, fun i => Shift.unmk _ (w i), hl, _, Cone.sndLinear_mem (A := A) hx, ?_⟩
  have hgen : ∀ i, (Shift.unmk _ (w i) : A) • gen c i = DirectSum.of _ i (w i) := fun i => by
    rw [gen, ← DirectSum.lof_eq_of A, ← LinearMap.map_smul, Shift.smul_mk (hl i), mul_zero,
      koszulSign_zero, one_smul, smul_eq_mul, mul_one, Shift.mk_unmk]
    exact DirectSum.lof_eq_of A ι (fun i => Shift (-(c i).deg) A) i (w i)
  have hinl : Cone.inl (attach c) w = ∑ i ∈ w.support, Shift.unmk _ (w i) • newGen s c i := by
    conv_lhs => rw [← DirectSum.sum_support_of w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hgen, Cochain.map_smul _ (hl i), mul_zero, koszulSign_zero, one_smul]
    rfl
  rw [← hinl]
  conv_lhs => rw [← Cone.inlLinear_fstHom_add_inr_sndLinear (A := A) (f := attach c) x, ← hw]
  rfl

end Degrees

end Step

/-! ### The minimal choice of cells -/

section Choice

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]
  {M : Type v} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  (hA : IsNonposGraded A) (hk : ∀ a : degreeZeroSubring A, IsUnit a ∨ a = 0)
  (s : Stage A M) (g : ℤ)

/-- The index set of a basis of `ker (H^{g+1}(s) → H^{g+1}(M))`. -/
def KerIndex : Type (max u v) :=
  (exists_linearIndependent_span_eq hk (LinearMap.ker (mapK hA s.π (g + 1)))).choose

/-- A basis of `ker (H^{g+1}(s) → H^{g+1}(M))`. -/
noncomputable def kerVec : KerIndex hA hk s g → HK hA s.obj (g + 1) :=
  (exists_linearIndependent_span_eq hk (LinearMap.ker (mapK hA s.π (g + 1)))).choose_spec.choose

theorem kerVec_linearIndependent : LinearIndependent (degreeZeroSubring A) (kerVec hA hk s g) :=
  (exists_linearIndependent_span_eq hk
    (LinearMap.ker (mapK hA s.π (g + 1)))).choose_spec.choose_spec.1

theorem span_kerVec : Submodule.span (degreeZeroSubring A) (Set.range (kerVec hA hk s g)) =
    LinearMap.ker (mapK hA s.π (g + 1)) :=
  (exists_linearIndependent_span_eq hk
    (LinearMap.ker (mapK hA s.π (g + 1)))).choose_spec.choose_spec.2

/-- A cocycle representing a basis vector of the kernel. -/
noncomputable def kerRep (i : KerIndex hA hk s g) : cocyclesK hA s.obj (g + 1) :=
  (Submodule.Quotient.mk_surjective _ (kerVec hA hk s g i)).choose

theorem mk_kerRep (i : KerIndex hA hk s g) :
    Submodule.Quotient.mk (kerRep hA hk s g i) = kerVec hA hk s g i :=
  (Submodule.Quotient.mk_surjective _ (kerVec hA hk s g i)).choose_spec

theorem exists_kerM (i : KerIndex hA hk s g) :
    ∃ m ∈ grading (M := M) (g + 1 - 1), d m = s.π (kerRep hA hk s g i) := by
  have h : kerVec hA hk s g i ∈ LinearMap.ker (mapK hA s.π (g + 1)) := by
    rw [← span_kerVec hA hk s g]
    exact Submodule.subset_span ⟨i, rfl⟩
  rw [LinearMap.mem_ker, ← mk_kerRep hA hk s g, mapK_mk, mkK_eq_zero_iff] at h
  exact h.2

/-- The cell killing a basis vector of the kernel. -/
noncomputable def kerCell (i : KerIndex hA hk s g) : Cell s.π where
  deg := g + 1
  z := kerRep hA hk s g i
  m := (exists_kerM hA hk s g i).choose
  z_mem := (kerRep hA hk s g i).2.1
  d_z := (kerRep hA hk s g i).2.2
  m_mem := (exists_kerM hA hk s g i).choose_spec.1
  p_z := (exists_kerM hA hk s g i).choose_spec.2.symm

/-- The index set of a basis of a complement of `im (H^g(s) → H^g(M))`. -/
def CokIndex : Type v :=
  (exists_linearIndependent_isCompl hk (LinearMap.range (mapK hA s.π g))).choose

/-- A basis of a complement of `im (H^g(s) → H^g(M))`. -/
noncomputable def cokVec : CokIndex hA hk s g → HK hA M g :=
  (exists_linearIndependent_isCompl hk (LinearMap.range (mapK hA s.π g))).choose_spec.choose

theorem cokVec_linearIndependent : LinearIndependent (degreeZeroSubring A) (cokVec hA hk s g) :=
  (exists_linearIndependent_isCompl hk
    (LinearMap.range (mapK hA s.π g))).choose_spec.choose_spec.1

theorem isCompl_cokVec : IsCompl (LinearMap.range (mapK hA s.π g))
    (Submodule.span (degreeZeroSubring A) (Set.range (cokVec hA hk s g))) :=
  (exists_linearIndependent_isCompl hk
    (LinearMap.range (mapK hA s.π g))).choose_spec.choose_spec.2

/-- A cocycle representing a basis vector of the complement. -/
noncomputable def cokRep (i : CokIndex hA hk s g) : cocyclesK hA M g :=
  (Submodule.Quotient.mk_surjective _ (cokVec hA hk s g i)).choose

theorem mk_cokRep (i : CokIndex hA hk s g) :
    Submodule.Quotient.mk (cokRep hA hk s g i) = cokVec hA hk s g i :=
  (Submodule.Quotient.mk_surjective _ (cokVec hA hk s g i)).choose_spec

/-- The cell attaching a cocycle generator over a basis vector of the complement. -/
noncomputable def cokCell (i : CokIndex hA hk s g) : Cell s.π where
  deg := g + 1
  z := 0
  m := cokRep hA hk s g i
  z_mem := zero_mem _
  d_z := d_zero
  m_mem := by simpa using (cokRep hA hk s g i).2.1
  p_z := by rw [map_zero, (cokRep hA hk s g i).2.2]

/-- The cells attached in degree `g`: kill a basis of the kernel in degree `g + 1` and hit a
basis of a complement of the image in degree `g`. -/
noncomputable def cells : KerIndex hA hk s g ⊕ CokIndex hA hk s g → Cell s.π :=
  Sum.elim (kerCell hA hk s g) (cokCell hA hk s g)

theorem cells_deg (i : KerIndex hA hk s g ⊕ CokIndex hA hk s g) :
    (cells hA hk s g i).deg = g + 1 := by
  rcases i with i | i <;> rfl

/-- The next stage of the minimal resolution, with generators of degree `g`. -/
noncomputable abbrev nextStage : Stage A M := step s (cells hA hk s g)

end Choice

/-! ### Cohomology of the next stage -/

section NextStage

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]
  {M : Type v} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]

/-- `H^i(s) → H^i(M)` is injective. -/
def InjAt (s : Stage A M) (i : ℤ) : Prop :=
  ∀ x ∈ grading (M := s.obj) i, d x = 0 → (∃ m ∈ grading (M := M) (i - 1), d m = s.π x) →
    ∃ y ∈ grading (M := s.obj) (i - 1), d y = x

/-- `H^i(s) → H^i(M)` is surjective. -/
def SurjAt (s : Stage A M) (i : ℤ) : Prop :=
  ∀ m ∈ grading (M := M) i, d m = 0 →
    ∃ x ∈ grading (M := s.obj) i, d x = 0 ∧ ∃ m' ∈ grading (M := M) (i - 1), d m' = s.π x - m

variable (hA : IsNonposGraded A) (hk : ∀ a : degreeZeroSubring A, IsUnit a ∨ a = 0)
  (s : Stage A M) (g : ℤ)

theorem d_smul_newGen {a : A} (ha : a ∈ grading (M := A) 0) (i) :
    d (a • newGen s (cells hA hk s g) i) = a • incl s (cells hA hk s g) (cells hA hk s g i).z := by
  rw [d_smul_of_mem_zero' hA _ ha, d_newGen]

/-- **Injectivity in degrees `≥ g + 1`** after attaching the cells of degree `g`. -/
theorem injAt_nextStage (hs : ∀ i ≥ g + 2, InjAt s i) :
    ∀ i ≥ g + 1, InjAt (nextStage hA hk s g) i := by
  intro i hi x' hx' hdx' ⟨m, hm, hdm⟩
  obtain ⟨x, hx, rfl⟩ := exists_eq_incl s (cells hA hk s g) hA (cells_deg hA hk s g)
    (by omega : g < i) hx'
  have hdx : d x = 0 := incl_injective s (cells hA hk s g)
    (by rw [DGModuleHom.map_d, hdx', map_zero])
  have hπ : d m = s.π x := by rw [hdm]; exact step_π_incl s (cells hA hk s g) x
  by_cases hi' : g + 2 ≤ i
  · obtain ⟨y, hy, hdy⟩ := hs i hi' x hx hdx ⟨m, hm, hπ⟩
    exact ⟨incl s _ y, (incl s _).map_mem hy, by rw [← DGModuleHom.map_d, hdy]⟩
  obtain rfl : i = g + 1 := by omega
  let xz : cocyclesK hA s.obj (g + 1) := ⟨x, hx, hdx⟩
  have hker : Submodule.Quotient.mk xz ∈ LinearMap.ker (mapK hA s.π (g + 1)) := by
    rw [LinearMap.mem_ker, mapK_mk, mkK_eq_zero_iff]
    exact ⟨s.π.map_mem hx, m, hm, hπ⟩
  rw [← span_kerVec hA hk s g] at hker
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hker
  let r : cocyclesK hA s.obj (g + 1) := c.sum fun i a => a • kerRep hA hk s g i
  have hr : Submodule.Quotient.mk r =
      (Submodule.Quotient.mk xz : HK hA s.obj (g + 1)) := by
    rw [← hc]
    show Submodule.Quotient.mk (∑ i ∈ c.support, c i • kerRep hA hk s g i) =
      ∑ i ∈ c.support, c i • kerVec hA hk s g i
    rw [← Submodule.mkQ_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Submodule.mkQ_apply, mk_kerRep]
  have hsub : Submodule.Quotient.mk (xz - r) = (0 : HK hA s.obj (g + 1)) := by
    rw [Submodule.Quotient.mk_sub, hr, sub_self]
  obtain ⟨-, y, hy, hdy⟩ := (mkK_eq_zero_iff hA _).mp hsub
  have hrval : (r : s.obj) =
      ∑ i ∈ c.support, ((c i : degreeZeroSubring A) : A) • (kerRep hA hk s g i : s.obj) := by
    simp only [r, Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul]
    rfl
  refine ⟨incl s _ y + ∑ i ∈ c.support,
      ((c i : degreeZeroSubring A) : A) • newGen s (cells hA hk s g) (Sum.inl i), ?_, ?_⟩
  · refine add_mem ((incl s _).map_mem hy) (sum_mem fun i _ => ?_)
    have := smul_mem_grading (mem_degreeZeroSubring.mp (c i).2)
      (newGen_mem s (cells hA hk s g) (Sum.inl i))
    simpa [cells, kerCell] using this
  · rw [d_add, ← DGModuleHom.map_d, hdy, Submodule.coe_sub, map_sub, map_sum]
    simp only [d_smul_newGen hA hk s g (mem_degreeZeroSubring.mp (c _).2)]
    change incl s _ x - incl s _ (r : s.obj) + _ = _
    rw [hrval, map_sum]
    simp only [map_smul]
    exact sub_add_cancel _ _

/-- **Surjectivity in degrees `≥ g`** after attaching the cells of degree `g`. -/
theorem surjAt_nextStage (hs : ∀ i ≥ g + 1, SurjAt s i) :
    ∀ i ≥ g, SurjAt (nextStage hA hk s g) i := by
  intro i hi m hm hdm
  by_cases hi' : g + 1 ≤ i
  · obtain ⟨x, hx, hdx, m', hm', hdm'⟩ := hs i hi' m hm hdm
    refine ⟨incl s _ x, (incl s _).map_mem hx, by rw [← DGModuleHom.map_d, hdx, map_zero], m', hm',
      ?_⟩
    rw [hdm']
    exact congrArg (· - m) (step_π_incl s (cells hA hk s g) x).symm
  obtain rfl : i = g := by omega
  let mz : cocyclesK hA M i := ⟨m, hm, hdm⟩
  have htop : Submodule.Quotient.mk mz ∈ LinearMap.range (mapK hA s.π i) ⊔
      Submodule.span (degreeZeroSubring A) (Set.range (cokVec hA hk s i)) := by
    rw [(isCompl_cokVec hA hk s i).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp htop
  obtain ⟨yq, rfl⟩ := LinearMap.mem_range.mp ha
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ yq
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hb
  let w : cocyclesK hA M i := cocyclesKMap hA s.π i y + c.sum (fun j a => a • cokRep hA hk s i j)
    - mz
  have hw : Submodule.Quotient.mk w = (0 : HK hA M i) := by
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_add, ← mapK_mk, ← hab, ← hc,
      sub_eq_zero]
    congr 1
    show Submodule.Quotient.mk (∑ j ∈ c.support, c j • cokRep hA hk s i j) =
      ∑ j ∈ c.support, c j • cokVec hA hk s i j
    rw [← Submodule.mkQ_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Submodule.mkQ_apply, mk_cokRep]
  obtain ⟨-, m', hm', hdm'⟩ := (mkK_eq_zero_iff hA _).mp hw
  refine ⟨incl s _ (y : s.obj) + ∑ j ∈ c.support,
      ((c j : degreeZeroSubring A) : A) • newGen s (cells hA hk s i) (Sum.inr j), ?_, ?_,
      m', hm', ?_⟩
  · refine add_mem ((incl s _).map_mem y.2.1) (sum_mem fun j _ => ?_)
    have := smul_mem_grading (mem_degreeZeroSubring.mp (c j).2)
      (newGen_mem s (cells hA hk s i) (Sum.inr j))
    simpa [cells, cokCell] using this
  · rw [d_add, ← DGModuleHom.map_d, y.2.2, map_zero, zero_add, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [d_smul_newGen hA hk s i (mem_degreeZeroSubring.mp (c j).2)]
    change _ • incl s _ 0 = 0
    rw [map_zero, smul_zero]
  · rw [hdm', map_add, map_sum, step_π_incl]
    simp only [map_smul, step_π_newGen]
    simp only [w, mz, Finsupp.sum, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_sum,
      Submodule.coe_smul]
    rfl

/-- **Minimality of the next stage.** If the cocycles of degree `g + 1` of `s` mapping to
coboundaries are decomposable, the next stage is minimal when `s` is. -/
theorem isMinimal_nextStage (hdA : ∀ a ∈ grading (M := A) (-1), d a = 0)
    (hmin : IsMinimal A s.obj)
    (hker : ∀ z ∈ grading (M := s.obj) (g + 1), d z = 0 →
      (∃ m ∈ grading (M := M) (g + 1 - 1), d m = s.π z) → z ∈ decomposables A s.obj) :
    IsMinimal A (nextStage hA hk s g).obj := by
  refine isMinimal_step s _ hA hdA hmin ?_
  rintro (i | i)
  · exact hker _ (kerRep hA hk s g i).2.1 (kerRep hA hk s g i).2.2 (exists_kerM hA hk s g i)
  · exact zero_mem _

/-- **The key minimality lemma.** If `s` is decomposable in degrees `≤ g`, every cocycle of the
next stage of degree `g` mapping to a coboundary of `M` is decomposable: its coefficients along
the new generators vanish, by the linear independence of the classes killed (for the generators
killing the kernel) and of the classes hit modulo the image (for the cocycle generators). -/
theorem mem_decomposables_of_cocycle
    (hD : ∀ j ≤ g, ∀ y ∈ grading (M := s.obj) j, y ∈ decomposables A s.obj)
    {z : (nextStage hA hk s g).obj} (hz : z ∈ grading g) (hdz : d z = 0)
    (hπ : ∃ m ∈ grading (M := M) (g - 1), d m = (nextStage hA hk s g).π z) :
    z ∈ decomposables A (nextStage hA hk s g).obj := by
  classical
  obtain ⟨t, l, hl, y, hy, rfl⟩ := exists_eq_sum s (cells hA hk s g) (cells_deg hA hk s g) hz
  let c := cells hA hk s g
  rw [← Finset.toLeft_disjSum_toRight (u := t), Finset.sum_disjSum] at hdz hπ ⊢
  -- the differential
  have hd : ∑ i ∈ t.toLeft, l (Sum.inl i) • (kerRep hA hk s g i : s.obj) + d y = 0 := by
    apply incl_injective s c
    rw [map_zero, ← hdz, map_add, map_sum, d_add, d_add, map_sum, map_sum, ← DGModuleHom.map_d]
    congr 1
    rw [Finset.sum_eq_zero (s := t.toRight) fun i _ => by
      rw [d_smul_newGen hA hk s g (hl _)]
      change _ • incl s c 0 = 0
      rw [map_zero, smul_zero], add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [d_smul_newGen hA hk s g (hl _), map_smul]
    rfl
  -- the kernel coefficients vanish
  have hL : ∀ i ∈ t.toLeft, l (Sum.inl i) = 0 := by
    let r : cocyclesK hA s.obj (g + 1) :=
      ∑ i ∈ t.toLeft, (⟨l (Sum.inl i), hl _⟩ : degreeZeroSubring A) • kerRep hA hk s g i
    have hr : (r : s.obj) = d (-y) := by
      rw [d_neg, ← add_eq_zero_iff_eq_neg.mp hd]
      simp only [r, Submodule.coe_sum, Submodule.coe_smul]
      rfl
    have hr0 : Submodule.Quotient.mk r = (0 : HK hA s.obj (g + 1)) := by
      rw [mkK_eq_zero_iff]
      exact ⟨r.2.1, -y, by simpa using neg_mem hy, hr.symm⟩
    have hsum : ∑ i ∈ t.toLeft, (⟨l (Sum.inl i), hl _⟩ : degreeZeroSubring A) •
        kerVec hA hk s g i = 0 := by
      rw [← hr0]
      show _ = Submodule.mkQ _ (∑ i ∈ t.toLeft,
        (⟨l (Sum.inl i), hl _⟩ : degreeZeroSubring A) • kerRep hA hk s g i)
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, Submodule.mkQ_apply, mk_kerRep]
    intro i hi
    exact congrArg Subtype.val
      (linearIndependent_iff'.mp (kerVec_linearIndependent hA hk s g) _ _ hsum i hi)
  have hdy : d y = 0 := by
    rw [← hd, Finset.sum_eq_zero fun i hi => by rw [hL i hi, zero_smul], zero_add]
  -- the cocycle coefficients vanish
  have hR : ∀ i ∈ t.toRight, l (Sum.inr i) = 0 := by
    obtain ⟨m, hm, hdm⟩ := hπ
    let yz : cocyclesK hA s.obj g := ⟨y, hy, hdy⟩
    let w : cocyclesK hA M g :=
      (∑ i ∈ t.toRight, (⟨l (Sum.inr i), hl _⟩ : degreeZeroSubring A) • cokRep hA hk s g i) +
        cocyclesKMap hA s.π g yz
    have hw : (w : M) = d m := by
      rw [hdm, map_add, map_add, map_sum, map_sum, step_π_incl,
        Finset.sum_eq_zero (s := t.toLeft) fun i hi => by rw [hL i hi, zero_smul, map_zero],
        zero_add]
      simp only [w, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, map_smul,
        step_π_newGen]
      rfl
    have hw0 : Submodule.Quotient.mk w = (0 : HK hA M g) := by
      rw [mkK_eq_zero_iff]
      exact ⟨w.2.1, m, by simpa using hm, hw.symm⟩
    have hsum : ∑ i ∈ t.toRight, (⟨l (Sum.inr i), hl _⟩ : degreeZeroSubring A) •
        cokVec hA hk s g i = 0 := by
      have hmem : ∑ i ∈ t.toRight, (⟨l (Sum.inr i), hl _⟩ : degreeZeroSubring A) •
          cokVec hA hk s g i = -mapK hA s.π g (Submodule.Quotient.mk yz) := by
        have hcomb : Submodule.mkQ _ (∑ i ∈ t.toRight,
            (⟨l (Sum.inr i), hl _⟩ : degreeZeroSubring A) • cokRep hA hk s g i) =
            ∑ i ∈ t.toRight, (⟨l (Sum.inr i), hl _⟩ : degreeZeroSubring A) •
              cokVec hA hk s g i := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_smul, Submodule.mkQ_apply, mk_cokRep]
        rw [eq_neg_iff_add_eq_zero, ← hw0, ← hcomb, mapK_mk, Submodule.mkQ_apply,
          ← Submodule.Quotient.mk_add]
      have h1 : ∑ i ∈ t.toRight, (⟨l (Sum.inr i), hl _⟩ : degreeZeroSubring A) •
          cokVec hA hk s g i ∈ LinearMap.range (mapK hA s.π g) := by
        rw [hmem]
        exact neg_mem (LinearMap.mem_range_self _ _)
      have h2 : ∑ i ∈ t.toRight, (⟨l (Sum.inr i), hl _⟩ : degreeZeroSubring A) •
          cokVec hA hk s g i ∈
            Submodule.span (degreeZeroSubring A) (Set.range (cokVec hA hk s g)) :=
        sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      have := (isCompl_cokVec hA hk s g).inf_eq_bot
      rw [← Submodule.mem_bot (R := degreeZeroSubring A), ← this]
      exact ⟨h1, h2⟩
    intro i hi
    exact congrArg Subtype.val
      (linearIndependent_iff'.mp (cokVec_linearIndependent hA hk s g) _ _ hsum i hi)
  rw [Finset.sum_eq_zero fun i hi => by rw [hL i hi, zero_smul],
    Finset.sum_eq_zero fun i hi => by rw [hR i hi, zero_smul], zero_add, zero_add]
  exact DGModuleHom.map_mem_decomposables _ (hD g le_rfl y hy)

end NextStage

/-! ### The stages and the resolution -/

section Construction

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]
  (M : Type v) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  (hA : IsNonposGraded A) (hk : ∀ a : degreeZeroSubring A, IsUnit a ∨ a = 0) (N : ℤ)

/-- The stages of the minimal resolution: `0`, then the generators of degree `N - n` at
stage `n + 1`. -/
noncomputable def stage : ℕ → Stage A M
  | 0 => ⟨DGModuleCat.of A PUnit, 0⟩
  | n + 1 => nextStage hA hk (stage n) (N - n)

/-- The underlying dg module of the `n`-th stage. -/
abbrev Obj (n : ℕ) : Type (max u v) := (stage M hA hk N n).obj

/-- The inclusion of the `n`-th stage into the next one. -/
noncomputable def ι (n : ℕ) : Obj M hA hk N n →ᵈᵍ[A] Obj M hA hk N (n + 1) :=
  incl (stage M hA hk N n) (cells hA hk (stage M hA hk N n) (N - n))

theorem ι_injective (n : ℕ) : Function.Injective (ι M hA hk N n) :=
  incl_injective _ _

/-- The underlying dg module of the minimal resolution: the colimit of the stages. -/
abbrev Colim : Type (max u v) := SeqColimit (Obj M hA hk N) (ι M hA hk N)

/-- The augmentation of the minimal resolution. -/
noncomputable def π : Colim M hA hk N →ᵈᵍ[A] M :=
  SeqColimit.desc (fun n => (stage M hA hk N n).π) fun _ => step_π_comp_incl _ _

theorem π_of (n : ℕ) (x : Obj M hA hk N n) :
    π M hA hk N (SeqColimit.of _ _ n x) = (stage M hA hk N n).π x :=
  SeqColimit.desc_of _ _ _ _

variable {M}

theorem stage_zero_eq_zero (x : Obj M hA hk N 0) : x = 0 := Subsingleton.elim (α := PUnit) _ _

variable (hdA : ∀ a ∈ grading (M := A) (-1), d a = 0)
  (hM : ∀ i > N, ∀ m ∈ grading (M := M) i, d m = 0 → ∃ m' ∈ grading (M := M) (i - 1), d m' = m)

include hdA hM in
/-- The invariants of the stages: injectivity and surjectivity on cohomology in high degrees,
decomposability in low degrees, decomposability of the cocycles to be killed next, and
minimality. -/
theorem invariants (n : ℕ) :
    (∀ i ≥ N - n + 2, InjAt (stage M hA hk N n) i) ∧
    (∀ i ≥ N - n + 1, SurjAt (stage M hA hk N n) i) ∧
    (∀ j ≤ N - n, ∀ y ∈ grading (M := Obj M hA hk N n) j,
      y ∈ decomposables A (Obj M hA hk N n)) ∧
    (∀ z ∈ grading (M := Obj M hA hk N n) (N - n + 1), d z = 0 →
      (∃ m ∈ grading (M := M) (N - n + 1 - 1), d m = (stage M hA hk N n).π z) →
        z ∈ decomposables A (Obj M hA hk N n)) ∧
    IsMinimal A (Obj M hA hk N n) := by
  induction n with
  | zero =>
    refine ⟨fun i _ x _ _ _ => ⟨0, zero_mem _, (stage_zero_eq_zero hA hk N x).symm ▸ d_zero⟩,
      fun i hi m hm hdm => ?_, fun j _ y _ => (stage_zero_eq_zero hA hk N y) ▸ zero_mem _,
      fun z _ _ _ => (stage_zero_eq_zero hA hk N z) ▸ zero_mem _,
      fun x => (stage_zero_eq_zero hA hk N x) ▸ (d_zero (M := Obj M hA hk N 0)).symm ▸ zero_mem _⟩
    obtain ⟨m', hm', hdm'⟩ := hM i (by push_cast at hi; omega) m hm hdm
    refine ⟨0, zero_mem _, d_zero, -m', neg_mem hm', ?_⟩
    rw [d_neg, hdm', map_zero, zero_sub]
  | succ n ih =>
    obtain ⟨hinj, hsurj, hD, hker, hmin⟩ := ih
    let s := stage M hA hk N n
    refine ⟨fun i hi => injAt_nextStage hA hk s (N - n) (fun i hi => hinj i (by omega)) i
        (by push_cast at hi; omega),
      fun i hi => surjAt_nextStage hA hk s (N - n) (fun i hi => hsurj i (by omega)) i
        (by push_cast at hi; omega),
      fun j hj y hy => mem_decomposables_of_le s (cells hA hk s (N - n)) (cells_deg hA hk s _)
        hD (by push_cast at hj; omega) hy,
      fun z hz hdz ⟨m, hm, hdm⟩ => mem_decomposables_of_cocycle hA hk s (N - n) hD
        (by rwa [show N - ((n + 1 : ℕ) : ℤ) + 1 = N - n by push_cast; ring] at hz) hdz
        ⟨m, by rwa [show N - ((n + 1 : ℕ) : ℤ) + 1 - 1 = N - n - 1 by push_cast; ring] at hm,
          hdm⟩,
      isMinimal_nextStage hA hk s (N - n) hdA hmin hker⟩

/-- Elements of the stages of degree `> N` vanish. -/
theorem stage_eq_zero (n : ℕ) {j : ℤ} (hj : N < j) {x : Obj M hA hk N n}
    (hx : x ∈ grading j) : x = 0 := by
  induction n with
  | zero => exact stage_zero_eq_zero hA hk N x
  | succ n ih =>
    obtain ⟨y, hy, rfl⟩ := exists_eq_incl (stage M hA hk N n) _ hA (cells_deg hA hk _ (N - n))
      (by omega : N - n < j) hx
    rw [ih hy, map_zero]

include hdA hM in
/-- The augmentation of the minimal resolution is a quasi-isomorphism. -/
theorem isQuasiIso_π : (π M hA hk N).IsQuasiIso := fun j => by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, N - n + 2 ≤ j := ⟨(N - j + 2).toNat, by omega⟩
  constructor
  · rw [cohomology.map_injective_iff]
    intro x hx hdx hpx
    obtain ⟨n₀, y₀, rfl⟩ := SeqColimit.exists_of_eq x
    obtain ⟨y, hy⟩ := SeqColimit.filtration_mono (le_max_left n₀ n)
      (SeqColimit.of_mem_filtration (ι := ι M hA hk N) n₀ y₀)
    replace hy : SeqColimit.of _ _ (max n₀ n) y = SeqColimit.of _ _ n₀ y₀ := hy
    have hinj := SeqColimit.of_injective (ι_injective M hA hk N) (max n₀ n)
    rw [← hy] at hx hdx hpx ⊢
    have hy' : y ∈ grading j := (SeqColimit.of _ _ _).mem_grading_of_injective hinj hx
    have hdy : d y = 0 := hinj (by rw [DGModuleHom.map_d, hdx, map_zero])
    obtain ⟨m, hm, hdm⟩ := mem_coboundaries.mp hpx
    rw [π_of] at hdm
    obtain ⟨z, hz, hdz⟩ := ((invariants hA hk N hdA hM (max n₀ n)).1 j
      (by have := le_max_right n₀ n; omega)) y hy' hdy ⟨m, hm, hdm⟩
    exact mem_coboundaries.mpr ⟨SeqColimit.of _ _ _ z, (SeqColimit.of _ _ _).map_mem hz, by
      rw [← DGModuleHom.map_d, hdz]⟩
  · rw [cohomology.map_surjective_iff]
    intro m hm hdm
    obtain ⟨x, hx, hdx, m', hm', hdm'⟩ :=
      (invariants hA hk N hdA hM n).2.1 j (by omega) m hm hdm
    exact ⟨SeqColimit.of _ _ n x, (SeqColimit.of _ _ n).map_mem hx,
      by rw [← DGModuleHom.map_d, hdx, map_zero],
      mem_coboundaries.mpr ⟨m', hm', by rw [π_of, hdm']⟩⟩

include hdA hM in
/-- The minimal resolution is minimal. -/
theorem isMinimal_colim : IsMinimal A (Colim M hA hk N) := fun x => by
  obtain ⟨n, y, rfl⟩ := SeqColimit.exists_of_eq x
  rw [← DGModuleHom.map_d]
  exact DGModuleHom.map_mem_decomposables _ ((invariants hA hk N hdA hM n).2.2.2.2 y)

/-- The minimal resolution vanishes in degrees `> N`. -/
theorem isBoundedAbove_colim : IsBoundedAbove (Colim M hA hk N) := ⟨N, fun i hi x hx => by
  obtain ⟨n, y, rfl⟩ := SeqColimit.exists_of_eq x
  have hinj := SeqColimit.of_injective (ι_injective M hA hk N) n
  rw [stage_eq_zero hA hk N n hi ((SeqColimit.of _ _ n).mem_grading_of_injective hinj hx),
    map_zero]⟩

/-! ### The semi-free filtration -/

section Filtration

variable (M)

theorem bijective_rangeRestrict (n : ℕ) :
    Function.Bijective (SeqColimit.of (Obj M hA hk N) (ι M hA hk N) n).rangeRestrict :=
  ⟨fun _ _ h => SeqColimit.of_injective (ι_injective M hA hk N) n (congrArg Subtype.val h),
    fun ⟨_, y, hy⟩ => ⟨y, Subtype.ext hy⟩⟩

/-- The `n`-th member of the filtration of the resolution, identified with the `n`-th stage. -/
noncomputable def toObj (n : ℕ) :
    SeqColimit.filtration (S := Obj M hA hk N) (ι := ι M hA hk N) n →ᵈᵍ[A] Obj M hA hk N n :=
  (SeqColimit.of _ _ n).rangeRestrict.inverse (bijective_rangeRestrict M hA hk N n)

theorem of_toObj {n : ℕ} (x : SeqColimit.filtration (S := Obj M hA hk N) (ι := ι M hA hk N) n) :
    SeqColimit.of _ _ n (toObj M hA hk N n x) = (x : Colim M hA hk N) :=
  congrArg Subtype.val (DGModuleHom.apply_inverse_apply _ (bijective_rangeRestrict M hA hk N n) x)

theorem toObj_eq {n : ℕ} {x : SeqColimit.filtration (S := Obj M hA hk N) (ι := ι M hA hk N) n}
    {y : Obj M hA hk N n} (h : SeqColimit.of _ _ n y = (x : Colim M hA hk N)) :
    toObj M hA hk N n x = y :=
  SeqColimit.of_injective (ι_injective M hA hk N) n (by rw [of_toObj, h])

/-- The projection of the `(n + 1)`-st member of the filtration onto the generators attached at
stage `n + 1`. -/
noncomputable def filtrationπ (n : ℕ) :
    SeqColimit.filtration (S := Obj M hA hk N) (ι := ι M hA hk N) (n + 1) →ᵈᵍ[A]
      ⨁ i : KerIndex hA hk (stage M hA hk N n) (N - n) ⊕ CokIndex hA hk (stage M hA hk N n) (N - n),
        Shift (1 + -(cells hA hk (stage M hA hk N n) (N - n) i).deg) A :=
  (DGModuleHom.shiftDirectSum 1 fun i => -(cells hA hk (stage M hA hk N n) (N - n) i).deg).comp
    ((Cone.fstHom (attach (cells hA hk (stage M hA hk N n) (N - n)))).comp (toObj M hA hk N (n + 1)))

theorem surjective_filtrationπ (n : ℕ) : Function.Surjective (filtrationπ M hA hk N n) := by
  refine (DGModuleHom.shiftDirectSum_bijective _ _).2.comp
    (Function.Surjective.comp (fun y => ⟨Cone.inlLinear _ y, Cone.fstHom_inlLinear y⟩) ?_)
  intro y
  exact ⟨⟨SeqColimit.of _ _ (n + 1) y, SeqColimit.of_mem_filtration (ι := ι M hA hk N) (n + 1) y⟩,
    toObj_eq M hA hk N rfl⟩

theorem filtrationπ_eq_zero_iff (n : ℕ)
    (x : SeqColimit.filtration (S := Obj M hA hk N) (ι := ι M hA hk N) (n + 1)) :
    filtrationπ M hA hk N n x = 0 ↔ (x : Colim M hA hk N) ∈ SeqColimit.filtration n := by
  rw [filtrationπ, DGModuleHom.comp_apply,
    map_eq_zero_iff _ (DGModuleHom.shiftDirectSum_bijective _ _).1, DGModuleHom.comp_apply]
  constructor
  · intro h
    have hy : toObj M hA hk N (n + 1) x = ι M hA hk N n (Cone.sndLinear
        (attach (cells hA hk (stage M hA hk N n) (N - n))) (toObj M hA hk N (n + 1) x)) :=
      Cone.ext (h.trans (Cone.fstHom_inr _).symm) (Cone.sndLinear_inr _).symm
    refine ⟨Cone.sndLinear (attach (cells hA hk (stage M hA hk N n) (N - n)))
      (toObj M hA hk N (n + 1) x), ?_⟩
    change SeqColimit.of _ _ n _ = _
    rw [← SeqColimit.of_succ_ι (ι := ι M hA hk N), ← hy, of_toObj]
  · rintro ⟨y, hy⟩
    have h' : toObj M hA hk N (n + 1) x = ι M hA hk N n y :=
      toObj_eq M hA hk N (by rw [SeqColimit.of_succ_ι]; exact hy)
    exact (congrArg (Cone.fstHom (attach (cells hA hk (stage M hA hk N n) (N - n)))) h').trans
      (Cone.fstHom_inr y)

/-- The minimal resolution is semi-free. -/
noncomputable def semiFreeFiltration : SemiFreeFiltration.{max u v} A (Colim M hA hk N) where
  F := SeqColimit.filtration
  mono := SeqColimit.filtration_mono
  eq_zero_of_mem_zero x hx := by
    obtain ⟨y, rfl⟩ := hx
    exact map_zero (SeqColimit.of (Obj M hA hk N) (ι M hA hk N) 0)
  exists_mem := SeqColimit.exists_mem_filtration
  ι n := KerIndex hA hk (stage M hA hk N n) (N - n) ⊕ CokIndex hA hk (stage M hA hk N n) (N - n)
  decEq _ := Classical.decEq _
  deg n i := 1 + -(cells hA hk (stage M hA hk N n) (N - n) i).deg
  π := filtrationπ M hA hk N
  surjective_π := surjective_filtrationπ M hA hk N
  π_eq_zero_iff := filtrationπ_eq_zero_iff M hA hk N

end Filtration

end Construction

end MinimalResolution

/-! ### Existence and uniqueness of minimal resolutions -/

section Main

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]
  (M : Type v) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]

/-- **Minimal semi-free resolutions over connective dg rings.** Let `A` be a dg ring
concentrated in non-positive degrees, with `d(A⁻¹) = 0` and every nonzero element of `A⁰` a
unit, and let `M` be a dg `A`-module with `Hⁱ(M) = 0` for `i > N`. Then `M` has a semi-free
resolution `π : P → M` (a quasi-isomorphism) with `P` minimal (`d(P) ⊆ A^{<0} P`) and
concentrated in degrees `≤ N`. -/
theorem exists_minimal_semiFreeResolution (hA : IsNonposGraded A)
    (hdA : ∀ a ∈ grading (M := A) (-1), d a = 0)
    (hk : ∀ a : degreeZeroSubring A, IsUnit a ∨ a = 0) (N : ℤ)
    (hM : ∀ i > N, ∀ m ∈ grading (M := M) i, d m = 0 →
      ∃ m' ∈ grading (M := M) (i - 1), d m' = m) :
    ∃ (P : Type (max u v)) (_ : AddCommGroup P) (_ : DGAddCommGroup P) (_ : Module A P)
      (_ : DGModule A P) (π : P →ᵈᵍ[A] M), π.IsQuasiIso ∧
        Nonempty (SemiFreeFiltration.{max u v} A P) ∧ IsMinimal A P ∧ IsBoundedAbove P :=
  ⟨MinimalResolution.Colim M hA hk N, inferInstance, inferInstance, inferInstance, inferInstance,
    MinimalResolution.π M hA hk N, MinimalResolution.isQuasiIso_π hA hk N hdA hM,
    ⟨MinimalResolution.semiFreeFiltration M hA hk N⟩, MinimalResolution.isMinimal_colim hA hk N hdA hM,
    MinimalResolution.isBoundedAbove_colim hA hk N⟩

/-- The minimal resolution is minimal and bounded above in the sense of the uniqueness theorem
`DG.IsKProjective.exists_bijective_of_isBoundedMinimal`. -/
theorem MinimalResolution.isBoundedMinimal_colim (hA : IsNonposGraded A)
    (hdA : ∀ a ∈ grading (M := A) (-1), d a = 0)
    (hk : ∀ a : degreeZeroSubring A, IsUnit a ∨ a = 0) (N : ℤ)
    (hM : ∀ i > N, ∀ m ∈ grading (M := M) i, d m = 0 →
      ∃ m' ∈ grading (M := M) (i - 1), d m' = m) :
    IsBoundedMinimal A (MinimalResolution.Colim M hA hk N) :=
  ⟨MinimalResolution.isMinimal_colim hA hk N hdA hM,
    Or.inr ⟨fun _ hj _ ha => hA.eq_zero hj ha, MinimalResolution.isBoundedAbove_colim hA hk N⟩⟩

end Main

end DG
