import DG.Homotopy.ConeCochain
import DG.Module.Corner
import DG.Module.DirectSum

/-!
# K-projective dg modules

Let `A` be a dg ring. This file defines acyclic dg modules and K-projective (homotopically
projective) dg modules, proves the basic closure properties of K-projective modules, and shows
that `HOM_A(P, -)` preserves quasi-isomorphisms when `P` is K-projective.

## Main definitions

* `DG.IsAcyclic M`: all cohomology groups of the dg abelian group `M` vanish. It applies to dg
  modules and to Hom complexes `DG.DGModule.HOM A M N`.
* `DG.IsKProjective A P`: every morphism from `P` to an acyclic dg module is null-homotopic,
  i.e. `Hom_{H(A)}(P, N) = 0` for all acyclic `N`. The test modules range over a fixed universe
  `w`, a parameter of the definition (`DG.IsKProjective.{w} A P`).
* `DG.GradedSplitting i p`: a splitting, by graded `A`-linear maps of degree `0`, of a sequence
  `F → G → Q` of dg modules; such data exist iff `0 → F → G → Q → 0` is a short exact sequence
  of dg modules which is split as a sequence of graded `A`-modules.
* `DG.Cochain.ofElement y`: the cochain `a ↦ (-1)^{k |a|} a • y` out of `A` attached to
  `y ∈ Nᵏ`; `DG.Cochain.directSumDesc`: cochains out of a direct sum.
* `DG.DGModule.HOM.postcomp A P s`: postcomposition with `s : N → N'` on Hom complexes;
  `DG.DGModuleHom.postcompHomotopy P s`: postcomposition on morphisms up to homotopy.

## Main results

* `DG.isKProjective_iff_subsingleton_cohomology_hom`: `P` is K-projective iff
  `H⁰(HOM_A(P, N)) = 0` for all acyclic `N`; `DG.isKProjective_iff_isAcyclic_hom`: iff
  `HOM_A(P, N)` is acyclic for all acyclic `N`.
* Closure properties: `DG.isKProjective_self` (`A` is K-projective),
  `DG.IsKProjective.shift`, `DG.IsKProjective.of_retract` (homotopy retracts, in particular
  direct summands), `DG.IsKProjective.of_dgModuleEquiv`, `DG.IsKProjective.of_dgHomotopyEquiv`,
  `DG.DGIdempotent.isKProjective_leftCorner` (`A e` for a degree-`0` idempotent cocycle `e`),
  `DG.IsKProjective.directSum` (arbitrary direct sums), `DG.IsKProjective.of_gradedSplitting`
  (extensions which split as graded modules), `DG.IsKProjective.cone` (mapping cones),
  `DG.IsContractible.isKProjective`.
* `DG.GradedSplitting.exists_extension`: null-homotopies extend along a graded-split
  monomorphism whose cokernel admits no non-null-homotopic maps to the target; this is the
  inductive step for semi-free modules (`DG.Homotopy.SemiFree`).
* `DG.DGModuleHom.isQuasiIso_iff_isAcyclic_cone`: a morphism is a quasi-isomorphism iff its
  mapping cone is acyclic (proved directly, by a diagram chase on cocycles).
* `DG.IsKProjective.bijective_cohomology_postcomp`: for K-projective `P`, `HOM_A(P, -)`
  preserves quasi-isomorphisms; `DG.IsKProjective.postcompHomotopyEquiv`: for a
  quasi-isomorphism `N → N'`, `Hom_{H(A)}(P, N) ≃ Hom_{H(A)}(P, N')`.

## References

* [B. Keller, *Deriving DG categories*, Ann. Sci. ÉNS 27 (1994), §3]
* [J. Bernstein, V. Lunts, *Equivariant sheaves and functors*, LNM 1578 (1994), §10.12]
* [The Stacks project, Tag 09KK and following]

## Universes

K-projectivity quantifies over test modules `N`, so it depends on a universe: `IsKProjective.{w}`
asks the condition for all `N : Type w`. The closure properties hold for each fixed `w`; the
statements about quasi-isomorphisms `N → N'` take `N N' : Type w` (so that the mapping cone is
again in `Type w`).
-/

open DirectSum

universe w

namespace DG

/-! ### Acyclic dg abelian groups -/

section Acyclic

variable (M : Type*) [AddCommGroup M] [DGAddCommGroup M]

/-- A dg abelian group (for instance a dg module, or a Hom complex) is acyclic if all its
cohomology groups vanish. -/
def IsAcyclic : Prop := ∀ n : ℤ, Subsingleton (cohomology M n)

variable {M}

/-- A dg abelian group is acyclic iff every homogeneous cocycle is a coboundary. -/
theorem isAcyclic_iff : IsAcyclic M ↔
    ∀ (n : ℤ) (m : M), m ∈ grading n → d m = 0 → ∃ m' ∈ grading (n - 1), d m' = m := by
  constructor
  · intro h n m hm hdm
    have := (h n).elim (cohomology.mk M n ⟨m, hm, hdm⟩) 0
    exact (cohomology.mk_eq_zero_iff _).mp this
  · intro h n
    refine subsingleton_of_forall_eq 0 fun x => ?_
    induction x using cohomology.induction_on with
    | h z => exact (cohomology.mk_eq_zero_iff z).mpr (h n z z.2.1 z.2.2)

theorem IsAcyclic.exists_d_eq (h : IsAcyclic M) {n : ℤ} {m : M} (hm : m ∈ grading n)
    (hdm : d m = 0) : ∃ m' ∈ grading (n - 1), d m' = m :=
  isAcyclic_iff.mp h n m hm hdm

/-- Shifts of acyclic dg abelian groups are acyclic. -/
theorem IsAcyclic.shift (h : IsAcyclic M) (k : ℤ) : IsAcyclic (Shift k M) := by
  refine isAcyclic_iff.mpr fun n m hm hdm => ?_
  have hdm' : d (Shift.unmk k m) = 0 := by
    have := congrArg (Shift.unmk k) hdm
    rw [Shift.unmk_d, Shift.unmk_zero] at this
    have h2 := congrArg (koszulSign k • ·) this
    simp only [smul_smul, Int.units_mul_self, one_smul, smul_zero] at h2
    exact h2
  obtain ⟨m', hm', hdm''⟩ := h.exists_d_eq (Shift.unmk_mem_grading hm) hdm'
  refine ⟨Shift.mk k (koszulSign k • m'), ?_, ?_⟩
  · rw [Shift.mem_grading_iff, sub_add_eq_add_sub]
    exact units_smul_mem_grading _ hm'
  · rw [Shift.d_mk, d_units_smul, smul_smul, Int.units_mul_self, one_smul, hdm'', Shift.mk_unmk]

theorem isAcyclic_of_subsingleton [Subsingleton M] : IsAcyclic M := by
  refine isAcyclic_iff.mpr fun n m _ _ => ⟨0, zero_mem _, Subsingleton.elim _ _⟩

end Acyclic

/-! ### Acyclic Hom complexes -/

section HomAcyclic

variable {A : Type*} {M N : Type*} [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]

/-- The Hom complex `HOM_A(M, N)` is acyclic iff every cocycle of the Hom complex is a
coboundary. -/
theorem isAcyclic_hom_iff : IsAcyclic (DGModule.HOM A M N) ↔
    ∀ (n m : ℤ), m + 1 = n → ∀ z : Cochain A M N n, δ n (n + 1) z = 0 →
      ∃ y : Cochain A M N m, δ m n y = z := by
  constructor
  · intro h n m hmn z hz
    have hsub := (DGModule.HOM.cohomologyAddEquiv A M N n).toEquiv.subsingleton_congr.mp (h n)
    have h0 : (QuotientAddGroup.mk (Cocycle.mk z (n + 1) rfl hz) :
        Cocycle A M N n ⧸ Cocycle.coboundaries A M N n) = 0 := Subsingleton.elim _ _
    rw [QuotientAddGroup.eq_zero_iff, Cocycle.mem_coboundaries_iff m hmn] at h0
    exact h0
  · intro h n
    refine (DGModule.HOM.cohomologyAddEquiv A M N n).toEquiv.subsingleton_congr.mpr ?_
    refine subsingleton_of_forall_eq 0 fun x => ?_
    induction x using QuotientAddGroup.induction_on with
    | H z =>
      rw [QuotientAddGroup.eq_zero_iff, Cocycle.mem_coboundaries_iff (n - 1) (sub_add_cancel n 1)]
      exact h n (n - 1) (sub_add_cancel n 1) z (Cocycle.δ_eq_zero z _)

/-- In an acyclic Hom complex, every cocycle is a coboundary. -/
theorem IsAcyclic.exists_δ_eq (h : IsAcyclic (DGModule.HOM A M N)) {n m : ℤ} (hmn : m + 1 = n)
    (z : Cochain A M N n) (hz : δ n (n + 1) z = 0) : ∃ y : Cochain A M N m, δ m n y = z :=
  isAcyclic_hom_iff.mp h n m hmn z hz

/-- A morphism is null-homotopic iff it is the differential of a `(-1)`-cochain. -/
theorem homotopic_zero_iff_exists {f : M →ᵈᵍ[A] N} :
    Homotopic f 0 ↔ ∃ h : Cochain A M N (-1), Cochain.ofHom f = δ (-1) 0 h :=
  mem_nullHomotopic_iff_exists

end HomAcyclic

/-! ### K-projective dg modules -/

section KProjective

variable (A : Type*) [Ring A] [DGAddCommGroup A]
  (P : Type*) [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]

/-- A dg module `P` is K-projective (homotopically projective) if every morphism from `P` to
an acyclic dg module is null-homotopic, that is, `Hom_{H(A)}(P, N) = 0` for every acyclic `N`.

The test modules `N` range over one universe `w`, which is a parameter of the definition:
`IsKProjective.{w} A P`. All closure properties below hold for every fixed `w`. -/
@[pp_with_univ]
def IsKProjective : Prop :=
  ∀ (N : Type w) [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N],
    IsAcyclic N → ∀ f : P →ᵈᵍ[A] N, Homotopic f 0

variable {A P}

theorem IsKProjective.homotopic_zero (hP : IsKProjective.{w} A P) {N : Type w} [AddCommGroup N]
    [DGAddCommGroup N] [Module A N] [DGModule A N] (hN : IsAcyclic N) (f : P →ᵈᵍ[A] N) :
    Homotopic f 0 :=
  hP N hN f

theorem subsingleton_quotient_nullHomotopic_iff {N : Type*} [AddCommGroup N] [DGAddCommGroup N]
    [Module A N] [DGModule A N] :
    Subsingleton ((P →ᵈᵍ[A] N) ⧸ nullHomotopic A P N) ↔ ∀ f : P →ᵈᵍ[A] N, Homotopic f 0 := by
  constructor
  · intro h f
    have h0 : (QuotientAddGroup.mk f : (P →ᵈᵍ[A] N) ⧸ nullHomotopic A P N) = 0 :=
      Subsingleton.elim _ _
    exact (QuotientAddGroup.eq_zero_iff f).mp h0
  · intro h
    refine subsingleton_of_forall_eq 0 fun x => ?_
    induction x using QuotientAddGroup.induction_on with
    | H f => exact (QuotientAddGroup.eq_zero_iff f).mpr (h f)

/-- `P` is K-projective iff `H⁰(HOM_A(P, N)) = 0` for every acyclic `N`. -/
theorem isKProjective_iff_subsingleton_cohomology_hom :
    IsKProjective.{w} A P ↔ ∀ (N : Type w) [AddCommGroup N] [DGAddCommGroup N] [Module A N]
      [DGModule A N], IsAcyclic N → Subsingleton (cohomology (DGModule.HOM A P N) 0) := by
  refine forall_congr' fun N => ?_
  refine forall₂_congr fun _ _ => forall₃_congr fun _ _ _ => ?_
  rw [← (quotientNullHomotopicAddEquivCohomology A P N).toEquiv.subsingleton_congr,
    subsingleton_quotient_nullHomotopic_iff]

variable [DGRing A]

/-- For a K-projective `P` and an acyclic `N`, the whole Hom complex `HOM_A(P, N)` is acyclic:
a cocycle `z` of degree `n` is a morphism `P → N⟦n⟧` (`Cochain.rightShift`), and `N⟦n⟧` is
acyclic. -/
theorem IsKProjective.isAcyclic_hom (hP : IsKProjective.{w} A P) {N : Type w} [AddCommGroup N]
    [DGAddCommGroup N] [Module A N] [DGModule A N] (hN : IsAcyclic N) :
    IsAcyclic (DGModule.HOM A P N) := by
  refine isAcyclic_hom_iff.mpr fun n m hmn z hz => ?_
  have hz' : δ 0 1 (z.rightShift n 0 (zero_add n)) = 0 := by
    rw [Cochain.δ_rightShift z n 0 1 (zero_add n) (n + 1) (add_comm 1 n), hz,
      Cochain.rightShift_zero, smul_zero]
  obtain ⟨h, hh⟩ := homotopic_zero_iff_exists.mp
    (hP (Shift n N) (hN.shift n) (Cocycle.homOf (Cocycle.mk _ 1 (zero_add 1) hz')))
  refine ⟨koszulSign n • h.rightUnshift m (by omega), ?_⟩
  rw [δ_units_smul, Cochain.δ_rightUnshift h m (by omega) n 0 (zero_add n), smul_smul,
    Int.units_mul_self, one_smul, ← hh, Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.mk_coe,
    Cochain.rightUnshift_rightShift]

/-- `P` is K-projective iff `HOM_A(P, N)` is acyclic for every acyclic `N`. -/
theorem isKProjective_iff_isAcyclic_hom :
    IsKProjective.{w} A P ↔ ∀ (N : Type w) [AddCommGroup N] [DGAddCommGroup N] [Module A N]
      [DGModule A N], IsAcyclic N → IsAcyclic (DGModule.HOM A P N) := by
  refine ⟨fun hP N _ _ _ _ hN => hP.isAcyclic_hom hN, fun h N _ _ _ _ hN f => ?_⟩
  obtain ⟨y, hy⟩ := (h N hN).exists_δ_eq (neg_add_cancel 1) (Cochain.ofHom f) (δ_ofHom _)
  exact homotopic_zero_iff_exists.mpr ⟨y, hy.symm⟩

end KProjective

/-! ### Cochains out of `A` -/

section Regular

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]

namespace Cochain

/-- The cochain of degree `k` from `A` to `N` attached to `y ∈ Nᵏ`:
`a ↦ (-1)^{k |a|} a • y` for `a` homogeneous. Every cochain of degree `k` out of `A` is of this
form (`DG.Cochain.eq_ofElement`). -/
def ofElement {k : ℤ} (y : N) (hy : y ∈ grading k) : Cochain A A N k where
  toFun a := Shift.twist A k a • y
  map_zero' := by simp
  map_add' a b := by simp [add_smul]
  map_mem' i a ha := smul_mem_grading (Shift.twist_mem ha) hy
  map_smul' {i b} hb a := by
    show Shift.twist A k (b • a) • y = koszulSign (k * i) • (b • (Shift.twist A k a • y))
    rw [smul_eq_mul, map_mul, Shift.twist_of_mem hb, mul_smul, smul_assoc]

theorem ofElement_apply {k : ℤ} (y : N) (hy : y ∈ grading k) (a : A) :
    ofElement y hy a = Shift.twist A k a • y := rfl

@[simp]
theorem ofElement_one {k : ℤ} (y : N) (hy : y ∈ grading k) : ofElement y hy (1 : A) = y := by
  rw [ofElement_apply, map_one, one_smul]

theorem ofElement_congr {k : ℤ} {y y' : N} (h : y = y') (hy : y ∈ grading k)
    (hy' : y' ∈ grading k) : ofElement (A := A) y hy = ofElement y' hy' := by
  subst h; rfl

omit [DGRing A] [DGModule A N] in
/-- A cochain of degree `0` is `A`-linear for all (not only homogeneous) scalars. -/
theorem map_smul_of_degree_zero {M : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M]
    (z : Cochain A M N 0) (a : A) (x : M) : z (a • x) = a • z x := by
  induction a using DG.induction_on with
  | h_zero => simp
  | h_homogeneous a =>
    rw [z.map_smul a.2, zero_mul, koszulSign, Int.negOnePow_zero, one_smul]
  | h_add a a' ha ha' => rw [add_smul, map_add, ha, ha', add_smul]

/-- Every cochain of degree `k` out of `A` is `ofElement` of its value at `1`. -/
theorem eq_ofElement {k : ℤ} (z : Cochain A A N k) :
    z = ofElement (z 1) (by simpa using z.map_mem (one_mem_grading (A := A))) := by
  ext a
  rw [ofElement_apply]
  induction a using DG.induction_on with
  | h_zero => simp
  | h_homogeneous a =>
    have h := z.map_smul a.2 (1 : A)
    rw [smul_eq_mul, mul_one] at h
    rw [h, Shift.twist_of_mem a.2, smul_assoc, mul_comm]
  | h_add a a' ha ha' => rw [map_add, ha, ha', map_add, add_smul]

theorem ofHom_eq_ofElement (f : A →ᵈᵍ[A] N) :
    ofHom f = ofElement (f 1) (f.map_mem (one_mem_grading (A := A))) := by
  ext a
  rw [ofHom_apply, ofElement_apply, Shift.twist_zero, ← _root_.map_smul, smul_eq_mul, mul_one]

/-- The differential of `ofElement y` is `ofElement (d y)`. -/
theorem δ_ofElement (k m : ℤ) (hkm : k + 1 = m) (y : N) (hy : y ∈ grading k)
    (hdy : d y ∈ grading m) : δ k m (ofElement (A := A) y hy) = ofElement (d y) hdy := by
  ext a
  induction a using DG.induction_on with
  | h_zero => simp
  | h_homogeneous a =>
    obtain ⟨a, ha⟩ := a
    rename_i i
    subst hkm
    rw [δ_apply _ _ rfl, ofElement_apply, ofElement_apply, ofElement_apply,
      Shift.twist_of_mem ha, Shift.twist_of_mem (d_mem ha), Shift.twist_of_mem ha, smul_assoc,
      smul_assoc, smul_assoc, d_units_smul, d_smul ha, smul_smul, smul_add, smul_smul]
    have e1 : koszulSign k * koszulSign (k * (i + 1)) = koszulSign (k * i) := by
      rw [← koszulSign_add]; exact koszulSign_eq_of_sub_eq_two_mul k (by ring)
    have e2 : koszulSign (k * i) * koszulSign i = koszulSign ((k + 1) * i) := by
      rw [← koszulSign_add]; congr 1; ring
    rw [e1, e2]
    abel
  | h_add a a' ha ha' => rw [map_add, ha, ha', map_add]

end Cochain

variable (A) in
/-- A dg ring is K-projective as a dg module over itself: a morphism `f : A → N` is determined
by the cocycle `f 1 ∈ N⁰`, which is a coboundary `d y` if `N` is acyclic, and then
`a ↦ (-1)^{|a|} a • y` is a null-homotopy of `f`. -/
theorem isKProjective_self : IsKProjective.{w} A A := by
  intro N _ _ _ _ hN f
  have hf1 : f 1 ∈ grading 0 := f.map_mem (one_mem_grading (A := A))
  have h1 : d (f 1) = 0 := by rw [← f.map_d, d_one, map_zero]
  obtain ⟨y, hy, hdy⟩ := hN.exists_d_eq hf1 h1
  have hy' : y ∈ grading (-1) := by simpa using hy
  refine homotopic_zero_iff_exists.mpr ⟨Cochain.ofElement y hy', ?_⟩
  rw [Cochain.δ_ofElement (-1) 0 (neg_add_cancel 1) y hy' (hdy ▸ hf1),
    Cochain.ofHom_eq_ofElement]
  exact Cochain.ofElement_congr hdy.symm _ _

end Regular

/-! ### Closure properties of K-projective modules -/

section Closure

variable {A : Type*} [Ring A] [DGAddCommGroup A]
  {P Q : Type*} [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]
  [AddCommGroup Q] [DGAddCommGroup Q] [Module A Q] [DGModule A Q]

/-- A homotopy retract of a K-projective dg module is K-projective: if `r ∘ i ≃ id` for
`i : Q → P` and `r : P → Q` and `P` is K-projective, so is `Q`. In particular direct summands
of K-projective modules are K-projective. -/
theorem IsKProjective.of_retract (hP : IsKProjective.{w} A P) (i : Q →ᵈᵍ[A] P)
    (r : P →ᵈᵍ[A] Q) (hri : Homotopic (r.comp i) DGModuleHom.id) : IsKProjective.{w} A Q := by
  intro N _ _ _ _ hN f
  have h1 : Homotopic ((f.comp r).comp i) 0 :=
    ((hP N hN (f.comp r)).comp_left i).trans (Homotopic.of_eq (DGModuleHom.zero_comp i))
  exact (hri.comp_right f).symm.trans h1

/-- K-projectivity is invariant under homotopy equivalence. -/
theorem IsKProjective.of_dgHomotopyEquiv (hP : IsKProjective.{w} A P)
    (e : DGHomotopyEquiv A Q P) : IsKProjective.{w} A Q :=
  hP.of_retract e.hom e.inv e.homotopyHomInvId.homotopic

/-- K-projectivity is invariant under isomorphism. -/
theorem IsKProjective.of_dgModuleEquiv (hP : IsKProjective.{w} A P) (e : Q ≃ᵈᵍ[A] P) :
    IsKProjective.{w} A Q :=
  hP.of_retract e.toDGModuleHom e.symm.toDGModuleHom
    (Homotopic.of_eq (DGModuleHom.ext fun x => e.symm_apply_apply x))

/-- A contractible dg module is acyclic. -/
theorem IsContractible.isAcyclic (hP : IsContractible A P) : IsAcyclic P :=
  hP.subsingleton_cohomology

/-- A contractible dg module is K-projective. -/
theorem IsContractible.isKProjective (hP : IsContractible A P) : IsKProjective.{w} A P :=
  fun _ _ _ _ _ _ f => hP.homotopic_zero_of_left f

/-- Shifts of K-projective dg modules are K-projective: a morphism `P⟦k⟧ → N` is a cocycle of
degree `-k` of `HOM_A(P, N)` (`Cochain.leftUnshift`), which is a coboundary since
`HOM_A(P, N)` is acyclic. -/
theorem IsKProjective.shift [DGRing A] (hP : IsKProjective.{w} A P) (k : ℤ) :
    IsKProjective.{w} A (Shift k P) := by
  intro N _ _ _ _ hN f
  have hz : δ (-k) (-k + 1) ((Cochain.ofHom f).leftUnshift (-k) (neg_add_cancel k)) = 0 := by
    rw [Cochain.δ_leftUnshift _ (-k) _ (-k + 1) 1 (by ring), δ_ofHom, Cochain.leftUnshift_zero,
      smul_zero]
  obtain ⟨y, hy⟩ := (hP.isAcyclic_hom hN).exists_δ_eq (m := -k - 1) (by ring) _ hz
  refine homotopic_zero_iff_exists.mpr ⟨koszulSign k • y.leftShift k (-1) (by ring), ?_⟩
  rw [δ_units_smul, Cochain.δ_leftShift y k (-1) 0 (by ring) (-k) (neg_add_cancel k), hy,
    smul_smul, Int.units_mul_self, one_smul, Cochain.leftShift_leftUnshift]

end Closure

/-! ### Corner modules `A e` -/

namespace DGIdempotent

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] (e : DGIdempotent A)

/-- The inclusion `A e → A`, as a morphism of dg modules. -/
def leftCornerInclusion : e.LeftCorner →ᵈᵍ[A] A where
  toFun a := a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mem' h := h
  map_d' _ := rfl

@[simp]
theorem leftCornerInclusion_apply (a : e.LeftCorner) : e.leftCornerInclusion a = a := rfl

/-- The projection `A → A e`, `a ↦ a * e`, as a morphism of dg modules. -/
def leftCornerProjection : A →ᵈᵍ[A] e.LeftCorner where
  toFun a := ⟨a * e.val, e.mul_val_mem_leftIdeal a⟩
  map_add' a b := Subtype.ext (add_mul a b e.val)
  map_smul' a b := Subtype.ext (mul_assoc a b e.val)
  map_mem' {n a} ha := by
    rw [LeftCorner.mem_grading_iff, ← add_zero n]
    exact mul_mem_grading ha e.mem_zero
  map_d' a := Subtype.ext (e.d_mul_val a).symm

@[simp]
theorem coe_leftCornerProjection_apply (a : A) :
    (e.leftCornerProjection a : A) = a * e.val := rfl

theorem leftCornerProjection_comp_inclusion :
    e.leftCornerProjection.comp e.leftCornerInclusion = DGModuleHom.id :=
  DGModuleHom.ext fun a => Subtype.ext a.2

/-- The dg module `A e` is K-projective, as a direct summand of `A`. -/
theorem isKProjective_leftCorner : IsKProjective.{w} A e.LeftCorner :=
  (isKProjective_self A).of_retract e.leftCornerInclusion e.leftCornerProjection
    (Homotopic.of_eq e.leftCornerProjection_comp_inclusion)

end DGIdempotent

/-! ### Direct sums -/

section DirectSum

variable {A : Type*} [Ring A] [DGAddCommGroup A] {ι : Type*} [DecidableEq ι]
  {P : ι → Type*} [∀ i, AddCommGroup (P i)] [∀ i, DGAddCommGroup (P i)] [∀ i, Module A (P i)]
  {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module A N]

namespace Cochain

/-- The cochain out of a direct sum with prescribed restrictions `c i` to the summands. -/
def directSumDesc {n : ℤ} (c : ∀ i, Cochain A (P i) N n) : Cochain A (⨁ i, P i) N n where
  toFun := DirectSum.toAddMonoid fun i => (c i : P i →+ N)
  map_zero' := map_zero _
  map_add' := map_add _
  map_mem' k x hx := by
    classical
    rw [← DirectSum.sum_support_of x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [DirectSum.toAddMonoid_of]
    exact (c i).map_mem (hx i)
  map_smul' {k a} ha x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of j y =>
      rw [← DirectSum.lof_eq_of A, ← _root_.map_smul, DirectSum.lof_eq_of, DirectSum.lof_eq_of,
        DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
      exact (c j).map_smul ha y
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add, smul_add]

@[simp]
theorem directSumDesc_of {n : ℤ} (c : ∀ i, Cochain A (P i) N n) (i : ι) (x : P i) :
    directSumDesc c (DirectSum.of P i x) = c i x :=
  DirectSum.toAddMonoid_of _ i x

/-- Two cochains out of a direct sum agreeing on the summands are equal. -/
theorem directSum_ext {n : ℤ} {c c' : Cochain A (⨁ i, P i) N n}
    (h : ∀ i x, c (DirectSum.of P i x) = c' (DirectSum.of P i x)) : c = c' := by
  ext x
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x => exact h i x
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end Cochain

variable [∀ i, DGModule A (P i)]

/-- A direct sum of K-projective dg modules is K-projective. -/
theorem IsKProjective.directSum (h : ∀ i, IsKProjective.{w} A (P i)) :
    IsKProjective.{w} A (⨁ i, P i) := by
  intro N _ _ _ _ hN f
  choose c hc using fun i => homotopic_zero_iff_exists.mp
    (h i N hN (f.comp (DGModuleHom.lof A P i)))
  refine homotopic_zero_iff_exists.mpr ⟨Cochain.directSumDesc c, Cochain.directSum_ext
    fun i x => ?_⟩
  have h1 := congrArg (fun z : Cochain A (P i) N 0 => z x)
    (δ_ofHom_comp (DGModuleHom.lof A P i) (Cochain.directSumDesc c) 0)
  have h2 : (Cochain.directSumDesc c).comp (Cochain.ofHom (DGModuleHom.lof A P i))
      (zero_add _) = c i := Cochain.ext fun y => Cochain.directSumDesc_of c i y
  simp only [Cochain.comp_apply, Cochain.ofHom_apply, DGModuleHom.lof_apply, h2] at h1
  rw [Cochain.ofHom_apply, ← h1, ← hc i]
  rfl

end DirectSum

/-! ### Extensions -/

section GradedSplitting

variable {A : Type*} [Ring A] [DGAddCommGroup A]
  {F G Q : Type*} [AddCommGroup F] [DGAddCommGroup F] [Module A F] [DGModule A F]
  [AddCommGroup G] [DGAddCommGroup G] [Module A G] [DGModule A G]
  [AddCommGroup Q] [DGAddCommGroup Q] [Module A Q] [DGModule A Q]

/-- A graded splitting of a sequence `F → G → Q` of morphisms of dg modules `i` and `p`:
graded `A`-linear maps of degree `0`, `r : G → F` and `s : Q → G`, which need not commute with
the differentials, with `r ∘ i = id`, `p ∘ s = id` and `i ∘ r + s ∘ p = id`. Such data exist
iff `0 → F → G → Q → 0` is a short exact sequence of dg modules which splits as a sequence of
graded `A`-modules (a "degreewise split" sequence in Mathlib's terminology for complexes). -/
structure GradedSplitting (i : F →ᵈᵍ[A] G) (p : G →ᵈᵍ[A] Q) where
  /-- The graded retraction of `i`. -/
  r : Cochain A G F 0
  /-- The graded section of `p`. -/
  s : Cochain A Q G 0
  r_i : ∀ x, r (i x) = x
  p_s : ∀ y, p (s y) = y
  i_r_add_s_p : ∀ x, i (r x) + s (p x) = x

namespace GradedSplitting

variable {i : F →ᵈᵍ[A] G} {p : G →ᵈᵍ[A] Q} (σ : GradedSplitting i p)

omit [DGModule A F] [DGModule A G] [DGModule A Q] in
include σ in
theorem p_i (x : F) : p (i x) = 0 := by
  have h := σ.i_r_add_s_p (i x)
  rw [σ.r_i, add_eq_left] at h
  rw [← σ.p_s (p (i x)), h, map_zero]

include σ in
/-- Null-homotopies extend along a graded-split monomorphism with K-projective cokernel: if
`f : G → N` restricts along `i` to a morphism null-homotopic via `h`, and every morphism
`Q → N` is null-homotopic, then `f` is null-homotopic via a homotopy extending `h`. -/
theorem exists_extension {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module A N]
    [DGModule A N] (hQ : ∀ g : Q →ᵈᵍ[A] N, Homotopic g 0) (f : G →ᵈᵍ[A] N)
    (h : Cochain A F N (-1)) (hh : Cochain.ofHom (f.comp i) = δ (-1) 0 h) :
    ∃ h' : Cochain A G N (-1), Cochain.ofHom f = δ (-1) 0 h' ∧ ∀ x, h' (i x) = h x := by
  set hr : Cochain A G N (-1) := h.comp σ.r (zero_add _)
  set g : Cochain A G N 0 := Cochain.ofHom f - δ (-1) 0 hr with hg
  have e1 : hr.comp (Cochain.ofHom i) (zero_add _) = h :=
    Cochain.ext fun x => by simp [hr, σ.r_i]
  have hg_i : ∀ x, g (i x) = 0 := fun x => by
    have h1 := congrArg (fun z : Cochain A F N 0 => z x) (δ_ofHom_comp i hr 0)
    have h2 := congrArg (fun z : Cochain A F N 0 => z x) hh
    simp only [Cochain.comp_apply, Cochain.ofHom_apply, e1, DGModuleHom.comp_apply] at h1 h2
    simp only [hg, Cochain.sub_apply, Cochain.ofHom_apply, h1, h2, sub_self]
  have hg_d : ∀ x, d (g x) = g (d x) := fun x => by
    have h1 : δ 0 1 g = 0 := by rw [hg, δ_sub, δ_ofHom, δ_δ, sub_zero]
    have h2 := congrArg (fun z : Cochain A G N 1 => z x) h1
    simpa [sub_eq_zero] using h2
  have hgs : δ 0 1 (g.comp σ.s (zero_add 0)) = 0 := by
    ext y
    have hp : p (d (σ.s y) - σ.s (d y)) = 0 := by rw [map_sub, p.map_d, σ.p_s, σ.p_s, sub_self]
    have hx := σ.i_r_add_s_p (d (σ.s y) - σ.s (d y))
    rw [hp, map_zero, add_zero] at hx
    rw [δ_zero_cochain_apply, Cochain.comp_apply, Cochain.comp_apply, hg_d, ← map_sub, ← hx,
      hg_i, Cochain.zero_apply]
  obtain ⟨k, hk⟩ := homotopic_zero_iff_exists.mp
    (hQ (Cocycle.homOf (Cocycle.mk _ 1 (zero_add 1) hgs)))
  rw [Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.mk_coe] at hk
  refine ⟨hr + k.comp (Cochain.ofHom p) (zero_add _), ?_, fun x => ?_⟩
  · ext x
    have h1 := congrArg (fun z : Cochain A G N 0 => z x) (δ_ofHom_comp p k 0)
    have h2 := congrArg (fun z : Cochain A Q N 0 => z (p x)) hk
    simp only [Cochain.comp_apply, Cochain.ofHom_apply] at h1 h2
    have h3 : g x = g (σ.s (p x)) := by
      conv_lhs => rw [← σ.i_r_add_s_p x]
      rw [map_add, hg_i, zero_add]
    rw [δ_add, Cochain.add_apply, h1, ← h2, ← h3, hg, Cochain.sub_apply, add_sub_cancel]
  · simp [hr, σ.r_i, σ.p_i]

end GradedSplitting

/-- An extension of K-projective dg modules is K-projective: if `F → G → Q` is a graded-split
short exact sequence with `F` and `Q` K-projective, then `G` is K-projective. -/
theorem IsKProjective.of_gradedSplitting {i : F →ᵈᵍ[A] G} {p : G →ᵈᵍ[A] Q}
    (σ : GradedSplitting i p) (hF : IsKProjective.{w} A F) (hQ : IsKProjective.{w} A Q) :
    IsKProjective.{w} A G := by
  intro N _ _ _ _ hN f
  obtain ⟨h, hh⟩ := homotopic_zero_iff_exists.mp (hF N hN (f.comp i))
  obtain ⟨h', hh', -⟩ := σ.exists_extension (hQ N hN) f h hh
  exact homotopic_zero_iff_exists.mpr ⟨h', hh'⟩

end GradedSplitting

/-! ### Mapping cones -/

section Cone

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  {M N : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]

/-- The standard sequence `N → Cone f → M⟦1⟧` of a mapping cone is graded-split. -/
def Cone.gradedSplitting (f : M →ᵈᵍ[A] N) : GradedSplitting (Cone.inr f) (Cone.fstHom f) where
  r := Cone.snd f
  s := Cochain.ofHoms (Cone.inlLinear f) Cone.inlLinear_mem
  r_i _ := rfl
  p_s _ := rfl
  i_r_add_s_p x := by
    rw [add_comm]
    exact Cone.inlLinear_fstHom_add_inr_sndLinear x

/-- The mapping cone of a morphism between K-projective dg modules is K-projective. -/
theorem IsKProjective.cone {f : M →ᵈᵍ[A] N} (hM : IsKProjective.{w} A M)
    (hN : IsKProjective.{w} A N) : IsKProjective.{w} A (Cone f) :=
  IsKProjective.of_gradedSplitting (Cone.gradedSplitting f) hN (hM.shift 1)

end Cone

/-! ### Quasi-isomorphisms and acyclic cones -/

section CohomologyMap

variable {M N : Type*} [AddCommGroup M] [DGAddCommGroup M] [AddCommGroup N] [DGAddCommGroup N]
  (φ : M →+ N) (hmem : ∀ {n : ℤ} {m : M}, m ∈ grading n → φ m ∈ grading n)
  (hd : ∀ m, φ (d m) = d (φ m))

/-- The map induced on `Hⁿ` is injective iff every cocycle of degree `n` whose image is a
coboundary is a coboundary. -/
theorem cohomology.mapAddMonoidHom_injective_iff (n : ℤ) :
    Function.Injective (cohomology.mapAddMonoidHom φ hmem hd n) ↔
      ∀ x ∈ grading n, d x = 0 → φ x ∈ coboundaries N n → x ∈ coboundaries M n := by
  rw [injective_iff_map_eq_zero]
  constructor
  · intro h x hx hdx hφx
    refine (cohomology.mkOf_eq_zero_iff hx hdx).mp (h _ ?_)
    rw [cohomology.mapAddMonoidHom_mkOf, cohomology.mkOf_eq_zero_iff]
    exact hφx
  · intro h c hc
    induction c using cohomology.induction_on with
    | h z =>
      rw [cohomology.mapAddMonoidHom_mk, cohomology.mk_eq_zero_iff] at hc
      exact (cohomology.mk_eq_zero_iff z).mpr (h z z.2.1 z.2.2 hc)

/-- The map induced on `Hⁿ` is surjective iff every cocycle of degree `n` is cohomologous to
the image of a cocycle. -/
theorem cohomology.mapAddMonoidHom_surjective_iff (n : ℤ) :
    Function.Surjective (cohomology.mapAddMonoidHom φ hmem hd n) ↔
      ∀ y ∈ grading n, d y = 0 → ∃ x ∈ grading n, d x = 0 ∧ φ x - y ∈ coboundaries N n := by
  constructor
  · intro h y hy hdy
    obtain ⟨c, hc⟩ := h (cohomology.mkOf hy hdy)
    induction c using cohomology.induction_on with
    | h z =>
      rw [cohomology.mapAddMonoidHom_mk, cohomology.mkOf_eq_mk, cohomology.mk_eq_mk_iff] at hc
      exact ⟨z, z.2.1, z.2.2, hc⟩
  · intro h c
    induction c using cohomology.induction_on with
    | h z =>
      obtain ⟨x, hx, hdx, hxy⟩ := h z z.2.1 z.2.2
      refine ⟨cohomology.mkOf hx hdx, ?_⟩
      rw [cohomology.mapAddMonoidHom_mkOf, cohomology.mkOf_eq_mk]
      exact cohomology.mk_eq_mk_of_sub_mem hxy

end CohomologyMap

section QuasiIso

variable {A : Type*} [Ring A] [DGAddCommGroup A]
  {M N : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N]

theorem cohomology.map_injective_iff (f : M →ᵈᵍ[A] N) (n : ℤ) :
    Function.Injective (cohomology.map f n) ↔
      ∀ x ∈ grading n, d x = 0 → f x ∈ coboundaries N n → x ∈ coboundaries M n :=
  cohomology.mapAddMonoidHom_injective_iff _ _ _ n

theorem cohomology.map_surjective_iff (f : M →ᵈᵍ[A] N) (n : ℤ) :
    Function.Surjective (cohomology.map f n) ↔
      ∀ y ∈ grading n, d y = 0 → ∃ x ∈ grading n, d x = 0 ∧ f x - y ∈ coboundaries N n :=
  cohomology.mapAddMonoidHom_surjective_iff _ _ _ n

/-- A morphism between acyclic dg modules is a quasi-isomorphism. -/
theorem DGModuleHom.isQuasiIso_of_isAcyclic (hM : IsAcyclic M) (hN : IsAcyclic N)
    (f : M →ᵈᵍ[A] N) : f.IsQuasiIso := fun n =>
  ⟨fun _ _ _ => (hM n).elim _ _, fun _ => ⟨0, (hN n).elim _ _⟩⟩

variable [DGRing A] [DGModule A M] [DGModule A N]

/-- A quasi-isomorphism has an acyclic mapping cone. -/
theorem DGModuleHom.IsQuasiIso.isAcyclic_cone {s : M →ᵈᵍ[A] N} (hs : s.IsQuasiIso) :
    IsAcyclic (Cone s) := by
  refine isAcyclic_iff.mpr fun k p hp hdp => ?_
  have hx : (Cone.fst s).1 p ∈ grading (k + 1) := (Cone.fst s).1.map_mem hp
  have hy : Cone.snd s p ∈ grading k := by simpa using (Cone.snd s).map_mem hp
  have hdx : d ((Cone.fst s).1 p) = 0 := by
    have h := congrArg (Cone.fst s).1 hdp
    rwa [Cone.d_fst_apply, map_zero, neg_eq_zero] at h
  have hsxy : s ((Cone.fst s).1 p) + d (Cone.snd s p) = 0 := by
    have h := congrArg (Cone.snd s) hdp
    rwa [Cone.d_snd_apply, map_zero] at h
  obtain ⟨u, hu, hdu⟩ := (cohomology.map_injective_iff s (k + 1)).mp (hs (k + 1)).1 _ hx hdx
    ⟨-Cone.snd s p, by simpa using neg_mem hy,
      by rw [d_neg, neg_eq_iff_add_eq_zero, add_comm, hsxy]⟩
  have hu' : u ∈ grading k := by simpa using hu
  obtain ⟨w, hw, hdw, v, hv, hdv⟩ := (cohomology.map_surjective_iff s k).mp (hs k).2
    (Cone.snd s p + s u) (add_mem hy (s.map_mem hu'))
    (by rw [d_add, ← s.map_d, hdu, add_comm, hsxy])
  refine ⟨Cone.inl s (w - u) + Cone.inr s (-v), add_mem ?_ ((Cone.inr s).map_mem (neg_mem hv)), ?_⟩
  · simpa [sub_eq_add_neg] using (Cone.inl s).map_mem (sub_mem hw hu')
  · refine Cone.ext_to ?_ ?_
    · simp only [Cone.d_fst_apply, map_add, Cone.inl_fst_apply, Cone.inr_fst_apply, add_zero,
        d_sub, hdw, hdu, zero_sub, neg_neg, d_zero, neg_zero]
    · simp only [Cone.d_snd_apply, map_add, Cone.inl_fst_apply, Cone.inr_fst_apply,
        Cone.inl_snd_apply, Cone.inr_snd_apply, add_zero, zero_add, d_neg, hdv, map_sub,
        map_zero]
      abel

/-- A morphism with an acyclic mapping cone is a quasi-isomorphism. -/
theorem DGModuleHom.isQuasiIso_of_isAcyclic_cone {s : M →ᵈᵍ[A] N} (h : IsAcyclic (Cone s)) :
    s.IsQuasiIso := by
  intro n
  constructor
  · rw [cohomology.map_injective_iff]
    rintro x hx hdx ⟨v, hv, hdv⟩
    have hp : Cone.inl s x + Cone.inr s (-v) ∈ grading (n - 1) :=
      add_mem (by simpa [sub_eq_add_neg] using (Cone.inl s).map_mem hx)
        ((Cone.inr s).map_mem (neg_mem hv))
    have hdp : d (Cone.inl s x + Cone.inr s (-v)) = 0 := by
      refine Cone.ext_to ?_ ?_
      · simp only [Cone.d_fst_apply, map_add, Cone.inl_fst_apply, Cone.inr_fst_apply, add_zero,
          hdx, neg_zero, map_zero]
      · simp only [Cone.d_snd_apply, map_add, Cone.inl_fst_apply, Cone.inr_fst_apply,
          Cone.inl_snd_apply, Cone.inr_snd_apply, add_zero, zero_add, d_neg, hdv, add_neg_cancel,
          map_zero]
    obtain ⟨q, hq, hdq⟩ := h.exists_d_eq hp hdp
    refine ⟨-(Cone.fst s).1 q, by simpa using neg_mem ((Cone.fst s).1.map_mem hq), ?_⟩
    have h1 := congrArg (Cone.fst s).1 hdq
    rw [Cone.d_fst_apply, map_add, Cone.inl_fst_apply, Cone.inr_fst_apply, add_zero] at h1
    rw [d_neg, h1]
  · rw [cohomology.map_surjective_iff]
    intro y hy hdy
    have hdp : d (Cone.inr s y) = 0 := by rw [Cone.inr_d_apply, hdy, map_zero]
    obtain ⟨q, hq, hdq⟩ := h.exists_d_eq ((Cone.inr s).map_mem hy) hdp
    have h1 := congrArg (Cone.fst s).1 hdq
    have h2 := congrArg (Cone.snd s) hdq
    rw [Cone.d_fst_apply, Cone.inr_fst_apply, neg_eq_zero] at h1
    rw [Cone.d_snd_apply, Cone.inr_snd_apply] at h2
    refine ⟨(Cone.fst s).1 q, by simpa using (Cone.fst s).1.map_mem hq, h1,
      -Cone.snd s q, by simpa using neg_mem ((Cone.snd s).map_mem hq), ?_⟩
    rw [d_neg, ← h2]
    abel

/-- A morphism of dg modules is a quasi-isomorphism iff its mapping cone is acyclic. -/
theorem DGModuleHom.isQuasiIso_iff_isAcyclic_cone (s : M →ᵈᵍ[A] N) :
    s.IsQuasiIso ↔ IsAcyclic (Cone s) :=
  ⟨fun hs => hs.isAcyclic_cone, isQuasiIso_of_isAcyclic_cone⟩

end QuasiIso

/-! ### `HOM_A(P, -)` for K-projective `P` -/

section HomQuasiIso

variable {A : Type*} [Ring A] [DGAddCommGroup A]
  {P : Type*} [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]
  {N N' : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]
  [AddCommGroup N'] [DGAddCommGroup N'] [Module A N'] [DGModule A N']

namespace DGModule.HOM

variable (A P) in
/-- Postcomposition with a morphism `s : N → N'`, as a map of Hom complexes
`HOM_A(P, N) → HOM_A(P, N')`. -/
noncomputable def postcomp (s : N →ᵈᵍ[A] N') : HOM A P N →+ HOM A P N' :=
  DirectSum.map fun n =>
    { toFun := fun z => (Cochain.ofHom s).comp z (add_zero n)
      map_zero' := Cochain.comp_zero _ _
      map_add' := fun z z' => Cochain.comp_add z z' _ _ }

omit [DGModule A P] [DGModule A N] [DGModule A N'] in
theorem postcomp_of (s : N →ᵈᵍ[A] N') (n : ℤ) (z : Cochain A P N n) :
    postcomp A P s (DirectSum.of _ n z) =
      DirectSum.of (fun n => Cochain A P N' n) n ((Cochain.ofHom s).comp z (add_zero n)) :=
  DirectSum.map_of _ _ _

theorem postcomp_mem (s : N →ᵈᵍ[A] N') {n : ℤ} {x : HOM A P N} (hx : x ∈ grading n) :
    postcomp A P s x ∈ grading n := by
  obtain ⟨z, rfl⟩ := mem_summand.mp hx
  rw [postcomp_of]
  exact of_mem_summand _ _

theorem postcomp_d (s : N →ᵈᵍ[A] N') (x : HOM A P N) :
    postcomp A P s (d x) = d (postcomp A P s x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n z => rw [d_of, postcomp_of, postcomp_of, d_of, δ_comp_ofHom]
  | add x y hx hy => rw [d_add, map_add, hx, hy, map_add, d_add]

theorem of_mem_grading_iff {n : ℤ} {x : HOM A P N} :
    x ∈ grading n ↔ ∃ z : Cochain A P N n, DirectSum.of _ n z = x :=
  mem_summand

theorem d_of_eq_zero_iff {n : ℤ} (z : Cochain A P N n) :
    d (DirectSum.of (fun n => Cochain A P N n) n z : HOM A P N) = 0 ↔ δ n (n + 1) z = 0 := by
  rw [d_of, ← map_zero (DirectSum.of (fun n => Cochain A P N n) (n + 1))]
  exact (DirectSum.of_injective (β := fun n => Cochain A P N n) (n + 1)).eq_iff

theorem of_mem_coboundaries_iff {n : ℤ} (z : Cochain A P N n) (hz : δ n (n + 1) z = 0) :
    (DirectSum.of (fun n => Cochain A P N n) n z : HOM A P N) ∈ coboundaries (HOM A P N) n ↔
      ∃ y : Cochain A P N (n - 1), δ (n - 1) n y = z :=
  (cocyclesAddEquiv_mem_coboundaries_iff n (Cocycle.mk z (n + 1) rfl hz)).trans
    (Cocycle.mem_coboundaries_iff (n - 1) (sub_add_cancel n 1) _)

end DGModule.HOM

namespace DGModuleHom

variable (P) in
/-- Postcomposition with `s : N → N'`, as an additive map `(P →ᵈᵍ[A] N) → (P →ᵈᵍ[A] N')`. -/
@[simps]
def postcompAddHom (s : N →ᵈᵍ[A] N') : (P →ᵈᵍ[A] N) →+ (P →ᵈᵍ[A] N') where
  toFun f := s.comp f
  map_zero' := DGModuleHom.comp_zero s
  map_add' f g := DGModuleHom.comp_add s f g

variable (P) in
/-- Postcomposition with `s : N → N'` on morphisms up to homotopy,
`Hom_{H(A)}(P, N) → Hom_{H(A)}(P, N')`. -/
def postcompHomotopy (s : N →ᵈᵍ[A] N') :
    ((P →ᵈᵍ[A] N) ⧸ nullHomotopic A P N) →+ ((P →ᵈᵍ[A] N') ⧸ nullHomotopic A P N') :=
  QuotientAddGroup.map _ _ (postcompAddHom P s) fun _ hf => comp_mem_nullHomotopic hf s

@[simp]
theorem postcompHomotopy_mk (s : N →ᵈᵍ[A] N') (f : P →ᵈᵍ[A] N) :
    postcompHomotopy P s (QuotientAddGroup.mk f) = QuotientAddGroup.mk (s.comp f) :=
  rfl

end DGModuleHom

variable [DGRing A]

/-- For a K-projective `P` and a quasi-isomorphism `s : N → N'`, every cocycle of
`HOM_A(P, N')` is cohomologous to `s ∘ α` for a cocycle `α` of `HOM_A(P, N)`. -/
theorem IsKProjective.exists_cocycle_of_isQuasiIso {N N' : Type w} [AddCommGroup N]
    [DGAddCommGroup N] [Module A N] [DGModule A N] [AddCommGroup N'] [DGAddCommGroup N']
    [Module A N'] [DGModule A N'] (hP : IsKProjective.{w} A P) {s : N →ᵈᵍ[A] N'}
    (hs : s.IsQuasiIso) {n m : ℤ} (hmn : m + 1 = n) (z' : Cochain A P N' n)
    (hz' : δ n (n + 1) z' = 0) :
    ∃ (α : Cochain A P N n) (β : Cochain A P N' m), δ n (n + 1) α = 0 ∧
      (Cochain.ofHom s).comp α (add_zero n) = z' - δ m n β := by
  have hC := hP.isAcyclic_hom hs.isAcyclic_cone
  have hw0 : δ n (n + 1) ((Cochain.ofHom (Cone.inr s)).comp z' (add_zero n)) = 0 := by
    rw [δ_comp_ofHom, hz', Cochain.comp_zero]
  obtain ⟨w, hw⟩ := hC.exists_δ_eq hmn _ hw0
  have hw' : w = Cone.liftCochain s ((Cone.fst s).1.comp w hmn) ((Cone.snd s).comp w
      (add_zero m)) hmn :=
    Cochain.ext fun x => Cone.ext_to (by simp) (by simp)
  rw [hw', Cone.δ_liftCochain s _ _ hmn (n + 1) rfl] at hw
  refine ⟨(Cone.fst s).1.comp w hmn, (Cone.snd s).comp w (add_zero m), ?_, ?_⟩
  · ext x
    have h := congrArg (fun c : Cochain A P (Cone s) n => (Cone.fst s).1 (c x)) hw
    simpa using h
  · ext x
    have h := congrArg (fun c : Cochain A P (Cone s) n => Cone.snd s (c x)) hw
    simp only [Cochain.add_apply, Cochain.neg_apply, Cochain.comp_apply, Cochain.ofHom_apply,
      map_add, map_neg, Cone.inl_snd_apply, Cone.inr_snd_apply, neg_zero, zero_add] at h
    rw [Cochain.comp_apply, Cochain.ofHom_apply, Cochain.sub_apply, ← h]
    abel

/-- For a K-projective `P` and a quasi-isomorphism `s : N → N'`, a cocycle `z` of
`HOM_A(P, N)` such that `s ∘ z` is a coboundary is itself a coboundary. -/
theorem IsKProjective.exists_δ_eq_of_isQuasiIso {N N' : Type w} [AddCommGroup N]
    [DGAddCommGroup N] [Module A N] [DGModule A N] [AddCommGroup N'] [DGAddCommGroup N']
    [Module A N'] [DGModule A N'] (hP : IsKProjective.{w} A P) {s : N →ᵈᵍ[A] N'}
    (hs : s.IsQuasiIso) {n m : ℤ} (hmn : m + 1 = n) (z : Cochain A P N n)
    (hz : δ n (n + 1) z = 0) (y' : Cochain A P N' m)
    (hy' : (Cochain.ofHom s).comp z (add_zero n) = δ m n y') :
    ∃ y : Cochain A P N m, δ m n y = z := by
  subst hmn
  have hC := hP.isAcyclic_hom hs.isAcyclic_cone
  have hw : δ m (m + 1) (Cone.liftCochain s z (-y') rfl) = 0 := by
    rw [Cone.δ_liftCochain s _ _ rfl (m + 1 + 1) rfl, hz, δ_neg, hy', neg_add_cancel,
      Cochain.comp_zero, Cochain.comp_zero, neg_zero, add_zero]
  obtain ⟨u, hu⟩ := hC.exists_δ_eq (sub_add_cancel m 1) _ hw
  have hu' : u = Cone.liftCochain s ((Cone.fst s).1.comp u (sub_add_cancel m 1))
      ((Cone.snd s).comp u (add_zero _)) (sub_add_cancel m 1) :=
    Cochain.ext fun x => Cone.ext_to (by simp) (by simp)
  rw [hu', Cone.δ_liftCochain s _ _ (sub_add_cancel m 1) (m + 1) rfl] at hu
  refine ⟨-(Cone.fst s).1.comp u (sub_add_cancel m 1), ?_⟩
  ext x
  have h := congrArg (fun c : Cochain A P (Cone s) m => (Cone.fst s).1 (c x)) hu
  simp only [Cochain.add_apply, Cochain.neg_apply, Cochain.comp_apply, Cochain.ofHom_apply,
    map_add, map_neg, Cone.inl_fst_apply, Cone.inr_fst_apply, add_zero,
    Cone.liftCochain_fst_apply] at h
  rw [δ_neg, Cochain.neg_apply, h]

/-- For a K-projective `P`, `HOM_A(P, -)` preserves quasi-isomorphisms: if `s : N → N'` is a
quasi-isomorphism, then postcomposition with `s` induces isomorphisms
`Hⁿ(HOM_A(P, N)) ≅ Hⁿ(HOM_A(P, N'))` for all `n`. -/
theorem IsKProjective.bijective_cohomology_postcomp {N N' : Type w} [AddCommGroup N]
    [DGAddCommGroup N] [Module A N] [DGModule A N] [AddCommGroup N'] [DGAddCommGroup N']
    [Module A N'] [DGModule A N'] (hP : IsKProjective.{w} A P) {s : N →ᵈᵍ[A] N'}
    (hs : s.IsQuasiIso) (n : ℤ) :
    Function.Bijective (cohomology.mapAddMonoidHom (DGModule.HOM.postcomp A P s)
      (DGModule.HOM.postcomp_mem s) (DGModule.HOM.postcomp_d s) n) := by
  constructor
  · rw [cohomology.mapAddMonoidHom_injective_iff]
    intro x hx hdx hsx
    obtain ⟨z, rfl⟩ := DGModule.HOM.of_mem_grading_iff.mp hx
    rw [DGModule.HOM.d_of_eq_zero_iff] at hdx
    have hsz : δ n (n + 1) ((Cochain.ofHom s).comp z (add_zero n)) = 0 := by
      rw [δ_comp_ofHom, hdx, Cochain.comp_zero]
    rw [DGModule.HOM.postcomp_of, DGModule.HOM.of_mem_coboundaries_iff _ hsz] at hsx
    obtain ⟨y', hy'⟩ := hsx
    obtain ⟨y, hy⟩ := hP.exists_δ_eq_of_isQuasiIso hs (sub_add_cancel n 1) z hdx y' hy'.symm
    exact (DGModule.HOM.of_mem_coboundaries_iff z hdx).mpr ⟨y, hy⟩
  · rw [cohomology.mapAddMonoidHom_surjective_iff]
    intro y hy hdy
    obtain ⟨z', rfl⟩ := DGModule.HOM.of_mem_grading_iff.mp hy
    rw [DGModule.HOM.d_of_eq_zero_iff] at hdy
    obtain ⟨α, β, hα, hαβ⟩ := hP.exists_cocycle_of_isQuasiIso hs (sub_add_cancel n 1) z' hdy
    refine ⟨DirectSum.of _ n α, of_mem_summand _ _, (DGModule.HOM.d_of_eq_zero_iff α).mpr hα, ?_⟩
    rw [DGModule.HOM.postcomp_of, hαβ, ← map_sub, sub_sub_cancel_left,
      DGModule.HOM.of_mem_coboundaries_iff _ (by rw [δ_neg, δ_δ, neg_zero])]
    exact ⟨-β, δ_neg _ _ β⟩


/-- For a K-projective `P` and a quasi-isomorphism `s : N → N'`, postcomposition with `s` is a
bijection `Hom_{H(A)}(P, N) ≅ Hom_{H(A)}(P, N')` on morphisms up to homotopy. -/
theorem IsKProjective.bijective_postcompHomotopy {N N' : Type w} [AddCommGroup N]
    [DGAddCommGroup N] [Module A N] [DGModule A N] [AddCommGroup N'] [DGAddCommGroup N']
    [Module A N'] [DGModule A N'] (hP : IsKProjective.{w} A P) {s : N →ᵈᵍ[A] N'}
    (hs : s.IsQuasiIso) : Function.Bijective (DGModuleHom.postcompHomotopy P s) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    induction c using QuotientAddGroup.induction_on with
    | H f =>
      rw [DGModuleHom.postcompHomotopy_mk, QuotientAddGroup.eq_zero_iff,
        mem_nullHomotopic_iff_exists] at hc
      obtain ⟨y', hy'⟩ := hc
      obtain ⟨y, hy⟩ := hP.exists_δ_eq_of_isQuasiIso hs (neg_add_cancel 1) (Cochain.ofHom f)
        (δ_ofHom _) y' hy'
      exact (QuotientAddGroup.eq_zero_iff f).mpr (mem_nullHomotopic_iff_exists.mpr ⟨y, hy.symm⟩)
  · intro c
    induction c using QuotientAddGroup.induction_on with
    | H f' =>
      obtain ⟨α, β, hα, hαβ⟩ := hP.exists_cocycle_of_isQuasiIso hs (neg_add_cancel 1)
        (Cochain.ofHom f') (δ_ofHom _)
      refine ⟨QuotientAddGroup.mk (Cocycle.homOf (Cocycle.mk α 1 (zero_add 1) hα)), ?_⟩
      rw [DGModuleHom.postcompHomotopy_mk, QuotientAddGroup.eq_iff_sub_mem,
        mem_nullHomotopic_iff_exists]
      refine ⟨-β, ?_⟩
      rw [Cochain.ofHom_sub, Cochain.ofHom_comp, Cocycle.cochain_ofHom_homOf_eq_coe,
        Cocycle.mk_coe, hαβ, δ_neg]
      abel

/-- For a K-projective `P` and a quasi-isomorphism `s : N → N'`,
`Hom_{H(A)}(P, N) ≃ Hom_{H(A)}(P, N')`, induced by postcomposition with `s`. -/
noncomputable def IsKProjective.postcompHomotopyEquiv {N N' : Type w} [AddCommGroup N]
    [DGAddCommGroup N] [Module A N] [DGModule A N] [AddCommGroup N'] [DGAddCommGroup N']
    [Module A N'] [DGModule A N'] (hP : IsKProjective.{w} A P) {s : N →ᵈᵍ[A] N'}
    (hs : s.IsQuasiIso) :
    ((P →ᵈᵍ[A] N) ⧸ nullHomotopic A P N) ≃+ ((P →ᵈᵍ[A] N') ⧸ nullHomotopic A P N') :=
  AddEquiv.ofBijective _ (hP.bijective_postcompHomotopy hs)

end HomQuasiIso

end DG
