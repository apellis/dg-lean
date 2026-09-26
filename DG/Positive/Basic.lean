import DG.Algebra.Constructions
import DG.Module.Cohomology
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Positive dg algebras

A dg ring `A` is *positive* in the sense of Schnürer [Sch] if

* (P1) `A` is positively (i.e. non-negatively) graded: `Aⁿ = 0` for `n < 0`;
* (P2) the degree-`0` part `A⁰` is a semisimple ring;
* (P3) the differential vanishes on `A⁰`: `d (A⁰) = 0`.

This file defines this notion (`DG.IsPositive`) and proves its first consequences.

## Main definitions

* `DG.degreeZeroSubring A`: the degree-`0` part `A⁰` of a dg ring, as a subring.
* `DG.truncGESubgroup M n`: the truncation `M^{≥ n} = ⨁_{i ≥ n} Mⁱ` of a dg abelian group, a
  homogeneous `d`-stable subgroup with `d (M^{≥ n}) ⊆ M^{≥ n + 1}`; for a dg module over a dg
  ring, `A^{≥ m} • M^{≥ n} ⊆ M^{≥ m + n}` (`DG.smul_mem_truncGESubgroup`).
* `DG.truncGE hA n`: for a non-negatively graded dg ring `A`, the truncation `A^{≥ n}` as a dg
  ideal (two-sided, homogeneous, `d`-stable); `A^{≥ 0} = A` (`DG.mem_truncGE_of_nonpos`).
* `DG.IsPositive A`: Schnürer's conditions (P1)–(P3).
* `DG.IsPositive.dgIdempotent`: an idempotent of `A⁰` is a degree-`0` idempotent cocycle.
* `DG.IsPositive.degreeZeroDGSubring`: `A⁰` as a dg subring; it is concentrated in degree `0`
  (`DG.IsPositive.mem_grading_degreeZeroDGSubring_iff`) with zero differential.
* `DG.IsPositive.projZero`: the projection `A → A⁰`, `a ↦ a₀`, as a morphism of dg rings; it is
  a retraction of the inclusion `DG.DGSubring.subtype` (`DG.IsPositive.projZero_comp_subtype`),
  its kernel is `A^{≥ 1}` (`DG.IsPositive.ker_projZero`), and it induces an isomorphism
  `A ⧸ A^{≥ 1} ≅ A⁰` (`DG.IsPositive.quotientTruncGEOneHom`, bijective, and the ring
  isomorphism `DG.IsPositive.quotientTruncGEOneEquiv`).
* `DG.IsPositive.cohomologyZeroEquiv`: `H⁰(A) ≅ A⁰`, and `Hⁿ(A) = 0` for `n < 0`
  (`DG.IsPositive.subsingleton_cohomology_of_neg`).

## Comparison with the source

[Sch] O. M. Schnürer, *Perfect derived categories of positively graded DG algebras*,
Appl. Categ. Structures 19 (2011), 757–782; arXiv:0809.4782v2, §1 and §4, conditions (P1)–(P3).

Schnürer works with a dg algebra over a commutative ring `k` and with right dg modules. The
conditions (P1)–(P3) only involve the underlying dg ring, so `DG.IsPositive` is stated for a dg
ring; for a dg `k`-algebra it is the same condition. The ring `A⁰` is required to be semisimple
as a ring; Mathlib's `IsSemisimpleRing` asks that `A⁰` be semisimple as a left module over
itself, which for rings is equivalent to right semisimplicity (Artin–Wedderburn). The notation
`A^{≥ n}` is ours; Schnürer writes `A⁺ = A^{≥ 1}` and uses `A → A / A⁺ = A⁰`.
-/

open DirectSum

namespace DG

/-! ### The degree-`0` subring -/

section DegreeZero

variable (A : Type*) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The degree-`0` part `A⁰` of a dg ring `A`, as a subring (it contains `1` and is closed under
multiplication since the grading is a ring grading). -/
def degreeZeroSubring : Subring A :=
  SetLike.GradeZero.subring (grading (M := A))

variable {A}

@[simp]
theorem mem_degreeZeroSubring {a : A} : a ∈ degreeZeroSubring A ↔ a ∈ grading (M := A) 0 :=
  Iff.rfl

end DegreeZero

/-! ### Truncations -/

section Trunc

variable (M : Type*) [AddCommGroup M] [DGAddCommGroup M]

/-- The truncation `M^{≥ n} = ⨁_{i ≥ n} Mⁱ` of a dg abelian group: the elements whose homogeneous
components of degree `< n` vanish. -/
def truncGESubgroup (n : ℤ) : AddSubgroup M where
  carrier := {m | ∀ i < n, decompose (grading (M := M)) m i = 0}
  zero_mem' i _ := by simp
  add_mem' {a b} ha hb i hi := by simp [ha i hi, hb i hi]
  neg_mem' {a} ha i hi := by rw [decompose_neg, DFinsupp.neg_apply, ha i hi, neg_zero]

variable {M}

theorem mem_truncGESubgroup_iff {n : ℤ} {m : M} :
    m ∈ truncGESubgroup M n ↔ ∀ i < n, decompose (grading (M := M)) m i = 0 :=
  Iff.rfl

/-- A homogeneous element of degree `i ≥ n` lies in `M^{≥ n}`. -/
theorem mem_truncGESubgroup_of_mem {n i : ℤ} {m : M} (hm : m ∈ grading i) (hi : n ≤ i) :
    m ∈ truncGESubgroup M n := fun j hj =>
  Subtype.ext (decompose_of_mem_ne _ hm (by omega))

/-- A homogeneous element of `M^{≥ n}` of degree `i` is zero unless `n ≤ i`. -/
theorem eq_zero_or_le_of_mem_truncGESubgroup {n i : ℤ} {m : M} (hm : m ∈ grading i)
    (hm' : m ∈ truncGESubgroup M n) : m = 0 ∨ n ≤ i := by
  rcases lt_or_le i n with hi | hi
  · left
    have h := congrArg Subtype.val (hm' i hi)
    rwa [decompose_of_mem_same _ hm, ZeroMemClass.coe_zero] at h
  · exact Or.inr hi

theorem truncGESubgroup_anti : Antitone (truncGESubgroup M) :=
  fun _ _ hnn' _ hm i hi => hm i (lt_of_lt_of_le hi hnn')

/-- The truncation `M^{≥ n}` is a homogeneous subgroup. -/
theorem isHomogeneous_truncGESubgroup (n : ℤ) :
    SetLike.IsHomogeneous (grading (M := M)) (truncGESubgroup M n) := by
  intro j m hm
  rcases lt_or_le j n with hj | hj
  · rw [hm j hj, ZeroMemClass.coe_zero]
    exact zero_mem _
  · exact mem_truncGESubgroup_of_mem (decompose (grading (M := M)) m j).2 hj

/-- The differential maps `M^{≥ n}` to `M^{≥ n + 1}`. -/
theorem d_mem_truncGESubgroup_add_one {n : ℤ} {m : M} (hm : m ∈ truncGESubgroup M n) :
    d m ∈ truncGESubgroup M (n + 1) := by
  intro i hi
  apply Subtype.ext
  have h := decompose_d m (i - 1)
  rw [sub_add_cancel] at h
  rw [h, hm (i - 1) (by omega), ZeroMemClass.coe_zero, d_zero, ZeroMemClass.coe_zero]

/-- The truncation `M^{≥ n}` is stable under the differential. -/
theorem d_mem_truncGESubgroup {n : ℤ} {m : M} (hm : m ∈ truncGESubgroup M n) :
    d m ∈ truncGESubgroup M n :=
  truncGESubgroup_anti (by omega : n ≤ n + 1) (d_mem_truncGESubgroup_add_one hm)

/-- If `M` has no components of negative degree, then `M^{≥ n} = M` for `n ≤ 0`. -/
theorem mem_truncGESubgroup_of_nonpos (hM : ∀ i < 0, grading (M := M) i = ⊥) {n : ℤ}
    (hn : n ≤ 0) (m : M) : m ∈ truncGESubgroup M n := by
  intro i hi
  have h : ∀ x ∈ grading (M := M) i, x = 0 := fun x hx => by
    rwa [hM i (by omega), AddSubgroup.mem_bot] at hx
  exact Subtype.ext (h _ (decompose (grading (M := M)) m i).2)

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] [Module A M] [DGModule A M]

omit [DGRing A] in
/-- The action maps `A^{≥ m} × M^{≥ n}` to `M^{≥ m + n}`. -/
theorem smul_mem_truncGESubgroup {m n : ℤ} {a : A} {x : M} (ha : a ∈ truncGESubgroup A m)
    (hx : x ∈ truncGESubgroup M n) : a • x ∈ truncGESubgroup M (m + n) := by
  refine induction_on_of_isHomogeneous (isHomogeneous_truncGESubgroup m)
    (P := fun a => a • x ∈ truncGESubgroup M (m + n)) ?_ ?_ ?_ ha
  · simp only [zero_smul, zero_mem]
  · intro i a hai ham
    refine induction_on_of_isHomogeneous (isHomogeneous_truncGESubgroup n)
      (P := fun x => a • x ∈ truncGESubgroup M (m + n)) ?_ ?_ ?_ hx
    · simp only [smul_zero, zero_mem]
    · intro j x hxj hxn
      rcases eq_zero_or_le_of_mem_truncGESubgroup hai ham with rfl | hi
      · rw [zero_smul]
        exact zero_mem _
      rcases eq_zero_or_le_of_mem_truncGESubgroup hxj hxn with rfl | hj
      · rw [smul_zero]
        exact zero_mem _
      exact mem_truncGESubgroup_of_mem (smul_mem_grading hai hxj) (by omega)
    · intro x x' hx hx'
      simp only [smul_add]
      exact add_mem hx hx'
  · intro a a' ha ha'
    simp only [add_smul]
    exact add_mem ha ha'

/-- The product maps `A^{≥ m} × A^{≥ n}` to `A^{≥ m + n}`. -/
theorem mul_mem_truncGESubgroup {m n : ℤ} {a b : A} (ha : a ∈ truncGESubgroup A m)
    (hb : b ∈ truncGESubgroup A n) : a * b ∈ truncGESubgroup A (m + n) :=
  smul_mem_truncGESubgroup (M := A) ha hb

end Trunc

section TruncIdeal

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]

/-- For a non-negatively graded dg ring `A` (`Aⁱ = 0` for `i < 0`), the truncation
`A^{≥ n} = ⨁_{i ≥ n} Aⁱ` is a dg ideal: a two-sided ideal (since `A = A^{≥ 0}` and
`A^{≥ 0} A^{≥ n} + A^{≥ n} A^{≥ 0} ⊆ A^{≥ n}`), homogeneous and stable under `d`. -/
def truncGE (hA : ∀ i < 0, grading (M := A) i = ⊥) (n : ℤ) : DGIdeal A where
  carrier := truncGESubgroup A n
  zero_mem' := zero_mem (truncGESubgroup A n)
  add_mem' := add_mem
  smul_mem' c a ha := by
    have h := mul_mem_truncGESubgroup (mem_truncGESubgroup_of_nonpos hA le_rfl c) ha
    rwa [zero_add] at h
  mul_mem_right' b ha := by
    have h := mul_mem_truncGESubgroup ha (mem_truncGESubgroup_of_nonpos hA le_rfl b)
    rwa [add_zero] at h
  isHomogeneous' := isHomogeneous_truncGESubgroup n
  d_mem' := d_mem_truncGESubgroup

section
variable (hA : ∀ i < 0, grading (M := A) i = ⊥)

@[simp]
theorem mem_truncGE {n : ℤ} {a : A} : a ∈ truncGE hA n ↔ a ∈ truncGESubgroup A n :=
  Iff.rfl

theorem mem_truncGE_iff {n : ℤ} {a : A} :
    a ∈ truncGE hA n ↔ ∀ i < n, decompose (grading (M := A)) a i = 0 :=
  Iff.rfl

/-- `A^{≥ n} = A` for `n ≤ 0`; in particular `A^{≥ 0} = A`. -/
theorem mem_truncGE_of_nonpos {n : ℤ} (hn : n ≤ 0) (a : A) : a ∈ truncGE hA n :=
  mem_truncGESubgroup_of_nonpos hA hn a

theorem truncGE_anti : Antitone (truncGE hA) :=
  fun _ _ hnn' _ ha => truncGESubgroup_anti hnn' ha

end

/-- The degree-`0` component of a product in a non-negatively graded ring is the product of the
degree-`0` components. -/
theorem coe_decompose_mul_zero (hA : ∀ i < 0, grading (M := A) i = ⊥) (a b : A) :
    (decompose (grading (M := A)) (a * b) 0 : A) =
      decompose (grading (M := A)) a 0 * decompose (grading (M := A)) b 0 := by
  have hneg : ∀ {i : ℤ} {x : A}, i < 0 → x ∈ grading i → x = 0 := fun hi hx => by
    rwa [hA _ hi, AddSubgroup.mem_bot] at hx
  induction a using induction_on with
  | h_zero => simp
  | h_add a a' ha ha' =>
    simp only [add_mul, decompose_add, DirectSum.add_apply, AddSubgroup.coe_add, ha, ha']
  | h_homogeneous a =>
    obtain ⟨a, ha⟩ := a
    rename_i i
    induction b using induction_on with
    | h_zero => simp
    | h_add b b' hb hb' =>
      simp only [mul_add, decompose_add, DirectSum.add_apply, AddSubgroup.coe_add, hb, hb']
    | h_homogeneous b =>
      obtain ⟨b, hb⟩ := b
      rename_i j
      rcases lt_or_le i 0 with hi | hi
      · simp [hneg hi ha]
      rcases lt_or_le j 0 with hj | hj
      · simp [hneg hj hb]
      by_cases h : i + j = 0
      · obtain rfl : i = 0 := by omega
        obtain rfl : j = 0 := by omega
        have hab : a * b ∈ grading (M := A) 0 := by simpa using mul_mem_grading ha hb
        rw [decompose_of_mem_same _ ha, decompose_of_mem_same _ hb,
          decompose_of_mem_same _ hab]
      · rw [decompose_of_mem_ne _ (mul_mem_grading ha hb) h]
        rcases (show i ≠ 0 ∨ j ≠ 0 by omega) with h' | h'
        · rw [decompose_of_mem_ne _ ha h', zero_mul]
        · rw [decompose_of_mem_ne _ hb h', mul_zero]

end TruncIdeal

/-! ### Positive dg rings -/

/-- A dg ring `A` is *positive* (Schnürer [Sch, §1, §4, conditions (P1)–(P3)]) if
(P1) `Aⁿ = 0` for `n < 0`, (P2) the degree-`0` part `A⁰` is a semisimple ring, and
(P3) the differential vanishes on `A⁰`.

O. M. Schnürer, *Perfect derived categories of positively graded DG algebras*, Appl. Categ.
Structures 19 (2011); arXiv:0809.4782v2. Schnürer states the conditions for a dg algebra over
a commutative ring `k`; they only involve the underlying dg ring. Semisimplicity is Mathlib's
`IsSemisimpleRing` (semisimple as a left module over itself), equivalent to right
semisimplicity. -/
structure IsPositive (A : Type*) [Ring A] [DGAddCommGroup A] [DGRing A] : Prop where
  /-- (P1) `A` is non-negatively graded. -/
  grading_eq_bot : ∀ n < 0, grading (M := A) n = ⊥
  /-- (P2) `A⁰` is a semisimple ring. -/
  isSemisimple : IsSemisimpleRing (degreeZeroSubring A)
  /-- (P3) `d (A⁰) = 0`. -/
  d_eq_zero_of_mem_zero : ∀ a ∈ grading (M := A) 0, d a = 0

namespace IsPositive

/-- A semisimple ring concentrated in degree `0` (with `d = 0`) is a positive dg ring
([Sch, Examples 8]). -/
theorem degreeZero (R : Type*) [Ring R] [IsSemisimpleRing R] :
    letI := DGAddCommGroup.degreeZero R
    haveI := DGRing.degreeZero R
    IsPositive R := by
  letI := DGAddCommGroup.degreeZero R
  haveI := DGRing.degreeZero R
  have htop : degreeZeroSubring R = ⊤ :=
    eq_top_iff.mpr fun r _ => mem_degreeZeroGrading_zero R r
  exact
    { grading_eq_bot := fun n hn => degreeZeroGrading_of_ne R (by omega)
      isSemisimple :=
        (Subring.topEquiv.symm.trans (RingEquiv.subringCongr htop.symm)).isSemisimpleRing
      d_eq_zero_of_mem_zero := fun _ _ => rfl }

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] (hA : IsPositive A)
include hA

theorem eq_zero_of_mem_grading {n : ℤ} (hn : n < 0) {a : A} (ha : a ∈ grading n) : a = 0 := by
  rwa [hA.grading_eq_bot n hn, AddSubgroup.mem_bot] at ha

theorem d_eq_zero {a : A} (ha : a ∈ grading 0) : d a = 0 :=
  hA.d_eq_zero_of_mem_zero a ha

/-- The degree-`0` component of `d a` vanishes. -/
theorem decompose_d_zero (a : A) : decompose (grading (M := A)) (d a) 0 = 0 := by
  apply Subtype.ext
  have h := decompose_d a (-1)
  rw [neg_add_cancel] at h
  rw [h, hA.eq_zero_of_mem_grading (by omega) (decompose (grading (M := A)) a (-1)).2, d_zero,
    ZeroMemClass.coe_zero]

/-! #### Idempotents of `A⁰` -/

/-- An idempotent `e` of `A⁰` is a degree-`0` idempotent cocycle of `A`, since `d (A⁰) = 0`. -/
def dgIdempotent (e : degreeZeroSubring A) (he : IsIdempotentElem e) : DGIdempotent A where
  val := e
  mem_zero := e.2
  mul_self := congrArg Subtype.val he
  d_eq_zero := hA.d_eq_zero e.2

@[simp]
theorem dgIdempotent_val (e : degreeZeroSubring A) (he : IsIdempotentElem e) :
    (hA.dgIdempotent e he).val = e :=
  rfl

/-! #### `A⁰` as a dg subring -/

/-- The degree-`0` part `A⁰` of a positive dg ring, as a dg subring. With the induced structure
it is concentrated in degree `0` (`mem_grading_degreeZeroDGSubring_iff`) and has zero
differential (`d_degreeZeroDGSubring`). -/
def degreeZeroDGSubring : DGSubring A where
  __ := degreeZeroSubring A
  isHomogeneous' n a ha := by
    by_cases hn : n = 0
    · subst hn
      exact (decompose (grading (M := A)) a 0).2
    · rw [decompose_of_mem_ne _ ha (Ne.symm hn)]
      exact zero_mem (degreeZeroSubring A)
  d_mem' {a} ha := by
    rw [hA.d_eq_zero ha]
    exact zero_mem (degreeZeroSubring A)

@[simp]
theorem mem_degreeZeroDGSubring {a : A} : a ∈ hA.degreeZeroDGSubring ↔ a ∈ grading (M := A) 0 :=
  Iff.rfl

@[simp]
theorem d_degreeZeroDGSubring (x : hA.degreeZeroDGSubring) : d x = 0 :=
  Subtype.ext (by rw [DGSubring.coe_d, hA.d_eq_zero x.2, ZeroMemClass.coe_zero])

/-- The dg subring `A⁰` is concentrated in degree `0`. -/
theorem mem_grading_degreeZeroDGSubring_iff {n : ℤ} {x : hA.degreeZeroDGSubring} :
    x ∈ grading n ↔ n = 0 ∨ x = 0 := by
  rw [DGSubring.mem_grading_iff]
  constructor
  · intro hx
    by_cases hn : n = 0
    · exact Or.inl hn
    · refine Or.inr (Subtype.ext ?_)
      have h := decompose_of_mem_same (grading (M := A)) hx
      rwa [decompose_of_mem_ne _ x.2 (Ne.symm hn), eq_comm] at h
  · rintro (rfl | rfl)
    · exact x.2
    · exact zero_mem _

/-! #### The projection `A → A⁰` -/

/-- The projection `A → A⁰`, `a ↦ a₀`, onto the degree-`0` component, as a morphism of dg rings
(Schnürer's `A → A / A⁺ = A⁰`). It is multiplicative because `A` is non-negatively graded, and
commutes with `d` because `A⁻¹ = 0` and `d (A⁰) = 0`. -/
def projZero : A →ᵈᵍ+* hA.degreeZeroDGSubring where
  toFun a := ⟨decompose (grading (M := A)) a 0, (decompose (grading (M := A)) a 0).2⟩
  map_one' := Subtype.ext (decompose_of_mem_same _ one_mem_grading)
  map_mul' a b := Subtype.ext (coe_decompose_mul_zero hA.grading_eq_bot a b)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)
  map_mem' {n} a ha := by
    rw [DGSubring.mem_grading_iff]
    by_cases hn : n = 0
    · subst hn
      exact (decompose (grading (M := A)) a 0).2
    · show (decompose (grading (M := A)) a 0 : A) ∈ grading n
      rw [decompose_of_mem_ne _ ha hn]
      exact zero_mem _
  map_d' a := Subtype.ext <| by
    show (decompose (grading (M := A)) (d a) 0 : A) = d (decompose (grading (M := A)) a 0 : A)
    rw [hA.decompose_d_zero, hA.d_eq_zero (decompose (grading (M := A)) a 0).2,
      ZeroMemClass.coe_zero]

@[simp]
theorem coe_projZero_apply (a : A) :
    (hA.projZero a : A) = decompose (grading (M := A)) a 0 :=
  rfl

theorem projZero_apply_of_mem_zero {a : A} (ha : a ∈ grading 0) :
    (hA.projZero a : A) = a :=
  decompose_of_mem_same _ ha

/-- The projection `A → A⁰` is a retraction of the inclusion `A⁰ → A`. -/
@[simp]
theorem projZero_comp_subtype :
    hA.projZero.comp (DGSubring.subtype hA.degreeZeroDGSubring) = DGRingHom.id :=
  DGRingHom.ext fun x => Subtype.ext (hA.projZero_apply_of_mem_zero x.2)

theorem projZero_surjective : Function.Surjective hA.projZero := fun x =>
  ⟨x, Subtype.ext (hA.projZero_apply_of_mem_zero x.2)⟩

/-- The kernel of the projection `A → A⁰` is the dg ideal `A⁺ = A^{≥ 1}`. -/
theorem ker_projZero : hA.projZero.ker = truncGE hA.grading_eq_bot 1 := by
  ext a
  rw [DGRingHom.mem_ker, mem_truncGE_iff]
  constructor
  · intro h i hi
    rcases lt_or_eq_of_le (show i ≤ 0 by omega) with hi | rfl
    · exact Subtype.ext (hA.eq_zero_of_mem_grading hi (decompose (grading (M := A)) a i).2)
    · exact Subtype.ext (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (congrArg Subtype.val (h 0 zero_lt_one))

/-- The morphism of dg rings `A ⧸ A^{≥ 1} → A⁰` induced by the projection; it is bijective
(`quotientTruncGEOneHom_bijective`). -/
def quotientTruncGEOneHom : (A ⧸ truncGE hA.grading_eq_bot 1) →ᵈᵍ+* hA.degreeZeroDGSubring :=
  DGIdeal.Quotient.lift hA.projZero fun a ha => by
    rw [← DGRingHom.mem_ker, hA.ker_projZero]
    exact ha

@[simp]
theorem quotientTruncGEOneHom_mk (a : A) :
    hA.quotientTruncGEOneHom (DGIdeal.Quotient.mk _ a) = hA.projZero a :=
  DGIdeal.Quotient.lift_mk _ _ a

theorem quotientTruncGEOneHom_bijective : Function.Bijective hA.quotientTruncGEOneHom := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨a, rfl⟩ := DGIdeal.Quotient.mk_surjective _ x
    rw [quotientTruncGEOneHom_mk, ← DGRingHom.mem_ker, hA.ker_projZero] at hx
    exact (DGIdeal.Quotient.mk_eq_zero_iff_mem _).mpr hx
  · obtain ⟨a, rfl⟩ := hA.projZero_surjective y
    exact ⟨DGIdeal.Quotient.mk _ a, hA.quotientTruncGEOneHom_mk a⟩

/-- The ring isomorphism `A ⧸ A^{≥ 1} ≃ A⁰`; its underlying map is the morphism of dg rings
`quotientTruncGEOneHom` (degree `0`, commuting with `d`). -/
noncomputable def quotientTruncGEOneEquiv :
    (A ⧸ truncGE hA.grading_eq_bot 1) ≃+* hA.degreeZeroDGSubring :=
  RingEquiv.ofBijective hA.quotientTruncGEOneHom hA.quotientTruncGEOneHom_bijective

@[simp]
theorem coe_quotientTruncGEOneEquiv :
    ⇑hA.quotientTruncGEOneEquiv = hA.quotientTruncGEOneHom :=
  rfl

/-! #### Cohomology in non-positive degrees -/

/-- A positive dg ring has no cohomology in negative degrees. -/
theorem subsingleton_cohomology_of_neg {n : ℤ} (hn : n < 0) : Subsingleton (cohomology A n) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  induction x using cohomology.induction_on with
  | h z =>
    have hz : z = 0 := Subtype.ext (hA.eq_zero_of_mem_grading hn z.2.1)
    rw [hz, map_zero]

/-- A positive dg ring has no non-zero coboundaries in degree `0`, since `A⁻¹ = 0`. -/
theorem eq_zero_of_mem_coboundaries_zero {a : A} (ha : a ∈ coboundaries A 0) : a = 0 := by
  obtain ⟨m, hm, rfl⟩ := ha
  rw [hA.eq_zero_of_mem_grading (by omega) hm, d_zero]

/-- For a positive dg ring, `H⁰(A) ≅ A⁰`: every element of `A⁰` is a cocycle, and there are no
non-zero coboundaries in degree `0` since `A⁻¹ = 0`. The map sends the class of a cocycle to
itself. -/
def cohomologyZeroEquiv : cohomology A 0 ≃+ grading (M := A) 0 where
  toFun := cohomology.lift (AddSubgroup.inclusion (cocycles_le_grading 0)) fun _ hz =>
    Subtype.ext (hA.eq_zero_of_mem_coboundaries_zero hz)
  invFun a := cohomology.mkOf a.2 (hA.d_eq_zero a.2)
  left_inv x := by
    induction x using cohomology.induction_on with
    | h z => rw [cohomology.lift_mk]; rfl
  right_inv a := cohomology.lift_mk _ _ _
  map_add' := map_add _

@[simp]
theorem coe_cohomologyZeroEquiv_mk (z : cocycles A 0) :
    (hA.cohomologyZeroEquiv (cohomology.mk A 0 z) : A) = z :=
  congrArg Subtype.val (cohomology.lift_mk (AddSubgroup.inclusion (cocycles_le_grading 0))
    (fun _ hz => Subtype.ext (hA.eq_zero_of_mem_coboundaries_zero hz)) z)

@[simp]
theorem cohomologyZeroEquiv_symm_apply (a : grading (M := A) 0) :
    hA.cohomologyZeroEquiv.symm a = cohomology.mkOf a.2 (hA.d_eq_zero a.2) :=
  rfl

end IsPositive

/-! ### Truncations of dg modules over positive dg rings -/

section Module

variable {A : Type*} [Ring A] [DGAddCommGroup A] {M : Type*} [AddCommGroup M]
  [DGAddCommGroup M] [Module A M] [DGModule A M]

/-- Over a non-negatively graded dg ring `A` (e.g. a positive one), the truncation `M^{≥ n}` of a
dg `A`-module is stable under the action of `A` (and under `d`, `d_mem_truncGESubgroup`): it is
a dg submodule. -/
theorem smul_mem_truncGESubgroup_of_nonneg (hA : ∀ i < 0, grading (M := A) i = ⊥) {n : ℤ}
    (a : A) {x : M} (hx : x ∈ truncGESubgroup M n) : a • x ∈ truncGESubgroup M n := by
  have h := smul_mem_truncGESubgroup (mem_truncGESubgroup_of_nonpos hA le_rfl a) hx
  rwa [zero_add] at h

end Module

end DG
