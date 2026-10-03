import DG.HalfGraded.Basic

/-!
# The diagonal half-grading of an ordinary dg ring

An ordinary integer-graded dg ring becomes a half-graded dg ring on the *same* ring,
with `Aⁿ` in internal degree `2n` and parity `n mod 2`. The differential is unchanged
and has bidegree `(2, 1)`. No field, commutativity, positivity or boundedness hypothesis
is required. This construction does not assert a derived-category equivalence.
-/

open DirectSum

namespace DG

/-- The diagonal index map: twice the cohomological degree and its parity. -/
def diagonalDegree : ℤ →+ ℤ × ZMod 2 where
  toFun n := (2 * n, (n : ZMod 2))
  map_zero' := by simp
  map_add' m n := by simp [mul_add]

@[simp] theorem diagonalDegree_apply (n : ℤ) :
    diagonalDegree n = (2 * n, (n : ZMod 2)) := rfl

theorem diagonalDegree_injective : Function.Injective diagonalDegree := by
  intro m n h
  have := congrArg Prod.fst h
  simp only [diagonalDegree_apply] at this
  omega

@[simp] theorem diagonalDegree_one : diagonalDegree 1 = (2, 1) := by
  simp

/-- Equal parity gives equal ordinary Koszul signs, also in negative degrees. -/
theorem koszulSign_eq_of_cast_eq {m n : ℤ} (h : (m : ZMod 2) = (n : ZMod 2)) :
    koszulSign m = koszulSign n := by
  apply (Int.negOnePow_eq_iff m n).2
  apply Int.even_iff.mpr
  have hmod := (ZMod.intCast_eq_intCast_iff' m n 2).mp h
  omega

namespace Diagonal

variable (M : Type*) [AddCommGroup M] [DGAddCommGroup M]

/-- The diagonal grading on the original abelian group, transported from its existing
homogeneous decomposition. Off the diagonal the components are zero. -/
def grading (p : ℤ × ZMod 2) : AddSubgroup M :=
  (coarseGrading (fun n => DG.grading (M := M) n) diagonalDegree p).comap
    (decomposeAddEquiv (DG.grading (M := M))).toAddMonoidHom

noncomputable instance : Decomposition (grading M) :=
  (isInternal_comap _ (decomposeAddEquiv (DG.grading (M := M))).toAddMonoidHom
    (decomposeAddEquiv (DG.grading (M := M))).injective
    (fun _ _ => (decomposeAddEquiv (DG.grading (M := M))).surjective _)).chooseDecomposition

variable {M}

/-- Induction on a diagonal homogeneous element, using the original components. -/
@[elab_as_elim]
theorem induction_on {p : ℤ × ZMod 2} {P : M → Prop} {a : M}
    (ha : a ∈ grading M p) (zero : P 0)
    (homogeneous : ∀ n (a : M), a ∈ DG.grading n → diagonalDegree n = p → P a)
    (add : ∀ a b, P a → P b → P (a + b)) : P a := by
  let e := decomposeAddEquiv (DG.grading (M := M))
  have h : P (e.symm (e a)) := by
    apply coarseGrading_induction (β := fun n => DG.grading (M := M) n)
      (f := diagonalDegree) (P := fun x => P (e.symm x))
      (by simpa using zero) (fun n a hn => ?_)
      (fun x y hx hy => by simpa only [map_add] using add _ _ hx hy) ha
    simpa only [e, decomposeAddEquiv_symm_apply, decompose_symm_of] using
      homogeneous n a a.2 hn
  simpa using h

/-- Each original degree is placed at precisely its diagonal bidegree. -/
theorem mem_grading {n : ℤ} {a : M} (ha : a ∈ DG.grading n) :
    a ∈ grading M (diagonalDegree n) := by
  change decompose (DG.grading (M := M)) a ∈
    coarseGrading (fun n => DG.grading (M := M) n) diagonalDegree (diagonalDegree n)
  rw [decompose_of_mem _ ha]
  exact of_mem_coarseGrading (β := fun n => DG.grading (M := M) n)
    (f := diagonalDegree) n ⟨a, ha⟩

@[simp] theorem grading_diagonal (n : ℤ) :
    grading M (diagonalDegree n) = DG.grading (M := M) n := by
  ext a
  constructor
  · intro ha
    exact induction_on ha (zero_mem _) (fun m b hb h =>
      diagonalDegree_injective h ▸ hb) (fun _ _ => add_mem)
  · exact mem_grading

/-- There are no extra components away from the diagonal. -/
theorem grading_eq_bot {p : ℤ × ZMod 2} (hp : p ∉ Set.range diagonalDegree) :
    grading M p = ⊥ := by
  ext a
  change a ∈ grading M p ↔ a = 0
  constructor
  · intro ha
    exact induction_on ha rfl (fun n _ _ hn => False.elim (hp ⟨n, hn⟩))
      (fun _ _ hx hy => by simp [hx, hy])
  · rintro rfl
    exact zero_mem _

/-- Diagonal projection recovers the original homogeneous projection. -/
theorem coe_decompose (a : M) (n : ℤ) :
    (decompose (grading M) a (diagonalDegree n) : M) =
      (decompose (DG.grading (M := M)) a n : M) := by
  induction a using DG.induction_on with
  | h_zero => simp
  | h_homogeneous a =>
    rename_i m
    by_cases h : m = n
    · subst n
      rw [decompose_of_mem_same _ (mem_grading a.2), decompose_of_mem_same _ a.2]
    · rw [decompose_of_mem_ne _ (mem_grading a.2)
        (fun he => h (diagonalDegree_injective he)), decompose_of_mem_ne _ a.2 h]
  | h_add a b ha hb =>
    simp only [decompose_add, DirectSum.add_apply, AddSubgroup.coe_add, ha, hb]

/-- The original differential has diagonal bidegree `(2,1)`. -/
theorem d_mem {p : ℤ × ZMod 2} {a : M} (ha : a ∈ grading M p) :
    d a ∈ grading M (p + (2, 1)) := by
  refine induction_on (P := fun x => d x ∈ grading M (p + (2, 1))) ha
    (by simp) (fun n a ha hn => ?_)
    (fun _ _ hx hy => by simpa only [d_add] using add_mem hx hy)
  rw [← hn, ← diagonalDegree_one, ← map_add]
  exact mem_grading (DG.d_mem ha)

end Diagonal

namespace Diagonal

section Module

variable {A M : Type*} [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]

/-- The original module action respects the diagonal gradings on both original types.
This is an action compatibility, not a construction of a weight-category module. -/
theorem smul_mem {p q : ℤ × ZMod 2} {a : A} {m : M}
    (ha : a ∈ grading A p) (hm : m ∈ grading M q) :
    a • m ∈ grading M (p + q) := by
  refine induction_on (P := fun x => x • m ∈ grading M (p + q)) ha
    (by simp) (fun i a ha hi => ?_)
    (fun _ _ hx hy => by simpa only [add_smul] using add_mem hx hy)
  refine induction_on (P := fun y => a • y ∈ grading M (p + q)) hm
    (by simp) (fun j m hm hj => ?_)
    (fun _ _ hx hy => by simpa only [smul_add] using add_mem hx hy)
  rw [← hi, ← hj, ← map_add]
  exact mem_grading (smul_mem_grading ha hm)

/-- The ordinary dg-module Leibniz rule has precisely the half-grading parity sign. -/
theorem d_smul {j n : ℤ} {a : A} (ha : a ∈ grading A (j, (n : ZMod 2))) (m : M) :
    d (a • m) = d a • m + koszulSign n • (a • d m) := by
  refine induction_on ha (by simp) (fun i a ha hi => ?_)
    (fun _ _ hx hy => by
      simp only [add_smul, d_add, hx, hy, smul_add]
      abel)
  rw [DG.d_smul ha, koszulSign_eq_of_cast_eq (congrArg Prod.snd hi)]

end Module

end Diagonal

namespace HalfGradedDGRing

variable (A : Type*) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- An ordinary dg ring as a diagonal half-graded dg ring, with internal differential
degree `2`. The underlying ring and differential are the original ones. -/
noncomputable def ofDGRing : HalfGradedDGRing A 2 where
  hgrading := Diagonal.grading A
  gradedMonoid := {
    one_mem := by
      change (1 : A) ∈ Diagonal.grading A (diagonalDegree 0)
      exact Diagonal.mem_grading one_mem_grading
    mul_mem := fun p q a b ha hb => by
      refine Diagonal.induction_on (P := fun x => x * b ∈ Diagonal.grading A (p + q))
        ha (by simp) (fun m a ha hm => ?_)
        (fun _ _ hx hy => by simpa only [add_mul] using add_mem hx hy)
      refine Diagonal.induction_on (P := fun y => a * y ∈ Diagonal.grading A (p + q))
        hb (by simp) (fun n b hb hn => ?_)
        (fun _ _ hx hy => by simpa only [mul_add] using add_mem hx hy)
      rw [← hm, ← hn, ← map_add]
      exact Diagonal.mem_grading (mul_mem_grading ha hb) }
  hd := d
  hd_mem := Diagonal.d_mem
  hd_hd := d_d
  hd_mul := fun {j n a} ha b => by
    refine Diagonal.induction_on ha (by simp) (fun m a ha hm => ?_)
      (fun _ _ hx hy => by
        simp only [add_mul, d_add, hx, hy, smul_add]
        abel)
    have hsign := koszulSign_eq_of_cast_eq (congrArg Prod.snd hm)
    rw [DG.d_mul ha, hsign]

@[simp] theorem ofDGRing_hd : (ofDGRing A).hd = d := rfl

@[simp] theorem ofDGRing_hgrading (n : ℤ) :
    (ofDGRing A).hgrading (2 * n, (n : ZMod 2)) = DG.grading (M := A) n :=
  Diagonal.grading_diagonal n

/-- The zero-weight slice of the existing half-regrading recovers `Aⁿ`. -/
@[simp] theorem ofDGRing_hgrading_halfDegree_zero (n : ℤ) :
    (ofDGRing A).hgrading (halfDegree 2 (n, 0)) = DG.grading (M := A) n := by
  simpa only [halfDegree_apply, zero_add, mul_comm] using ofDGRing_hgrading A n

/-- Off the diagonal the half-graded components vanish. -/
theorem ofDGRing_hgrading_eq_bot {p : ℤ × ZMod 2} (hp : p ∉ Set.range diagonalDegree) :
    (ofDGRing A).hgrading p = ⊥ := Diagonal.grading_eq_bot hp

/-- Recovery of homogeneous components; the underlying elements do not change. -/
noncomputable def ofDGRingComponentEquiv (n : ℤ) :
    (ofDGRing A).hgrading (2 * n, (n : ZMod 2)) ≃+ DG.grading (M := A) n :=
  AddEquiv.addSubgroupCongr (ofDGRing_hgrading A n)

end HalfGradedDGRing

end DG
