import DG.HalfGraded.Hom

/-!
# The part of internal degree `0` of a half-graded dg ring

Let `H` be a half-graded dg ring with parameter `k`: a ring `A = ⨁ (j, ε), A^{j,ε}` graded by an
internal degree `j : ℤ` and a parity `ε : ℤ/2`, with a differential of bidegree `(k, 1̄)`.

* Its part of internal degree `0`, `A^{0,•} = A^{0,0̄} ⊕ A^{0,1̄}`, is a subring
  (`DG.HalfGradedDGRing.internalZeroSubring`), graded by `ℤ × ℤ/2` with components
  `A^{0,•} ∩ A^{j,ε}` (`DG.HalfGradedDGRing.internalZeroGrading`; these vanish for `j ≠ 0`, so this
  is the `ℤ/2`-grading of `A^{0,•}` by parity). With zero differential it is a half-graded dg ring
  (`DG.HalfGradedDGRing.internalZeroPart`).
* Conversely a `ℤ/2`-graded ring `B = B_0̄ ⊕ B_1̄` (a superring) placed in internal degree `0`,
  with zero differential, is a half-graded dg ring (`DG.HalfGradedDGRing.ofSuper ℬ k`).

The graded semisimplicity of `A^{0,•}` (as a `ℤ × ℤ/2`-graded ring concentrated in internal
degree `0`, that is, as a `ℤ/2`-graded ring) is the semisimplicity hypothesis of positivity
(`DG/HalfGraded/Positive.lean`). It is implied by the semisimplicity of `A^{0,0̄}` when
`A^{0,1̄} = 0` (`DG.HalfGradedDGRing.isGradedSemisimpleRing_internalZeroGrading_of_odd`), and for
`ofSuper ℬ k` it is the graded semisimplicity of `ℬ`
(`DG.HalfGradedDGRing.isGradedSemisimpleRing_internalZeroGrading_ofSuper`).
-/

open DirectSum

universe u

noncomputable section

namespace DG

namespace HalfGradedDGRing

theorem zmod_two_cases (ε : ZMod 2) : ε = 0 ∨ ε = 1 := by
  revert ε
  decide

/-! ### Superrings placed in internal degree `0` -/

section Super

variable {B : Type u} [Ring B] (ℬ : ZMod 2 → AddSubgroup B)

/-- The `ℤ × ℤ/2`-grading of a `ℤ/2`-graded ring placed in internal degree `0`. -/
def superGrading (p : ℤ × ZMod 2) : AddSubgroup B := if p.1 = 0 then ℬ p.2 else ⊥

variable {ℬ}

theorem superGrading_zero (ε : ZMod 2) : superGrading ℬ (0, ε) = ℬ ε := by
  simp [superGrading]

theorem eq_zero_of_mem_superGrading {p : ℤ × ZMod 2} (hp : p.1 ≠ 0) {x : B}
    (hx : x ∈ superGrading ℬ p) : x = 0 := by
  simpa [superGrading, hp] using hx

variable (ℬ) [Decomposition ℬ]

/-- The inclusion `B_ε → B^{0,ε}`. -/
def superIncl (ε : ZMod 2) : ℬ ε →+ superGrading ℬ (0, ε) where
  toFun x := ⟨x, by rw [superGrading_zero]; exact x.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The decomposition for the grading of a superring placed in internal degree `0`. -/
def superDecompose : B →+ ⨁ p, superGrading ℬ p :=
  (DirectSum.toAddMonoid fun ε =>
    (DirectSum.of (fun p => superGrading ℬ p) (0, ε)).comp (superIncl ℬ ε)).comp
    (decomposeAddEquiv ℬ).toAddMonoidHom

theorem superDecompose_of_mem {ε : ZMod 2} {x : B} (hx : x ∈ ℬ ε) :
    superDecompose ℬ x =
      DirectSum.of (fun p => superGrading ℬ p) (0, ε) (superIncl ℬ ε ⟨x, hx⟩) := by
  simp only [superDecompose, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    decomposeAddEquiv_apply, decompose_of_mem ℬ hx, toAddMonoid_of]

instance : Decomposition (superGrading ℬ) :=
  Decomposition.ofAddHom _ (superDecompose ℬ)
    (AddMonoidHom.ext fun x => by
      induction x using Decomposition.inductionOn ℬ with
      | zero => simp
      | homogeneous x =>
        rename_i ε
        simp only [AddMonoidHom.comp_apply, superDecompose_of_mem ℬ x.2,
          DirectSum.coeAddMonoidHom_of, AddMonoidHom.id_apply]
        rfl
      | add x y hx hy =>
        simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, map_add] at hx hy ⊢
        rw [hx, hy])
    (DirectSum.addHom_ext fun p x => by
      obtain ⟨j, ε⟩ := p
      obtain ⟨x, hx⟩ := x
      simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of, AddMonoidHom.id_apply]
      by_cases hj : j = 0
      · subst hj
        have hx' : x ∈ ℬ ε := by rwa [superGrading_zero] at hx
        rw [superDecompose_of_mem ℬ hx']
        rfl
      · have h0 : x = 0 := eq_zero_of_mem_superGrading hj hx
        subst h0
        rw [map_zero]
        exact (map_zero (DirectSum.of (fun p => superGrading ℬ p) (j, ε))).symm)

variable [SetLike.GradedMonoid ℬ]

instance : SetLike.GradedMonoid (superGrading ℬ) where
  one_mem := by
    rw [show (0 : ℤ × ZMod 2) = (0, 0) from rfl, superGrading_zero]
    exact SetLike.GradedOne.one_mem
  mul_mem p q a b ha hb := by
    by_cases hp : p.1 = 0
    · by_cases hq : q.1 = 0
      · obtain ⟨j, ε⟩ := p
        obtain ⟨j', ε'⟩ := q
        simp only at hp hq
        subst hp hq
        rw [superGrading_zero] at ha hb
        rw [Prod.mk_add_mk, add_zero, superGrading_zero]
        exact SetLike.GradedMul.mul_mem ha hb
      · rw [eq_zero_of_mem_superGrading hq hb, mul_zero]
        exact zero_mem _
    · rw [eq_zero_of_mem_superGrading hp ha, zero_mul]
      exact zero_mem _

instance : GradedRing (superGrading ℬ) where

/-- A `ℤ/2`-graded ring placed in internal degree `0` (`B^{0,ε} = B_ε`), with zero differential,
as a half-graded dg ring with parameter `k`. -/
def ofSuper (k : ℤ) : HalfGradedDGRing B k where
  hgrading := superGrading ℬ
  hd := 0
  hd_mem _ := zero_mem _
  hd_hd _ := rfl
  hd_mul _ _ := by simp

@[simp]
theorem ofSuper_hd (k : ℤ) (b : B) : (ofSuper ℬ k).hd b = 0 := rfl

theorem ofSuper_hgrading (k : ℤ) : (ofSuper ℬ k).hgrading = superGrading ℬ := rfl

end Super

/-! ### The subring `A^{0,•}` -/

variable {A : Type u} [Ring A] {k : ℤ} (H : HalfGradedDGRing A k)

/-- The subring `A^{0,•} = A^{0,0̄} ⊕ A^{0,1̄}` of elements of internal degree `0`. -/
def internalZeroSubring : Subring A where
  toAddSubgroup := H.hgrading (0, 0) ⊔ H.hgrading (0, 1)
  one_mem' := AddSubgroup.mem_sup_left SetLike.GradedOne.one_mem
  mul_mem' := by
    intro a b ha hb
    have hmem : ∀ {ε : ZMod 2} {x : A}, x ∈ H.hgrading (0, ε) →
        x ∈ H.hgrading (0, 0) ⊔ H.hgrading (0, 1) := fun {ε} {x} hx => by
      rcases zmod_two_cases ε with rfl | rfl
      · exact AddSubgroup.mem_sup_left hx
      · exact AddSubgroup.mem_sup_right hx
    have hmul : ∀ {ε ε' : ZMod 2} {x y : A}, x ∈ H.hgrading (0, ε) → y ∈ H.hgrading (0, ε') →
        x * y ∈ H.hgrading (0, 0) ⊔ H.hgrading (0, 1) := fun hx hy => hmem (by
      have := SetLike.GradedMul.mul_mem hx hy
      rwa [Prod.mk_add_mk, add_zero] at this)
    obtain ⟨x, hx, y, hy, rfl⟩ := AddSubgroup.mem_sup.mp ha
    obtain ⟨x', hx', y', hy', rfl⟩ := AddSubgroup.mem_sup.mp hb
    simp only [mul_add, add_mul]
    exact add_mem (add_mem (hmul hx hx') (hmul hy hx')) (add_mem (hmul hx hy') (hmul hy hy'))

variable {H}

theorem mem_internalZeroSubring_iff {a : A} :
    a ∈ H.internalZeroSubring ↔ a ∈ H.hgrading (0, 0) ⊔ H.hgrading (0, 1) :=
  Iff.rfl

theorem mem_internalZeroSubring_of_mem {ε : ZMod 2} {a : A} (ha : a ∈ H.hgrading (0, ε)) :
    a ∈ H.internalZeroSubring := by
  rcases zmod_two_cases ε with rfl | rfl
  · exact AddSubgroup.mem_sup_left ha
  · exact AddSubgroup.mem_sup_right ha

/-- An induction principle for `A^{0,•}`: a property of elements of `A`, additive and holding on
`A^{0,0̄}` and `A^{0,1̄}`, holds on `A^{0,•}`. -/
theorem internalZeroSubring_induction {P : A → Prop} (hP : ∀ {ε : ZMod 2} {a : A},
    a ∈ H.hgrading (0, ε) → P a) (hadd : ∀ a b, P a → P b → P (a + b)) {a : A}
    (ha : a ∈ H.internalZeroSubring) : P a := by
  obtain ⟨x, hx, y, hy, rfl⟩ := AddSubgroup.mem_sup.mp ha
  exact hadd _ _ (hP hx) (hP hy)

/-- The homogeneous components of an element of `A^{0,•}` lie in `A^{0,•}`. -/
theorem coe_decompose_mem_internalZeroSubring {a : A} (ha : a ∈ H.internalZeroSubring)
    (p : ℤ × ZMod 2) : (decompose H.hgrading a p : A) ∈ H.internalZeroSubring := by
  refine internalZeroSubring_induction (P := fun a =>
    (decompose H.hgrading a p : A) ∈ H.internalZeroSubring) (fun {ε} {a} ha' => ?_)
    (fun a b ha hb => ?_) ha
  · by_cases hp : (0, ε) = p
    · subst hp
      rw [decompose_of_mem_same _ ha']
      exact mem_internalZeroSubring_of_mem ha'
    · rw [decompose_of_mem_ne _ ha' hp]
      exact zero_mem _
  · simp only [decompose_add, DirectSum.add_apply, AddSubgroup.coe_add]
    exact add_mem ha hb

/-- An element of `A^{0,•}` of internal degree `j ≠ 0` vanishes. -/
theorem eq_zero_of_mem_internalZeroSubring {a : A} (ha : a ∈ H.internalZeroSubring)
    {p : ℤ × ZMod 2} (hp : p.1 ≠ 0) (hap : a ∈ H.hgrading p) : a = 0 := by
  have h := decompose_of_mem_same _ hap
  rw [← h]
  refine internalZeroSubring_induction (P := fun a => (decompose H.hgrading a p : A) = 0)
    (fun {ε} {a} ha' => decompose_of_mem_ne _ ha' (fun h => hp (by rw [← h]))) (fun a b ha hb => ?_)
    ha
  simp only [decompose_add, DirectSum.add_apply, AddSubgroup.coe_add, ha, hb, add_zero]

variable (H)

/-- The `ℤ × ℤ/2`-grading of `A^{0,•}`: its components `A^{0,•} ∩ A^{j,ε}` vanish for `j ≠ 0`. -/
def internalZeroGrading (p : ℤ × ZMod 2) : AddSubgroup H.internalZeroSubring :=
  (H.hgrading p).comap (AddSubgroupClass.subtype H.internalZeroSubring)

variable {H}

theorem mem_internalZeroGrading_iff {p : ℤ × ZMod 2} {s : H.internalZeroSubring} :
    s ∈ H.internalZeroGrading p ↔ (s : A) ∈ H.hgrading p :=
  Iff.rfl

variable (H)

theorem isInternal_internalZeroGrading : DirectSum.IsInternal H.internalZeroGrading :=
  isInternal_comap _ _ Subtype.val_injective fun p a =>
    ⟨⟨_, coe_decompose_mem_internalZeroSubring a.2 p⟩, rfl⟩

instance : Decomposition H.internalZeroGrading :=
  (H.isInternal_internalZeroGrading).chooseDecomposition

instance : SetLike.GradedMonoid H.internalZeroGrading where
  one_mem := mem_internalZeroGrading_iff.mpr SetLike.GradedOne.one_mem
  mul_mem _ _ _ _ ha hb := mem_internalZeroGrading_iff.mpr (SetLike.GradedMul.mul_mem
    (mem_internalZeroGrading_iff.mp ha) (mem_internalZeroGrading_iff.mp hb))

instance : GradedRing H.internalZeroGrading where

/-- The components of an element of `A^{0,•}` are its components in `A`. -/
theorem coe_decompose_internalZeroGrading (s : H.internalZeroSubring) (p : ℤ × ZMod 2) :
    ((decompose H.internalZeroGrading s p : H.internalZeroSubring) : A) =
      decompose H.hgrading (s : A) p :=
  letI : Decomposition fun p => (H.hgrading p).comap
      (AddSubgroupClass.subtype H.internalZeroSubring) :=
    inferInstanceAs (Decomposition H.internalZeroGrading)
  coe_decompose_comap H.hgrading (AddSubgroupClass.subtype H.internalZeroSubring) s p

/-- The part `A^{0,•}` of internal degree `0`, with zero differential, as a half-graded dg ring. -/
def internalZeroPart : HalfGradedDGRing H.internalZeroSubring k where
  hgrading := H.internalZeroGrading
  hd := 0
  hd_mem _ := zero_mem _
  hd_hd _ := rfl
  hd_mul _ _ := by simp

@[simp]
theorem internalZeroPart_hd (s : H.internalZeroSubring) : H.internalZeroPart.hd s = 0 := rfl

theorem internalZeroPart_hgrading : H.internalZeroPart.hgrading = H.internalZeroGrading := rfl

/-! ### Graded semisimplicity of `A^{0,•}` -/

section Semisimple

variable {H}

/-- If `A^{0,1̄} = 0`, then `A^{0,•} = A^{0,0̄}`. -/
theorem internalZeroSubring_eq_of_odd (hodd : ∀ a ∈ H.hgrading (0, 1), a = 0) :
    H.internalZeroSubring = SetLike.GradeZero.subring H.hgrading := by
  ext a
  refine ⟨fun ha => ?_, fun ha => AddSubgroup.mem_sup_left ha⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := AddSubgroup.mem_sup.mp ha
  rw [hodd y hy, add_zero]
  exact hx

/-- If `A^{0,1̄} = 0` and `A^{0,0̄}` is a semisimple ring, then `A^{0,•}` is graded semisimple. -/
theorem isGradedSemisimpleRing_internalZeroGrading_of_odd
    (hodd : ∀ a ∈ H.hgrading (0, 1), a = 0)
    (hss : IsSemisimpleRing (SetLike.GradeZero.subring H.hgrading)) :
    IsGradedSemisimpleRing H.internalZeroGrading := by
  have : IsSemisimpleRing H.internalZeroSubring :=
    (RingEquiv.subringCongr (internalZeroSubring_eq_of_odd hodd).symm).isSemisimpleRing
  exact isGradedSemisimpleRing_of_isSemisimpleRing _

variable {B : Type u} [Ring B] {ℬ : ZMod 2 → AddSubgroup B} [GradedRing ℬ]

/-- A graded semisimple `ℤ/2`-graded ring placed in internal degree `0` is graded semisimple as a
`ℤ × ℤ/2`-graded ring. -/
theorem isGradedSemisimpleRing_superGrading (h : IsGradedSemisimpleRing ℬ) :
    IsGradedSemisimpleRing (superGrading ℬ) := by
  obtain ⟨l, hl, hlp, hsum⟩ := h.exists_list_sum_eq_one
  refine isGradedSemisimpleRing_iff_exists_list.mpr ⟨l, fun e he => ?_, hlp, hsum⟩
  obtain ⟨he0, heI, hes⟩ := hl e he
  refine ⟨by rw [show (0 : ℤ × ZMod 2) = (0, 0) from rfl, superGrading_zero]; exact he0, heI,
    hes.1, fun p x hx hxe hx0 => ?_⟩
  obtain ⟨j, ε⟩ := p
  by_cases hj : j = 0
  · subst hj
    rw [superGrading_zero] at hx
    obtain ⟨g, hg, hgx⟩ := hes.2 hx hxe hx0
    refine ⟨g, ?_, hgx⟩
    rw [Prod.neg_mk, neg_zero, superGrading_zero]
    exact hg
  · exact absurd (eq_zero_of_mem_superGrading hj hx) hx0

/-- For a superring `B` placed in internal degree `0`, `A^{0,•} = B`. -/
def ofSuperInternalZeroEquiv (k : ℤ) : B ≃+* (ofSuper ℬ k).internalZeroSubring where
  toFun b := ⟨b, by
    classical
    rw [← DirectSum.sum_support_decompose ℬ b]
    refine sum_mem fun ε _ => mem_internalZeroSubring_of_mem (H := ofSuper ℬ k) (ε := ε) ?_
    rw [ofSuper_hgrading, superGrading_zero]
    exact SetLike.coe_mem _⟩
  invFun s := s
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- A graded semisimple superring placed in internal degree `0` has graded semisimple
`A^{0,•}`. -/
theorem isGradedSemisimpleRing_internalZeroGrading_ofSuper (k : ℤ)
    (h : IsGradedSemisimpleRing ℬ) :
    IsGradedSemisimpleRing (ofSuper ℬ k).internalZeroGrading :=
  isGradedSemisimpleRing_ringEquiv (𝒜 := superGrading ℬ) (ofSuperInternalZeroEquiv k)
    (fun _ _ => Iff.rfl)
    (isGradedSemisimpleRing_superGrading h)

end Semisimple

end HalfGradedDGRing

end DG

end
