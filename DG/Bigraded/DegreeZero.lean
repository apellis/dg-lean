import DG.Bigraded.Schnurer

/-!
# The degree-`0` part of a graded positive bigraded dg ring

Let `A` be a bigraded dg ring which is graded positive (`DG.IsGradedPositive A`: `Aⁿ = 0` for
`n < 0`, `d (A⁰) = 0`, and `A⁰` graded semisimple). Its degree-`0` part `A⁰ = ⨁ k, A^{0,k}` is a
bigraded dg ring concentrated in cohomological degree `0`, with zero differential and weight
grading `A⁰⟨k⟩ = A^{0,k}`. This file constructs it and the two morphisms of bigraded dg rings
relating it to `A`, and the induced dg functors between the weight dg categories.

## Main definitions

* `DG.DGSubring.internalGradingOfIsHomogeneous`: a dg subring stable under the weight
  decomposition is a bigraded dg ring (`DG.DGSubring.bigradedDGRingOfIsHomogeneous`).
* `DG.IsGradedPositive.degreeZeroDGSubring`: `A⁰` as a dg subring of `A`, with instances
  `DG.InternalGrading` and `DG.BigradedDGRing`.
* `DG.IsGradedPositive.projZero : A →ᵈᵍ+* A⁰`, `a ↦ a₀`, a retraction of the inclusion
  (`DG.IsGradedPositive.projZero_comp_subtype`); both preserve the weights.
* `DG.WeightCategory.mapFunctor φ hφ : C_A ⥤ C_B`, the dg functor induced by a morphism of dg
  rings `φ : A → B` preserving the weight gradings (the identity on objects).
* `DG.IsGradedPositive.isGradedPositive_degreeZeroDGSubring`: `A⁰` is graded positive.
-/

open CategoryTheory DirectSum

universe u

noncomputable section

namespace DG

/-! ### Graded semisimplicity is invariant under graded ring isomorphisms -/

section GradedRingEquiv

variable {ι : Type*} [AddCommGroup ι] [DecidableEq ι] {R S : Type*} [Ring R] [Ring S]
  {𝒜 : ι → AddSubgroup R} [GradedRing 𝒜]
  {𝒮 : ι → AddSubgroup S} [GradedRing 𝒮] (φ : R ≃+* S) (hφ : ∀ i x, φ x ∈ 𝒮 i ↔ x ∈ 𝒜 i)
include hφ

omit [DecidableEq ι] [GradedRing 𝒜] [GradedRing 𝒮] in
theorem isGradedSimpleIdempotent_ringEquiv {e : R} (he : IsGradedSimpleIdempotent 𝒜 e) :
    IsGradedSimpleIdempotent 𝒮 (φ e) := by
  refine ⟨fun h => he.1 (φ.injective (by rw [h, map_zero])), fun j h hh hhe hh0 => ?_⟩
  have hh' : φ.symm h ∈ 𝒜 j := (hφ j _).mp (by rwa [RingEquiv.apply_symm_apply])
  obtain ⟨g, hg, hgh⟩ := he.2 hh' (φ.injective (by
    rw [map_mul, RingEquiv.apply_symm_apply, hhe])) (fun h0 => hh0 (by
      rw [← φ.apply_symm_apply h, h0, map_zero]))
  refine ⟨φ g, (hφ _ _).mpr hg, ?_⟩
  rw [← hgh, map_mul, RingEquiv.apply_symm_apply]

/-- A graded ring isomorphic to a graded semisimple ring is graded semisimple. -/
theorem isGradedSemisimpleRing_ringEquiv (h : IsGradedSemisimpleRing 𝒜) :
    IsGradedSemisimpleRing 𝒮 := by
  obtain ⟨l, hl, hlp, hsum⟩ := h.exists_list_sum_eq_one
  refine isGradedSemisimpleRing_iff_exists_list.mpr ⟨l.map φ, fun e he => ?_, ?_, ?_⟩
  · obtain ⟨e, he', rfl⟩ := List.mem_map.mp he
    obtain ⟨h0, hI, hs⟩ := hl e he'
    exact ⟨(hφ _ _).mpr h0, hI.map φ, isGradedSimpleIdempotent_ringEquiv φ hφ hs⟩
  · rw [List.pairwise_map]
    exact hlp.imp fun h => ⟨by rw [← map_mul, h.1, map_zero], by rw [← map_mul, h.2, map_zero]⟩
  · rw [← map_list_sum, hsum, map_one]

end GradedRingEquiv

/-! ### Weight-homogeneous dg subrings -/

namespace DGSubring

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [InternalGrading A]
  (S : DGSubring A) (hS : ∀ (k : ℤ) {a : A}, a ∈ S → (decompose (wgrading (M := A)) a k : A) ∈ S)

/-- The weight components `S⟨k⟩ = S ∩ A⟨k⟩` of a dg subring. -/
def wgradingOf (k : ℤ) : AddSubgroup S :=
  (wgrading (M := A) k).comap (AddSubgroupClass.subtype S)

include hS in
theorem isInternal_wgradingOf : DirectSum.IsInternal S.wgradingOf :=
  isInternal_comap _ _ Subtype.val_injective fun k a => ⟨⟨_, hS k a.2⟩, rfl⟩

/-- A dg subring stable under the weight decomposition inherits the internal grading:
`S⟨k⟩ = S ∩ A⟨k⟩`. -/
@[instance_reducible]
def internalGradingOfIsHomogeneous : InternalGrading S :=
  letI : Decomposition S.wgradingOf := (S.isInternal_wgradingOf hS).chooseDecomposition
  { wgrading := S.wgradingOf
    isHomogeneous_grading' := fun n k a ha => by
      let : Decomposition fun i => (wgrading (M := A) i).comap (AddSubgroupClass.subtype S) :=
        (S.isInternal_wgradingOf hS).chooseDecomposition
      rw [mem_grading_iff]
      rw [show ((decompose S.wgradingOf a k : S) : A) =
          decompose (wgrading (M := A)) (a : A) k from
        coe_decompose_comap (wgrading (M := A)) (AddSubgroupClass.subtype S) a k]
      exact decompose_wgrading_mem_grading ((mem_grading_iff S).mp ha) k
    d_mem_wgrading' := fun {_ a} ha => d_mem_wgrading (M := A) (m := (a : A)) ha }

theorem mem_wgrading_iff {k : ℤ} {a : S} :
    letI := S.internalGradingOfIsHomogeneous hS
    a ∈ wgrading k ↔ (a : A) ∈ wgrading k :=
  Iff.rfl

/-- A weight-homogeneous dg subring of a bigraded dg ring is a bigraded dg ring. -/
theorem bigradedDGRingOfIsHomogeneous [BigradedDGRing A] :
    letI := S.internalGradingOfIsHomogeneous hS
    BigradedDGRing S :=
  letI := S.internalGradingOfIsHomogeneous hS
  { one_mem := (S.mem_wgrading_iff hS).mpr one_mem_wgrading
    mul_mem := fun _ _ _ _ ha hb =>
      (S.mem_wgrading_iff hS).mpr (mul_mem_wgrading (A := A) ha hb) }

end DGSubring

/-! ### The weight functor of a morphism of bigraded dg rings -/

namespace WeightCategory

variable {A : Type u} [Ring A] [DGAddCommGroup A] [InternalGrading A] [BigradedDGRing A]
  [DGRing A] {B : Type u} [Ring B] [DGAddCommGroup B] [InternalGrading B] [BigradedDGRing B]
  [DGRing B] (φ : A →ᵈᵍ+* B) (hφ : ∀ {k : ℤ} {a : A}, a ∈ wgrading k → φ a ∈ wgrading k)

/-- The dg functor `C_A ⥤ C_B` induced by a morphism of dg rings preserving the weights: the
identity on objects and `φ` on the Hom complexes `A⟨l - k⟩ → B⟨l - k⟩`. -/
@[simps obj]
def mapFunctor : WeightCategory A ⥤ WeightCategory B where
  obj k := ⟨k.as⟩
  map f := ⟨φ f.1, hφ f.2⟩
  map_id _ := hom_ext (map_one φ)
  map_comp _ _ := hom_ext (map_mul φ _ _)

omit [DGRing A] [DGRing B] in
@[simp]
theorem mapFunctor_map_val {k l : WeightCategory A} (f : k ⟶ l) :
    ((mapFunctor φ hφ).map f).1 = φ f.1 :=
  rfl

instance : (mapFunctor φ hφ).Additive where
  map_add := hom_ext (map_add φ _ _)

instance : (mapFunctor φ hφ).IsDGFunctor where
  map_mem' hf := φ.map_mem hf
  map_d' f := hom_ext (φ.map_d f.1)

end WeightCategory

/-! ### The degree-`0` part of a graded positive bigraded dg ring -/

namespace IsGradedPositive

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [InternalGrading A]
  [BigradedDGRing A] (hA : IsGradedPositive A)
include hA

/-- The degree-`0` part `A⁰` of a graded positive bigraded dg ring, as a dg subring. It is
concentrated in degree `0` with zero differential. -/
def degreeZeroDGSubring : DGSubring A where
  __ := degreeZeroSubring A
  isHomogeneous' n a ha := by
    by_cases hn : n = 0
    · subst hn
      exact (decompose (grading (M := A)) a 0).2
    · rw [decompose_of_mem_ne _ ha (Ne.symm hn)]
      exact zero_mem (degreeZeroSubring A)
  d_mem' {a} ha := by
    rw [hA.d_eq_zero_of_mem_zero a ha]
    exact zero_mem (degreeZeroSubring A)

@[simp]
theorem mem_degreeZeroDGSubring {a : A} :
    a ∈ hA.degreeZeroDGSubring ↔ a ∈ grading (M := A) 0 :=
  Iff.rfl

theorem decompose_wgrading_mem_degreeZeroDGSubring (k : ℤ) {a : A}
    (ha : a ∈ hA.degreeZeroDGSubring) :
    (decompose (wgrading (M := A)) a k : A) ∈ hA.degreeZeroDGSubring :=
  decompose_wgrading_mem_grading ha k

/-- The weight grading of `A⁰`: `A⁰⟨k⟩ = A^{0,k}`. -/
instance : InternalGrading hA.degreeZeroDGSubring :=
  hA.degreeZeroDGSubring.internalGradingOfIsHomogeneous
    hA.decompose_wgrading_mem_degreeZeroDGSubring

/-- `A⁰` is a bigraded dg ring. -/
instance : BigradedDGRing hA.degreeZeroDGSubring :=
  hA.degreeZeroDGSubring.bigradedDGRingOfIsHomogeneous
    hA.decompose_wgrading_mem_degreeZeroDGSubring

theorem mem_wgrading_degreeZeroDGSubring_iff {k : ℤ} {a : hA.degreeZeroDGSubring} :
    a ∈ wgrading k ↔ (a : A) ∈ wgrading k :=
  Iff.rfl

theorem d_degreeZeroDGSubring (x : hA.degreeZeroDGSubring) : d x = 0 :=
  Subtype.ext (by rw [DGSubring.coe_d, hA.d_eq_zero_of_mem_zero _ x.2, ZeroMemClass.coe_zero])

theorem eq_zero_of_mem_grading_degreeZeroDGSubring {n : ℤ} (hn : n ≠ 0)
    {x : hA.degreeZeroDGSubring} (hx : x ∈ grading n) : x = 0 := by
  rw [DGSubring.mem_grading_iff] at hx
  have h := decompose_of_mem_same (grading (M := A)) hx
  rw [decompose_of_mem_ne _ x.2 (Ne.symm hn)] at h
  exact Subtype.ext h.symm

theorem decompose_d_zero (a : A) : decompose (grading (M := A)) (d a) 0 = 0 := by
  apply Subtype.ext
  have h := decompose_d a (-1)
  rw [neg_add_cancel] at h
  have h0 : ∀ y ∈ grading (M := A) (-1), y = 0 := fun y hy => by
    rwa [hA.grading_eq_bot _ (by omega), AddSubgroup.mem_bot] at hy
  rw [h, h0 _ (decompose (grading (M := A)) a (-1)).2, d_zero, ZeroMemClass.coe_zero]

/-- The projection `A → A⁰`, `a ↦ a₀`, onto the degree-`0` component, as a morphism of dg rings.
It is multiplicative because `A` is non-negatively graded, and commutes with `d` because
`A⁻¹ = 0` and `d (A⁰) = 0`. -/
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
    rw [hA.decompose_d_zero, hA.d_eq_zero_of_mem_zero _ (decompose (grading (M := A)) a 0).2,
      ZeroMemClass.coe_zero]

@[simp]
theorem coe_projZero_apply (a : A) :
    (hA.projZero a : A) = decompose (grading (M := A)) a 0 :=
  rfl

theorem projZero_apply_of_mem_zero {a : A} (ha : a ∈ grading 0) : (hA.projZero a : A) = a :=
  decompose_of_mem_same _ ha

/-- The projection `A → A⁰` is a retraction of the inclusion `A⁰ → A`. -/
theorem projZero_comp_subtype :
    hA.projZero.comp (DGSubring.subtype hA.degreeZeroDGSubring) = DGRingHom.id :=
  DGRingHom.ext fun x => Subtype.ext (hA.projZero_apply_of_mem_zero x.2)

/-- The projection `A → A⁰` preserves the weights. -/
theorem projZero_mem_wgrading {k : ℤ} {a : A} (ha : a ∈ wgrading k) :
    hA.projZero a ∈ wgrading k :=
  decompose_grading_mem_wgrading ha 0

/-- The inclusion `A⁰ → A` preserves the weights. -/
theorem subtype_mem_wgrading {k : ℤ} {a : hA.degreeZeroDGSubring} (ha : a ∈ wgrading k) :
    DGSubring.subtype hA.degreeZeroDGSubring a ∈ wgrading k :=
  ha

/-- The dg functor `C_A ⥤ C_{A⁰}` induced by the projection `A → A⁰`. -/
abbrev projFunctor : WeightCategory A ⥤ WeightCategory hA.degreeZeroDGSubring :=
  WeightCategory.mapFunctor hA.projZero hA.projZero_mem_wgrading

/-- The dg functor `C_{A⁰} ⥤ C_A` induced by the inclusion `A⁰ → A`. -/
abbrev inclFunctor : WeightCategory hA.degreeZeroDGSubring ⥤ WeightCategory A :=
  WeightCategory.mapFunctor (DGSubring.subtype hA.degreeZeroDGSubring) hA.subtype_mem_wgrading

/-- `C_{A⁰} ⥤ C_A ⥤ C_{A⁰}` is the identity. -/
theorem inclFunctor_comp_projFunctor : hA.inclFunctor ⋙ hA.projFunctor = 𝟭 _ :=
  CategoryTheory.Functor.hext (fun _ => rfl) fun _ _ f => heq_of_eq
    (WeightCategory.hom_ext (Subtype.ext (hA.projZero_apply_of_mem_zero f.1.2)))

/-- The ring isomorphism `(A)⁰ ≃ (A⁰)⁰` between the degree-`0` parts of `A` and of `A⁰`. -/
def degreeZeroRingEquiv : degreeZeroSubring A ≃+* degreeZeroSubring hA.degreeZeroDGSubring where
  toFun a := ⟨⟨a.1, a.2⟩, mem_degreeZeroSubring.mpr a.2⟩
  invFun x := ⟨x.1.1, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- `A⁰`, concentrated in degree `0`, is graded positive. -/
theorem isGradedPositive_degreeZeroDGSubring : IsGradedPositive hA.degreeZeroDGSubring where
  grading_eq_bot n hn := eq_bot_iff.mpr fun x hx =>
    (AddSubgroup.mem_bot).mpr (hA.eq_zero_of_mem_grading_degreeZeroDGSubring (by omega) hx)
  isGradedSemisimple := isGradedSemisimpleRing_ringEquiv hA.degreeZeroRingEquiv
    (fun _ _ => Iff.rfl) hA.isGradedSemisimple
  d_eq_zero_of_mem_zero a _ := hA.d_degreeZeroDGSubring a

end IsGradedPositive

end DG

end
