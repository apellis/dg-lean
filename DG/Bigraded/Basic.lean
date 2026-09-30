import DG.Module.Basic

/-!
# Internal gradings of dg abelian groups, rings and modules

A *bigraded* (or *internally graded*) dg object carries, besides its cohomological
`ℤ`-grading, a second `ℤ`-grading, the *internal* or *weight* grading, which is compatible
with the cohomological one and preserved by the differential. This file sets up this layer on
top of the core definitions of `DG.Algebra.Basic` and `DG.Module.Basic`.

## Design

The split between data and `Prop`-valued mixins follows the core library:

* `DG.InternalGrading M` (data), for a dg abelian group `M`: a weight grading
  `wgrading : ℤ → AddSubgroup M` which is an internal direct sum (a `DirectSum.Decomposition`),
  compatible with the cohomological grading (the weight projections preserve every `Mⁿ`,
  `DG.isHomogeneous_grading`) and preserved by the differential, `d (M⟨k⟩) ⊆ M⟨k⟩`
  (`DG.d_mem_wgrading`). The compatibilities belong to the structure in the same way as
  `d_mem'` belongs to `DG.DGAddCommGroup`.
* `DG.BigradedDGRing A` (`Prop`): for a ring `A` with an internal grading, the weight grading
  is a ring grading (`SetLike.GradedMonoid`, hence `GradedRing`).
* `DG.BigradedDGModule A M` (`Prop`): for an `A`-module `M` with an internal grading, the
  action adds weights, `A⟨i⟩ • M⟨j⟩ ⊆ M⟨i + j⟩` (`SetLike.GradedSMul`).

Weights carry **no** Koszul signs: the sign rule of `docs/CONVENTIONS.md` only involves the
cohomological degree. The Leibniz rules of `DG.DGRing` and `DG.DGModule` are unchanged, and no
sign enters the compatibilities above.

## The bigrading

The compatibility of the two gradings says that the projections onto the weight components
preserve each `Mⁿ`; equivalently the projections onto the cohomological components preserve
each `M⟨k⟩` (`DG.isHomogeneous_wgrading`), equivalently the two families of projections commute
(`DG.decompose_wgrading_decompose_grading`), equivalently `M` is the internal direct sum of the
bihomogeneous pieces `M^{n,k} = Mⁿ ∩ M⟨k⟩`. The last equivalence is
`DG.isInternal_inf_iff`, stated for any two decompositions; for an internal grading this gives
the `ℤ × ℤ`-grading `DG.bigrading M` with its decomposition (`DG.isInternal_bigrading`). For a
bigraded dg ring the bigrading is a ring grading (`DG.bigrading.gradedMonoid`), and for a
bigraded dg module the action is graded for it (`DG.bigrading.gradedSMul`).

## Main declarations

* `DG.isInternal_inf_iff`, `DG.InternalGrading`, `DG.wgrading`, `DG.bigrading`,
  `DG.isInternal_bigrading`, `DG.BigradedDGRing`, `DG.BigradedDGModule`.
* `DG.isInternal_comap`, `DG.coe_decompose_comap`: a decomposition restricts to a subgroup (or
  along an injective map) whose image is closed under the homogeneous projections; used for the
  weight gradings of cocycles, of cohomology and of `A⁰`.
* `DirectSum.Decomposition.coe_decompose_reindex`: the components of a reindexed decomposition.
-/

open DirectSum

namespace DirectSum.Decomposition

variable {ι κ M σ : Type*} [DecidableEq ι] [DecidableEq κ] [AddCommMonoid M] [SetLike σ M]
  [AddSubmonoidClass σ M] (ℳ : ι → σ) [Decomposition ℳ] (e : κ ≃ ι)

/-- The components of a decomposition of `M` by `fun k => ℳ (e k)` (for instance the reindexed
decomposition `DirectSum.Decomposition.reindex`) are the components of `ℳ`. -/
theorem coe_decompose_reindex [Decomposition fun k => ℳ (e k)] (m : M) (k : κ) :
    (decompose (fun k => ℳ (e k)) m k : M) = decompose ℳ m (e k) := by
  induction m using Decomposition.inductionOn ℳ with
  | zero => simp
  | homogeneous x =>
    rename_i i
    have hx : (x : M) ∈ (fun k => ℳ (e k)) (e.symm i) := by
      simp only [Equiv.apply_symm_apply]; exact x.2
    by_cases h : e.symm i = k
    · subst h
      rw [decompose_of_mem_same (fun k => ℳ (e k)) hx,
        decompose_of_mem_same ℳ (show (x : M) ∈ ℳ (e (e.symm i)) from hx)]
    · rw [decompose_of_mem_ne (fun k => ℳ (e k)) hx h, decompose_of_mem_ne ℳ x.2]
      rintro rfl
      exact h (e.symm_apply_apply k)
  | add m m' hm hm' => simp only [decompose_add, add_apply, AddMemClass.coe_add, hm, hm']

end DirectSum.Decomposition

namespace DG

/-! ### Two commuting decompositions -/

section Inf

variable {M : Type*} [AddCommGroup M] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
  (ℳ : ι → AddSubgroup M) (𝒩 : κ → AddSubgroup M) [Decomposition ℳ] [Decomposition 𝒩]

/-- For an element `y` of the external direct sum of the `ℳ i ⊓ 𝒩 j`, the `(i, j)` component
of `y` is obtained from its image in `M` by projecting to `ℳ i` and then to `𝒩 j`. -/
theorem decompose_decompose_coeAddMonoidHom_inf
    (y : ⨁ p : ι × κ, (ℳ p.1 ⊓ 𝒩 p.2 : AddSubgroup M)) (p : ι × κ) :
    (decompose 𝒩 (decompose ℳ
      (DirectSum.coeAddMonoidHom (fun p : ι × κ => ℳ p.1 ⊓ 𝒩 p.2) y) p.1 : M) p.2 : M) =
      (y p : M) := by
  induction y using DirectSum.induction_on with
  | zero => simp
  | of q x =>
    rw [DirectSum.coeAddMonoidHom_of]
    obtain ⟨x, hx₁, hx₂⟩ := x
    by_cases h : q = p
    · subst h
      rw [of_eq_same, decompose_of_mem_same ℳ hx₁, decompose_of_mem_same 𝒩 hx₂]
    · rw [of_eq_of_ne _ _ _ (Ne.symm h), ZeroMemClass.coe_zero]
      by_cases h₁ : q.1 = p.1
      · have h₂ : q.2 ≠ p.2 := fun h₂ => h (Prod.ext h₁ h₂)
        rw [← h₁, decompose_of_mem_same ℳ hx₁, decompose_of_mem_ne 𝒩 hx₂ h₂]
      · rw [decompose_of_mem_ne ℳ hx₁ h₁]
        simp
  | add y y' hy hy' =>
    simp only [map_add, decompose_add, add_apply, AddSubgroup.coe_add, hy, hy']

/-- Two decompositions `M = ⨁ i, ℳ i` and `M = ⨁ j, 𝒩 j` commute (the projections onto the
`𝒩 j` preserve every `ℳ i`) if and only if `M` is the internal direct sum of the intersections
`ℳ i ⊓ 𝒩 j`, i.e. `(i, j) ↦ ℳ i ⊓ 𝒩 j` is an `ι × κ`-grading of `M`. -/
theorem isInternal_inf_iff :
    DirectSum.IsInternal (fun p : ι × κ => ℳ p.1 ⊓ 𝒩 p.2) ↔
      ∀ i, SetLike.IsHomogeneous 𝒩 (ℳ i) := by
  constructor
  · intro h i j m hm
    obtain ⟨y, rfl⟩ := h.2 m
    have key := decompose_decompose_coeAddMonoidHom_inf ℳ 𝒩 y (i, j)
    rw [decompose_of_mem_same _ hm] at key
    rw [key]
    exact (y (i, j)).2.1
  · intro h
    refine ⟨(injective_iff_map_eq_zero _).mpr fun y hy => ?_, fun m => ?_⟩
    · ext p
      rw [← decompose_decompose_coeAddMonoidHom_inf ℳ 𝒩 y p, hy]
      simp
    · classical
      suffices hm : m ∈ (DirectSum.coeAddMonoidHom (fun p : ι × κ => ℳ p.1 ⊓ 𝒩 p.2)).range from
        hm
      induction m using Decomposition.inductionOn ℳ with
      | zero => exact zero_mem _
      | homogeneous x =>
        rename_i i
        rw [← DirectSum.sum_support_decompose 𝒩 (x : M)]
        refine sum_mem fun j _ => ⟨DirectSum.of (fun p : ι × κ => (ℳ p.1 ⊓ 𝒩 p.2 : AddSubgroup M))
          (i, j) ⟨_, h i j x.2, (decompose 𝒩 (x : M) j).2⟩, ?_⟩
        rw [DirectSum.coeAddMonoidHom_of]
      | add m m' hm hm' => exact add_mem hm hm'

end Inf

/-! ### Restricting a decomposition along an injective map -/

section Comap

variable {M : Type*} [AddCommGroup M] {ι : Type*} [DecidableEq ι] (ℳ : ι → AddSubgroup M)
  [Decomposition ℳ] {T : Type*} [AddCommGroup T] (f : T →+ M)

set_option backward.isDefEq.respectTransparency false in
theorem isInternal_comap (hf : Function.Injective f)
    (hhom : ∀ (i : ι) (t : T), (decompose ℳ (f t) i : M) ∈ f.range) :
    DirectSum.IsInternal fun i => (ℳ i).comap f := by
  classical
  let r : (⨁ i, (ℳ i).comap f) →+ ⨁ i, ℳ i :=
    DirectSum.map fun i => (f.domRestrict ((ℳ i).comap f)).codRestrict (ℳ i) fun t => t.2
  have key : ∀ x, DirectSum.coeAddMonoidHom ℳ (r x) =
      f (DirectSum.coeAddMonoidHom (fun i => (ℳ i).comap f) x) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i t => simp [r]
    | add x y hx hy => simp only [map_add, hx, hy]
  constructor
  · intro x y hxy
    have h : r x = r y := (Decomposition.isInternal ℳ).injective (by rw [key, key, hxy])
    rw [DirectSum.map_eq_iff] at h
    ext i
    exact hf (by simpa using h i)
  · intro t
    choose s hs using fun i => hhom i t
    refine ⟨∑ i ∈ (decompose ℳ (f t)).support,
      DirectSum.of (fun i => (ℳ i).comap f) i ⟨s i, ?_⟩, ?_⟩
    · rw [AddSubgroup.mem_comap, hs]; exact Subtype.property _
    · apply hf
      simp only [map_sum, DirectSum.coeAddMonoidHom_of]
      conv_rhs => rw [← DirectSum.sum_support_decompose ℳ (f t)]
      exact Finset.sum_congr rfl fun i _ => hs i

/-- The components of an element for a decomposition pulled back along an injective map are
the pullbacks of its components. -/
theorem coe_decompose_comap [Decomposition fun i => (ℳ i).comap f] (t : T) (i : ι) :
    f (decompose (fun i => (ℳ i).comap f) t i) = decompose ℳ (f t) i := by
  induction t using Decomposition.inductionOn (fun i => (ℳ i).comap f) with
  | zero => simp
  | homogeneous x =>
    rename_i j
    by_cases h : j = i
    · subst h
      rw [decompose_of_mem_same (fun i => (ℳ i).comap f) x.2,
        decompose_of_mem_same ℳ (show f x ∈ ℳ j from x.2)]
    · rw [decompose_of_mem_ne (fun i => (ℳ i).comap f) x.2 h,
        decompose_of_mem_ne ℳ (show f x ∈ ℳ j from x.2) h, map_zero]
  | add t t' ht ht' => simp only [decompose_add, add_apply, AddSubgroup.coe_add, map_add, ht, ht']

end Comap

/-! ### Internal gradings -/

/-- An internal (or weight) grading of a dg abelian group `M`: a second `ℤ`-grading
`M = ⨁ k, wgrading k` such that the projections onto the weight components preserve every
cohomological component `Mⁿ`, and such that `d (M⟨k⟩) ⊆ M⟨k⟩`. Equivalently, `M` is
`ℤ × ℤ`-graded by `Mⁿ ∩ M⟨k⟩` (`DG.isInternal_bigrading`) and `d` has bidegree `(1, 0)`.
No Koszul sign is attached to weights. -/
class InternalGrading (M : Type*) [AddCommGroup M] [DGAddCommGroup M] where
  /-- The weight components `M⟨k⟩`. -/
  wgrading : ℤ → AddSubgroup M
  /-- The weight grading is an internal direct sum decomposition. -/
  [wdecomposition : DirectSum.Decomposition wgrading]
  isHomogeneous_grading' : ∀ n : ℤ, SetLike.IsHomogeneous wgrading (grading (M := M) n)
  d_mem_wgrading' : ∀ {k : ℤ} {m : M}, m ∈ wgrading k → d m ∈ wgrading k

attribute [instance_reducible, instance] InternalGrading.wdecomposition

/-- An internal grading from a weight decomposition `𝒩` such that `(n, k) ↦ Mⁿ ∩ 𝒩 k` is a
decomposition of `M` (a `ℤ × ℤ`-grading) and `d (𝒩 k) ⊆ 𝒩 k`. By `DG.isInternal_inf_iff`, the
first condition is equivalent to the compatibility required in `DG.InternalGrading`. -/
@[instance_reducible]
def InternalGrading.ofIsInternal {M : Type*} [AddCommGroup M] [DGAddCommGroup M]
    (𝒩 : ℤ → AddSubgroup M) [Decomposition 𝒩]
    (h : DirectSum.IsInternal fun p : ℤ × ℤ => grading (M := M) p.1 ⊓ 𝒩 p.2)
    (hd : ∀ {k : ℤ} {m : M}, m ∈ 𝒩 k → d m ∈ 𝒩 k) : InternalGrading M where
  wgrading := 𝒩
  isHomogeneous_grading' := (isInternal_inf_iff _ _).mp h
  d_mem_wgrading' := hd

export InternalGrading (wgrading)

section InternalGrading

variable {M : Type*} [AddCommGroup M] [DGAddCommGroup M] [InternalGrading M]

variable (M) in
/-- The cohomological components are homogeneous for the weight grading. -/
theorem isHomogeneous_grading (n : ℤ) : SetLike.IsHomogeneous (wgrading (M := M)) (grading n) :=
  InternalGrading.isHomogeneous_grading' n

theorem decompose_wgrading_mem_grading {n : ℤ} {m : M} (hm : m ∈ grading n) (k : ℤ) :
    (decompose (wgrading (M := M)) m k : M) ∈ grading n :=
  isHomogeneous_grading M n k hm

theorem d_mem_wgrading {k : ℤ} {m : M} (hm : m ∈ wgrading k) : d m ∈ wgrading k :=
  InternalGrading.d_mem_wgrading' hm

/-- The weight projections and the cohomological projections commute. -/
theorem decompose_wgrading_decompose_grading (m : M) (n k : ℤ) :
    (decompose (wgrading (M := M)) (decompose (grading (M := M)) m n : M) k : M) =
      decompose (grading (M := M)) (decompose (wgrading (M := M)) m k : M) n := by
  induction m using induction_on with
  | h_zero => simp
  | h_homogeneous x =>
    rename_i i
    have hx := decompose_wgrading_mem_grading x.2 k
    by_cases h : i = n
    · subst h
      rw [decompose_of_mem_same _ x.2, decompose_of_mem_same _ hx]
    · rw [decompose_of_mem_ne _ x.2 h, decompose_of_mem_ne _ hx h]
      simp
  | h_add m m' hm hm' =>
    simp only [decompose_add, add_apply, AddSubgroup.coe_add, hm, hm']

variable (M) in
/-- The weight components are homogeneous for the cohomological grading. -/
theorem isHomogeneous_wgrading (k : ℤ) : SetLike.IsHomogeneous (grading (M := M)) (wgrading k) := by
  intro n m hm
  rw [← decompose_of_mem_same _ hm, ← decompose_wgrading_decompose_grading]
  exact (decompose (wgrading (M := M)) _ k).2

theorem decompose_grading_mem_wgrading {k : ℤ} {m : M} (hm : m ∈ wgrading k) (n : ℤ) :
    (decompose (grading (M := M)) m n : M) ∈ wgrading k :=
  isHomogeneous_wgrading M k n hm

/-- The differential commutes with the weight projections. -/
theorem decompose_wgrading_d (m : M) (k : ℤ) :
    (decompose (wgrading (M := M)) (d m) k : M) = d (decompose (wgrading (M := M)) m k : M) := by
  induction m using Decomposition.inductionOn (wgrading (M := M)) with
  | zero => simp
  | homogeneous x =>
    rename_i j
    by_cases h : j = k
    · subst h
      rw [decompose_of_mem_same _ x.2, decompose_of_mem_same _ (d_mem_wgrading x.2)]
    · rw [decompose_of_mem_ne _ x.2 h, decompose_of_mem_ne _ (d_mem_wgrading x.2) h, d_zero]
  | add m m' hm hm' => simp only [d_add, decompose_add, add_apply, AddSubgroup.coe_add, hm, hm']

/-- The kernel of `d` is homogeneous for the weight grading. -/
theorem isHomogeneous_wgrading_ker_d :
    SetLike.IsHomogeneous (wgrading (M := M)) (d : M →+ M).ker := by
  intro k m hm
  rw [AddMonoidHom.mem_ker] at hm ⊢
  rw [← decompose_wgrading_d, hm, decompose_zero, zero_apply, ZeroMemClass.coe_zero]

/-- The cocycles `Zⁿ(M)` are homogeneous for the weight grading. -/
theorem isHomogeneous_wgrading_cocycles (n : ℤ) :
    SetLike.IsHomogeneous (wgrading (M := M)) (cocycles M n) :=
  fun k _ hm => ⟨decompose_wgrading_mem_grading hm.1 k, isHomogeneous_wgrading_ker_d k hm.2⟩

/-- The coboundaries `Bⁿ(M)` are homogeneous for the weight grading. -/
theorem isHomogeneous_wgrading_coboundaries (n : ℤ) :
    SetLike.IsHomogeneous (wgrading (M := M)) (coboundaries M n) := by
  rintro k _ ⟨m, hm, rfl⟩
  exact ⟨_, decompose_wgrading_mem_grading hm k, (decompose_wgrading_d m k).symm⟩

variable (M) in
/-- The bigrading `(n, k) ↦ Mⁿ ∩ M⟨k⟩` of a dg abelian group with an internal grading. -/
def bigrading (p : ℤ × ℤ) : AddSubgroup M :=
  grading (M := M) p.1 ⊓ wgrading (M := M) p.2

theorem mem_bigrading {p : ℤ × ℤ} {m : M} :
    m ∈ bigrading M p ↔ m ∈ grading p.1 ∧ m ∈ wgrading p.2 :=
  AddSubgroup.mem_inf

variable (M) in
/-- `M` is the internal direct sum of its bihomogeneous components `Mⁿ ∩ M⟨k⟩`. -/
theorem isInternal_bigrading : DirectSum.IsInternal (bigrading M) :=
  (isInternal_inf_iff (grading (M := M)) (wgrading (M := M))).mpr (isHomogeneous_grading M)

/-- The decomposition `M = ⨁ (n, k), Mⁿ ∩ M⟨k⟩`. -/
noncomputable instance bigrading.decomposition : DirectSum.Decomposition (bigrading M) :=
  (isInternal_bigrading M).chooseDecomposition

/-- The bihomogeneous components are obtained by projecting to the cohomological and then to the
weight components. -/
theorem coe_decompose_bigrading (m : M) (p : ℤ × ℤ) :
    (decompose (bigrading M) m p : M) =
      decompose (wgrading (M := M)) (decompose (grading (M := M)) m p.1 : M) p.2 := by
  have h := decompose_decompose_coeAddMonoidHom_inf (grading (M := M)) (wgrading (M := M))
    (decompose (bigrading M) m) p
  have hm : DirectSum.coeAddMonoidHom (fun p : ℤ × ℤ => grading (M := M) p.1 ⊓ wgrading p.2)
      (decompose (bigrading M) m) = m :=
    (decompose (bigrading M)).symm_apply_apply m
  rw [hm] at h
  exact h.symm

/-- The differential has bidegree `(1, 0)`. -/
theorem d_mem_bigrading {n k : ℤ} {m : M} (hm : m ∈ bigrading M (n, k)) :
    d m ∈ bigrading M (n + 1, k) :=
  ⟨d_mem hm.1, d_mem_wgrading hm.2⟩

end InternalGrading

/-! ### Bigraded dg rings -/

/-- A bigraded dg ring: a ring `A` with a dg structure and an internal grading, such that the
internal grading is a ring grading (`1 ∈ A⟨0⟩`, `A⟨i⟩ * A⟨j⟩ ⊆ A⟨i + j⟩`). This is a mixin: the
dg ring structure is `DG.DGRing A`. -/
class BigradedDGRing (A : Type*) [Ring A] [DGAddCommGroup A] [InternalGrading A] : Prop
    extends SetLike.GradedMonoid (wgrading (M := A))

section BigradedDGRing

variable {A : Type*} [Ring A] [DGAddCommGroup A] [InternalGrading A] [BigradedDGRing A]

instance BigradedDGRing.toGradedRing : GradedRing (wgrading (M := A)) :=
  { BigradedDGRing.toGradedMonoid (A := A), InternalGrading.wdecomposition (M := A) with }

theorem one_mem_wgrading : (1 : A) ∈ wgrading (M := A) 0 :=
  SetLike.GradedOne.one_mem

theorem mul_mem_wgrading {i j : ℤ} {a b : A} (ha : a ∈ wgrading i) (hb : b ∈ wgrading j) :
    a * b ∈ wgrading (i + j) :=
  SetLike.GradedMul.mul_mem ha hb

variable [DGRing A]

/-- The bigrading of a bigraded dg ring is a ring grading. -/
instance bigrading.gradedMonoid : SetLike.GradedMonoid (bigrading A) where
  one_mem := ⟨one_mem_grading, one_mem_wgrading⟩
  mul_mem _ _ _ _ ha hb := ⟨mul_mem_grading ha.1 hb.1, mul_mem_wgrading ha.2 hb.2⟩

noncomputable instance bigrading.gradedRing : GradedRing (bigrading A) :=
  { bigrading.gradedMonoid (A := A), bigrading.decomposition (M := A) with }

end BigradedDGRing

/-! ### Bigraded dg modules -/

/-- A bigraded dg module over a ring `A` with an internal grading: an `A`-module `M` with a dg
structure and an internal grading such that the action adds weights,
`A⟨i⟩ • M⟨j⟩ ⊆ M⟨i + j⟩`. This is a mixin: the dg module structure is `DG.DGModule A M`. -/
class BigradedDGModule (A : Type*) (M : Type*) [Ring A] [DGAddCommGroup A] [InternalGrading A]
    [AddCommGroup M] [DGAddCommGroup M] [InternalGrading M] [Module A M] : Prop
    extends SetLike.GradedSMul (wgrading (M := A)) (wgrading (M := M))

section BigradedDGModule

variable {A : Type*} {M : Type*} [Ring A] [DGAddCommGroup A] [InternalGrading A]
  [AddCommGroup M] [DGAddCommGroup M] [InternalGrading M] [Module A M] [BigradedDGModule A M]

theorem smul_mem_wgrading {i j : ℤ} {a : A} {m : M} (ha : a ∈ wgrading i)
    (hm : m ∈ wgrading j) : a • m ∈ wgrading (i + j) :=
  SetLike.GradedSMul.smul_mem ha hm

/-- A bigraded dg ring is a bigraded dg module over itself. -/
instance BigradedDGModule.regular [BigradedDGRing A] : BigradedDGModule A A where
  smul_mem _ _ _ _ ha hb := mul_mem_wgrading ha hb

/-- The action on a bigraded dg module is graded for the bigradings. -/
instance bigrading.gradedSMul [DGModule A M] : SetLike.GradedSMul (bigrading A) (bigrading M) where
  smul_mem _ _ _ _ ha hm := ⟨smul_mem_grading ha.1 hm.1, smul_mem_wgrading ha.2 hm.2⟩

end BigradedDGModule

end DG
