import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.RingTheory.GradedAlgebra.Basic
import DG.Basic

/-!
# Generic helpers for internally graded objects

This file collects generic constructions about objects graded by an additive monoid `ι` in
Mathlib's internal style: a type `M` with a family `ℳ : ι → σ` of subobjects (`σ` a `SetLike`
type with `AddSubmonoidClass σ M`) and a `DirectSum.Decomposition ℳ`. In the rest of the
library `ι = ℤ`.

## Main definitions

* `DG.summand β i`: the `i`-th summand of an external direct sum `⨁ i, β i`, as an
  additive subgroup, together with the `DirectSum.Decomposition` instance exhibiting the external
  direct sum as internally graded by its summands, and the `GradedRing` instance when `β` is a
  `DirectSum.GSemiring`.
* `DG.proj ℳ i : M →+ ℳ i`: the projection onto the degree-`i` homogeneous component.
* `DG.liftHomogeneous ℳ φ : M →+ N`: the extension of a family `φ i : ℳ i →+ N` of additive maps
  on the homogeneous components to all of `M`.
* `DG.decompose_addHom_ext`: two additive maps out of `M` agreeing on homogeneous elements are
  equal.
-/

namespace DG

open DirectSum

/-! ### External direct sums as internally graded objects -/

section Summand

variable {ι : Type*} [DecidableEq ι] (β : ι → Type*) [∀ i, AddCommGroup (β i)]

/-- The `i`-th summand of the external direct sum `⨁ i, β i`, as an additive subgroup: the range
of `DirectSum.of β i`. -/
def summand (i : ι) : AddSubgroup (⨁ i, β i) := (DirectSum.of β i).range

variable {β}

theorem mem_summand {i : ι} {x : ⨁ i, β i} : x ∈ summand β i ↔ ∃ b, DirectSum.of β i b = x :=
  AddMonoidHom.mem_range

theorem of_mem_summand (i : ι) (b : β i) : DirectSum.of β i b ∈ summand β i := ⟨b, rfl⟩

variable (β)

/-- The summand `β i` is isomorphic to its image in the external direct sum. -/
noncomputable def summandEquiv (i : ι) : β i ≃+ summand β i :=
  AddMonoidHom.ofInjective (DirectSum.of_injective i)

@[simp]
theorem coe_summandEquiv_apply (i : ι) (b : β i) :
    (summandEquiv β i b : ⨁ i, β i) = DirectSum.of β i b := rfl

/-- The external direct sum `⨁ i, β i` is internally graded by its summands. -/
noncomputable instance instDecompositionSummand : Decomposition (summand β) :=
  Decomposition.ofAddHom (summand β)
    (DirectSum.toAddMonoid fun i =>
      (DirectSum.of (fun i => summand β i) i).comp (summandEquiv β i).toAddMonoidHom)
    (by ext i b; simp)
    (by
      ext i ⟨x, hx⟩
      obtain ⟨b, rfl⟩ := hx
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, DirectSum.coeAddMonoidHom_of,
        DirectSum.toAddMonoid_of, AddMonoidHom.id_comp]
      rfl)

theorem decompose_summand_of (i : ι) (b : β i) :
    decompose (summand β) (DirectSum.of β i b) = DirectSum.of _ i (summandEquiv β i b) :=
  decompose_of_mem _ (of_mem_summand i b)

section GSemiring

variable [AddMonoid ι] [GSemiring β]

instance instGradedMonoidSummand : SetLike.GradedMonoid (summand β) where
  one_mem := ⟨GradedMonoid.GOne.one, rfl⟩
  mul_mem := by
    rintro i j _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨GradedMonoid.GMul.mul a b, (DirectSum.of_mul_of a b).symm⟩

/-- The external direct sum of a graded semiring is a graded ring with respect to the grading
by its summands. -/
noncomputable instance instGradedRingSummand : GradedRing (summand β) := {}

end GSemiring

section GRing
variable [AddMonoid ι] [GRing β]
noncomputable example : GradedRing (summand β) := inferInstance
end GRing

end Summand

/-! ### Homogeneous components -/

section Decomposition

variable {ι M σ : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike σ M] [AddSubmonoidClass σ M]
variable (ℳ : ι → σ) [Decomposition ℳ]

/-- The projection of a graded object onto its degree-`i` homogeneous component. -/
def proj (i : ι) : M →+ ℳ i where
  toFun m := decompose ℳ m i
  map_zero' := by simp
  map_add' _ _ := by simp

@[simp]
theorem proj_apply (i : ι) (m : M) : proj ℳ i m = decompose ℳ m i := rfl

@[simp]
theorem proj_coe {i : ι} (m : ℳ i) : proj ℳ i m = m := by
  simp [proj_apply]

theorem proj_of_mem_same {i : ι} {m : M} (h : m ∈ ℳ i) : proj ℳ i m = ⟨m, h⟩ :=
  proj_coe ℳ ⟨m, h⟩

theorem coe_proj_of_mem_same {i : ι} {m : M} (h : m ∈ ℳ i) : (proj ℳ i m : M) = m :=
  decompose_of_mem_same ℳ h

theorem coe_proj_of_mem_ne {i j : ι} {m : M} (h : m ∈ ℳ i) (hij : i ≠ j) :
    (proj ℳ j m : M) = 0 :=
  decompose_of_mem_ne ℳ h hij

theorem proj_of_mem_ne {i j : ι} {m : M} (h : m ∈ ℳ i) (hij : i ≠ j) : proj ℳ j m = 0 :=
  Subtype.ext (coe_proj_of_mem_ne ℳ h hij)

theorem proj_coe_of_ne {i j : ι} (m : ℳ i) (hij : i ≠ j) : proj ℳ j m = 0 :=
  proj_of_mem_ne ℳ m.2 hij

variable {N : Type*} [AddCommMonoid N]

/-- Two additive maps out of a graded object which agree on homogeneous elements are equal. -/
theorem decompose_addHom_ext ⦃f g : M →+ N⦄ (h : ∀ (i : ι) (m : ℳ i), f m = g m) : f = g :=
  AddMonoidHom.ext fun m =>
    Decomposition.inductionOn ℳ (by simp) (fun m => h _ m)
      (fun a b ha hb => by simp [ha, hb]) m

/-- The additive map `M →+ N` obtained by extending a family of additive maps `ℳ i →+ N` on the
homogeneous components. -/
def liftHomogeneous (φ : ∀ i, ℳ i →+ N) : M →+ N :=
  (DirectSum.toAddMonoid φ).comp (decomposeAddEquiv ℳ).toAddMonoidHom

@[simp]
theorem liftHomogeneous_coe (φ : ∀ i, ℳ i →+ N) {i : ι} (m : ℳ i) :
    liftHomogeneous ℳ φ m = φ i m := by
  simp [liftHomogeneous]

theorem liftHomogeneous_of_mem (φ : ∀ i, ℳ i →+ N) {i : ι} {m : M} (h : m ∈ ℳ i) :
    liftHomogeneous ℳ φ m = φ i ⟨m, h⟩ :=
  liftHomogeneous_coe ℳ φ ⟨m, h⟩

theorem liftHomogeneous_apply (φ : ∀ i, ℳ i →+ N) (m : M) :
    liftHomogeneous ℳ φ m = DirectSum.toAddMonoid φ (decompose ℳ m) := rfl

/-- Extending the restrictions of an additive map to the homogeneous components recovers it. -/
@[simp]
theorem liftHomogeneous_comp_subtype (f : M →+ N) :
    liftHomogeneous ℳ (fun i => f.comp (AddSubmonoidClass.subtype (ℳ i))) = f :=
  decompose_addHom_ext ℳ fun _ _ => by simp

theorem liftHomogeneous_comp_subtype' (φ : ∀ i, ℳ i →+ N) (i : ι) :
    (liftHomogeneous ℳ φ).comp (AddSubmonoidClass.subtype (ℳ i)) = φ i :=
  AddMonoidHom.ext fun _ => by simp

/-- Additive maps out of a graded object are the same as families of additive maps on its
homogeneous components. -/
def liftHomogeneousEquiv : (∀ i, ℳ i →+ N) ≃+ (M →+ N) where
  toFun := liftHomogeneous ℳ
  invFun f i := f.comp (AddSubmonoidClass.subtype (ℳ i))
  left_inv φ := funext fun i => liftHomogeneous_comp_subtype' ℳ φ i
  right_inv := liftHomogeneous_comp_subtype ℳ
  map_add' φ ψ := decompose_addHom_ext ℳ fun _ _ => by simp

end Decomposition

end DG
