import DG.Compact.Basic
import Mathlib.Algebra.FiveLemma
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Compact objects of a pretriangulated category

Let `C` be a pretriangulated category with coproducts indexed by types in the universe `w`.
The compact objects of `C` (`DG.IsCompact.{w}`, see `DG.Compact.Basic`) are closed under
shifts in both directions and under cones: in a distinguished triangle
`X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧`, if two of the three objects are compact, so is the third.
Together with the closure under retracts of `DG.Compact.Basic`, this says that the compact
objects form a thick triangulated subcategory `C^c` of `C`, packaged as
`DG.compactSubcategory C : ObjectProperty C` (with `ObjectProperty.IsTriangulated`); compare
[Ne, Def. 4.2.7 and Lemma 4.2.4] (A. Neeman, *Triangulated categories*, Ann. Math. Studies 148).

## Proofs

* Shifts: the additive bijection `(X⟦n⟧ ⟶ M) ≃+ (X ⟶ M⟦-n⟧)` from the shift equivalence,
  together with the fact that `⟦-n⟧` preserves coproducts, transports the comparison map of
  `X⟦n⟧` for a family `Y` to the comparison map of `X` for the family `Y⟦-n⟧`.
* Cones: for a distinguished triangle `T` and an object `M`, the contravariant Yoneda sequence
  `(X₂⟦1⟧ ⟶ M) → (X₁⟦1⟧ ⟶ M) → (X₃ ⟶ M) → (X₂ ⟶ M) → (X₁ ⟶ M)` is exact
  (`Pretriangulated.Triangle.yoneda_exact₂` and rotations). Taking `M = ∐ Y` and the direct
  sum over `i` of the sequences for `M = Y i` gives a commutative ladder of abelian groups whose
  vertical maps are the comparison maps; the five lemma for abelian groups
  (`AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective`) then shows
  that `X₃` is compact when `X₁` and `X₂` are. The other two cases follow by rotation.
-/

universe w v u

namespace DG

open CategoryTheory Limits Pretriangulated

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ]

section yoneda

variable [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Exactness of `(T.obj₃ ⟶ M) → (T.obj₂ ⟶ M) → (T.obj₁ ⟶ M)` for a distinguished triangle `T`,
as `Function.Exact`. -/
theorem exact_leftComp_of_distTriang (T : Triangle C) (hT : T ∈ distTriang C) (M : C) :
    Function.Exact (Preadditive.leftComp M T.mor₂) (Preadditive.leftComp M T.mor₁) := by
  intro f
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := T.yoneda_exact₂ hT f hf
    exact ⟨g, hg.symm⟩
  · rintro ⟨g, rfl⟩
    change T.mor₁ ≫ T.mor₂ ≫ g = 0
    rw [← Category.assoc, comp_distTriang_mor_zero₁₂ T hT, Limits.zero_comp]

/-- Exactness of `(T.obj₁⟦1⟧ ⟶ M) → (T.obj₃ ⟶ M) → (T.obj₂ ⟶ M)`. -/
theorem exact_leftComp_of_distTriang' (T : Triangle C) (hT : T ∈ distTriang C) (M : C) :
    Function.Exact (Preadditive.leftComp M T.mor₃) (Preadditive.leftComp M T.mor₂) :=
  exact_leftComp_of_distTriang T.rotate (rot_of_distTriang T hT) M

/-- Exactness of `(T.obj₂⟦1⟧ ⟶ M) → (T.obj₁⟦1⟧ ⟶ M) → (T.obj₃ ⟶ M)`. -/
theorem exact_leftComp_of_distTriang'' (T : Triangle C) (hT : T ∈ distTriang C) (M : C) :
    Function.Exact (Preadditive.leftComp M (-T.mor₁⟦(1 : ℤ)⟧')) (Preadditive.leftComp M T.mor₃) :=
  exact_leftComp_of_distTriang T.rotate.rotate (rot_of_distTriang _ (rot_of_distTriang T hT)) M

end yoneda

section shift

variable [∀ n : ℤ, (shiftFunctor C n).Additive] [HasCoproducts.{w} C]

/-- Compact objects are closed under shifts. -/
theorem IsCompact.shift {X : C} (hX : IsCompact.{w} X) (n : ℤ) : IsCompact.{w} (X⟦n⟧) := by
  intro ι _ W _
  let adj : shiftFunctor C n ⊣ shiftFunctor C (-n) := (shiftEquiv C n).toAdjunction
  let W' : ι → C := fun i => (W i)⟦-n⟧
  let sc : ∐ W' ⟶ (∐ W)⟦-n⟧ := sigmaComparison (shiftFunctor C (-n)) W
  let Φ : (DirectSum ι fun i => (X⟦n⟧ ⟶ W i)) →+ DirectSum ι fun i => (X ⟶ W' i) :=
    DirectSum.map fun i => (adj.homAddEquiv X (W i)).toAddMonoidHom
  let ψ : (X⟦n⟧ ⟶ ∐ W) →+ (X ⟶ ∐ W') :=
    (Preadditive.rightComp X (inv sc)).comp (adj.homAddEquiv X (∐ W)).toAddMonoidHom
  have hΦ : Function.Bijective Φ :=
    ⟨(DirectSum.map_injective _).2 fun i => (adj.homAddEquiv X (W i)).injective,
      (DirectSum.map_surjective _).2 fun i => (adj.homAddEquiv X (W i)).surjective⟩
  have hψ : Function.Bijective ψ := by
    change Function.Bijective (fun f => adj.homEquiv X (∐ W) f ≫ inv sc)
    exact ⟨fun f g h => (adj.homEquiv X _).injective ((cancel_mono (inv sc)).1 h),
      fun g => ⟨(adj.homEquiv X _).symm (g ≫ sc), by simp⟩⟩
  have comm : ψ.comp (coproductComparison (X⟦n⟧) W) = (coproductComparison X W').comp Φ := by
    ext i g
    simp only [AddMonoidHom.comp_apply, coproductComparison_of, DirectSum.map_of,
      AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, Adjunction.homAddEquiv_apply, ψ, Φ]
    change adj.homEquiv X (∐ W) (g ≫ Sigma.ι W i) ≫ inv sc = adj.homEquiv X (W i) g ≫ Sigma.ι W' i
    rw [Adjunction.homEquiv_naturality_right, Category.assoc]
    congr 1
    rw [← ι_comp_sigmaComparison, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hcomp : ψ ∘ coproductComparison (X⟦n⟧) W = coproductComparison X W' ∘ Φ := by
    rw [← AddMonoidHom.coe_comp, ← AddMonoidHom.coe_comp, comm]
  have : Function.Bijective (ψ ∘ coproductComparison (X⟦n⟧) W) := by
    rw [hcomp]
    exact (hX ι W').comp hΦ
  exact (Function.Bijective.of_comp_iff' hψ _).1 this

theorem isCompact_shift_iff (X : C) (n : ℤ) : IsCompact.{w} (X⟦n⟧) ↔ IsCompact.{w} X :=
  ⟨fun h => (h.shift (-n)).of_iso ((shiftEquiv C n).unitIso.app X), fun h => h.shift n⟩

end shift

section cone

variable [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasCoproducts.{w} C]

/-- In a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧`, if `X₁` and `X₂` are compact then so is
`X₃`: the five lemma applied to the comparison maps between the direct sum of the Yoneda
sequences of the `Y i` and the Yoneda sequence of `∐ Y`. -/
theorem IsCompact.ext₃ (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : IsCompact.{w} T.obj₁) (h₂ : IsCompact.{w} T.obj₂) : IsCompact.{w} T.obj₃ := by
  intro ι _ W _
  refine AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (precompDirectSum W (-T.mor₁⟦(1 : ℤ)⟧')) (precompDirectSum W T.mor₃)
    (precompDirectSum W T.mor₂) (precompDirectSum W T.mor₁)
    (Preadditive.leftComp (∐ W) (-T.mor₁⟦(1 : ℤ)⟧')) (Preadditive.leftComp (∐ W) T.mor₃)
    (Preadditive.leftComp (∐ W) T.mor₂) (Preadditive.leftComp (∐ W) T.mor₁)
    (coproductComparison _ W) (coproductComparison _ W) (coproductComparison _ W)
    (coproductComparison _ W) (coproductComparison _ W)
    (leftComp_comp_coproductComparison _) (leftComp_comp_coproductComparison _)
    (leftComp_comp_coproductComparison _) (leftComp_comp_coproductComparison _)
    (exact_directSum_map _ _ fun i => exact_leftComp_of_distTriang'' T hT (W i))
    (exact_directSum_map _ _ fun i => exact_leftComp_of_distTriang' T hT (W i))
    (exact_directSum_map _ _ fun i => exact_leftComp_of_distTriang T hT (W i))
    (exact_leftComp_of_distTriang'' T hT (∐ W)) (exact_leftComp_of_distTriang' T hT (∐ W))
    (exact_leftComp_of_distTriang T hT (∐ W))
    ((h₂.shift 1) ι W).2 ((h₁.shift 1) ι W) (h₂ ι W) (h₁ ι W).1

/-- In a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧`, if `X₁` and `X₃` are compact then so is
`X₂`. -/
theorem IsCompact.ext₂ (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : IsCompact.{w} T.obj₁) (h₃ : IsCompact.{w} T.obj₃) : IsCompact.{w} T.obj₂ :=
  IsCompact.ext₃ T.invRotate (inv_rot_of_distTriang T hT) (h₃.shift (-1)) h₁

/-- In a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧`, if `X₂` and `X₃` are compact then so is
`X₁`. -/
theorem IsCompact.ext₁ (T : Triangle C) (hT : T ∈ distTriang C)
    (h₂ : IsCompact.{w} T.obj₂) (h₃ : IsCompact.{w} T.obj₃) : IsCompact.{w} T.obj₁ :=
  (isCompact_shift_iff T.obj₁ 1).1 (IsCompact.ext₃ T.rotate (rot_of_distTriang T hT) h₂ h₃)

variable (C)

/-- The compact objects of a pretriangulated category with coproducts form a (strictly full)
triangulated subcategory `C^c` [Ne, Def. 4.2.7, Lemma 4.2.4]. It is closed under retracts
(`DG.compactSubcategory_of_retract`), i.e. thick. -/
def compactSubcategory : ObjectProperty C := IsCompact.{w}

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] [HasCoproducts.{w} C] in
@[simp]
theorem compactSubcategory_P : compactSubcategory.{w} C = IsCompact.{w} := rfl

instance : (compactSubcategory.{w} C).IsClosedUnderIsomorphisms :=
  isClosedUnderIsomorphisms_isCompact

instance : (compactSubcategory.{w} C).IsTriangulated where
  toContainsZero := ⟨⟨_, isZero_zero C, IsCompact.of_isZero (isZero_zero C)⟩⟩
  toIsStableUnderShift := ⟨fun n => ⟨fun _ hX => IsCompact.shift hX n⟩⟩
  toIsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ => IsCompact.ext₂ T hT h₁ h₃)

variable {C}

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] [HasCoproducts.{w} C] in
/-- The subcategory of compact objects is closed under retracts (it is thick). -/
theorem compactSubcategory_of_retract {X Y : C} (h : Retract X Y)
    (hY : compactSubcategory.{w} C Y) : compactSubcategory.{w} C X :=
  IsCompact.of_retract h hY

end cone

end DG
