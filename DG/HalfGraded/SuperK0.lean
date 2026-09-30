import DG.HalfGraded.Derived
import DG.K0.Rel

/-!
# The super Grothendieck group of half-graded dg modules

Let `H` be a half-graded dg ring with parameter `k` and `D(C_H)` the derived category of
half-graded dg modules (`DG.HalfGraded.Derived`). Objects of `D(C_H)` can be isomorphic by even
isomorphisms (isomorphisms of `D(C_H)`) or by odd isomorphisms (`DG.HalfGradedDGRing.OddIso`,
odd closed maps between K-projective representatives, invertible up to homotopy).

## Main definitions and results

* `DG.HalfGradedDGRing.IsoEitherParity X Y`: `X` and `Y` are isomorphic by an even or an odd
  isomorphism.
* `DG.HalfGradedDGRing.SuperK0 H`: the super Grothendieck group of `D(C_H)`, the free abelian
  group on the objects modulo isomorphisms of either parity and the relations
  `[Y] = [X] + [Z]` for the distinguished triangles `X → Y → Z → X⟦1⟧` (`DG.K0Rel`), and
  `DG.HalfGradedDGRing.SuperK0c H`, the same for the compact objects `D(C_H)^c`.
* `DG.HalfGradedDGRing.superK0Equiv`, `DG.HalfGradedDGRing.superK0cEquiv` (item 7.4 (c)): the
  super Grothendieck group is the ordinary Grothendieck group `K₀` of the (even) triangulated
  category modulo the relations `[Π X] = [X]`.
-/

open CategoryTheory Category Limits

universe w' w u

noncomputable section

namespace DG

namespace HalfGradedDGRing

variable {A : Type u} [Ring A] {k : ℤ} (H : HalfGradedDGRing A k)
  [CatModule.HasDerivedCategory.{w', max u w} (WeightCategory H.Regraded)]

open CatModule.DerivedCategory

variable {H} in
/-- Two objects of `D(C_H)` are isomorphic by an even isomorphism or by an odd isomorphism. -/
def IsoEitherParity (X Y : CatModule.DerivedCategory.{w', max u w} (WeightCategory H.Regraded)) :
    Prop :=
  Nonempty (X ≅ Y) ∨ OddIso X Y

/-- The super Grothendieck group of the derived category of half-graded dg modules: the free
abelian group on the objects of `D(C_H)` up to isomorphisms of either parity, modulo the
relations `[Y] = [X] + [Z]` for the distinguished triangles `X → Y → Z → X⟦1⟧`. -/
abbrev SuperK0 : Type _ :=
  K0Rel (CatModule.DerivedCategory.{w', max u w} (WeightCategory H.Regraded)) IsoEitherParity

/-- The super Grothendieck group is the Grothendieck group of `D(C_H)` modulo the relations
`[Π X] = [X]`. -/
def superK0Equiv : SuperK0.{w', w} H ≃+
    K0 (CatModule.DerivedCategory.{w', max u w} (WeightCategory H.Regraded)) ⧸
      K0Rel.parityRelations (parityShiftD H).obj :=
  K0Rel.equivQuotient _ (fun X Y h => h.imp id fun h => (oddIso_iff' X Y).mp h)
    (fun X => Or.inr (oddIso_parityShift X))

theorem superK0Equiv_mk (X : CatModule.DerivedCategory.{w', max u w} (WeightCategory H.Regraded)) :
    superK0Equiv H (K0Rel.mk X) = QuotientAddGroup.mk (K0.mk X) :=
  rfl

/-! ### Compact objects -/

variable {H}

/-- The parity shift preserves compact objects of `D(C_H)`. -/
theorem isCompact_parityShiftD_obj
    {X : CatModule.DerivedCategory.{w', max u w} (WeightCategory H.Regraded)}
    (hX : IsCompact.{max u w} X) : IsCompact.{max u w} ((parityShiftD H).obj X) :=
  ((isCompact_internalShift_obj_iff H.Regraded (-k) X).mpr hX).shift 1

variable (H)

/-- The parity shift of a compact object. -/
def parityShiftCompact
    (X : (compactSubcategory.{max u w}
      (CatModule.DerivedCategory.{w', max u w} (WeightCategory H.Regraded))).FullSubcategory) :
    (compactSubcategory.{max u w}
      (CatModule.DerivedCategory.{w', max u w} (WeightCategory H.Regraded))).FullSubcategory :=
  ⟨(parityShiftD H).obj X.obj, isCompact_parityShiftD_obj X.property⟩

/-- The super Grothendieck group of the compact objects `D(C_H)^c`: the free abelian group on
the compact objects up to isomorphisms of either parity, modulo the triangle relations. -/
abbrev SuperK0c : Type _ :=
  K0Rel (compactSubcategory.{max u w}
    (CatModule.DerivedCategory.{w', max u w} (WeightCategory H.Regraded))).FullSubcategory
    (fun X Y => IsoEitherParity X.obj Y.obj)

/-- The super Grothendieck group of `D(C_H)^c` is the Grothendieck group of `D(C_H)^c` modulo the
relations `[Π X] = [X]`. -/
def superK0cEquiv : SuperK0c.{w', w} H ≃+
    K0 (compactSubcategory.{max u w}
      (CatModule.DerivedCategory.{w', max u w} (WeightCategory H.Regraded))).FullSubcategory ⧸
      K0Rel.parityRelations (parityShiftCompact H) :=
  K0Rel.equivQuotient _
    (fun X Y h => h.imp
      (fun ⟨e⟩ => ⟨(compactSubcategory _).fullyFaithfulι.preimageIso e⟩)
      (fun h => let ⟨e⟩ := (oddIso_iff' X.obj Y.obj).mp h
        ⟨(compactSubcategory _).fullyFaithfulι.preimageIso e⟩))
    (fun X => Or.inr (oddIso_parityShift X.obj))

theorem superK0cEquiv_mk
    (X : (compactSubcategory.{max u w}
      (CatModule.DerivedCategory.{w', max u w} (WeightCategory H.Regraded))).FullSubcategory) :
    superK0cEquiv H (K0Rel.mk X) = QuotientAddGroup.mk (K0.mk X) :=
  rfl

end HalfGradedDGRing

end DG

end
