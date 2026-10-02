import DG.HalfGraded.DiagonalCompact

/-!
# The actual diagonal functor on compact objects and their Grothendieck groups

This consumes coproduct preservation by the actual recovery adjoint. The functor is the
restriction of the original `toDerived`, and `K₀` is taken only on the existing compact
subcategories. This is a homomorphism, not a claim of equivalence or of an isomorphism
with the Grothendieck group of the whole target.
-/

open CategoryTheory
universe w' w v u
namespace DG.Diagonal
noncomputable section

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]
  [HasDerivedCategory.{w, v} A]
  [CatModule.HasDerivedCategory.{w', v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]

/-- The original diagonal derived functor restricted to the actual compact objects. -/
abbrev toDerivedCompact :
    (compactSubcategory.{v} (DerivedCategory.{w, v} A)).FullSubcategory ⥤
      (compactSubcategory.{v} (CatModule.DerivedCategory.{w', v}
        (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded))).FullSubcategory :=
  compactRestriction (toDerived A) (fun _ h => isCompact_toDerived A h)

/-- On underlying objects this is exactly the original diagonal derived functor. -/
@[simp] theorem toDerivedCompact_obj
    (X : (compactSubcategory.{v} (DerivedCategory.{w, v} A)).FullSubcategory) :
    ((toDerivedCompact.{w', w, v} A).obj X).obj = (toDerived A).obj X.obj := rfl

/-- The map on `K₀` of compact objects induced by the actual triangulated diagonal. -/
def mapCompactK0 :
    K0 (compactSubcategory.{v} (DerivedCategory.{w, v} A)).FullSubcategory →+
      K0 (compactSubcategory.{v} (CatModule.DerivedCategory.{w', v}
        (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded))).FullSubcategory :=
  K0.mapCompact (toDerived A) (fun _ h => isCompact_toDerived A h)

/-- The compact `K₀` map sends the class of `X` to the class of its actual diagonal image. -/
@[simp] theorem mapCompactK0_mk
    (X : (compactSubcategory.{v} (DerivedCategory.{w, v} A)).FullSubcategory) :
    mapCompactK0.{w', w, v} A (K0.mk X) = K0.mk ((toDerivedCompact A).obj X) :=
  K0.mapCompact_mk _ _ X

end
end DG.Diagonal
