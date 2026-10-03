import DG.HalfGraded.DiagonalDerivedTriangulated
import DG.Category.Derived.Compact
import DG.Derived.Coproducts
import DG.K0.Compact

/-!
# Compactness preservation by the actual diagonal functor

Actual recovery is restriction along `scalarInclusion` followed by one-object evaluation.
Both preserve coproducts of modules. The existing localization comparison then proves
that the original `recoveryDerived` preserves coproducts at every weight, without tying
either derived Hom universe to the module universe. The original diagonal adjunction
therefore proves preservation of all compact objects by `toDerived`.

Compactness is `DG.IsCompact` for coproducts indexed in the module universe. No support,
field, or boundedness hypothesis is imposed, and no equivalence with the whole target
or explicit cone comparison is claimed.
-/

open CategoryTheory Limits
universe w' w v u
namespace DG.Diagonal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- Actual restriction at a weight commutes with objectwise direct sums, including its
scalar action, grading, and differential. -/
def scalarRestrictionDirectSumIso (s : ℤ) {J : Type v} [DecidableEq J]
    (N : J → CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    (CatModule.precomp (scalarInclusion A s)).obj (CatModule.directSum N) ≅
      CatModule.directSum fun j => (CatModule.precomp (scalarInclusion A s)).obj (N j) :=
  CatModule.isoMk (fun _ => AddEquiv.refl _) (fun {_ _ _} => Iff.rfl)
    (fun _ => rfl) (fun _ _ => rfl)

/-- Restriction along the actual scalar inclusion preserves coproducts. -/
instance scalarRestriction_preservesCoproducts (s : ℤ) (J : Type v) :
    PreservesColimitsOfShape (Discrete J) (CatModule.precomp.{v} (scalarInclusion A s)) := by
  suffices ∀ N : J → CatModule.{v}
      (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded),
      PreservesColimit (Discrete.functor N) (CatModule.precomp (scalarInclusion A s)) from
    preservesColimitsOfShape_of_discrete _
  intro N
  classical
  refine preservesColimit_of_preserves_colimit_cocone
    (CatModule.coproductCoconeIsColimit.{v, v} N) ?_
  refine (isColimitMapCoconeCofanMkEquiv _ _ _).symm ?_
  refine IsColimit.ofIsoColimit
    (CatModule.coproductCoconeIsColimit.{v, v}
      fun j => (CatModule.precomp (scalarInclusion A s)).obj (N j))
    (Cocone.ext (scalarRestrictionDirectSumIso A s N).symm fun j => ?_)
  exact CatModule.hom_ext fun _ _ => rfl

/-- Actual recovery preserves coproducts before localization, by restriction and the
one-object evaluation equivalence. -/
instance recover_preservesCoproducts (s : ℤ) (J : Type v) :
    PreservesColimitsOfShape (Discrete J) (recover.{v} A s) := by
  change PreservesColimitsOfShape (Discrete J)
    (CatModule.precomp (scalarInclusion A s) ⋙ (CatModule.singleObjEquivalence A).functor)
  infer_instance

variable [HasDerivedCategory.{w, v} A]
  [CatModule.HasDerivedCategory.{w', v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]

/-- The existing derived recovery preserves coproducts at every weight. The proof uses
actual localized module coproducts, not a replacement recovery functor. -/
instance recoveryDerived_preservesCoproducts (s : ℤ) (J : Type v) :
    PreservesColimitsOfShape (Discrete J) (recoveryDerived.{w', w, v} A s) := by
  suffices ∀ Y : J → CatModule.DerivedCategory.{w', v}
      (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded),
      PreservesColimit (Discrete.functor Y) (recoveryDerived A s) from
    preservesColimitsOfShape_of_discrete _
  intro Y
  classical
  choose N e using fun j => CatModule.DerivedCategory.exists_iso_Q_obj (Y j)
  suffices PreservesColimit (Discrete.functor N ⋙ CatModule.DerivedCategory.Q)
      (recoveryDerived A s) from
    preservesColimit_of_iso_diagram _
      (Discrete.natIso fun j => (e j.as).some.symm :
        Discrete.functor N ⋙ CatModule.DerivedCategory.Q ≅ Discrete.functor Y)
  have : PreservesColimit (Discrete.functor N)
      (CatModule.DerivedCategory.Q ⋙ recoveryDerived A s) :=
    preservesColimit_of_natIso _ (QCompRecoveryDerivedIso A s).symm
  exact preservesColimit_of_preserves_colimit_cocone
    (isColimitOfPreserves CatModule.DerivedCategory.Q
      (CatModule.coproductCoconeIsColimit.{v, v} N))
    (isColimitOfPreserves (CatModule.DerivedCategory.Q ⋙ recoveryDerived A s)
      (CatModule.coproductCoconeIsColimit.{v, v} N))

/-- The actual diagonal derived functor preserves every compact object, because its
actual right adjoint preserves coproducts. The two derived Hom universes are independent. -/
theorem isCompact_toDerived {X : DerivedCategory.{w, v} A} (hX : IsCompact.{v} X) :
    IsCompact.{v} ((toDerived.{w', w, v} A).obj X) :=
  hX.map_of_adjunction (diagonalDerivedAdjunction A)

end
end DG.Diagonal
