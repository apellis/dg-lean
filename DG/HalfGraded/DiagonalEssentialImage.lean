import DG.HalfGraded.DiagonalDerivedAdjunction

/-!
# The concrete essential image of the diagonal functor

Over any dg ring, an actual module over the diagonal weight category lies in the
image of `toCatModule`, up to isomorphism, exactly when its values vanish outside
weights divisible by four. The proof uses the existing adjunction counit. At each
supported weight its inverse is explicit: act by the inverse periodic unit, lift
at weight zero, and act by the periodic unit in the diagonal source.

The counit is a quasi-isomorphism exactly when off-support weight cohomology
vanishes in every degree. The existing localized adjunction therefore identifies
the derived essential image by that concrete acyclicity criterion, for every
module representative and every derived object isomorphic to it. No field,
compactness, or shift/cone compatibility hypothesis is imposed or asserted.
-/

open CategoryTheory
universe w' w v u
namespace DG.Diagonal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The inverse periodic unit, as an actual arrow of the weight category. -/
def periodicUnitInv (t : ℤ) :
    (⟨4 * t⟩ : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) ⟶ ⟨0⟩ :=
  ⟨(periodicUnit A (-t)).1, by
    simpa only [sub_zero, zero_sub, mul_neg] using (periodicUnit A (-t)).2⟩

@[simp] theorem periodicUnit_comp_inv (t : ℤ) :
    periodicUnit A t ≫ periodicUnitInv A t = 𝟙 _ := by
  apply Subtype.ext
  change (periodicUnit A (-t)).1 * (periodicUnit A t).1 = _
  simp only [periodicUnit, HalfGradedDGRing.place_mul_place, one_mul]
  exact (HalfGradedDGRing.place_congr (by ext <;> dsimp <;> ring) rfl _ _).trans
    (HalfGradedDGRing.one_eq_place.symm)

@[simp] theorem periodicUnit_inv_comp (t : ℤ) :
    periodicUnitInv A t ≫ periodicUnit A t = 𝟙 _ := by
  apply Subtype.ext
  change (periodicUnit A t).1 * (periodicUnit A (-t)).1 = _
  simp only [periodicUnit, HalfGradedDGRing.place_mul_place, one_mul]
  exact (HalfGradedDGRing.place_congr (by ext <;> dsimp <;> ring) rfl _ _).trans
    (HalfGradedDGRing.one_eq_place.symm)

variable (N : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded))

@[simp] theorem counitApp_zero :
    counitApp A N 0 = valueEvaluation A ((recover A 0).obj N) 0 := by
  change counitApp A N (4 * 0) = _
  rw [counitApp_supported]
  ext x
  change N.act (periodicUnit A 0) _ = _
  rw [periodicUnit_zero]
  exact N.act_id' _ _

/-- Explicit inverse on a supported weight: move to zero, lift, then move back. -/
def supportedCounitInv (t : ℤ) :
    N.obj ⟨4 * t⟩ →+ Value A ((recover A 0).obj N) (4 * t) :=
  ((((toCatModule A).obj ((recover A 0).obj N)).act (periodicUnit A t)).comp
    (weightZeroLift A ((recover A 0).obj N))).comp (N.act (periodicUnitInv A t))

@[simp] theorem counit_supported_inv (t : ℤ) (x : N.obj ⟨4 * t⟩) :
    counitApp A N (4 * t) (supportedCounitInv A N t x) = x := by
  change (counitMap A N).app _
    (((toCatModule A).obj ((recover A 0).obj N)).act (periodicUnit A t) _) = x
  erw [(counitMap A N).map_smul (periodicUnit A t)]
  change N.act (periodicUnit A t) (counitApp A N 0 _) = x
  rw [counitApp_zero]
  refine (congrArg (N.act (periodicUnit A t))
    (valueEvaluation_weightZeroLift A ((recover A 0).obj N) _)).trans ?_
  refine (N.act_comp' (periodicUnitInv A t) (periodicUnit A t) x).symm.trans ?_
  rw [periodicUnit_inv_comp]
  exact N.act_id' _ _

@[simp] theorem supported_inv_counit (t : ℤ)
    (x : Value A ((recover A 0).obj N) (4 * t)) :
    supportedCounitInv A N t (counitApp A N (4 * t) x) = x := by
  change ((toCatModule A).obj ((recover A 0).obj N)).act (periodicUnit A t)
    (weightZeroLift A ((recover A 0).obj N)
      (N.act (periodicUnitInv A t) ((counitMap A N).app _ x))) = x
  refine (congrArg (fun y : N.obj ⟨0⟩ =>
    ((toCatModule A).obj ((recover A 0).obj N)).act (periodicUnit A t)
      (weightZeroLift A ((recover A 0).obj N) y))
    ((counitMap A N).map_smul (periodicUnitInv A t) x).symm).trans ?_
  change ((toCatModule A).obj ((recover A 0).obj N)).act (periodicUnit A t)
    (weightZeroLift A ((recover A 0).obj N) (counitApp A N 0 _)) = x
  rw [counitApp_zero]
  refine (congrArg (((toCatModule A).obj ((recover A 0).obj N)).act (periodicUnit A t))
    (weightZeroLift_valueEvaluation A ((recover A 0).obj N) _)).trans ?_
  refine (((toCatModule A).obj ((recover A 0).obj N)).act_comp'
    (periodicUnitInv A t) (periodicUnit A t) x).symm.trans ?_
  rw [periodicUnit_inv_comp]
  exact CatModule.act_id' _ _ _

/-- Every supported component of the actual counit is bijective, without support assumptions. -/
theorem counitApp_supported_bijective (t : ℤ) :
    Function.Bijective (counitApp A N (4 * t)) :=
  ⟨Function.LeftInverse.injective (supported_inv_counit A N t),
    Function.RightInverse.surjective (counit_supported_inv A N t)⟩

/-- A module is supported on the diagonal precisely when other weight values vanish. -/
def Supported : Prop :=
  ∀ w : ℤ, (¬ ∃ t : ℤ, w = 4 * t) → Subsingleton (N.obj ⟨w⟩)

/-- The action-compatible counit is invertible exactly for modules supported at multiples of four. -/
theorem isIso_counitMap_iff_supported : IsIso (counitMap A N) ↔ Supported A N := by
  rw [CatModule.isIso_iff_bijective]
  constructor
  · intro h w hw
    let := value_subsingleton A ((recover A 0).obj N) w hw
    exact (h ⟨w⟩).surjective.subsingleton
  · intro h
    rintro ⟨w⟩
    by_cases hw : ∃ t : ℤ, w = 4 * t
    · obtain ⟨t, rfl⟩ := hw
      exact counitApp_supported_bijective A N t
    · let := h w hw
      let := value_subsingleton A ((recover A 0).obj N) w hw
      exact ⟨Function.injective_of_subsingleton _, fun y => ⟨0, Subsingleton.elim _ y⟩⟩

/-- A concrete essential-image criterion for the actual diagonal module functor. -/
theorem mem_essImage_toCatModule_iff_supported :
    (toCatModule A).essImage N ↔ Supported A N := by
  rw [← (diagonalAdjunction A).isIso_counit_app_iff_mem_essImage]
  exact isIso_counitMap_iff_supported A N

/-- All off-support weight cohomology groups vanish, in every integer degree. -/
def CohomologicallySupported : Prop :=
  ∀ w : ℤ, (¬ ∃ t : ℤ, w = 4 * t) → ∀ n : ℤ,
    Subsingleton (cohomology (N.obj ⟨w⟩) n)

/-- The supported counit components are already cohomology isomorphisms. -/
theorem counit_supported_cohomology_bijective (t n : ℤ) :
    Function.Bijective (CatModule.cohomologyMap (counitMap A N) ⟨4 * t⟩ n) := by
  let f := (CatModule.precomp (scalarInclusion A (4 * t))).map (counitMap A N)
  have : IsIso f := CatModule.isIso_of_bijective f (fun _ => counitApp_supported_bijective A N t)
  exact CatModule.IsQuasiIso.of_isIso f (SingleObj.star A) n

/-- The actual counit is a quasi-isomorphism exactly when off-support values are acyclic. -/
theorem isQuasiIso_counitMap_iff_cohomologicallySupported :
    CatModule.IsQuasiIso (counitMap A N) ↔ CohomologicallySupported A N := by
  constructor
  · intro h w hw n
    let := unsupportedCohomology_subsingleton A ((recover A 0).obj N) w n hw
    exact (h ⟨w⟩ n).surjective.subsingleton
  · intro h
    rintro ⟨w⟩ n
    by_cases hw : ∃ t : ℤ, w = 4 * t
    · obtain ⟨t, rfl⟩ := hw
      exact counit_supported_cohomology_bijective A N t n
    · let := unsupportedCohomology_subsingleton A ((recover A 0).obj N) w n hw
      let := h w hw n
      exact ⟨Function.injective_of_subsingleton _, fun y => ⟨0, Subsingleton.elim _ y⟩⟩

variable [HasDerivedCategory.{w, v} A]
  [CatModule.HasDerivedCategory.{w', v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]

/-- On any localized module, the actual derived counit is invertible exactly when
its off-support weight cohomology vanishes. -/
theorem isIso_derivedCounit_Q_iff_cohomologicallySupported :
    IsIso ((diagonalDerivedAdjunction.{w', w, v} A).counit.app
      (CatModule.DerivedCategory.Q.obj N)) ↔ CohomologicallySupported A N := by
  rw [diagonalDerivedAdjunction_counit_app_Q, isIso_comp_left_iff,
    isIso_comp_left_iff, CatModule.DerivedCategory.isIso_Q_map_iff]
  exact isQuasiIso_counitMap_iff_cohomologicallySupported A N

/-- Concrete derived essential-image criterion, for every dg module representative.
Only unsupported cohomology must vanish; the values themselves need not be zero. -/
theorem mem_essImage_toDerived_Q_iff_cohomologicallySupported :
    (toDerived.{w', w, v} A).essImage (CatModule.DerivedCategory.Q.obj N) ↔
      CohomologicallySupported A N := by
  rw [← (diagonalDerivedAdjunction A).isIso_counit_app_iff_mem_essImage]
  exact isIso_derivedCounit_Q_iff_cohomologicallySupported A N

/-- The same cohomological criterion for an arbitrary derived object and any chosen
module representative. It is independent of the representative and of the isomorphism. -/
theorem mem_essImage_toDerived_iff_of_iso
    (X : CatModule.DerivedCategory.{w', v}
      (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded))
    (e : CatModule.DerivedCategory.Q.obj N ≅ X) :
    (toDerived.{w', w, v} A).essImage X ↔ CohomologicallySupported A N := by
  constructor
  · rintro ⟨M, ⟨f⟩⟩
    exact (mem_essImage_toDerived_Q_iff_cohomologicallySupported A N).mp
      ⟨M, ⟨f ≪≫ e.symm⟩⟩
  · intro h
    obtain ⟨M, ⟨f⟩⟩ := (mem_essImage_toDerived_Q_iff_cohomologicallySupported A N).mpr h
    exact ⟨M, ⟨f ≪≫ e⟩⟩

end
end DG.Diagonal
