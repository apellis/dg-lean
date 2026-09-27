import DG.Category.Derived.Basic
import DG.Category.Derived.HomotopyCoproducts
import DG.Derived.LocalizationCoproducts
import DG.Module.CohomologyDirectSum

/-!
# Coproducts in the derived category of a dg category

Let `C` be a dg category. The derived category `D(C)` has arbitrary coproducts, and the
localization functors `Qh : H(C) ⥤ D(C)` and `Q : CatModule C ⥤ D(C)` preserve them. This is a
port of `DG.Derived.Coproducts` (the case of a dg ring).

The proof: the homotopy category has coproducts (objectwise direct sums,
`DG/Category/Derived/HomotopyCoproducts.lean`); a direct sum of quasi-isomorphisms is a
quasi-isomorphism since cohomology commutes with direct sums
(`DG.CatModule.IsQuasiIso.directSum`, from `DG.cohomology.directSumAddEquiv`), so the class of
quasi-isomorphisms is stable under coproducts
(`DG.CatModule.HomotopyCategory.quasiIso_isStableUnderCoproductsOfShape`); and a localization
functor at a class of morphisms with a calculus of right fractions which is stable under
coproducts preserves coproducts (`DG/Derived/LocalizationCoproducts.lean`).

## Universes

Coproducts indexed by `J : Type w` exist in the derived category of dg modules with values in
`Type (max w'' w)` (`DG.CatModule.DerivedCategory.hasColimitsOfShape_discrete`); in particular
`D(C)` built from dg modules with values in `Type w` has coproducts indexed by `Type w`
(`DG.CatModule.DerivedCategory.hasCoproducts`).
-/

open CategoryTheory Limits DirectSum

universe w w'' w' v u

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

section DirectSum

variable {J : Type w} [DecidableEq J] {F G : J → CatModule.{max w'' w} C}

/-- A direct sum of quasi-isomorphisms of dg modules is a quasi-isomorphism. -/
theorem IsQuasiIso.directSum (f : ∀ j, F j ⟶ G j) (hf : ∀ j, IsQuasiIso (f j)) :
    IsQuasiIso (directSumDesc fun j => f j ≫ directSumι G j) := by
  intro X n
  set Φ := directSumDesc fun j => f j ≫ directSumι G j
  let e : ∀ j, cohomology ((F j).obj X) n ≃+ cohomology ((G j).obj X) n := fun j =>
    AddEquiv.ofBijective (cohomologyMap (f j) X n) (hf j X n)
  let E : (⨁ j, cohomology ((F j).obj X) n) ≃+ ⨁ j, cohomology ((G j).obj X) n :=
    DFinsupp.mapRange.addEquiv e
  have key : ∀ x, cohomologyMap Φ X n
      ((cohomology.directSumAddEquiv (fun j => (F j).obj X) n).symm x) =
      (cohomology.directSumAddEquiv (fun j => (G j).obj X) n).symm (E x) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of j y =>
      have h₁ : cohomologyMap Φ X n (cohomologyMap (directSumι F j) X n y) =
          cohomologyMap (directSumι G j) X n (cohomologyMap (f j) X n y) := by
        rw [← cohomologyMap_comp_apply, ← cohomologyMap_comp_apply, directSumι_desc]
      have h₂ : E (DirectSum.of _ j y) = DirectSum.of _ j (e j y) :=
        DFinsupp.mapRange_single (hf := fun j => (e j).map_zero)
      rw [cohomology.directSumAddEquiv_symm_of, h₂, cohomology.directSumAddEquiv_symm_of]
      exact h₁
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have h : ⇑(cohomologyMap Φ X n) =
      ⇑(((cohomology.directSumAddEquiv (fun j => (F j).obj X) n).trans E).trans
        (cohomology.directSumAddEquiv (fun j => (G j).obj X) n).symm) :=
    funext fun z => by
      simpa using key (cohomology.directSumAddEquiv (fun j => (F j).obj X) n z)
  rw [h]
  exact AddEquiv.bijective _

end DirectSum

namespace HomotopyCategory

variable (C) [DGCategory C]

/-- The quasi-isomorphisms of the homotopy category are stable under coproducts. -/
theorem quasiIso_isStableUnderCoproductsOfShape (J : Type w) :
    (quasiIso.{max w'' w} C).IsStableUnderCoproductsOfShape J := by
  classical
  refine MorphismProperty.IsStableUnderCoproductsOfShape.mk _ _ fun X₁ X₂ _ _ f hf => ?_
  let Φ := directSumDesc fun j => Quot.out (f j) ≫ directSumι (fun j => (X₂ j).as) j
  have hΦ : quasiIso C ((quotient C).map Φ) := by
    rw [quotient_map_mem_quasiIso_iff]
    refine IsQuasiIso.directSum _ fun j => ?_
    rw [← quotient_map_mem_quasiIso_iff, quotient_map_out]
    exact hf j
  let e₁ := (colimit.isColimit _).coconePointUniqueUpToIso (isColimitCoproductCofan X₁)
  let e₂ := (colimit.isColimit _).coconePointUniqueUpToIso (isColimitCoproductCofan X₂)
  refine ((quasiIso C).arrow_mk_iso_iff (Arrow.isoMk (f := Arrow.mk (Limits.Sigma.map f))
    (g := Arrow.mk ((quotient C).map Φ)) e₁ e₂ ?_)).2 hΦ
  refine Sigma.hom_ext _ _ fun j => ?_
  have h₁ : Sigma.ι X₁ j ≫ e₁.hom = (coproductCofan X₁).inj j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (⟨j⟩ : Discrete J)
  have h₂ : Sigma.ι X₂ j ≫ e₂.hom = (coproductCofan X₂).inj j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (⟨j⟩ : Discrete J)
  dsimp
  rw [reassoc_of% h₁, ι_colimMap_assoc, Discrete.natTrans_app,
    show colimit.ι (Discrete.functor X₂) ⟨j⟩ ≫ e₂.hom = _ from h₂, coproductCofan_inj,
    coproductCofan_inj, ← Functor.map_comp, directSumι_desc, Functor.map_comp, quotient_map_out]

instance : MorphismProperty.IsStableUnderCoproducts.{w} (quasiIso.{max w'' w} C) :=
  ⟨quasiIso_isStableUnderCoproductsOfShape C⟩

end HomotopyCategory

namespace DerivedCategory

variable (C) [DGCategory C]

section

variable [HasDerivedCategory.{w', max w'' w} C] (J : Type w)

/-- The localization functor `H(C) ⥤ D(C)` preserves coproducts. -/
theorem Qh_preservesColimitsOfShape :
    PreservesColimitsOfShape (Discrete J) (Qh : HomotopyCategory.{max w'' w} C ⥤ _) :=
  LocalizationCoproducts.preservesColimitsOfShape (J := J) Qh (HomotopyCategory.quasiIso C)
    (HomotopyCategory.quasiIso_isStableUnderCoproductsOfShape C J)

/-- The derived category has coproducts indexed by `J : Type w` (for dg modules with values in
`Type (max w'' w)`). -/
theorem hasColimitsOfShape_discrete : HasColimitsOfShape (Discrete J) (DerivedCategory C) :=
  LocalizationCoproducts.hasColimitsOfShape (J := J) Qh (HomotopyCategory.quasiIso C)
    (HomotopyCategory.quasiIso_isStableUnderCoproductsOfShape C J)

end

variable [HasDerivedCategory.{w', w} C]

/-- The derived category has arbitrary coproducts. -/
instance hasCoproducts : HasCoproducts.{w} (DerivedCategory C) :=
  hasColimitsOfShape_discrete.{w, w, w'} C

/-- The localization functor `H(C) ⥤ D(C)` preserves coproducts. -/
instance Qh_preservesCoproducts (J : Type w) :
    PreservesColimitsOfShape (Discrete J) (Qh : HomotopyCategory.{w} C ⥤ _) :=
  Qh_preservesColimitsOfShape.{w, w, w'} C J

/-- The localization functor `CatModule C ⥤ D(C)` preserves coproducts. -/
instance Q_preservesCoproducts (J : Type w) :
    PreservesColimitsOfShape (Discrete J) (Q : CatModule.{w} C ⥤ _) := by
  dsimp only [Q]
  infer_instance

end DerivedCategory

end CatModule

end DG
