import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.HasLocalization

/-!
# Localization functors preserving coproducts

Let `L : C ⥤ D` be a localization functor for a class of morphisms `W` of a preadditive category
`C` (with `D` preadditive and `L` additive). If `W` has a calculus of right fractions and is
stable under coproducts indexed by `J`, and `C` has coproducts indexed by `J`, then `L` preserves
them and `D` has coproducts indexed by `J`
(`DG.LocalizationCoproducts.preservesColimitsOfShape`,
`DG.LocalizationCoproducts.hasColimitsOfShape`).

This applies to the Verdier localization of a triangulated category with coproducts at a
triangulated subcategory closed under coproducts (compare A. Neeman, *Triangulated categories*,
Ann. of Math. Studies 148 (2001), Proposition 3.2.11), in particular to the derived category of a
dg ring (`DG/Derived/Coproducts.lean`).

## Proof

Let `X : J → C`. A family of morphisms `L (X j) ⟶ L Y` is represented by right fractions
`X j ← X' j → Y` with denominators `s j` in `W`; since `∐ s j` is in `W`, they glue to a right
fraction `∐ X j ← ∐ X' j → Y` (`DG.LocalizationCoproducts.exists_desc`). For uniqueness, if
`g : L (∐ X) ⟶ L Y` vanishes on all summands, write `g` as a right fraction `(s, f)`; the right
Ore condition and `L (f ∘ -) = 0` on each summand produce a morphism `B` with `L B` invertible
and `B ≫ f = 0`, whence `g = 0` (`DG.LocalizationCoproducts.eq_zero_of_comp_eq_zero`).
-/

open CategoryTheory Limits Category

namespace DG

namespace LocalizationCoproducts

/-- A coproduct of morphisms in `W` is in `W` if `W` is stable under coproducts. -/
theorem sigmaMap_mem {C : Type*} [Category C] (W : MorphismProperty C) {J : Type*}
    (hW : W.IsStableUnderCoproductsOfShape J) {X X' : J → C} [HasCoproduct X] [HasCoproduct X']
    (s : ∀ j, X' j ⟶ X j) (hs : ∀ j, W (s j)) : W (Limits.Sigma.map s) :=
  hW.colimMap _ fun j => hs j.as

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [W.HasRightCalculusOfFractions]
  [L.Additive] {J : Type*} [HasColimitsOfShape (Discrete J) C]
  (hW : W.IsStableUnderCoproductsOfShape J)

include hW

/-- A morphism out of the image of a coproduct vanishing on all summands is zero. -/
theorem eq_zero_of_comp_eq_zero (X : J → C) {Y : D} (g : L.obj (∐ X) ⟶ Y)
    (hg : ∀ j, L.map (Sigma.ι X j) ≫ g = 0) : g = 0 := by
  have := Localization.essSurj L W
  let e := L.objObjPreimageIso Y
  rw [← cancel_mono e.inv, zero_comp]
  obtain ⟨ψ, hψ⟩ := Localization.exists_rightFraction L W (g ≫ e.inv)
  have := Localization.inverts L W _ ψ.hs
  choose ρ hρ using fun j =>
    (MorphismProperty.LeftFraction.mk (Sigma.ι X j) ψ.s ψ.hs).exists_rightFraction
  have h₀ : ∀ j, L.map ((ρ j).f ≫ ψ.f) = L.map 0 := fun j => by
    have hρ' : (ρ j).s ≫ Sigma.ι X j = (ρ j).f ≫ ψ.s := hρ j
    rw [L.map_comp, ← ψ.map_s_comp_map L (Localization.inverts L W), ← hψ,
      ← L.map_comp_assoc, ← hρ', L.map_comp, assoc, reassoc_of% (hg j)]
    simp
  choose Z u hu hu' using fun j => (MorphismProperty.map_eq_iff_precomp L W _ _).mp (h₀ j)
  let U : ∐ Z ⟶ ∐ fun j => (ρ j).X' := Limits.Sigma.map u
  let T : (∐ fun j => (ρ j).X') ⟶ ∐ X := Limits.Sigma.map fun j => (ρ j).s
  let B : ∐ Z ⟶ ψ.X' := Sigma.desc fun j => u j ≫ (ρ j).f
  have hB₁ : B ≫ ψ.s = U ≫ T := Sigma.hom_ext _ _ fun j => by
    have hρ' : (ρ j).s ≫ Sigma.ι X j = (ρ j).f ≫ ψ.s := hρ j
    simp [B, U, T, hρ']
  have hB₂ : B ≫ ψ.f = 0 := Sigma.hom_ext _ _ fun j => by
    simpa [B] using hu' j
  have := Localization.inverts L W _ (sigmaMap_mem W hW u hu)
  have := Localization.inverts L W _ (sigmaMap_mem W hW _ fun j => (ρ j).hs)
  have : IsIso (L.map B) := by
    have h : IsIso (L.map B ≫ L.map ψ.s) := by
      rw [← L.map_comp, hB₁, L.map_comp]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (L.map ψ.s)
  have hf : L.map ψ.f = 0 := by
    rw [← cancel_epi (L.map B), ← L.map_comp, hB₂, L.map_zero, comp_zero]
  rw [hψ, MorphismProperty.RightFraction.map, hf, comp_zero]

omit [Preadditive C] [Preadditive D] [L.Additive] in
/-- A family of morphisms out of the images of the summands extends to the image of the
coproduct. -/
theorem exists_desc (X : J → C) {Y : D} (φ : ∀ j, L.obj (X j) ⟶ Y) :
    ∃ g : L.obj (∐ X) ⟶ Y, ∀ j, L.map (Sigma.ι X j) ≫ g = φ j := by
  have := Localization.essSurj L W
  let e := L.objObjPreimageIso Y
  choose ψ hψ using fun j => Localization.exists_rightFraction L W (φ j ≫ e.inv)
  let S := Limits.Sigma.map fun j => (ψ j).s
  have hS : W S := sigmaMap_mem W hW _ fun j => (ψ j).hs
  let F : ∐ (fun j => (ψ j).X') ⟶ L.objPreimage Y := Sigma.desc fun j => (ψ j).f
  have := Localization.inverts L W _ hS
  refine ⟨inv (L.map S) ≫ L.map F ≫ e.hom, fun j => ?_⟩
  have := Localization.inverts L W _ (ψ j).hs
  have hS' : (ψ j).s ≫ Sigma.ι X j = Sigma.ι _ j ≫ S := by simp [S]
  rw [← cancel_mono e.inv, assoc, assoc, assoc, e.hom_inv_id, comp_id, hψ j,
    ← cancel_epi (L.map (ψ j).s), MorphismProperty.RightFraction.map_s_comp_map,
    ← L.map_comp_assoc, hS', L.map_comp, assoc, IsIso.hom_inv_id_assoc, ← L.map_comp,
    Sigma.ι_desc]

/-- The image under a localization functor `L` of a coproduct is a coproduct, provided that the
class `W` has a calculus of right fractions and is stable under coproducts. -/
noncomputable def isColimitCofan (X : J → C) :
    IsColimit (Cofan.mk (L.obj (∐ X)) fun j => L.map (Sigma.ι X j)) :=
  IsColimit.ofExistsUnique fun s => by
    obtain ⟨g, hg⟩ := exists_desc L W hW X fun j => s.ι.app ⟨j⟩
    refine ⟨g, fun ⟨j⟩ => hg j, fun g' hg' => ?_⟩
    rw [← sub_eq_zero]
    exact eq_zero_of_comp_eq_zero L W hW X _ fun j => by
      rw [Preadditive.comp_sub, hg j]
      exact sub_eq_zero.mpr (hg' ⟨j⟩)

/-- The localization functor preserves coproducts indexed by `J`. -/
theorem preservesColimitsOfShape : PreservesColimitsOfShape (Discrete J) L where
  preservesColimit {K} := by
    have : PreservesColimit (Discrete.functor (K.obj ∘ Discrete.mk)) L :=
      preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct _)
        ((isColimitMapCoconeCofanMkEquiv _ _ _).symm (isColimitCofan L W hW _))
    exact preservesColimit_of_iso_diagram L Discrete.natIsoFunctor.symm

include L in
/-- The localized category has coproducts indexed by `J`. -/
theorem hasColimitsOfShape : HasColimitsOfShape (Discrete J) D where
  has_colimit K := by
    have := Localization.essSurj L W
    have := preservesColimitsOfShape L W hW
    let X : J → C := fun j => L.objPreimage (K.obj ⟨j⟩)
    have : HasColimit (Discrete.functor X ⋙ L) :=
      ⟨⟨_, isColimitOfPreserves L (colimit.isColimit _)⟩⟩
    exact hasColimit_of_iso (F := Discrete.functor X ⋙ L)
      (Discrete.natIso fun j => (L.objObjPreimageIso (K.obj j)).symm)

end LocalizationCoproducts

end DG
