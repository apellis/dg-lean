import DG.Derived.Basic
import DG.Derived.LocalizationCoproducts
import DG.Homotopy.Coproducts
import DG.Module.CohomologyDirectSum

/-!
# Coproducts in the derived category

Let `A` be a dg ring. The derived category `D(A)` has arbitrary coproducts, and the localization
functors `Qh : H(A) ⥤ D(A)` and `Q : DGModuleCat A ⥤ D(A)` preserve them.

The proof: the homotopy category has coproducts (direct sums, `DG/Homotopy/Coproducts.lean`);
a direct sum of quasi-isomorphisms is a quasi-isomorphism since cohomology commutes with direct
sums (`DG.DGModuleHom.IsQuasiIso.directSum`, from `DG.cohomology.directSumAddEquiv`), so the
class of quasi-isomorphisms is stable under coproducts
(`DG.HomotopyCategory.quasiIso_isStableUnderCoproductsOfShape`); and a localization functor at
a class of morphisms with a calculus of right fractions which is stable under coproducts
preserves coproducts (`DG/Derived/LocalizationCoproducts.lean`).

## Universes

Coproducts indexed by `J : Type w` exist in the derived category of dg modules in
`Type (max v w)` (`DG.DerivedCategory.hasColimitsOfShape_discrete`); in particular
`D(A)` built from dg modules in `Type v` has coproducts indexed by `Type v`
(`DG.DerivedCategory.hasCoproducts`).
-/

open CategoryTheory Limits DirectSum

universe w w' v u

namespace DG

section DirectSum

variable {A : Type*} [Ring A] [DGAddCommGroup A] {ι : Type*} [DecidableEq ι]
  {M N : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, DGAddCommGroup (M i)]
  [∀ i, Module A (M i)] [∀ i, AddCommGroup (N i)] [∀ i, DGAddCommGroup (N i)]
  [∀ i, Module A (N i)]

/-- A direct sum of quasi-isomorphisms of dg modules is a quasi-isomorphism. -/
theorem DGModuleHom.IsQuasiIso.directSum (f : ∀ i, M i →ᵈᵍ[A] N i)
    (hf : ∀ i, (f i).IsQuasiIso) :
    (DGModuleHom.toModule fun i => (DGModuleHom.lof A N i).comp (f i)).IsQuasiIso := by
  intro n
  set F := DGModuleHom.toModule fun i => (DGModuleHom.lof A N i).comp (f i)
  let e : ∀ i, cohomology (M i) n ≃+ cohomology (N i) n := fun i =>
    AddEquiv.ofBijective (cohomology.map (f i) n) (hf i n)
  let E : (⨁ i, cohomology (M i) n) ≃+ ⨁ i, cohomology (N i) n := DFinsupp.mapRange.addEquiv e
  have key : ∀ x, cohomology.map F n ((cohomology.directSumAddEquiv M n).symm x) =
      (cohomology.directSumAddEquiv N n).symm (E x) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i y =>
      rw [cohomology.directSumAddEquiv_symm_of, ← cohomology.map_lof (A := A),
        ← cohomology.map_comp_apply, DGModuleHom.toModule_comp_lof, cohomology.map_comp_apply]
      have : E (DirectSum.of _ i y) = DirectSum.of _ i (e i y) :=
        DFinsupp.mapRange_single (hf := fun i => (e i).map_zero)
      rw [this, cohomology.directSumAddEquiv_symm_of, ← cohomology.map_lof (A := A)]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have h : ⇑(cohomology.map F n) = ⇑(((cohomology.directSumAddEquiv M n).trans E).trans
      (cohomology.directSumAddEquiv N n).symm) :=
    funext fun z => by simpa using key (cohomology.directSumAddEquiv M n z)
  rw [h]
  exact AddEquiv.bijective _

end DirectSum

namespace HomotopyCategory

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

set_option backward.isDefEq.respectTransparency false in
/-- The quasi-isomorphisms of the homotopy category are stable under coproducts. -/
theorem quasiIso_isStableUnderCoproductsOfShape (J : Type w) :
    (quasiIso.{max v w} A).IsStableUnderCoproductsOfShape J := by
  classical
  refine MorphismProperty.IsStableUnderCoproductsOfShape.mk _ _ fun X₁ X₂ _ _ f hf => ?_
  let F := DGModuleHom.toModule fun j =>
    (DGModuleHom.lof A (fun j => ((X₂ j).as : Type (max v w))) j).comp (Quot.out (f j)).hom
  have hF : quasiIso A ((quotient A).map (DGModuleCat.ofHom F)) := by
    rw [quotient_map_mem_quasiIso_iff]
    refine DGModuleHom.IsQuasiIso.directSum _ fun j => ?_
    rw [← quotient_map_mem_quasiIso_iff, quotient_map_out]
    exact hf j
  let e₁ := (colimit.isColimit _).coconePointUniqueUpToIso (isColimitCoproductCofan X₁)
  let e₂ := (colimit.isColimit _).coconePointUniqueUpToIso (isColimitCoproductCofan X₂)
  refine ((quasiIso A).arrow_mk_iso_iff (Arrow.isoMk (f := Arrow.mk (Limits.Sigma.map f))
    (g := Arrow.mk ((quotient A).map (DGModuleCat.ofHom F))) e₁ e₂ ?_)).2 hF
  refine Sigma.hom_ext _ _ fun j => ?_
  have h₁ : Sigma.ι X₁ j ≫ e₁.hom = (coproductCofan X₁).inj j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (⟨j⟩ : Discrete J)
  have h₂ : Sigma.ι X₂ j ≫ e₂.hom = (coproductCofan X₂).inj j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (⟨j⟩ : Discrete J)
  dsimp
  rw [reassoc_of% h₁, Sigma.ι_map_assoc, h₂, coproductCofan_inj,
    coproductCofan_inj, ← Functor.map_comp, ← DGModuleCat.ofHom_comp,
    DGModuleHom.toModule_comp_lof, DGModuleCat.ofHom_comp, DGModuleCat.ofHom_hom,
    Functor.map_comp, quotient_map_out]

instance : MorphismProperty.IsStableUnderCoproducts.{w} (quasiIso.{max v w} A) :=
  ⟨quasiIso_isStableUnderCoproductsOfShape A⟩

end HomotopyCategory

namespace DerivedCategory

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

section

variable [HasDerivedCategory.{w', max v w} A] (J : Type w)

/-- The localization functor `H(A) ⥤ D(A)` preserves coproducts. -/
theorem Qh_preservesColimitsOfShape :
    PreservesColimitsOfShape (Discrete J) (Qh : HomotopyCategory.{max v w} A ⥤ _) :=
  LocalizationCoproducts.preservesColimitsOfShape (J := J) Qh (HomotopyCategory.quasiIso A)
    (HomotopyCategory.quasiIso_isStableUnderCoproductsOfShape A J)

/-- The derived category has coproducts indexed by `J : Type w` (for dg modules in
`Type (max v w)`). -/
theorem hasColimitsOfShape_discrete : HasColimitsOfShape (Discrete J) (DerivedCategory A) :=
  LocalizationCoproducts.hasColimitsOfShape (J := J) Qh (HomotopyCategory.quasiIso A)
    (HomotopyCategory.quasiIso_isStableUnderCoproductsOfShape A J)

end

variable [HasDerivedCategory.{w', v} A]

/-- The derived category has arbitrary coproducts. -/
instance hasCoproducts : HasCoproducts.{v} (DerivedCategory A) :=
  hasColimitsOfShape_discrete.{v, w', v} A

/-- The localization functor `H(A) ⥤ D(A)` preserves coproducts. -/
instance Qh_preservesCoproducts (J : Type v) :
    PreservesColimitsOfShape (Discrete J) (Qh : HomotopyCategory.{v} A ⥤ _) :=
  Qh_preservesColimitsOfShape.{v, w', v} A J

/-- The localization functor `DGModuleCat A ⥤ D(A)` preserves coproducts. -/
instance Q_preservesCoproducts (J : Type v) :
    PreservesColimitsOfShape (Discrete J) (Q : DGModuleCat.{v} A ⥤ _) := by
  dsimp only [Q]
  infer_instance

end DerivedCategory

end DG
