import DG.Homotopy.HomotopyCategory
import DG.Homotopy.KProjective
import DG.Homotopy.Products

/-!
# Coproducts in the homotopy category of dg modules

The homotopy category `DG.HomotopyCategory A` of dg modules over a dg ring `A` has arbitrary
coproducts, and the quotient functor `DG.DGModuleCat A ⥤ DG.HomotopyCategory A` preserves them:
the coproduct of a family `X j` is (the image of) the direct sum `⨁ j, X j` of dg modules. The
key point is `DG.Homotopic.of_directSum`: two morphisms out of a direct sum are homotopic as
soon as their restrictions to all summands are, since homotopies can be glued along the
summands (`DG.Cochain.directSumDesc`).

## Main definitions and results

* `DG.HomotopyCategory.coproductCofan X` and `DG.HomotopyCategory.isColimitCoproductCofan X`:
  the direct sum is a coproduct in the homotopy category.
* `DG.HomotopyCategory.hasCoproducts`: `HasCoproducts.{w} (HomotopyCategory.{max v w} A)`.
* `DG.HomotopyCategory.quotient_preservesColimitsOfShape_discrete`: the quotient functor
  preserves coproducts.

## Universes

As for `DG.DGModuleCat` (`DG/Homotopy/Products.lean`), coproducts indexed by `J : Type w` are
constructed in `HomotopyCategory.{max v w} A`.
-/

open CategoryTheory Limits DirectSum

universe w v u

namespace DG

section DirectSum

variable {A : Type*} [Ring A] [DGAddCommGroup A] {ι : Type*} [DecidableEq ι]
  {P : ι → Type*} [∀ i, AddCommGroup (P i)] [∀ i, DGAddCommGroup (P i)]
  [∀ i, Module A (P i)]
  [∀ i, DGModule A (P i)] {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module A N]
  [DGModule A N]

/-- Two morphisms out of a direct sum of dg modules are homotopic if their restrictions to all
summands are homotopic. -/
theorem Homotopic.of_directSum {f g : (⨁ i, P i) →ᵈᵍ[A] N}
    (h : ∀ i, Homotopic (f.comp (DGModuleHom.lof A P i)) (g.comp (DGModuleHom.lof A P i))) :
    Homotopic f g := by
  rw [Homotopic.iff_sub]
  choose c hc using fun i => homotopic_zero_iff_exists.mp (Homotopic.iff_sub.mp (h i))
  refine homotopic_zero_iff_exists.mpr ⟨Cochain.directSumDesc c, Cochain.directSum_ext
    fun i x => ?_⟩
  have h1 := congrArg (fun z : Cochain A (P i) N 0 => z x)
    (δ_ofHom_comp (DGModuleHom.lof A P i) (Cochain.directSumDesc c) 0)
  have h2 : (Cochain.directSumDesc c).comp (Cochain.ofHom (DGModuleHom.lof A P i))
      (zero_add _) = c i := Cochain.ext fun y => Cochain.directSumDesc_of c i y
  simp only [Cochain.comp_apply, Cochain.ofHom_apply, DGModuleHom.lof_apply, h2] at h1
  rw [Cochain.ofHom_apply, ← h1, ← hc i]
  rfl

end DirectSum

namespace HomotopyCategory

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]

section

variable {J : Type w} [DecidableEq J] (X : J → HomotopyCategory.{max v w} A)

/-- The direct sum of (representatives of) a family of objects of the homotopy category, as a
cofan. -/
noncomputable def coproductCofan : Cofan X :=
  Cofan.mk ((quotient A).obj (DGModuleCat.of A (⨁ j, ((X j).as : Type (max v w)))))
    fun j => (quotient A).map (DGModuleCat.ofHom
      (DGModuleHom.lof A (fun j => ((X j).as : Type (max v w))) j))

omit [DGRing A] in
@[simp]
theorem coproductCofan_inj (j : J) :
    (coproductCofan X).inj j = (quotient A).map (DGModuleCat.ofHom
      (DGModuleHom.lof A (fun j => ((X j).as : Type (max v w))) j)) := rfl

/-- The direct sum is a coproduct in the homotopy category. -/
noncomputable def isColimitCoproductCofan : IsColimit (coproductCofan X) :=
  mkCofanColimit _
    (fun t => (quotient A).map (DGModuleCat.ofHom
      (DGModuleHom.toModule fun j => (Quot.out (t.inj j)).hom)))
    (fun t j => by
      dsimp only
      rw [coproductCofan_inj, ← Functor.map_comp, ← DGModuleCat.ofHom_comp,
        DGModuleHom.toModule_comp_lof, DGModuleCat.ofHom_hom, quotient_map_out])
    (fun t m hm => by
      obtain ⟨m, rfl⟩ := (quotient A).map_surjective m
      refine (quotient_map_eq_iff _ _).mpr (Homotopic.of_directSum fun j => ?_)
      have := hm j
      rw [coproductCofan_inj, ← Functor.map_comp, ← quotient_map_out (t.inj j),
        quotient_map_eq_iff] at this
      refine this.trans ?_
      rw [DGModuleCat.hom_ofHom, DGModuleHom.toModule_comp_lof])

instance : HasCoproduct X := ⟨⟨_, isColimitCoproductCofan X⟩⟩

variable (F : J → DGModuleCat.{max v w} A)

/-- The quotient functor sends the direct sum of dg modules to a coproduct. -/
instance quotient_preservesColimit_discreteFunctor :
    PreservesColimit (Discrete.functor F) (quotient A) :=
  preservesColimit_of_preserves_colimit_cocone (DGModuleCat.coproductCoconeIsColimit F)
    ((isColimitMapCoconeCofanMkEquiv _ _ _).symm
      (isColimitCoproductCofan fun j => (quotient A).obj (F j)))

end

variable (A)

/-- The homotopy category of dg modules has arbitrary coproducts. -/
instance hasCoproducts : HasCoproducts.{w} (HomotopyCategory.{max v w} A) := fun J =>
  { has_colimit := fun K => by
      letI := Classical.decEq J
      exact hasColimit_of_iso (Discrete.natIsoFunctor (F := K)) }

instance hasCoproducts' : HasCoproducts.{v} (HomotopyCategory.{v} A) :=
  hasCoproducts.{v, v} A

/-- The quotient functor from dg modules to the homotopy category preserves coproducts. -/
instance quotient_preservesColimitsOfShape_discrete (J : Type w) :
    PreservesColimitsOfShape (Discrete J) (quotient.{max v w} A) where
  preservesColimit {K} := by
    letI := Classical.decEq J
    exact preservesColimit_of_iso_diagram (quotient A) (Discrete.natIsoFunctor (F := K)).symm

end HomotopyCategory

end DG
