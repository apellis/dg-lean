import DG.Category.Coproducts
import DG.Category.Homotopy.HomotopyCategory

/-!
# Coproducts in the homotopy category of dg modules over a dg category

The homotopy category `DG.CatModule.HomotopyCategory C` of dg modules over a category `C` with
dg Hom groups has arbitrary coproducts, and the quotient functor
`DG.CatModule C ⥤ DG.CatModule.HomotopyCategory C` preserves them: the coproduct of a family
`X j` is (the image of) the objectwise direct sum `DG.CatModule.directSum` of representatives.
The key point is `DG.CatModule.Homotopic.of_directSum`: two morphisms out of a direct sum are
homotopic as soon as their restrictions to all summands are, since homotopies can be glued along
the summands (`DG.CatModule.Cochain.directSumDesc`). This is a port of `DG.Homotopy.Coproducts`
(the case of a dg ring).

## Main definitions and results

* `DG.CatModule.HomotopyCategory.coproductCofan X` and
  `DG.CatModule.HomotopyCategory.isColimitCoproductCofan X`: the direct sum is a coproduct in the
  homotopy category.
* `DG.CatModule.HomotopyCategory.hasCoproducts`:
  `HasCoproducts.{w'} (HomotopyCategory.{max w w'} C)`.
* `DG.CatModule.HomotopyCategory.quotient_preservesColimitsOfShape_discrete`: the quotient
  functor preserves coproducts.

## Universes

As for `DG.CatModule` (`DG/Category/Coproducts.lean`), coproducts indexed by `J : Type w'` are
constructed in `HomotopyCategory.{max w w'} C`.
-/

open CategoryTheory Limits DirectSum

universe w w' v u

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

section DirectSum

variable {J : Type w'} [DecidableEq J] {F : J → CatModule.{max w w'} C}
  {N : CatModule.{max w w'} C}

/-- The cochain out of a direct sum with prescribed restrictions `c j` to the summands. -/
def Cochain.directSumDesc {n : ℤ} (c : ∀ j, Cochain (F j) N n) : Cochain (directSum F) N n where
  app X := DirectSum.toAddMonoid fun j => (c j).app X
  map_mem' {X i x} hx := by
    classical
    change DirectSum.toAddMonoid (fun j => (c j).app X) x ∈ _
    rw [← DirectSum.sum_support_of x, map_sum]
    refine sum_mem fun j _ => ?_
    rw [DirectSum.toAddMonoid_of]
    exact (c j).map_mem (hx j)
  map_smul' {X Y i f} hf x := by
    change DirectSum.toAddMonoid (fun j => (c j).app Y)
      (DirectSum.map (fun j => (F j).act f) x) =
      koszulSign (n * i) • N.act f (DirectSum.toAddMonoid (fun j => (c j).app X) x)
    induction x using DirectSum.induction_on with
    | zero => simp
    | of j y =>
      rw [DirectSum.map_of, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
      exact (c j).map_smul hf y
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, _root_.smul_add]

@[simp]
theorem Cochain.directSumDesc_app_of {n : ℤ} (c : ∀ j, Cochain (F j) N n) (j : J) {X : C}
    (x : (F j).obj X) :
    (Cochain.directSumDesc c).app X (DirectSum.of (fun j => (F j).obj X) j x) = (c j).app X x :=
  DirectSum.toAddMonoid_of (fun j => (c j).app X) j x

/-- Two morphisms out of a direct sum of dg modules are homotopic if their restrictions to all
summands are homotopic. -/
theorem Homotopic.of_directSum {φ ψ : directSum F ⟶ N}
    (h : ∀ j, Homotopic (directSumι F j ≫ φ) (directSumι F j ≫ ψ)) : Homotopic φ ψ := by
  rw [Homotopic.iff_sub]
  choose c hc using fun j => mem_nullHomotopic_iff_exists.mp (Homotopic.iff_sub.mp (h j))
  refine mem_nullHomotopic_iff_exists.mpr ⟨Cochain.directSumDesc c, Cochain.ext fun X x => ?_⟩
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of j y =>
    have := congrArg (fun z : Cochain (F j) N 0 => z.app X y) (hc j)
    simp only [Cochain.ofHom_apply, δ_neg_one_apply] at this ⊢
    refine this.trans ?_
    have hd : DGAddCommGroup.d (M := (directSum F).obj X)
        (DirectSum.of (fun j => (F j).obj X) j y) =
        DirectSum.of (fun j => (F j).obj X) j (d y) :=
      DG.DirectSum.d_of (fun j => (F j).obj X) j y
    rw [Cochain.directSumDesc_app_of, hd, Cochain.directSumDesc_app_of]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end DirectSum

namespace HomotopyCategory

section

variable {J : Type w'} [DecidableEq J] (X : J → HomotopyCategory.{max w w'} C)

/-- The direct sum of (representatives of) a family of objects of the homotopy category, as a
cofan. -/
noncomputable def coproductCofan : Cofan X :=
  Cofan.mk ((quotient C).obj (directSum fun j => (X j).as)) fun j =>
    (quotient C).map (directSumι (fun j => (X j).as) j)

@[simp]
theorem coproductCofan_inj (j : J) :
    (coproductCofan X).inj j = (quotient C).map (directSumι (fun j => (X j).as) j) := rfl

/-- The direct sum is a coproduct in the homotopy category. -/
noncomputable def isColimitCoproductCofan : IsColimit (coproductCofan X) :=
  mkCofanColimit _
    (fun t => (quotient C).map (directSumDesc fun j => Quot.out (t.inj j)))
    (fun t j => by
      dsimp only
      rw [coproductCofan_inj, ← Functor.map_comp, directSumι_desc, quotient_map_out])
    (fun t m hm => by
      obtain ⟨m, rfl⟩ := (quotient C).map_surjective m
      refine (quotient_map_eq_iff _ _).mpr (Homotopic.of_directSum fun j => ?_)
      have := hm j
      rw [coproductCofan_inj, ← Functor.map_comp, ← quotient_map_out (t.inj j),
        quotient_map_eq_iff] at this
      rwa [directSumι_desc])

instance : HasCoproduct X := ⟨⟨_, isColimitCoproductCofan X⟩⟩

variable (F : J → CatModule.{max w w'} C)

/-- The quotient functor sends the direct sum of dg modules to a coproduct. -/
instance quotient_preservesColimit_discreteFunctor :
    PreservesColimit (Discrete.functor F) (quotient C) :=
  preservesColimit_of_preserves_colimit_cocone (coproductCoconeIsColimit F)
    ((isColimitMapCoconeCofanMkEquiv _ _ _).symm
      (isColimitCoproductCofan fun j => (quotient C).obj (F j)))

end

variable (C)

/-- The homotopy category of dg modules has arbitrary coproducts. -/
instance hasCoproducts : HasCoproducts.{w'} (HomotopyCategory.{max w w'} C) := fun J =>
  { has_colimit := fun K => by
      letI := Classical.decEq J
      exact hasColimit_of_iso (Discrete.natIsoFunctor (F := K)) }

instance hasCoproducts' : HasCoproducts.{w} (HomotopyCategory.{w} C) :=
  hasCoproducts.{w, w} C

/-- The quotient functor from dg modules to the homotopy category preserves coproducts. -/
instance quotient_preservesColimitsOfShape_discrete (J : Type w') :
    PreservesColimitsOfShape (Discrete J) (quotient.{max w w'} C) where
  preservesColimit {K} := by
    letI := Classical.decEq J
    exact preservesColimit_of_iso_diagram (quotient C) (Discrete.natIsoFunctor (F := K)).symm

end HomotopyCategory

end CatModule

end DG
