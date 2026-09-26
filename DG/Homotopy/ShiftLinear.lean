import DG.Homotopy.ForgetTriangulated

/-!
# Linearity of the shift and forgetful functors on the homotopy category

Let `A` be a dg `R`-algebra. The homotopy category `DG.HomotopyCategory A` is `R`-linear
(`DG.HomotopyCategory.instLinear`), and so is the quotient functor from dg modules. This file
shows:

* `DG.HomotopyCategory.shiftFunctor_linear`: the shift functors of `DG.HomotopyCategory A` are
  `R`-linear; hence both sides of the commutation isomorphism
  `(quotient A).commShiftIso n : shiftFunctor _ n ⋙ quotient A ≅ quotient A ⋙ shiftFunctor _ n`
  are `R`-linear functors;
* `DG.HomotopyCategory.forget_linear`: the forgetful functor
  `DG.HomotopyCategory.forget R A` to Mathlib's homotopy category of cochain complexes of
  `R`-modules is `R`-linear.

Both are deduced from the corresponding statements on `DGModuleCat A` with two general
lemmas, `CategoryTheory.Functor.linear_of_iso` and
`CategoryTheory.Functor.linear_of_full_essSurj_comp`, the `R`-linear analogues of Mathlib's
`Functor.additive_of_iso` and `Functor.additive_of_full_essSurj_comp`.
-/

open CategoryTheory

universe v u w

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {R : Type*} [Semiring R] {C : Type u₁} {D : Type u₂} {E : Type u₃} [Category.{v₁} C]
  [Category.{v₂} D] [Category.{v₃} E] [Preadditive C] [Preadditive D] [Preadditive E]
  [CategoryTheory.Linear R C] [CategoryTheory.Linear R D] [CategoryTheory.Linear R E]

/-- A functor isomorphic to an `R`-linear functor is `R`-linear. -/
theorem linear_of_iso {F G : C ⥤ D} [F.Linear R] (e : F ≅ G) : G.Linear R where
  map_smul {X Y} f r := by
    rw [← NatIso.naturality_1 e (r • f), ← NatIso.naturality_1 e f, F.map_smul,
      CategoryTheory.Linear.smul_comp, CategoryTheory.Linear.comp_smul]

/-- If `F` is full, essentially surjective and `R`-linear, and `F ⋙ G` is `R`-linear, then `G`
is `R`-linear. -/
theorem linear_of_full_essSurj_comp (F : C ⥤ D) [F.Full] [F.EssSurj] [F.Linear R] (G : D ⥤ E)
    [(F ⋙ G).Linear R] : G.Linear R where
  map_smul {X Y} f r := by
    obtain ⟨f', hf'⟩ := F.map_surjective ((F.objObjPreimageIso X).hom ≫ f ≫
      (F.objObjPreimageIso Y).inv)
    rw [← cancel_mono (G.map (F.objObjPreimageIso Y).inv),
      ← cancel_epi (G.map (F.objObjPreimageIso X).hom), CategoryTheory.Linear.smul_comp,
      CategoryTheory.Linear.comp_smul, ← G.map_comp, ← G.map_comp, ← G.map_comp, ← G.map_comp,
      CategoryTheory.Linear.smul_comp, CategoryTheory.Linear.comp_smul, ← hf', ← F.map_smul]
    exact (F ⋙ G).map_smul r f'

end CategoryTheory.Functor

namespace DG

namespace HomotopyCategory

variable (R : Type w) (A : Type u) [CommRing R] [Ring A] [DGAddCommGroup A] [Algebra R A]
  [DGRing A] [DGAlgebra R A]

/-- The shift functors of the homotopy category of a dg `R`-algebra are `R`-linear. -/
instance (priority := 100) shiftFunctor_linear (n : ℤ) :
    (shiftFunctor (HomotopyCategory.{v} A) n).Linear R := by
  have : (quotient A ⋙ shiftFunctor (HomotopyCategory.{v} A) n).Linear R :=
    Functor.linear_of_iso ((quotient A).commShiftIso n)
  exact Functor.linear_of_full_essSurj_comp (quotient A) _

/-- The forgetful functor from the homotopy category of dg `A`-modules to the homotopy category
of cochain complexes of `R`-modules is `R`-linear. -/
instance forget_linear : (forget.{v} R A).Linear R := by
  have : (quotient A ⋙ forget.{v} R A).Linear R := Functor.linear_of_iso (forgetFactors R A).symm
  exact Functor.linear_of_full_essSurj_comp (quotient A) _

end HomotopyCategory

end DG
