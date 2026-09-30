import DG.Category.Derived.Tensor
import DG.Category.Derived.Keller
import DG.Category.Tensor.YonedaHom
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Derived induction as a derived tensor product

Let `F : C ⥤ D` be a dg functor and `D(F -, -)` the dg `(D, C)`-bimodule
`DG.CatBimodule.ofFunctor F`, so that induction along `F` is `F_! = D(F -, -) ⊗_C -`
(`DG.CatModule.induction`). Its modules `D(F -, -)(-, Y) = D(F Y, -)` are representable, hence
K-projective (`DG.CatBimodule.isKProjective_ofFunctor_left`), and the dg Yoneda lemma for Hom
complexes (`DG.CatModule.yonedaHOM`) identifies `HOM_D(D(F -, -), N)` with the restriction
`F^* N = N ∘ F` (`DG.CatBimodule.homFunctorOfFunctorIso`). Consequently:

* `DG.CatModule.DerivedCategory.rhomOfFunctorIso F : RHOM_D(D(F -, -), -) ≅ F^*`: the derived Hom
  functor of `D(F -, -)` is the (underived) restriction along `F`;
* `DG.CatModule.DerivedCategory.derivedTensorOfFunctorIso F : D(F -, -) ⊗^L_C - ≅ LF_!`: derived
  induction (`DG.CatModule.DerivedCategory.induction`) is the derived tensor product with
  `D(F -, -)`, both being left adjoint to restriction.

For a morphism of dg rings `φ : B → A` and the dg functor `SingleObj B ⥤ SingleObj A`, the
bimodule `D(F -, -)` is `A` as an `(A, B)`-bimodule, so derived induction `φ^* = A ⊗^L_B -` is
left adjoint to restriction `φ_*`. Transported along the equivalences
`D(SingleObj A) ≌ D(A)` (`DG.CatModule.DerivedCategory.singleObjEquivalence`), this gives the
adjunction `DG.DGRingHom.derivedInductionAdjunction φ : φ^* ⊣ φ_*` between the derived
categories of dg modules `D(B)` and `D(A)`, with `φ^*` identified with `A ⊗^L_B -`
(`DG.DGRingHom.derivedInductionIsoDerivedTensor`).

## Universes

The Hom complexes `HOM_D(D(F Y, -), N)` must have values in the universe of `N`, and the derived
tensor product is constructed for modules containing the objects of `C` and `D`: the results are
stated for dg categories `C : Type u₁`, `D : Type u₂` whose morphisms are in
`Type (max u₁ u₂ v)` (for instance `SingleObj A` for a dg ring `A : Type v`), with dg modules in
the same universe.
-/

open CategoryTheory

universe w₁ w₂ w₃ w₄ v v₁ u₁ u₂

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DG

open DGOpposite
open scoped CatModule
open CatModule (HOM)

namespace CatBimodule

section General

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] {D : Type u₂} [Category.{max u₁ u₂ v} D] [Preadditive D]
  [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] [DGCategory D] (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]

omit [DGCategory C] in
/-- The left dg modules `D(F -, -)(-, Y)` of the bimodule of a dg functor are the representable
modules `D(F Y, -)`. -/
theorem ofFunctor_left (Y : C) : (ofFunctor F).left Y = CatModule.representable (F.obj Y) :=
  rfl

omit [DGCategory C] in
/-- The bimodule `D(F -, -)` of a dg functor is K-projective over `D` in each variable. -/
theorem isKProjective_ofFunctor_left (Y : C) : CatModule.IsKProjective ((ofFunctor F).left Y) :=
  CatModule.isKProjective_representable (F.obj Y)

variable {F}

theorem ractCochain_ofFunctor_app_id {Y Y' : C} {i : ℤ} {f : Y ⟶ Y'} (hf : f ∈ grading i) :
    ((ofFunctor F).ractCochain f hf).app (F.obj Y') (𝟙 (F.obj Y')) = F.map f := by
  rw [ractCochain_app_of_mem hf (id_mem_grading (F.obj Y')), mul_zero, koszulSign_zero,
    one_smul]
  exact Category.comp_id (F.map f)

variable (F) (N : CatModule.{max u₁ u₂ v} D)

omit [DGCategory C] in
theorem yonedaHOM_ofFunctor_of {Y : C} {n : ℤ}
    (z : CatModule.Cochain ((ofFunctor F).left Y) N n) :
    CatModule.yonedaHOM (F.obj Y) N
        (DirectSum.of (fun n => CatModule.Cochain ((ofFunctor F).left Y) N n) n z) =
      z.app (F.obj Y) (𝟙 (F.obj Y)) :=
  CatModule.yonedaHOM_of z

/-- The dg Yoneda lemma `HOM_D(D(F Y, -), N) ≅ N(F Y)` is compatible with the actions: for
`f : Y ⟶ Y'`, evaluating `f • w` at `𝟙` gives `F f • w(𝟙)`. -/
theorem yonedaHOM_homAct {Y Y' : C} (f : Y ⟶ Y') (w : HOM ((ofFunctor F).left Y) N) :
    CatModule.yonedaHOM (F.obj Y') N ((ofFunctor F).homAct N f w) =
      F.map f • CatModule.yonedaHOM (F.obj Y) N w := by
  induction f using DG.induction_on with
  | h_zero => simp [CatModule.zero_smul]
  | h_add f g hf hg =>
    rw [map_add, AddMonoidHom.add_apply, map_add, hf, hg, F.map_add, CatModule.add_smul]
  | h_homogeneous f =>
    rename_i i
    rw [homAct_of_mem f.2]
    induction w using DirectSum.induction_on with
    | zero => simp [CatModule.smul_zero]
    | add w w' hw hw' => rw [map_add, map_add, hw, hw', map_add, CatModule.smul_add]
    | of n z =>
      rw [HOM.precompCochain_of, Units.smul_def, map_zsmul, ← Units.smul_def,
        yonedaHOM_ofFunctor_of, yonedaHOM_ofFunctor_of, CatModule.Cochain.comp_apply,
        ractCochain_ofFunctor_app_id f.2]
      have h := z.map_smul (F.map_mem_grading f.2)
        (𝟙 (F.obj Y) : (CatModule.representable (F.obj Y)).obj _)
      change z.app (F.obj Y') (𝟙 (F.obj Y) ≫ F.map (f : Y ⟶ Y')) = _ at h
      rw [Category.id_comp] at h
      rw [h, smul_smul, ← koszulSign_add, show i * n + n * i = 2 * (i * n) by ring,
        koszulSign_even (even_two_mul _), one_smul]

/-- `HOM_D(D(F -, -), N) ≅ F^* N`, by the dg Yoneda lemma for Hom complexes,
`w ↦ w(𝟙)`. -/
def homObjOfFunctorIso : (ofFunctor F).homObj N ≅ (CatModule.precomp F).obj N :=
  CatModule.isoMk (fun Y => (CatModule.yonedaHOM (F.obj Y) N).toAddEquiv)
    (fun {Y k w} => ⟨fun h => by
      have := (CatModule.yonedaHOM (F.obj Y) N).symm.map_mem h
      have h2 : (CatModule.yonedaHOM (F.obj Y) N).symm (CatModule.yonedaHOM (F.obj Y) N w) = w :=
        (CatModule.yonedaHOM (F.obj Y) N).symm_apply_apply w
      exact h2 ▸ this,
      fun h => (CatModule.yonedaHOM (F.obj Y) N).map_mem h⟩)
    (fun {Y} w => (CatModule.yonedaHOM (F.obj Y) N).map_d w)
    (fun {Y Y'} f w => yonedaHOM_homAct F N f w)

theorem homObjOfFunctorIso_hom_app (Y : C) (w : ((ofFunctor F).homObj N).obj Y) :
    ((homObjOfFunctorIso F N).hom.app Y) w = CatModule.yonedaHOM (F.obj Y) N w :=
  rfl

/-- The Hom functor of the bimodule `D(F -, -)` is restriction along `F`. -/
def homFunctorOfFunctorIso :
    (ofFunctor F).homFunctor ≅
      (CatModule.precomp.{max u₁ u₂ v} F : CatModule.{max u₁ u₂ v} D ⥤ _) :=
  NatIso.ofComponents (fun N => homObjOfFunctorIso F N) fun {N N'} φ =>
    CatModule.hom_ext fun Y w => by
      change CatModule.yonedaHOM (F.obj Y) N'
          (HOM.postcompCochain (CatModule.Cochain.ofHom φ) w) =
        φ.app (F.obj Y) (CatModule.yonedaHOM (F.obj Y) N w)
      induction w using DirectSum.induction_on with
      | zero => simp
      | add w w' hw hw' => rw [map_add, map_add, hw, hw', map_add, map_add]
      | of n z =>
        erw [HOM.postcompCochain_of]
        rw [yonedaHOM_ofFunctor_of, CatModule.yonedaHOM_of]
        rfl

end General

end CatBimodule

namespace CatModule

section Comparison

variable {C : Type u₁} [Category.{max u₁ u₂ v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C] {D : Type u₂}
  [Category.{max u₁ u₂ v} D] [Preadditive D] [∀ X Y : D, DGAddCommGroup (X ⟶ Y)]
  [DGCategory D] (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]

namespace HomotopyCategory

/-- On homotopy categories, the Hom functor of `D(F -, -)` is restriction along `F`. -/
def homFunctorOfFunctorIso :
    homFunctor (CatBimodule.ofFunctor F) ≅
      (precomp F : HomotopyCategory.{max u₁ u₂ v} D ⥤ HomotopyCategory.{max u₁ u₂ v} C) :=
  CategoryTheory.Quotient.natIsoLift _
    (homFunctorFactors (CatBimodule.ofFunctor F) ≪≫
      Functor.isoWhiskerRight (CatBimodule.homFunctorOfFunctorIso F) (quotient C) ≪≫
      (precompFactors F).symm)

end HomotopyCategory

namespace DerivedCategory

variable [HasDerivedCategory.{w₁, max u₁ u₂ v} C] [HasDerivedCategory.{w₂, max u₁ u₂ v} D]

/-- The derived Hom functor of the bimodule `D(F -, -)` of a dg functor is restriction along
`F`: `RHOM_D(D(F -, -), -) ≅ F^*`. -/
def rhomOfFunctorIso :
    rhom (CatBimodule.ofFunctor F) (CatBimodule.isKProjective_ofFunctor_left F) ≅
      (restrict F : DerivedCategory.{w₂, max u₁ u₂ v} D ⥤
        DerivedCategory.{w₁, max u₁ u₂ v} C) :=
  Localization.liftNatIso Qh (HomotopyCategory.quasiIso D)
    (HomotopyCategory.homFunctor (CatBimodule.ofFunctor F) ⋙ Qh)
    (HomotopyCategory.precomp F ⋙ Qh) _ _
    (Functor.isoWhiskerRight (HomotopyCategory.homFunctorOfFunctorIso F) Qh)

/-- **Derived induction is a derived tensor product**: for a dg functor `F : C ⥤ D`, derived
induction `LF_!` is the derived tensor product with the bimodule `D(F -, -)`, both being left
adjoint to restriction along `F`. -/
def derivedTensorOfFunctorIso :
    derivedTensor.{w₁, w₂, v} (CatBimodule.ofFunctor F)
        (CatBimodule.isKProjective_ofFunctor_left F) ≅
      induction.{w₁, w₂, v} F :=
  (derivedTensorAdjunction _ _).leftAdjointUniq
    ((inductionAdjunction F).ofNatIsoRight (rhomOfFunctorIso F).symm)

end DerivedCategory

end Comparison

end CatModule

/-! ### Dg rings -/

section DGRing

variable {A : Type v} [Ring A] [DGAddCommGroup A] [DGRing A] {B : Type v} [Ring B]
  [DGAddCommGroup B] [DGRing B]

namespace DGRingHom

variable (φ : B →ᵈᵍ+* A)
  [CatModule.HasDerivedCategory.{w₁, v} (SingleObj B)]
  [CatModule.HasDerivedCategory.{w₂, v} (SingleObj A)]
  [DG.HasDerivedCategory.{w₃, v} B] [DG.HasDerivedCategory.{w₄, v} A]

/-- Derived induction `φ^* : D(B) ⥤ D(A)` along a morphism of dg rings `φ : B → A`: derived
induction along the dg functor `SingleObj B ⥤ SingleObj A`, transported along the
equivalences `D(SingleObj B) ≌ D(B)` and `D(SingleObj A) ≌ D(A)`. It is `A ⊗^L_B -`
(`DG.DGRingHom.derivedInductionIsoDerivedTensor`). -/
def derivedInduction : DG.DerivedCategory B ⥤ DG.DerivedCategory A :=
  (CatModule.DerivedCategory.singleObjEquivalence B).inverse ⋙
    CatModule.DerivedCategory.induction.{w₁, w₂, v} φ.singleObjFunctor ⋙
      (CatModule.DerivedCategory.singleObjEquivalence A).functor

/-- Derived restriction `φ_* : D(A) ⥤ D(B)` along a morphism of dg rings: the functor induced by
restriction of scalars along `SingleObj B ⥤ SingleObj A` (which needs no deriving), transported
along the equivalences `D(SingleObj A) ≌ D(A)` and `D(SingleObj B) ≌ D(B)`. -/
def derivedRestriction : DG.DerivedCategory A ⥤ DG.DerivedCategory B :=
  (CatModule.DerivedCategory.singleObjEquivalence A).inverse ⋙
    CatModule.DerivedCategory.restrict.{w₁, w₂, v} φ.singleObjFunctor ⋙
      (CatModule.DerivedCategory.singleObjEquivalence B).functor

/-- The adjunction `φ^* ⊣ φ_*` between the derived categories of dg modules over dg rings. -/
def derivedInductionAdjunction : φ.derivedInduction.{w₁, w₂, w₃, w₄} ⊣ φ.derivedRestriction :=
  (CatModule.DerivedCategory.singleObjEquivalence B).symm.toAdjunction.comp
    ((CatModule.DerivedCategory.inductionAdjunction φ.singleObjFunctor).comp
      (CatModule.DerivedCategory.singleObjEquivalence A).toAdjunction)

/-- Derived induction along a morphism of dg rings `φ : B → A` is the derived tensor product with
`A`, as an `(A, B)`-bimodule (`DG.CatBimodule.ofFunctor φ.singleObjFunctor`):
`φ^* ≅ A ⊗^L_B -`. -/
def derivedInductionIsoDerivedTensor :
    φ.derivedInduction.{w₁, w₂, w₃, w₄} ≅
      (CatModule.DerivedCategory.singleObjEquivalence B).inverse ⋙
        CatModule.DerivedCategory.derivedTensor.{w₁, w₂, v}
          (CatBimodule.ofFunctor φ.singleObjFunctor)
          (CatBimodule.isKProjective_ofFunctor_left φ.singleObjFunctor) ⋙
        (CatModule.DerivedCategory.singleObjEquivalence A).functor :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
    (CatModule.DerivedCategory.derivedTensorOfFunctorIso φ.singleObjFunctor).symm _)

end DGRingHom

end DGRing

end DG
