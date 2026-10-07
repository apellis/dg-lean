import DG.Category.Derived.ExtendScalars

/-!
# The derived tensor product with a dg bimodule over dg rings

Let `A`, `B` be dg rings and `M` a dg `(A, B)`-bimodule (`DG.DGBimodule`) which is K-projective as
a left dg `A`-module. The derived tensor product over dg categories
(`DG.CatModule.DerivedCategory.derivedTensor`) is transported to dg rings:

* `DG.DGBimodule.catBimodule A B M`: `M` as a dg bimodule over the one-object dg categories
  `SingleObj A`, `SingleObj B`, with the same actions; its left modules are `M`
  (`DG.DGBimodule.catBimodule_left`);
* `DG.DGBimodule.derivedTensor A B M hM : D(B) ⥤ D(A)`, the functor `M ⊗^L_B -`, triangulated
  (`DG.DGBimodule.derivedTensor_commShift`, `DG.DGBimodule.derivedTensor_isTriangulated`);
* `DG.DGBimodule.derivedTensorSelfIso`: `M ⊗^L_B B ≅ M` in `D(A)`;
* `DG.DerivedCategory.isCompact_obj_of_isCompact_self`: a triangulated functor out of `D(B)`
  taking `B` to a compact object preserves compact objects; so `M ⊗^L_B -` preserves compact
  objects when `M` is compact in `D(A)` (`DG.DGBimodule.isCompact_derivedTensor_obj`);
* derived induction along a morphism of dg rings is triangulated
  (`DG.DGRingHom.derivedInduction_commShift`, `DG.DGRingHom.derivedInduction_isTriangulated`).

All dg rings and dg modules are in one universe `v`.
-/

open CategoryTheory MulOpposite

universe w₁ w₂ w₃ w₄ v

noncomputable section

namespace DG

/-! ### Bimodules over dg rings as bimodules over one-object dg categories -/

namespace DGBimodule

section CatBimodule

variable (A B : Type v) [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B] (M : Type v) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [DGBimodule A B M]

/-- A dg `(A, B)`-bimodule as a dg bimodule over the one-object dg categories `SingleObj A` and
`SingleObj B`, with the same left and right actions. -/
def catBimodule : CatBimodule.{v} (SingleObj A) (SingleObj B) where
  obj _ _ := M
  lact := smulAddHom A M
  ract := (smulAddHom Bᵐᵒᵖ M).comp (opAddEquiv : B ≃+ Bᵐᵒᵖ).toAddMonoidHom
  lact_mem' hf hx := smul_mem_grading (A := A) hf hx
  lact_id' _ _ x := one_smul A x
  lact_comp' f f' x := mul_smul (f' : A) (f : A) x
  d_lact' hf x := d_smul (A := A) hf x
  ract_mem' hg hx := op_smul_mem_grading (A := B) hg hx
  ract_id' _ _ x := one_smul Bᵐᵒᵖ x
  ract_comp' g g' x := mul_smul (op (g : B)) (op (g' : B)) x
  d_ract' hx g := d_op_smul (A := B) hx g
  lact_ract' f g x := smul_comm (f : A) (op (g : B)) x

omit [DGRing A] [DGRing B] in
/-- The left dg module `M(-, Y)` over `SingleObj A` is the dg `A`-module `M`. -/
theorem catBimodule_left (Y : SingleObj B) :
    (catBimodule A B M).left Y = DGModuleCat.toCatModuleObj (DGModuleCat.of A M) := rfl

variable {A B M} in
omit [DGRing A] [DGRing B] in
theorem catBimodule_ract {X : SingleObj A} {Y Y' : SingleObj B} (g : Y ⟶ Y') (x : M) :
    (catBimodule A B M).ract (X := X) g x = op (g : B) • x := rfl

variable (hM : IsKProjective.{v} A M)

include hM in
omit [DGRing A] [DGRing B] in
theorem catBimodule_left_isKProjective (Y : SingleObj B) :
    CatModule.IsKProjective ((catBimodule A B M).left Y) :=
  IsKProjective.toCatModuleObj (P := DGModuleCat.of A M) hM

end CatBimodule

/-! ### The derived tensor product -/

section DerivedTensor

variable (A B : Type v) [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B] (M : Type v) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [DGBimodule A B M] (hM : IsKProjective.{v} A M)
  [CatModule.HasDerivedCategory.{w₁, v} (SingleObj B)]
  [CatModule.HasDerivedCategory.{w₂, v} (SingleObj A)]
  [DG.HasDerivedCategory.{w₃, v} B] [DG.HasDerivedCategory.{w₄, v} A]

/-- **The derived tensor product** `M ⊗^L_B - : D(B) ⥤ D(A)` with a dg `(A, B)`-bimodule `M`
which is K-projective as a left dg `A`-module: the derived tensor product with
`catBimodule A B M` over the one-object dg categories, transported along `D(SingleObj _) ≌ D(_)`. -/
def derivedTensor : DG.DerivedCategory B ⥤ DG.DerivedCategory A :=
  (CatModule.DerivedCategory.singleObjEquivalence B).inverse ⋙
    CatModule.DerivedCategory.derivedTensor.{w₁, w₂, v} (catBimodule A B M)
      (catBimodule_left_isKProjective A B M hM) ⋙
      (CatModule.DerivedCategory.singleObjEquivalence A).functor

/-- `M ⊗^L_B -` commutes with the shifts. -/
instance derivedTensor_commShift : (derivedTensor.{w₁, w₂, w₃, w₄} A B M hM).CommShift ℤ :=
  letI := (CatModule.DerivedCategory.singleObjEquivalence B).commShiftInverse ℤ
  inferInstanceAs (((CatModule.DerivedCategory.singleObjEquivalence B).inverse ⋙
    CatModule.DerivedCategory.derivedTensor.{w₁, w₂, v} (catBimodule A B M)
      (catBimodule_left_isKProjective A B M hM) ⋙
      (CatModule.DerivedCategory.singleObjEquivalence A).functor).CommShift ℤ)

/-- `M ⊗^L_B -` is a triangulated functor. -/
instance derivedTensor_isTriangulated :
    (derivedTensor.{w₁, w₂, w₃, w₄} A B M hM).IsTriangulated := by
  let := (CatModule.DerivedCategory.singleObjEquivalence B).commShiftInverse ℤ
  have := (CatModule.DerivedCategory.singleObjEquivalence B).commShift_of_functor ℤ
  have : (CatModule.DerivedCategory.singleObjEquivalence B).IsTriangulated :=
    Equivalence.IsTriangulated.mk' _ inferInstance
  exact inferInstanceAs (((CatModule.DerivedCategory.singleObjEquivalence B).inverse ⋙
    CatModule.DerivedCategory.derivedTensor.{w₁, w₂, v} (catBimodule A B M)
      (catBimodule_left_isKProjective A B M hM) ⋙
      (CatModule.DerivedCategory.singleObjEquivalence A).functor).IsTriangulated)

omit [DGRing A] [DGRing B] in
/-- `M ⊗_B B ≅ M` as dg modules over `SingleObj A` (`m ⊗ b ↦ m b`). -/
def catBimoduleTensorRepresentableIso :
    (catBimodule A B M).tensorObj (CatModule.representable (SingleObj.star B)) ≅
      DGModuleCat.toCatModuleObj (DGModuleCat.of A M) :=
  CatModule.isoMk
    (fun X => (CatTensorProduct.rid ((catBimodule A B M).right X) (SingleObj.star B)).toAddEquiv)
    (fun {X k w} => ⟨fun h => by
      have h1 := (CatTensorProduct.rid ((catBimodule A B M).right X)
        (SingleObj.star B)).symm.map_mem h
      have h2 : (CatTensorProduct.rid ((catBimodule A B M).right X) (SingleObj.star B)).symm
          (CatTensorProduct.rid ((catBimodule A B M).right X) (SingleObj.star B) w) = w :=
        (CatTensorProduct.rid ((catBimodule A B M).right X) (SingleObj.star B)).symm_apply_apply w
      exact h2 ▸ h1,
      fun h => (CatTensorProduct.rid ((catBimodule A B M).right X) (SingleObj.star B)).map_mem h⟩)
    (fun {X} w =>
      (CatTensorProduct.rid ((catBimodule A B M).right X) (SingleObj.star B)).map_d w)
    (fun {X Y} f w => by
      change CatTensorProduct.rid ((catBimodule A B M).right Y) (SingleObj.star B)
          ((catBimodule A B M).tensorAct (CatModule.representable (SingleObj.star B)) f w) =
        (f : A) • (show M from
          CatTensorProduct.rid ((catBimodule A B M).right X) (SingleObj.star B) w)
      induction w using CatTensorProduct.induction_on with
      | zero =>
        rw [map_zero, map_zero, map_zero]
        exact (smul_zero (M := A) (A := M) f).symm
      | tmul Y' n h =>
        have e0 := CatBimodule.tensorAct_tmul (B := catBimodule A B M)
          (CatModule.representable (SingleObj.star B)) f Y' n h
        have e1 := CatTensorProduct.rid_tmul (N := (catBimodule A B M).right Y) (SingleObj.star B)
          Y' ((catBimodule A B M).lact (Y := Y') f n) h
        have e2 := CatTensorProduct.rid_tmul (N := (catBimodule A B M).right X) (SingleObj.star B)
          Y' n h
        have e3 := CatBimodule.right_ract (catBimodule A B M) Y h
          ((catBimodule A B M).lact (Y := Y') f n)
        have e4 := CatBimodule.right_ract (catBimodule A B M) X h n
        have e2' := e2.trans e4
        exact (congrArg _ e0).trans ((e1.trans e3).trans ((smul_comm (M := A) (N := Bᵐᵒᵖ) (α := M)
          (f : A) (op h) n).symm.trans (congrArg (fun x : M => (f : A) • x) e2'.symm)))
      | add x y hx hy =>
        rw [map_add, map_add, hx, hy, map_add]
        exact (smul_add (M := A) (A := M) f _ _).symm)

/-- **`M ⊗^L_B B ≅ M`** in `D(A)`. -/
def derivedTensorSelfIso :
    (derivedTensor.{w₁, w₂, w₃, w₄} A B M hM).obj
        (DG.DerivedCategory.Q.obj (DGModuleCat.of B B)) ≅
      DG.DerivedCategory.Q.obj (DGModuleCat.of A M) :=
  (CatModule.DerivedCategory.singleObjEquivalence A).functor.mapIso
    ((CatModule.DerivedCategory.derivedTensor.{w₁, w₂, v} (catBimodule A B M)
        (catBimodule_left_isKProjective A B M hM)).mapIso
      ((CatModule.DerivedCategory.singleObjEquivalence B).inverse.mapIso
          (DG.DerivedCategory.singleObjEquivalenceObjIso (DGModuleCat.of B B)).symm ≪≫
        ((CatModule.DerivedCategory.singleObjEquivalence B).unitIso.app _).symm ≪≫
        CatModule.DerivedCategory.Q.mapIso (CatModule.IsCornerGenerator.isoOfGen
          CatModule.isCornerGenerator_toCatModuleObj_self
          (CatModule.isCornerGenerator_representable (SingleObj.star B)))) ≪≫
      (CatModule.DerivedCategory.derivedTensorObjIso (catBimodule A B M)
        (catBimodule_left_isKProjective A B M hM)
        (CatModule.isKProjective_representable (SingleObj.star B))).symm ≪≫
      CatModule.DerivedCategory.Q.mapIso (catBimoduleTensorRepresentableIso A B M)) ≪≫
    DG.DerivedCategory.singleObjEquivalenceObjIso (DGModuleCat.of A M)

end DerivedTensor

end DGBimodule

/-! ### Preservation of compact objects -/

section Compact

open Limits Pretriangulated

variable {B : Type v} [Ring B] [DGAddCommGroup B] [DGRing B] [DG.HasDerivedCategory.{v, v} B]
  {T : Type*} [Category T] [HasZeroObject T] [HasShift T ℤ] [Preadditive T]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [HasCoproducts.{v} T]

/-- A triangulated functor out of `D(B)` which takes `B` to a compact object preserves compact
objects: the compact objects of `D(B)` form the thick subcategory generated by `B`
(`DG.DerivedCategory.thickClosure_self_eq_isCompact`), and the objects with compact image form a
thick subcategory. -/
theorem DerivedCategory.isCompact_obj_of_isCompact_self (F : DG.DerivedCategory.{v, v} B ⥤ T)
    [F.CommShift ℤ] [F.IsTriangulated]
    (hF : IsCompact.{v} (F.obj (DG.DerivedCategory.Q.obj (DGModuleCat.of B B))))
    {X : DG.DerivedCategory.{v, v} B} (hX : IsCompact.{v} X) : IsCompact.{v} (F.obj X) := by
  rw [← DG.DerivedCategory.thickClosure_self_eq_isCompact] at hX
  have hP : IsThick (fun Y : DG.DerivedCategory.{v, v} B => IsCompact.{v} (F.obj Y)) :=
    { zero := IsCompact.of_isZero (F.map_isZero (isZero_zero _))
      shift := fun Y n hY => (hY.shift n).of_iso ((F.commShiftIso n).app Y)
      ext₂ := fun R hR h₁ h₃ => IsCompact.ext₂ _ (F.map_distinguished R hR) h₁ h₃
      retract := fun e hY => hY.of_retract (e.map F) }
  refine thickClosure_le hP ?_ X hX
  rintro _ ⟨-, rfl⟩
  exact hF

end Compact

namespace DGBimodule

variable {A B : Type v} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B] {M : Type v} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [DGBimodule A B M] (hM : IsKProjective.{v} A M)
  [CatModule.HasDerivedCategory.{w₁, v} (SingleObj B)]
  [CatModule.HasDerivedCategory.{w₂, v} (SingleObj A)]
  [DG.HasDerivedCategory.{v, v} B] [DG.HasDerivedCategory.{w₄, v} A]

/-- If `M` is compact in `D(A)`, then `M ⊗^L_B -` preserves compact objects. -/
theorem isCompact_derivedTensor_obj
    (hc : IsCompact.{v} (DG.DerivedCategory.Q.obj (DGModuleCat.of A M)))
    {X : DG.DerivedCategory.{v, v} B} (hX : IsCompact.{v} X) :
    IsCompact.{v} ((derivedTensor.{w₁, w₂, v, w₄} A B M hM).obj X) :=
  DerivedCategory.isCompact_obj_of_isCompact_self _
    (hc.of_iso (derivedTensorSelfIso A B M hM)) hX

end DGBimodule

/-! ### Derived induction is triangulated -/

namespace DGRingHom

variable {A B : Type v} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B] (φ : B →ᵈᵍ+* A)
  [CatModule.HasDerivedCategory.{w₁, v} (SingleObj B)]
  [CatModule.HasDerivedCategory.{w₂, v} (SingleObj A)]
  [DG.HasDerivedCategory.{w₃, v} B] [DG.HasDerivedCategory.{w₄, v} A]

/-- Derived induction along a morphism of dg rings commutes with the shifts. -/
instance derivedInduction_commShift : (φ.derivedInduction.{w₁, w₂, w₃, w₄}).CommShift ℤ :=
  letI := (CatModule.DerivedCategory.singleObjEquivalence B).commShiftInverse ℤ
  inferInstanceAs (((CatModule.DerivedCategory.singleObjEquivalence B).inverse ⋙
    CatModule.DerivedCategory.induction.{w₁, w₂, v} φ.singleObjFunctor ⋙
      (CatModule.DerivedCategory.singleObjEquivalence A).functor).CommShift ℤ)

/-- Derived induction along a morphism of dg rings is a triangulated functor. -/
instance derivedInduction_isTriangulated :
    (φ.derivedInduction.{w₁, w₂, w₃, w₄}).IsTriangulated := by
  let := (CatModule.DerivedCategory.singleObjEquivalence B).commShiftInverse ℤ
  have := (CatModule.DerivedCategory.singleObjEquivalence B).commShift_of_functor ℤ
  have : (CatModule.DerivedCategory.singleObjEquivalence B).IsTriangulated :=
    Equivalence.IsTriangulated.mk' _ inferInstance
  exact inferInstanceAs (((CatModule.DerivedCategory.singleObjEquivalence B).inverse ⋙
    CatModule.DerivedCategory.induction.{w₁, w₂, v} φ.singleObjFunctor ⋙
      (CatModule.DerivedCategory.singleObjEquivalence A).functor).IsTriangulated)

end DGRingHom

end DG

end
