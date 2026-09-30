import DG.K0.DGRing
import DG.Category.Derived.InductionComp

/-!
# `K₀` of a morphism of dg rings on the classes `[A e]`

For a morphism of dg rings `φ : B → A` and a degree-`0` idempotent cocycle `e` of `B`, derived
induction takes `B e` to `A φ(e)` (`DG.CatModule.DerivedCategory.inductionLeftCornerIso`), hence
`K₀(φ) [B e] = [A φ(e)]` (`DG.DGRing.K0.map_leftCorner`).

Over `SingleObj B`, the module `B e` is the direct summand of the representable module cut out
by the idempotent `h ↦ e ≫ h` (`DG.CatModule.leftCornerRetract`). Induction takes the
representable module to the representable module (`DG.CatModule.inductionULiftRepresentableIso`)
and this idempotent to the one of `φ(e)`
(`DG.CatModule.DerivedCategory.induction_map_leftCornerRetract_idem`); since
`Q (F_! P) ≅ LF_! (Q P)` is natural in the K-projective module `P`, the two direct summands are
isomorphic (`CategoryTheory.Retract.isoOfConj`).

## Main definitions and results

* `CategoryTheory.Retract.isoOfConj`: retracts with conjugate idempotents are isomorphic.
* `DG.DGIdempotent.map φ e`: the image `φ(e)` of an idempotent cocycle.
* `DG.DGRing.K0.singleObjEquiv_leftCorner`, `DG.DGRing.K0.map_leftCorner`.
-/

open CategoryTheory Limits Pretriangulated

universe w₁ w₂ u

set_option backward.isDefEq.respectTransparency false

namespace DG

/-- Two retracts `Y` of `X` and `Y'` of `X'` whose idempotents correspond under an isomorphism
`X ≅ X'` are isomorphic. -/
def _root_.CategoryTheory.Retract.isoOfConj {C : Type*} [Category C] {X X' Y Y' : C}
    (r : Retract Y X) (r' : Retract Y' X') (θ : X ≅ X')
    (h : r.r ≫ r.i ≫ θ.hom = θ.hom ≫ r'.r ≫ r'.i) : Y ≅ Y' where
  hom := r.i ≫ θ.hom ≫ r'.r
  inv := r'.i ≫ θ.inv ≫ r.r
  hom_inv_id := by
    have h' : θ.hom ≫ r'.r ≫ r'.i = r.r ≫ r.i ≫ θ.hom := h.symm
    calc (r.i ≫ θ.hom ≫ r'.r) ≫ r'.i ≫ θ.inv ≫ r.r
        = r.i ≫ (θ.hom ≫ r'.r ≫ r'.i) ≫ θ.inv ≫ r.r := by simp only [Category.assoc]
      _ = 𝟙 Y := by
        rw [h']
        simp only [Category.assoc, Iso.hom_inv_id_assoc, r.retract_assoc, r.retract]
  inv_hom_id := by
    have h' : θ.inv ≫ r.r ≫ r.i ≫ θ.hom = r'.r ≫ r'.i := by
      rw [h, Iso.inv_hom_id_assoc]
    calc (r'.i ≫ θ.inv ≫ r.r) ≫ r.i ≫ θ.hom ≫ r'.r
        = r'.i ≫ (θ.inv ≫ r.r ≫ r.i ≫ θ.hom) ≫ r'.r := by simp only [Category.assoc]
      _ = 𝟙 Y' := by
        rw [h']
        simp only [Category.assoc, r'.retract_assoc, r'.retract]

/-- The image of a degree-`0` idempotent cocycle under a morphism of dg rings. -/
@[simps]
def DGIdempotent.map {A B : Type*} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]
    (φ : B →ᵈᵍ+* A) (e : DGIdempotent B) : DGIdempotent A where
  val := φ e.val
  mem_zero := φ.map_mem e.mem_zero
  mul_self := by rw [← map_mul, e.mul_self]
  d_eq_zero := by rw [← φ.map_d, e.d_eq_zero, map_zero]

namespace CatModule

variable {B : Type u} [Ring B] [DGAddCommGroup B] [DGRing B]

/-- The isomorphism between `B`, as a dg module over `SingleObj B`, and the (lifted)
representable module. -/
noncomputable abbrev selfIsoULiftRepresentable (B : Type u) [Ring B] [DGAddCommGroup B]
    [DGRing B] :
    DGModuleCat.toCatModuleObj (DGModuleCat.of B B) ≅
      ulift.{u} (representable (SingleObj.star B)) :=
  IsCornerGenerator.isoOfGen isCornerGenerator_toCatModuleObj_self
    (isCornerGenerator_representable (SingleObj.star B)).ulift

/-- For a degree-`0` idempotent cocycle `e`, the module `B e` over `SingleObj B` is a retract of
the (lifted) representable module. -/
noncomputable def leftCornerRetract (e : DGIdempotent B) :
    Retract (DGModuleCat.toCatModuleObj (DGModuleCat.of B e.LeftCorner))
      (ulift.{u} (representable (SingleObj.star B))) where
  i := (DGModuleCat.toCatModule B).map (DGModuleCat.ofHom e.leftCornerInclusion) ≫
    (selfIsoULiftRepresentable B).hom
  r := (selfIsoULiftRepresentable B).inv ≫
    (DGModuleCat.toCatModule B).map (DGModuleCat.ofHom e.leftCornerProjection)
  retract := by
    have h : DGModuleCat.ofHom e.leftCornerInclusion ≫ DGModuleCat.ofHom e.leftCornerProjection =
        𝟙 (DGModuleCat.of B e.LeftCorner) :=
      DGModuleCat.hom_ext e.leftCornerProjection_comp_inclusion
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, h,
      CategoryTheory.Functor.map_id]
    rfl

theorem leftCornerRetract_idem_app (e : DGIdempotent B) :
    ((leftCornerRetract e).r ≫ (leftCornerRetract e).i).app (SingleObj.star B)
      (ULift.up (𝟙 (SingleObj.star B))) =
        ULift.up (e.val : SingleObj.star B ⟶ SingleObj.star B) := by
  have hU := (isCornerGenerator_representable (SingleObj.star B)).ulift.{u}
  have hR := isCornerGenerator_toCatModuleObj_self (A := B)
  rw [comp_app]
  change (selfIsoULiftRepresentable B).hom.app _ ((e.leftCornerInclusion)
    (e.leftCornerProjection ((selfIsoULiftRepresentable B).inv.app _
      (ULift.up (𝟙 (SingleObj.star B)))))) = _
  have h1 : (selfIsoULiftRepresentable B).inv.app (SingleObj.star B)
      (ULift.up (𝟙 (SingleObj.star B))) = (1 : B) :=
    hU.homOfCocycle_app_gen _ hR.mem_grading hR.d_eq_zero
  rw [h1]
  have h3 : (e.leftCornerInclusion (e.leftCornerProjection 1) :
      (DGModuleCat.toCatModuleObj (DGModuleCat.of B B)).obj (SingleObj.star B)) =
      (show SingleObj.star B ⟶ SingleObj.star B from e.val) •
        (show (DGModuleCat.toCatModuleObj (DGModuleCat.of B B)).obj (SingleObj.star B) from
          (1 : B)) := by
    change 1 * e.val = e.val * 1
    rw [one_mul, mul_one]
  rw [h3, Hom.map_smul]
  have h2 : (selfIsoULiftRepresentable B).hom.app (SingleObj.star B)
      (show (DGModuleCat.toCatModuleObj (DGModuleCat.of B B)).obj (SingleObj.star B) from
        (1 : B)) = ULift.up (𝟙 (SingleObj.star B)) :=
    hR.homOfCocycle_app_gen _ hU.mem_grading hU.d_eq_zero
  rw [h2]
  exact ULift.ext _ _
    (Category.id_comp (X := SingleObj.star B) (e.val : SingleObj.star B ⟶ SingleObj.star B))

namespace DerivedCategory

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] (φ : B →ᵈᵍ+* A)

/-- Induction along `SingleObj B ⥤ SingleObj A` on the lifted representable modules is
compatible with the idempotents of `B e` and `A φ(e)`. -/
theorem induction_map_leftCornerRetract_idem (e : DGIdempotent B) :
    (CatModule.induction.{u} φ.singleObjFunctor).map
        ((leftCornerRetract e).r ≫ (leftCornerRetract e).i) ≫
      (inductionULiftRepresentableIso.{u} φ.singleObjFunctor (SingleObj.star B)).hom =
    (inductionULiftRepresentableIso.{u} φ.singleObjFunctor (SingleObj.star B)).hom ≫
      ((leftCornerRetract (e.map φ)).r ≫ (leftCornerRetract (e.map φ)).i) := by
  set ι := inductionULiftRepresentableIso.{u} φ.singleObjFunctor (SingleObj.star B)
  rw [← Iso.inv_comp_eq]
  refine (isCornerGenerator_representable (SingleObj.star A)).ulift.{u}.ext_hom ?_
  let t := CatTensorProduct.tmul (N := (CatBimodule.ofFunctor φ.singleObjFunctor).right
    (SingleObj.star A)) (SingleObj.star B) (𝟙 (SingleObj.star A))
      (show (ulift.{u} (representable (SingleObj.star B))).obj (SingleObj.star B) from
        ULift.up (𝟙 (SingleObj.star B)))
  have ht : ι.hom.app (SingleObj.star A) t = ULift.up (𝟙 (SingleObj.star A)) := by
    refine ULift.ext _ _ ?_
    erw [inductionULiftRepresentableIso_hom_app_tmul]
    exact (Category.comp_id (X := SingleObj.star A)
      (φ.singleObjFunctor.map (𝟙 (SingleObj.star B)))).trans (φ.singleObjFunctor.map_id _)
  have ht' : ι.inv.app (SingleObj.star A) (ULift.up (𝟙 (SingleObj.star A))) = t := by
    rw [← ht]
    change (ι.hom ≫ ι.inv).app (SingleObj.star A) t = t
    rw [ι.hom_inv_id]
    rfl
  rw [comp_app, comp_app]
  erw [ht']
  rw [induction_map_app_tmul]
  erw [leftCornerRetract_idem_app, leftCornerRetract_idem_app]
  refine ULift.ext _ _ ?_
  erw [inductionULiftRepresentableIso_hom_app_tmul]
  exact Category.comp_id (X := SingleObj.star A) (φ e.val : SingleObj.star A ⟶ SingleObj.star A)

variable [HasDerivedCategory.{w₁, u} (SingleObj B)] [HasDerivedCategory.{w₂, u} (SingleObj A)]

/-- Derived induction along `SingleObj B ⥤ SingleObj A` sends `B e` to `A φ(e)`: both are the
direct summands cut out by corresponding idempotents of the representable modules. -/
noncomputable def inductionLeftCornerIso (e : DGIdempotent B) :
    (induction.{w₁, w₂, u} φ.singleObjFunctor).obj
        (Q.obj (DGModuleCat.toCatModuleObj (DGModuleCat.of B e.LeftCorner))) ≅
      Q.obj (DGModuleCat.toCatModuleObj (DGModuleCat.of A (e.map φ).LeftCorner)) :=
  let hU := (isCornerGenerator_representable (SingleObj.star B)).ulift.{u}.isKProjective
  Retract.isoOfConj (((leftCornerRetract e).map Q).map (induction.{w₁, w₂, u} φ.singleObjFunctor))
    ((leftCornerRetract (e.map φ)).map Q)
    ((inductionObjIso φ.singleObjFunctor hU).symm ≪≫
      Q.mapIso (inductionULiftRepresentableIso.{u} φ.singleObjFunctor (SingleObj.star B))) (by
      have nat := inductionObjIso_hom_naturality φ.singleObjFunctor hU hU
        ((leftCornerRetract e).r ≫ (leftCornerRetract e).i)
      have mod := induction_map_leftCornerRetract_idem φ e
      have nat' : (induction.{w₁, w₂, u} φ.singleObjFunctor).map
          (Q.map ((leftCornerRetract e).r ≫ (leftCornerRetract e).i)) ≫
            (inductionObjIso φ.singleObjFunctor hU).inv =
          (inductionObjIso φ.singleObjFunctor hU).inv ≫ Q.map
            ((CatModule.induction.{u} φ.singleObjFunctor).map
              ((leftCornerRetract e).r ≫ (leftCornerRetract e).i)) := by
        rw [Iso.comp_inv_eq, Category.assoc, nat, Iso.inv_hom_id_assoc]
      simp only [Retract.map_r, Retract.map_i, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
        Category.assoc]
      rw [← Functor.map_comp_assoc, ← Q.map_comp, reassoc_of% nat', ← Q.map_comp, mod,
        Q.map_comp, Q.map_comp])

end DerivedCategory

end CatModule

namespace DGRing.K0

section LeftCorner

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [HasDerivedCategory.{w₂, u} A]

omit [HasDerivedCategory.{w₂, u} A] in
/-- The module `A e` over `SingleObj A` is compact in `D(SingleObj A)`. -/
theorem isCompact_Q_toCatModuleObj_leftCorner
    [CatModule.HasDerivedCategory.{w₁, u} (SingleObj A)] (e : DGIdempotent A) :
    IsCompact.{u} (CatModule.DerivedCategory.Q.obj
      (DGModuleCat.toCatModuleObj (DGModuleCat.of A e.LeftCorner))) :=
  IsCompact.of_retract ((CatModule.leftCornerRetract e).map CatModule.DerivedCategory.Q)
    (CatModule.DerivedCategory.isCompact_Q_representable _)

/-- Under `K₀(SingleObj A) ≃+ K₀(A)`, the class of the module `A e` over `SingleObj A` is
`[A e]`. -/
theorem singleObjEquiv_leftCorner [CatModule.HasDerivedCategory.{w₁, u} (SingleObj A)]
    (e : DGIdempotent A) :
    singleObjEquiv A (DG.K0.mk ⟨CatModule.DerivedCategory.Q.obj
      (DGModuleCat.toCatModuleObj (DGModuleCat.of A e.LeftCorner)),
        isCompact_Q_toCatModuleObj_leftCorner e⟩) = leftCorner e := by
  rw [singleObjEquiv, DG.K0.compactMapEquiv_mk]
  exact DG.K0.mk_eq_of_iso_obj (DerivedCategory.singleObjEquivalenceObjIso _)

/-- `K₀(φ) [B e] = [A φ(e)]` for a morphism of dg rings `φ : B → A` and a degree-`0` idempotent
cocycle `e` of `B`. -/
theorem map_leftCorner {B : Type u} [Ring B] [DGAddCommGroup B] [DGRing B]
    [HasDerivedCategory.{w₁, u} B] (φ : B →ᵈᵍ+* A) (e : DGIdempotent B) :
    map φ (leftCorner e) = leftCorner (e.map φ) := by
  let := CatModule.HasDerivedCategory.small.{u} (SingleObj B)
  let := CatModule.HasDerivedCategory.small.{u} (SingleObj A)
  change singleObjEquiv A (DGCategory.K0.map φ.singleObjFunctor
    ((singleObjEquiv B).symm (leftCorner e))) = _
  rw [(AddEquiv.symm_apply_eq _).mpr (singleObjEquiv_leftCorner e).symm, DGCategory.K0.map_mk,
    ← singleObjEquiv_leftCorner (e.map φ)]
  congr 1
  exact DG.K0.mk_eq_of_iso_obj (CatModule.DerivedCategory.inductionLeftCornerIso φ e)

end LeftCorner

end DGRing.K0

end DG
