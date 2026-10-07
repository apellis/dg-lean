import DG.Category.Derived.TensorInduction
import DG.Derived.Perfect
import DG.Homotopy.ChangeOfRings

/-!
# Derived induction along a morphism of dg rings on K-projective modules

Let `φ : B → A` be a morphism of dg rings. Derived induction `φ^* : D(B) ⥤ D(A)`
(`DG.DGRingHom.derivedInduction`) is defined through the one-object dg categories `SingleObj B`,
`SingleObj A`. Here it is compared with extension of scalars `A ⊗_B - : DGModuleCat B ⥤
DGModuleCat A` (`DG.DGModuleCat.extendScalars`):

* `DG.DGRingHom.toDGModuleCatCompRestrictScalarsIso`: under `CatModule (SingleObj A) ≌
  DGModuleCat A`, restriction along `SingleObj B ⥤ SingleObj A` is restriction of scalars
  (the identity on elements);
* `DG.DGRingHom.extendScalarsCompToCatModuleIso`: hence, by uniqueness of left adjoints,
  induction along `SingleObj B ⥤ SingleObj A` is extension of scalars;
* `DG.IsKProjective.toCatModuleObj`: a K-projective dg `B`-module is K-projective over
  `SingleObj B`;
* `DG.DGRingHom.derivedInductionObjIso`: **for a K-projective dg `B`-module `P`,
  `φ^*(P) ≅ A ⊗_B P` in `D(A)`**.

All dg rings and dg modules are in one universe `u`.
-/

open CategoryTheory

universe w₁ w₂ w₃ w₄ u

noncomputable section

namespace DG

variable {A B : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B]

/-! ### Induction along `SingleObj B ⥤ SingleObj A` is extension of scalars -/

namespace DGRingHom

variable (φ : B →ᵈᵍ+* A)

/-- Restriction along `SingleObj B ⥤ SingleObj A` is restriction of scalars along `φ`, under the
equivalences `CatModule (SingleObj _) ≌ DGModuleCat _` (identity on elements). -/
def toDGModuleCatCompRestrictScalarsIso :
    CatModule.toDGModuleCat.{u} A ⋙ DGModuleCat.restrictScalars.{u} φ ≅
      CatModule.precomp.{u} φ.singleObjFunctor ⋙ CatModule.toDGModuleCat.{u} B :=
  NatIso.ofComponents (fun _ =>
    { hom := DGModuleCat.Hom.mk
        { toFun := fun m => m
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          map_mem' := fun hm => hm
          map_d' := fun _ => rfl }
      inv := DGModuleCat.Hom.mk
        { toFun := fun m => m
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          map_mem' := fun hm => hm
          map_d' := fun _ => rfl }
      hom_inv_id := rfl
      inv_hom_id := rfl }) fun _ => rfl

/-- `A ⊗_B - ⋙ toCatModule ⊣ toDGModuleCat ⋙ restrictScalars φ`. -/
def extendScalarsCompToCatModuleAdj :
    DGModuleCat.extendScalars.{u} φ ⋙ DGModuleCat.toCatModule.{u} A ⊣
      CatModule.toDGModuleCat.{u} A ⋙ DGModuleCat.restrictScalars.{u} φ :=
  (DGModuleCat.extendRestrictScalarsAdj.{u} φ).comp
    (CatModule.singleObjEquivalence.{u} A).symm.toAdjunction

/-- `toCatModule ⋙ F_! ⊣ F^* ⋙ toDGModuleCat`, for `F = SingleObj B ⥤ SingleObj A`. -/
def toCatModuleCompInductionAdj :
    DGModuleCat.toCatModule.{u} B ⋙ CatModule.induction.{u} φ.singleObjFunctor ⊣
      CatModule.precomp.{u} φ.singleObjFunctor ⋙ CatModule.toDGModuleCat.{u} B :=
  (CatModule.singleObjEquivalence.{u} B).symm.toAdjunction.comp
    (CatModule.inductionAdjunction.{u} φ.singleObjFunctor)

/-- **Induction along `SingleObj B ⥤ SingleObj A` is extension of scalars along `φ`**: both are
left adjoint to restriction (`toDGModuleCatCompRestrictScalarsIso`). -/
def extendScalarsCompToCatModuleIso :
    DGModuleCat.extendScalars.{u} φ ⋙ DGModuleCat.toCatModule.{u} A ≅
      DGModuleCat.toCatModule.{u} B ⋙ CatModule.induction.{u} φ.singleObjFunctor :=
  (extendScalarsCompToCatModuleAdj φ).leftAdjointUniq
    ((toCatModuleCompInductionAdj φ).ofNatIsoRight (toDGModuleCatCompRestrictScalarsIso φ).symm)

end DGRingHom

/-! ### K-projective modules -/

omit [DGRing B] in
/-- A K-projective dg `B`-module is K-projective as a dg module over `SingleObj B`. -/
theorem IsKProjective.toCatModuleObj {P : DGModuleCat.{u} B} (hP : IsKProjective.{u} B P) :
    CatModule.IsKProjective (DGModuleCat.toCatModuleObj P) := by
  intro N hN f
  rw [CatModule.homotopic_iff_toDGModuleCat]
  let e : P →ᵈᵍ[B] (CatModule.toDGModuleCat.{u} B).obj (DGModuleCat.toCatModuleObj P) :=
    ((CatModule.singleObjEquivalence.{u} B).counitIso.inv.app P).hom
  let e' : (CatModule.toDGModuleCat.{u} B).obj (DGModuleCat.toCatModuleObj P) →ᵈᵍ[B] P :=
    ((CatModule.singleObjEquivalence.{u} B).counitIso.hom.app P).hom
  have hN' : DG.IsAcyclic ((CatModule.toDGModuleCat.{u} B).obj N) := hN (SingleObj.star B)
  have h := (hP.homotopic_zero hN' (((CatModule.toDGModuleCat B).map f).hom.comp e)).comp_left e'
  refine (Homotopic.of_eq ?_).trans (h.trans (Homotopic.of_eq ?_))
  · exact DGModuleHom.ext fun _ => rfl
  · exact DGModuleHom.ext fun _ => rfl

/-! ### Derived induction on K-projective modules -/

namespace DGRingHom

variable (φ : B →ᵈᵍ+* A)
  [CatModule.HasDerivedCategory.{w₁, u} (SingleObj B)]
  [CatModule.HasDerivedCategory.{w₂, u} (SingleObj A)]
  [DG.HasDerivedCategory.{w₃, u} B] [DG.HasDerivedCategory.{w₄, u} A]

/-- **Derived induction of a K-projective module is extension of scalars**: for a morphism of dg
rings `φ : B → A` and a K-projective dg `B`-module `P`, `φ^*(P) ≅ A ⊗_B P` in `D(A)`. -/
def derivedInductionObjIso {P : DGModuleCat.{u} B} (hP : IsKProjective.{u} B P) :
    φ.derivedInduction.{w₁, w₂, w₃, w₄}.obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((DGModuleCat.extendScalars.{u} φ).obj P) :=
  (CatModule.DerivedCategory.singleObjEquivalence A).functor.mapIso
      ((CatModule.DerivedCategory.induction.{w₁, w₂, u} φ.singleObjFunctor).mapIso
        ((CatModule.DerivedCategory.singleObjEquivalence B).inverse.mapIso
            (DerivedCategory.singleObjEquivalenceObjIso P).symm ≪≫
          ((CatModule.DerivedCategory.singleObjEquivalence B).unitIso.app _).symm) ≪≫
        (CatModule.DerivedCategory.inductionObjIso φ.singleObjFunctor hP.toCatModuleObj).symm ≪≫
        CatModule.DerivedCategory.Q.mapIso ((extendScalarsCompToCatModuleIso φ).app P).symm) ≪≫
    DerivedCategory.singleObjEquivalenceObjIso _

end DGRingHom

end DG

end
