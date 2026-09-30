import DG.Category.Homotopy.HomBimodule
import DG.Category.Homotopy.Triangulated

set_option backward.isDefEq.respectTransparency false

/-!
# The Hom functor of a dg bimodule on homotopy categories

Let `B` be a dg `(D, C)`-bimodule. The Hom functor `HOM_D(B, -) : CatModule D ⥤ CatModule C`
(`DG.CatBimodule.homFunctor`) sends mapping cones to mapping cones: the cochains `fst`, `snd`,
`inl`, `inr` of the cone of `φ : M ⟶ N` are sent to cochains satisfying the relations which
characterize the cone of `HOM_D(B, φ)`, which gives an isomorphism
`DG.CatBimodule.homConeIso B φ : HOM_D(B, cone φ) ≅ cone (HOM_D(B, φ))`, compatible with the
standard triangles (`DG.CatBimodule.homTriangleIso`). Since it also preserves homotopies and
commutes with the shifts (`DG/Category/Homotopy/HomBimodule.lean`), it induces a triangulated
functor on homotopy categories
`DG.CatModule.HomotopyCategory.homFunctor B : HomotopyCategory D ⥤ HomotopyCategory C`
(`DG.CatModule.HomotopyCategory.homFunctor_isTriangulated`).
-/

open CategoryTheory Pretriangulated

universe w v₁ v₂ u₁ u₂

noncomputable section

namespace DG

open DGOpposite
open scoped CatModule
open CatModule (HOM)

namespace CatBimodule

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] [DGCategory D]

section Cone

variable (B : CatBimodule.{w} D C) {M N : CatModule.{w} D} (φ : M ⟶ N)

/-- The `1`-cocycle `HOM_D(B, fst φ)`. -/
def homConeFst : CatModule.Cocycle (B.homObj (CatModule.cone φ)) (B.homObj M) 1 :=
  CatModule.Cocycle.mk (B.homCochain (CatModule.cone.fst φ).1) 2 rfl (by
    rw [homCochain_δ, CatModule.Cocycle.δ_eq_zero, homCochain_zero])

/-- The morphism `HOM_D(B, cone φ) ⟶ cone (HOM_D(B, φ))`, `w ↦ (fst ∘ w, snd ∘ w)`. -/
def homConeHom : B.homObj (CatModule.cone φ) ⟶ CatModule.cone (B.homMap φ) :=
  CatModule.cone.lift (B.homMap φ) (B.homConeFst φ) (B.homCochain (CatModule.cone.snd φ)) (by
    rw [homCochain_δ, CatModule.cone.δ_snd, homCochain_neg, homCochain_comp, homCochain_ofHom]
    exact neg_add_cancel _)

/-- The morphism `cone (HOM_D(B, φ)) ⟶ HOM_D(B, cone φ)`, `(a, b) ↦ inl ∘ a + inr ∘ b`. -/
def homConeInv : CatModule.cone (B.homMap φ) ⟶ B.homObj (CatModule.cone φ) :=
  CatModule.cone.desc (B.homMap φ) (B.homCochain (CatModule.cone.inl φ))
    (B.homMap (CatModule.cone.inr φ)) (by
      rw [homCochain_δ, CatModule.cone.δ_inl, homCochain_ofHom]
      congr 1
      exact (B.homFunctor).map_comp φ (CatModule.cone.inr φ))

@[reassoc (attr := simp)]
theorem homConeHom_inv : B.homConeHom φ ≫ B.homConeInv φ = 𝟙 _ := by
  apply CatModule.Cochain.ofHom_injective
  rw [CatModule.Cochain.ofHom_comp, homConeInv, homConeHom, CatModule.cone.ofHom_desc,
    CatModule.cone.ofHom_lift, CatModule.cone.liftCochain_descCochain, homConeFst,
    CatModule.Cocycle.mk_coe, ← homCochain_ofHom, ← homCochain_comp, ← homCochain_comp,
    ← homCochain_add, CatModule.cone.id, homCochain_id, CatModule.Cochain.ofHom_id]

@[reassoc (attr := simp)]
theorem homConeInv_hom : B.homConeInv φ ≫ B.homConeHom φ = 𝟙 _ := by
  refine CatModule.hom_ext fun Y p => ?_
  rw [CatModule.comp_app, CatModule.id_app]
  refine CatModule.cone.ext_to ?_ ?_
  · rw [homConeHom, CatModule.cone.lift_fst_apply, homConeFst, CatModule.Cocycle.mk_coe,
      homCochain_app, homConeInv, CatModule.cone.desc_apply, homCochain_app, homMap_app,
      map_add, HOM.postcompCochain_postcompCochain, HOM.postcompCochain_postcompCochain,
      HOM.postcompCochain_eq_self (neg_add_cancel 1) (fun _ _ => rfl),
      HOM.postcompCochain_eq_zero (fun _ _ => rfl), add_zero]
  · rw [homConeHom, CatModule.cone.lift_snd_apply, homCochain_app, homConeInv,
      CatModule.cone.desc_apply, homCochain_app, homMap_app, map_add,
      HOM.postcompCochain_postcompCochain,
      HOM.postcompCochain_postcompCochain,
      HOM.postcompCochain_eq_self (add_zero 0) (fun _ _ => rfl),
      HOM.postcompCochain_eq_zero (fun _ _ => rfl), zero_add]

/-- The Hom functor of a dg bimodule sends mapping cones to mapping cones:
`HOM_D(B, cone φ) ≅ cone (HOM_D(B, φ))`. -/
@[simps]
def homConeIso : B.homObj (CatModule.cone φ) ≅ CatModule.cone (B.homMap φ) where
  hom := B.homConeHom φ
  inv := B.homConeInv φ

theorem inr_homConeHom : B.homMap (CatModule.cone.inr φ) ≫ B.homConeHom φ =
    CatModule.cone.inr (B.homMap φ) := by
  refine CatModule.hom_ext fun Y w => ?_
  rw [CatModule.comp_app]
  refine CatModule.cone.ext_to ?_ ?_
  · rw [homConeHom, CatModule.cone.lift_fst_apply, homConeFst, CatModule.Cocycle.mk_coe,
      homCochain_app, homMap_app, HOM.postcompCochain_postcompCochain,
      HOM.postcompCochain_eq_zero (fun _ _ => rfl),
      CatModule.cone.inr_fst_apply]
  · rw [homConeHom, CatModule.cone.lift_snd_apply, homCochain_app, homMap_app,
      HOM.postcompCochain_postcompCochain,
      HOM.postcompCochain_eq_self (add_zero 0) (fun _ _ => rfl),
      CatModule.cone.inr_snd_apply]

theorem homConeHom_fstHom : B.homConeHom φ ≫ CatModule.cone.fstHom (B.homMap φ) =
    B.homMap (CatModule.cone.fstHom φ) ≫ B.homShiftHom 1 M := by
  refine CatModule.hom_ext fun Y w => ?_
  rw [CatModule.comp_app, CatModule.comp_app, homShiftHom_app, homMap_app,
    HOM.postcompCochain_postcompCochain]
  refine (CatModule.shift.mk_unmk (n := 1) _).symm.trans ?_
  rw [← CatModule.cone.fst_apply, homConeHom, CatModule.cone.lift_fst_apply, homConeFst,
    CatModule.Cocycle.mk_coe, homCochain_app]
  refine congrArg (CatModule.shift.mk (M := B.homObj M) (X := Y) 1) ?_
  apply HOM.postcompCochain_congr
  · omega
  · intro _ _
    rfl

/-- The Hom functor of a dg bimodule sends the standard triangle of `φ` to the standard
triangle of `HOM_D(B, φ)`. -/
def homTriangleIso :
    (B.homFunctor).mapTriangle.obj (CatModule.cone.triangle φ) ≅
      CatModule.cone.triangle (B.homMap φ) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (B.homConeIso φ)
    (by
      change B.homMap φ ≫ 𝟙 _ = 𝟙 _ ≫ B.homMap φ
      rw [Category.comp_id, Category.id_comp])
    (by
      change B.homMap (CatModule.cone.inr φ) ≫ B.homConeHom φ =
        𝟙 _ ≫ CatModule.cone.inr (B.homMap φ)
      rw [Category.id_comp, inr_homConeHom])
    (by
      change (B.homMap (-CatModule.cone.fstHom φ) ≫ B.homShiftHom 1 M) ≫
          (shiftFunctor (CatModule.{max u₂ w} C) (1 : ℤ)).map (𝟙 _) =
        B.homConeHom φ ≫ (-CatModule.cone.fstHom (B.homMap φ))
      rw [CategoryTheory.Functor.map_id]
      refine (Category.comp_id _).trans ?_
      rw [Preadditive.comp_neg, homConeHom_fstHom, ← Preadditive.neg_comp]
      congr 1
      exact (B.homFunctor).map_neg (f := CatModule.cone.fstHom φ))

end Cone

end CatBimodule

namespace CatModule

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] [DGCategory D] (B : CatBimodule.{w} D C)

namespace HomotopyCategory

/-- The Hom functor of a dg bimodule, on homotopy categories. -/
def homFunctor : HomotopyCategory.{w} D ⥤ HomotopyCategory.{max u₂ w} C :=
  CategoryTheory.Quotient.lift _ (B.homFunctor ⋙ quotient C)
    (fun _ _ _ _ h => eq_of_homotopy _ _ (h.some.homMap B))

/-- The Hom functor on homotopy categories is induced by the Hom functor on dg modules. -/
def homFunctorFactors : quotient.{w} D ⋙ homFunctor B ≅ B.homFunctor ⋙ quotient C :=
  CategoryTheory.Quotient.lift.isLift _ _ _

omit [DGCategory D] in
@[simp]
theorem homFunctor_map_quotient_map {M N : CatModule.{w} D} (f : M ⟶ N) :
    (homFunctor B).map ((quotient D).map f) = (quotient C).map (B.homMap f) :=
  rfl

instance : (homFunctor B).Additive := by
  have := Functor.additive_of_iso (homFunctorFactors B).symm
  exact Functor.additive_of_full_essSurj_comp (quotient D) _

/-- The Hom functor on homotopy categories commutes with the shifts. -/
instance homFunctor_commShift : (homFunctor B).CommShift ℤ :=
  CategoryTheory.Quotient.liftCommShift (B.homFunctor ⋙ quotient C) (homotopic.{w} D) ℤ _

instance : NatTrans.CommShift (homFunctorFactors B).hom ℤ :=
  CategoryTheory.Quotient.liftCommShift_compatibility (B.homFunctor ⋙ quotient C)
    (homotopic.{w} D) ℤ _

/-- The image of the standard triangle `triangleh φ` under the Hom functor is the standard
triangle of `HOM_D(B, φ)`. -/
def homMapTrianglehIso {M N : CatModule.{w} D} (φ : M ⟶ N) :
    (homFunctor B).mapTriangle.obj (cone.triangleh φ) ≅ cone.triangleh (B.homMap φ) :=
  (Functor.mapTriangleCompIso _ _).symm.app _ ≪≫
    (Functor.mapTriangleIso (homFunctorFactors B)).app _ ≪≫
    (Functor.mapTriangleCompIso _ _).app _ ≪≫
    (quotient C).mapTriangle.mapIso (B.homTriangleIso φ)

/-- The Hom functor of a dg bimodule is a triangulated functor on homotopy categories. -/
instance homFunctor_isTriangulated : (homFunctor B).IsTriangulated where
  map_distinguished := by
    rintro T ⟨M, N, φ, ⟨e⟩⟩
    exact ⟨_, _, _, ⟨(homFunctor B).mapTriangle.mapIso e ≪≫ homMapTrianglehIso B φ⟩⟩

end HomotopyCategory

end CatModule

end DG
