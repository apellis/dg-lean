import DG.Category.Derived.Restriction

/-!
# Functoriality of restriction along dg functors

Restriction of dg modules along dg functors (`DG.CatModule.precomp`) is contravariantly
functorial in the dg functor, up to canonical isomorphism, on dg modules, on homotopy categories
and on derived categories:

* `precomp (F ⋙ G) ≅ precomp G ⋙ precomp F` and `precomp (𝟭 C) ≅ 𝟭`
  (`DG.CatModule.precompCompIso`, `DG.CatModule.precompIdIso`, the identity on elements);
* a natural transformation `α : F ⟶ G` of dg functors whose components are cocycles of
  degree `0` (a morphism of dg functors in the sense of `Z⁰`) induces
  `precomp F ⟶ precomp G`, `m ↦ α_X • m` (`DG.CatModule.precompNatTrans`), and a natural
  isomorphism with such components induces `precomp F ≅ precomp G`
  (`DG.CatModule.precompNatIso`).

The corresponding statements on homotopy categories are in the namespace
`DG.CatModule.HomotopyCategory` and those on derived categories (for
`DG.CatModule.DerivedCategory.restrict`) in the namespace `DG.CatModule.DerivedCategory`:
`restrictCompIso`, `restrictIdIso`, `restrictNatIso`. They are obtained from the statements on
dg modules through the universal properties of the quotient `CatModule C ⥤ H(C)` and of the
localization `H(C) ⥤ D(C)`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Category

universe w₁ w₂ w₃ w v₁ v₂ v₃ u₁ u₂ u₃

namespace DG

namespace CatModule

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [∀ X Y : D, DGAddCommGroup (X ⟶ Y)]
  {E : Type u₃} [Category.{v₃} E] [Preadditive E] [∀ X Y : E, DGAddCommGroup (X ⟶ Y)]

/-! ### Dg modules -/

section Module

variable (F : C ⥤ D) [F.Additive] [F.IsDGFunctor] (G : D ⥤ E) [G.Additive] [G.IsDGFunctor]

/-- Restriction along a composite `F ⋙ G` is restriction along `G` followed by restriction
along `F` (the identity on elements). -/
def precompCompIso : precomp.{w} (F ⋙ G) ≅ precomp G ⋙ precomp F :=
  NatIso.ofComponents
    (fun _ => isoMk (fun _ => AddEquiv.refl _) Iff.rfl (fun _ => rfl) (fun _ _ => rfl))
    (fun _ => hom_ext fun _ _ => rfl)

@[simp]
theorem precompCompIso_hom_app_app (M : CatModule.{w} E) (X : C)
    (m : ((precomp (F ⋙ G)).obj M).obj X) : ((precompCompIso F G).hom.app M).app X m = m :=
  rfl

variable (C) in
/-- Restriction along the identity functor is the identity (on elements). -/
def precompIdIso : precomp.{w} (𝟭 C) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun _ => isoMk (fun _ => AddEquiv.refl _) Iff.rfl (fun _ => rfl) (fun _ _ => rfl))
    (fun _ => hom_ext fun _ _ => rfl)

variable {F} {F' F'' : C ⥤ D} [F'.Additive] [F'.IsDGFunctor] [F''.Additive] [F''.IsDGFunctor]

/-- A natural transformation `α : F ⟶ F'` of dg functors whose components are cocycles of
degree `0` induces a morphism `precomp F ⟶ precomp F'`, `m ↦ α_X • m` at the object `X`. -/
@[simps]
def precompNatTrans (α : F ⟶ F') (hα : ∀ X, α.app X ∈ grading 0) (hdα : ∀ X, d (α.app X) = 0) :
    precomp.{w} F ⟶ precomp F' where
  app M :=
    { app := fun X => M.act (α.app X)
      map_mem' := fun {X n m} hm => by
        have := smul_mem_grading (M := M) (hα X) (m := (m : M.obj (F.obj X))) hm
        rwa [zero_add] at this
      map_d' := fun {X} m => by
        change M.act (α.app X) (d (m : M.obj (F.obj X))) = d (M.act (α.app X) m)
        rw [act_apply, act_apply, d_smul_of_d_eq_zero (hα X) (hdα X), koszulSign_zero, one_smul]
      map_smul' := fun {X Y} f m => by
        change M.act (α.app Y) (M.act (F.map f) (m : M.obj (F.obj X))) =
          M.act (F'.map f) (M.act (α.app X) m)
        rw [act_apply, act_apply, act_apply, act_apply, ← comp_smul, ← comp_smul,
          α.naturality] }
  naturality _ _ φ := hom_ext fun X m => (φ.map_smul (α.app X) m).symm

theorem precompNatTrans_comp (α : F ⟶ F') (β : F' ⟶ F'') (hα : ∀ X, α.app X ∈ grading 0)
    (hdα : ∀ X, d (α.app X) = 0) (hβ : ∀ X, β.app X ∈ grading 0)
    (hdβ : ∀ X, d (β.app X) = 0) (hαβ : ∀ X, (α ≫ β).app X ∈ grading 0)
    (hdαβ : ∀ X, d ((α ≫ β).app X) = 0) :
    precompNatTrans.{w} (α ≫ β) hαβ hdαβ = precompNatTrans α hα hdα ≫ precompNatTrans β hβ hdβ := by
  ext M : 2
  exact hom_ext fun X m => comp_smul (α.app X) (β.app X) m

theorem precompNatTrans_id (h : ∀ X, (𝟙 F : F ⟶ F).app X ∈ grading 0)
    (hd : ∀ X, d ((𝟙 F : F ⟶ F).app X) = 0) :
    precompNatTrans.{w} (𝟙 F) h hd = 𝟙 _ := by
  ext M : 2
  exact hom_ext fun X m => id_smul (M := M) m

/-- A natural isomorphism `e : F ≅ F'` of dg functors whose components (and those of its
inverse) are cocycles of degree `0` induces `precomp F ≅ precomp F'`. -/
@[simps]
def precompNatIso (e : F ≅ F') (h : ∀ X, e.hom.app X ∈ grading 0)
    (hd : ∀ X, d (e.hom.app X) = 0) (h' : ∀ X, e.inv.app X ∈ grading 0)
    (hd' : ∀ X, d (e.inv.app X) = 0) : precomp.{w} F ≅ precomp F' where
  hom := precompNatTrans e.hom h hd
  inv := precompNatTrans e.inv h' hd'
  hom_inv_id := by
    ext M : 2
    refine hom_ext fun X m => ?_
    change M.act (e.inv.app X) (M.act (e.hom.app X) (m : M.obj (F.obj X))) = m
    rw [act_apply, act_apply, ← comp_smul, e.hom_inv_id_app, id_smul]
  inv_hom_id := by
    ext M : 2
    refine hom_ext fun X m => ?_
    change M.act (e.hom.app X) (M.act (e.inv.app X) (m : M.obj (F'.obj X))) = m
    rw [act_apply, act_apply, ← comp_smul, e.inv_hom_id_app, id_smul]

end Module

/-! ### Homotopy categories -/

namespace HomotopyCategory

section

variable (F : C ⥤ D) [F.Additive] [F.IsDGFunctor] (G : D ⥤ E) [G.Additive] [G.IsDGFunctor]

/-- Restriction along `F ⋙ G` on homotopy categories is restriction along `G` followed by
restriction along `F`. -/
noncomputable def precompCompIso : precomp.{w} (F ⋙ G) ≅ precomp G ⋙ precomp F :=
  Quotient.natIsoLift _ (precompFactors (F ⋙ G) ≪≫
    Functor.isoWhiskerRight (CatModule.precompCompIso F G) (quotient C) ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (precompFactors F).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (precompFactors G).symm _ ≪≫ Functor.associator _ _ _)

variable (C) in
/-- Restriction along the identity functor on homotopy categories is the identity. -/
noncomputable def precompIdIso : precomp.{w} (𝟭 C) ≅ 𝟭 _ :=
  Quotient.natIsoLift _ (precompFactors (𝟭 C) ≪≫
    Functor.isoWhiskerRight (CatModule.precompIdIso C) (quotient C) ≪≫ Functor.leftUnitor _ ≪≫
    (Functor.rightUnitor _).symm)

variable {F} {F' : C ⥤ D} [F'.Additive] [F'.IsDGFunctor]

/-- A natural isomorphism of dg functors whose components (and those of its inverse) are
cocycles of degree `0` induces an isomorphism of the restriction functors on homotopy
categories. -/
noncomputable def precompNatIso (e : F ≅ F') (h : ∀ X, e.hom.app X ∈ grading 0)
    (hd : ∀ X, d (e.hom.app X) = 0) (h' : ∀ X, e.inv.app X ∈ grading 0)
    (hd' : ∀ X, d (e.inv.app X) = 0) : precomp.{w} F ≅ precomp F' :=
  Quotient.natIsoLift _ (precompFactors F ≪≫
    Functor.isoWhiskerRight (CatModule.precompNatIso e h hd h' hd') (quotient C) ≪≫
    (precompFactors F').symm)

end

end HomotopyCategory

/-! ### Derived categories -/

namespace DerivedCategory

variable [DGCategory C] [DGCategory D] [DGCategory E]

section

variable [HasDerivedCategory.{w₁, w} C] [HasDerivedCategory.{w₂, w} D]
  [HasDerivedCategory.{w₃, w} E]
  (F : C ⥤ D) [F.Additive] [F.IsDGFunctor] (G : D ⥤ E) [G.Additive] [G.IsDGFunctor]

/-- Restriction along `F ⋙ G` on derived categories is restriction along `G` followed by
restriction along `F`. -/
noncomputable def restrictCompIso : restrict (F ⋙ G) ≅ restrict G ⋙ restrict F :=
  ((Functor.whiskeringLeft _ _ _).obj Qh).preimageIso (QhCompRestrictIso (F ⋙ G) ≪≫
    Functor.isoWhiskerRight (HomotopyCategory.precompCompIso F G) Qh ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (QhCompRestrictIso F).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (QhCompRestrictIso G).symm _ ≪≫ Functor.associator _ _ _)

variable (C) in
/-- Restriction along the identity functor on derived categories is the identity. -/
noncomputable def restrictIdIso : restrict (𝟭 C) ≅ 𝟭 (DerivedCategory C) :=
  ((Functor.whiskeringLeft _ _ _).obj Qh).preimageIso (QhCompRestrictIso (𝟭 C) ≪≫
    Functor.isoWhiskerRight (HomotopyCategory.precompIdIso C) Qh ≪≫ Functor.leftUnitor _ ≪≫
    (Functor.rightUnitor _).symm)

variable {F} {F' : C ⥤ D} [F'.Additive] [F'.IsDGFunctor]

/-- A natural isomorphism of dg functors whose components (and those of its inverse) are
cocycles of degree `0` induces an isomorphism of the restriction functors on derived
categories. -/
noncomputable def restrictNatIso (e : F ≅ F') (h : ∀ X, e.hom.app X ∈ grading 0)
    (hd : ∀ X, d (e.hom.app X) = 0) (h' : ∀ X, e.inv.app X ∈ grading 0)
    (hd' : ∀ X, d (e.inv.app X) = 0) : restrict F ≅ restrict F' :=
  ((Functor.whiskeringLeft _ _ _).obj Qh).preimageIso (QhCompRestrictIso F ≪≫
    Functor.isoWhiskerRight (HomotopyCategory.precompNatIso e h hd h' hd') Qh ≪≫
    (QhCompRestrictIso F').symm)

end

end DerivedCategory

end CatModule

end DG
