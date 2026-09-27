import DG.Category.Tensor.Bimodule

/-!
# Induction of dg modules along a dg functor

For a dg functor `F : C ⥤ D` between dg categories, restriction along `F`
(`DG.CatModule.precomp F`, `F^* N = N ∘ F`) has a left adjoint, the induction
`F_! M = D(F -, -) ⊗_C M` (`DG.CatModule.induction F`). Here `D(F -, -)` is the dg
`(D, C)`-bimodule `(Y, X) ↦ D(F X, Y)` (`DG.CatBimodule.ofFunctor F`), with `D` acting by
postcomposition, `g • h = h ≫ g`, and `C` acting on the right through `F`, `h • f = F f ≫ h`;
so `(F_! M)(Y) = D(F -, Y) ⊗_C M` with `g • (h ⊗ m) = (h ≫ g) ⊗ m`.

## Main definitions and results

* `DG.CatBimodule.ofFunctor F`, `DG.CatModule.inductionObj F M`,
  `DG.CatModule.induction F : CatModule C ⥤ CatModule D`.
* `DG.CatModule.inductionAdjunction F : induction F ⊣ precomp F`: a morphism
  `Φ : F_! M ⟶ N` corresponds to `m ↦ Φ (𝟙 ⊗ m)`, and a morphism `ψ : M ⟶ F^* N` to
  `h ⊗ m ↦ h • ψ m` (`DG.CatModule.inductionHomEquiv`).
* `DG.CatModule.inductionRepresentableIso F X : F_! C(X, -) ≅ D(F X, -)`, from the co-Yoneda
  isomorphism `N ⊗_C C(X, -) ≅ N(X)` (`DG.CatTensorProduct.rid`).

## Universes

As for coproducts (`DG.Category.Coproducts`), `F_! M` lives in a universe containing the objects
of `C` and the morphisms of `D`: induction is a functor
`CatModule.{max u₁ v₂ w} C ⥤ CatModule.{max u₁ v₂ w} D`. The comparison with representable
modules is stated for `C : Type v` with `Category.{v} C` and `Category.{v} D`, so that both sides
are dg modules with values in `Type v`.
-/

open CategoryTheory

universe w v v₁ v₂ u₁ u₂

noncomputable section

namespace DG

open DGOpposite
open scoped CatModule

section General

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [∀ X Y : D, DGAddCommGroup (X ⟶ Y)]
  [DGCategory D]
  (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]

namespace CatBimodule

/-- The dg `(D, C)`-bimodule `D(F -, -)`: `(Y, X) ↦ D(F X, Y)`, with the left action of `D` by
postcomposition, `g • h = h ≫ g`, and the right action of `C` by precomposition with the image
under `F`, `h • f = F f ≫ h`. -/
def ofFunctor : CatBimodule.{v₂} D C where
  obj Y X := F.obj X ⟶ Y
  lact {_ _ X} := AddMonoidHom.mk' (fun g => Preadditive.rightComp (F.obj X) g) fun g g' => by
    ext h
    exact Preadditive.comp_add _ _ _ h g g'
  ract {Y _ _} := AddMonoidHom.mk' (fun f => Preadditive.leftComp Y (F.map f)) fun f f' => by
    ext h
    change F.map (f + f') ≫ h = F.map f ≫ h + F.map f' ≫ h
    rw [F.map_add, Preadditive.add_comp]
  lact_mem' hg hh := by
    rw [add_comm]
    exact comp_mem_grading hh hg
  lact_id' _ _ h := Category.comp_id h
  lact_comp' g g' h := (Category.assoc h g g').symm
  d_lact' hg h := d_comp h hg
  ract_mem' hf hh := by
    rw [add_comm]
    exact comp_mem_grading (F.map_mem_grading hf) hh
  ract_id' Y X h := by
    change F.map (𝟙 X) ≫ h = h
    rw [F.map_id, Category.id_comp]
  ract_comp' f f' h := by
    change F.map (f ≫ f') ≫ h = F.map f ≫ F.map f' ≫ h
    rw [F.map_comp, Category.assoc]
  d_ract' {_ _ _ j h} hh f := by
    change d (F.map f ≫ h) = F.map f ≫ d h + koszulSign j • (F.map (d f) ≫ h)
    rw [d_comp _ hh, F.map_d]
  lact_ract' g f h := Category.assoc (F.map f) h g

omit [DGCategory C] in
@[simp]
theorem ofFunctor_obj (Y : D) (X : C) : (ofFunctor F).obj Y X = (F.obj X ⟶ Y) := rfl

omit [DGCategory C] in
@[simp]
theorem ofFunctor_lact {Y Y' : D} {X : C} (g : Y ⟶ Y') (h : F.obj X ⟶ Y) :
    (ofFunctor F).lact g h = h ≫ g := rfl

omit [DGCategory C] in
@[simp]
theorem ofFunctor_ract {Y : D} {X X' : C} (f : X ⟶ X') (h : F.obj X' ⟶ Y) :
    (ofFunctor F).ract f h = F.map f ≫ h := rfl

end CatBimodule

namespace CatModule

open CatBimodule

/-- The induction `F_! M = D(F -, -) ⊗_C M` of a dg module `M` over `C` along a dg functor
`F : C ⥤ D`: the dg module `Y ↦ D(F -, Y) ⊗_C M` over `D`, with
`g • (h ⊗ m) = (h ≫ g) ⊗ m`. -/
def inductionObj (M : CatModule.{w} C) : CatModule.{max u₁ v₂ w} D :=
  (ofFunctor F).tensorObj M

/-- Induction along a dg functor `F : C ⥤ D`, `M ↦ D(F -, -) ⊗_C M`, the left adjoint of the
restriction `precomp F` (`DG.CatModule.inductionAdjunction`). -/
def induction : CatModule.{max u₁ v₂ w} C ⥤ CatModule.{max u₁ v₂ w} D :=
  (ofFunctor F).tensorFunctor

@[simp]
theorem induction_obj (M : CatModule.{max u₁ v₂ w} C) :
    (induction.{w} F).obj M = inductionObj F M := rfl

variable {F}

theorem inductionObj_obj (M : CatModule.{w} C) (Y : D) :
    (inductionObj F M).obj Y = CatTensorProduct ((ofFunctor F).right Y) M := rfl

/-- The action on `F_! M`: `g • (h ⊗ m) = (h ≫ g) ⊗ m`. -/
theorem inductionObj_act_tmul (M : CatModule.{w} C) {Y Y' : D} (g : Y ⟶ Y') (X : C)
    (h : F.obj X ⟶ Y) (m : M.obj X) :
    (inductionObj F M).act g (CatTensorProduct.tmul (N := (ofFunctor F).right Y) X h m) =
      CatTensorProduct.tmul (N := (ofFunctor F).right Y') X (h ≫ g) m :=
  (ofFunctor F).tensorAct_tmul M g X h m

theorem induction_map_app_tmul {M M' : CatModule.{max u₁ v₂ w} C} (ψ : M ⟶ M') (Y : D) (X : C)
    (h : F.obj X ⟶ Y) (m : M.obj X) :
    ((induction.{w} F).map ψ).app Y (CatTensorProduct.tmul (N := (ofFunctor F).right Y) X h m) =
      CatTensorProduct.tmul (N := (ofFunctor F).right Y) X h (ψ.app X m) :=
  (ofFunctor F).tensorMap_tmul ψ Y X h m

/-! ### The adjunction `F_! ⊣ F^*` -/

section Adjunction

variable {M : CatModule.{max u₁ v₂ w} C} {N : CatModule.{max u₁ v₂ w} D}

/-- The morphism `M ⟶ F^* N` attached to `Φ : F_! M ⟶ N`: `m ↦ Φ (𝟙 ⊗ m)`. -/
@[simps]
def inductionHomEquivToFun (Φ : inductionObj F M ⟶ N) : M ⟶ (precomp F).obj N where
  app X := (Φ.app (F.obj X)).comp
    (CatTensorProduct.tmulAddHom ((ofFunctor F).right (F.obj X)) M X (𝟙 (F.obj X)))
  map_mem' {X n m} hm := by
    have := CatTensorProduct.tmul_mem_grading (N := (ofFunctor F).right (F.obj X))
      (id_mem_grading (F.obj X)) hm
    rw [zero_add] at this
    exact Φ.map_mem this
  map_d' {X} m := by
    change Φ.app (F.obj X) (CatTensorProduct.tmul X (𝟙 (F.obj X)) (d m)) =
      d (Φ.app (F.obj X) (CatTensorProduct.tmul X (𝟙 (F.obj X)) m))
    rw [← Φ.map_d]
    congr 1
    erw [CatTensorProduct.d_tmul_of_mem X (N := (ofFunctor F).right (F.obj X))
      (id_mem_grading (F.obj X)), d_id]
    rw [CatTensorProduct.zero_tmul, zero_add, koszulSign_zero, one_smul]
  map_smul' {X X'} f m := by
    change Φ.app (F.obj X') (CatTensorProduct.tmul X' (𝟙 (F.obj X')) (f • m)) =
      F.map f • Φ.app (F.obj X) (CatTensorProduct.tmul X (𝟙 (F.obj X)) m)
    rw [← Φ.map_smul]
    congr 1
    change _ = (ofFunctor F).tensorAct M (F.map f) (CatTensorProduct.tmul X (𝟙 (F.obj X)) m)
    rw [tensorAct_tmul, ← CatTensorProduct.ract_tmul, right_ract, ofFunctor_ract, ofFunctor_lact,
      Category.comp_id, Category.id_comp]

/-- The balanced family `(h, m) ↦ h • ψ m` attached to `ψ : M ⟶ F^* N`. -/
theorem balanced_inductionHomEquivInvFun (ψ : M ⟶ (precomp F).obj N) (Y : D) :
    CatTensorProduct.Balanced (N := (ofFunctor F).right Y) (M := M)
      fun X => (N.act (X := F.obj X) (Y := Y)).compl₂ (ψ.app X) := fun {X X'} f h m => by
  change N.act (((ofFunctor F).right Y).ract f h) (ψ.app X m) = N.act h (ψ.app X' (f • m))
  rw [right_ract, ofFunctor_ract, ψ.map_smul, act_apply, act_apply, comp_smul]
  rfl

/-- The morphism `F_! M ⟶ N` attached to `ψ : M ⟶ F^* N`: `h ⊗ m ↦ h • ψ m`. -/
def inductionHomEquivInvFun (ψ : M ⟶ (precomp F).obj N) : inductionObj F M ⟶ N where
  app Y := CatTensorProduct.lift _ (balanced_inductionHomEquivInvFun ψ Y)
  map_mem' {Y _ _} hy := CatTensorProduct.lift_mem _ (balanced_inductionHomEquivInvFun ψ Y)
    (fun _ _ _ _ _ hh hm => smul_mem_grading hh (ψ.map_mem hm)) hy
  map_d' {Y} y := CatTensorProduct.lift_d _ (balanced_inductionHomEquivInvFun ψ Y)
    (fun X _ _ hh m => by
      change d (N.act _ (ψ.app X m)) = N.act (d _) (ψ.app X m) + _ • N.act _ (ψ.app X (d m))
      rw [ψ.map_d]
      exact d_smul hh _) y
  map_smul' {Y Y'} g y := by
    change CatTensorProduct.lift _ (balanced_inductionHomEquivInvFun ψ Y')
        ((ofFunctor F).tensorAct M g y) =
      g • CatTensorProduct.lift _ (balanced_inductionHomEquivInvFun ψ Y) y
    induction y using CatTensorProduct.induction_on with
    | zero => simp
    | tmul X h m =>
      rw [tensorAct_tmul, CatTensorProduct.lift_tmul, CatTensorProduct.lift_tmul]
      exact comp_smul (M := N) h g (ψ.app X m)
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, smul_add]

@[simp]
theorem inductionHomEquivInvFun_app_tmul (ψ : M ⟶ (precomp F).obj N) {Y : D} (X : C)
    (h : F.obj X ⟶ Y) (m : M.obj X) :
    (inductionHomEquivInvFun ψ).app Y (CatTensorProduct.tmul (N := (ofFunctor F).right Y) X h m) =
      N.act (X := F.obj X) (Y := Y) h (ψ.app X m) :=
  CatTensorProduct.lift_tmul _ (balanced_inductionHomEquivInvFun ψ Y) X h m

variable (F M N) in
/-- The adjunction bijection `(F_! M ⟶ N) ≃ (M ⟶ F^* N)`. -/
def inductionHomEquiv : (inductionObj F M ⟶ N) ≃ (M ⟶ (precomp F).obj N) where
  toFun := inductionHomEquivToFun (F := F)
  invFun := inductionHomEquivInvFun (F := F)
  left_inv Φ := hom_ext fun Y y => by
    induction y using CatTensorProduct.induction_on with
    | zero => simp
    | tmul X h m =>
      rw [inductionHomEquivInvFun_app_tmul]
      change N.act (X := F.obj X) (Y := Y) h
        (Φ.app (F.obj X) (CatTensorProduct.tmul X (𝟙 (F.obj X)) m)) = _
      rw [act_apply, ← Φ.map_smul]
      congr 1
      change (ofFunctor F).tensorAct M h (CatTensorProduct.tmul X (𝟙 (F.obj X)) m) = _
      rw [tensorAct_tmul, ofFunctor_lact, Category.id_comp]
    | add x y hx hy => rw [map_add, hx, hy, map_add]
  right_inv ψ := hom_ext fun X m => by
    show (inductionHomEquivInvFun ψ).app (F.obj X)
      (CatTensorProduct.tmul X (𝟙 (F.obj X)) m) = ψ.app X m
    rw [inductionHomEquivInvFun_app_tmul]
    exact id_smul (M := N) _

end Adjunction

/-- Naturality of the adjunction bijection in the first variable. -/
theorem inductionHomEquivInvFun_comp {M' M : CatModule.{max u₁ v₂ w} C}
    {N : CatModule.{max u₁ v₂ w} D} (f : M' ⟶ M) (g : M ⟶ (precomp F).obj N) :
    inductionHomEquivInvFun.{w} (f ≫ g) =
      (induction.{w} F).map f ≫ inductionHomEquivInvFun.{w} g :=
  hom_ext fun Y y => by
    induction y using CatTensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul X h m =>
      rw [comp_app]
      refine Eq.trans ?_ (congrArg (DFunLike.coe ((inductionHomEquivInvFun g).app Y))
        (induction_map_app_tmul.{w} (F := F) f Y X h m)).symm
      rw [inductionHomEquivInvFun_app_tmul.{w}, inductionHomEquivInvFun_app_tmul.{w}]
      rfl
    | add x y hx hy => rw [map_add, hx, hy, map_add]

variable (F) in
/-- Induction along a dg functor is left adjoint to restriction: `F_! ⊣ F^*`. -/
def inductionAdjunction : induction.{w} F ⊣ precomp F :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N => inductionHomEquiv.{w} F M N
      homEquiv_naturality_left_symm := fun f g => inductionHomEquivInvFun_comp.{w} f g
      homEquiv_naturality_right := fun _ _ => rfl }

@[simp]
theorem inductionAdjunction_homEquiv_apply_app {M : CatModule.{max u₁ v₂ w} C}
    {N : CatModule.{max u₁ v₂ w} D} (Φ : (induction F).obj M ⟶ N) (X : C) (m : M.obj X) :
    (((inductionAdjunction F).homEquiv M N) Φ).app X m =
      Φ.app (F.obj X) (CatTensorProduct.tmul (N := (ofFunctor F).right (F.obj X)) X
        (𝟙 (F.obj X)) m) :=
  rfl

end CatModule

end General

/-! ### Induction of representable modules -/

namespace CatModule

open CatBimodule

section Representable

variable {C : Type v} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] {D : Type u₂} [Category.{v} D] [Preadditive D]
  [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] [DGCategory D] (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]

/-- Induction takes representable modules to representable modules:
`F_! C(X, -) ≅ D(F X, -)`, `h ⊗ k ↦ F k ≫ h`, by the co-Yoneda isomorphism
`D(F -, Y) ⊗_C C(X, -) ≅ D(F X, Y)`. -/
def inductionRepresentableIso (X : C) :
    inductionObj F (representable X) ≅ representable (F.obj X) :=
  isoMk (fun Y => (CatTensorProduct.rid ((ofFunctor F).right Y) X).toAddEquiv)
    (fun {Y n y} => ⟨fun h => by
      have := (CatTensorProduct.rid ((ofFunctor F).right Y) X).symm.map_mem h
      convert this using 2
      exact ((CatTensorProduct.rid ((ofFunctor F).right Y) X).symm_apply_apply y).symm,
      fun h => (CatTensorProduct.rid ((ofFunctor F).right Y) X).map_mem h⟩)
    (fun {Y} y => (CatTensorProduct.rid ((ofFunctor F).right Y) X).map_d y)
    (fun {Y Y'} g y => by
      change CatTensorProduct.rid _ X ((ofFunctor F).tensorAct (representable X) g y) =
        (CatTensorProduct.rid ((ofFunctor F).right Y) X y : F.obj X ⟶ Y) ≫ g
      induction y using CatTensorProduct.induction_on with
      | zero => rw [map_zero, map_zero, map_zero, Limits.zero_comp]
      | tmul X' h k =>
        rw [tensorAct_tmul, CatTensorProduct.rid_tmul, CatTensorProduct.rid_tmul, right_ract,
          right_ract, ofFunctor_ract, ofFunctor_ract, ofFunctor_lact, Category.assoc]
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, Preadditive.add_comp])

@[simp]
theorem inductionRepresentableIso_hom_app_tmul (X : C) {Y : D} (X' : C) (h : F.obj X' ⟶ Y)
    (k : X ⟶ X') :
    (inductionRepresentableIso F X).hom.app Y
      (CatTensorProduct.tmul (N := (ofFunctor F).right Y) X' h k) = F.map k ≫ h :=
  (CatTensorProduct.rid_tmul (N := (ofFunctor F).right Y) X X' h k).trans (right_ract _ _ _ _)

end Representable

end CatModule

end DG
