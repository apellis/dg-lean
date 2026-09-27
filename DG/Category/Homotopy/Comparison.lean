import DG.Category.Comparison
import DG.Category.Homotopy.Triangulated
import DG.Homotopy.Triangulated

/-!
# The homotopy category of a one-object dg category

Let `A` be a dg ring and `SingleObj A` the corresponding one-object dg category. The equivalence
`DG.CatModule.singleObjEquivalence A : CatModule (SingleObj A) ≌ DGModuleCat A` (evaluation at
the unique object) identifies the constructions of tier 3 for dg categories with those for dg
rings. This file shows:

* `DG.CatModule.Cochain.toDGModuleCochain`: a cochain of the Hom complex of dg modules over
  `SingleObj A` is a cochain `DG.Cochain` of the associated dg `A`-modules; this is an additive
  equivalence (`DG.CatModule.Cochain.dgModuleCochainAddEquiv`) compatible with `δ`, so that
  homotopies correspond (`DG.CatModule.DGHomotopy.toDGHomotopy`,
  `DG.CatModule.DGHomotopy.ofDGHomotopy`);
* `DG.CatModule.toDGModuleCatCommShift`: evaluation at the unique object commutes with the
  shifts (the isomorphisms are the identity on elements; the twists of the actions agree,
  `DG.CatModule.twist_eq_shiftTwist`), and it sends the mapping cone of `φ` to the mapping cone
  `DG.Cone` of the corresponding morphism of dg `A`-modules, and standard triangles to standard
  triangles (`DG.CatModule.cone.toDGModuleCatTriangleIso`);
* `DG.CatModule.HomotopyCategory.toDGHomotopyCategory A`: the induced functor
  `HomotopyCategory (SingleObj A) ⥤ DG.HomotopyCategory A`, which commutes with the shifts, is
  a triangulated functor, and is an equivalence of categories
  (`DG.CatModule.HomotopyCategory.singleObjEquivalence A`).
-/

open CategoryTheory Category Limits Pretriangulated

universe w u

namespace DG

namespace CatModule

variable {A : Type u} [Ring A] [DGAddCommGroup A]

/-! ### Cochains and homotopies -/

section Cochain

variable {M N : CatModule.{w} (SingleObj A)}

/-- A cochain between dg modules over `SingleObj A` as a cochain of the Hom complex of the
associated dg `A`-modules: the component at the unique object. -/
def Cochain.toDGModuleCochain {n : ℤ} (z : Cochain M N n) :
    DG.Cochain A (toDGModuleCatObj M) (toDGModuleCatObj N) n where
  toFun := z.app (SingleObj.star A)
  map_zero' := map_zero _
  map_add' := map_add _
  map_mem' _ _ hx := z.map_mem hx
  map_smul' ha x := z.map_smul (X := SingleObj.star A) (Y := SingleObj.star A) ha x

/-- A cochain of the Hom complex of the dg `A`-modules associated to dg modules over
`SingleObj A` as a cochain of dg modules over `SingleObj A`. -/
def Cochain.ofDGModuleCochain {n : ℤ}
    (z : DG.Cochain A (toDGModuleCatObj M) (toDGModuleCatObj N) n) : Cochain M N n where
  app _ := AddMonoidHomClass.toAddMonoidHom z
  map_mem' hx := z.map_mem hx
  map_smul' hf x := z.map_smul hf x

@[simp]
theorem Cochain.toDGModuleCochain_apply {n : ℤ} (z : Cochain M N n)
    (x : M.obj (SingleObj.star A)) : z.toDGModuleCochain x = z.app (SingleObj.star A) x := rfl

variable (M N) in
/-- Cochains between dg modules over `SingleObj A` are the cochains of the associated dg
`A`-modules. -/
@[simps]
def Cochain.dgModuleCochainAddEquiv (n : ℤ) :
    Cochain M N n ≃+ DG.Cochain A (toDGModuleCatObj M) (toDGModuleCatObj N) n where
  toFun z := z.toDGModuleCochain
  invFun z := Cochain.ofDGModuleCochain z
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem Cochain.toDGModuleCochain_ofHom (φ : M ⟶ N) :
    (Cochain.ofHom φ).toDGModuleCochain =
      DG.Cochain.ofHom ((toDGModuleCat A).map φ).hom := rfl

theorem Cochain.toDGModuleCochain_add {n : ℤ} (z₁ z₂ : Cochain M N n) :
    (z₁ + z₂).toDGModuleCochain = z₁.toDGModuleCochain + z₂.toDGModuleCochain := rfl

theorem Cochain.toDGModuleCochain_δ {n m : ℤ} (z : Cochain M N n) :
    (δ n m z).toDGModuleCochain = DG.δ n m z.toDGModuleCochain := by
  by_cases hnm : n + 1 = m
  · refine DG.Cochain.ext fun x => ?_
    rw [Cochain.toDGModuleCochain_apply, δ_apply _ _ hnm, DG.δ_apply _ _ hnm]
    rfl
  · rw [δ_shape _ _ hnm, DG.δ_shape _ _ hnm]
    rfl

/-- A homotopy of dg modules over `SingleObj A` as a homotopy of dg `A`-modules. -/
@[simps]
def DGHomotopy.toDGHomotopy {f g : M ⟶ N} (h : DGHomotopy f g) :
    DG.DGHomotopy ((toDGModuleCat A).map f).hom ((toDGModuleCat A).map g).hom where
  hom := h.hom.toDGModuleCochain
  ofHom_eq := by
    rw [← Cochain.toDGModuleCochain_ofHom, ← Cochain.toDGModuleCochain_ofHom,
      ← Cochain.toDGModuleCochain_δ, h.ofHom_eq, Cochain.toDGModuleCochain_add]

/-- A homotopy of the associated dg `A`-modules as a homotopy of dg modules over
`SingleObj A`. -/
@[simps]
def DGHomotopy.ofDGHomotopy {f g : M ⟶ N}
    (h : DG.DGHomotopy ((toDGModuleCat A).map f).hom ((toDGModuleCat A).map g).hom) :
    DGHomotopy f g where
  hom := Cochain.ofDGModuleCochain h.hom
  ofHom_eq := (Cochain.dgModuleCochainAddEquiv M N 0).injective (by
    change (Cochain.ofHom f).toDGModuleCochain =
      (δ (-1) 0 (Cochain.ofDGModuleCochain h.hom) + Cochain.ofHom g).toDGModuleCochain
    rw [Cochain.toDGModuleCochain_add, Cochain.toDGModuleCochain_δ,
      Cochain.toDGModuleCochain_ofHom, Cochain.toDGModuleCochain_ofHom, h.ofHom_eq]
    rfl)

theorem homotopic_iff_toDGModuleCat {f g : M ⟶ N} :
    Homotopic f g ↔ DG.Homotopic ((toDGModuleCat A).map f).hom ((toDGModuleCat A).map g).hom :=
  ⟨fun ⟨h⟩ => ⟨h.toDGHomotopy⟩, fun ⟨h⟩ => ⟨DGHomotopy.ofDGHomotopy h⟩⟩

end Cochain

instance toDGModuleCat_additive : (toDGModuleCat.{w} A).Additive where
  map_add := rfl

instance : (toDGModuleCat.{w} A).Full :=
  inferInstanceAs (singleObjEquivalence.{w} A).functor.Full

instance : (toDGModuleCat.{w} A).Faithful :=
  inferInstanceAs (singleObjEquivalence.{w} A).functor.Faithful

/-! ### The homotopy categories -/

namespace HomotopyCategory

variable (A)

/-- The functor `HomotopyCategory (SingleObj A) ⥤ DG.HomotopyCategory A` induced by evaluation
at the unique object. -/
noncomputable def toDGHomotopyCategory :
    HomotopyCategory.{w} (SingleObj A) ⥤ DG.HomotopyCategory.{w} A :=
  CategoryTheory.Quotient.lift _ (toDGModuleCat.{w} A ⋙ DG.HomotopyCategory.quotient A)
    (fun _ _ _ _ h => DG.HomotopyCategory.eq_of_homotopy _ _ h.some.toDGHomotopy)

/-- The functor `toDGHomotopyCategory A` is induced by evaluation at the unique object. -/
noncomputable def toDGHomotopyCategoryFactors :
    quotient (SingleObj A) ⋙ toDGHomotopyCategory A ≅
      toDGModuleCat.{w} A ⋙ DG.HomotopyCategory.quotient A :=
  CategoryTheory.Quotient.lift.isLift _ _ _

variable {A}

@[simp]
theorem toDGHomotopyCategory_map_quotient_map {M N : CatModule.{w} (SingleObj A)} (f : M ⟶ N) :
    (toDGHomotopyCategory A).map ((quotient (SingleObj A)).map f) =
      (DG.HomotopyCategory.quotient A).map ((toDGModuleCat A).map f) :=
  rfl

variable (A)

instance : (toDGHomotopyCategory.{w} A).Additive := by
  have := Functor.additive_of_iso (toDGHomotopyCategoryFactors A).symm
  exact Functor.additive_of_full_essSurj_comp (quotient (SingleObj A)) _

end HomotopyCategory

variable [DGRing A]

/-! ### Shifts -/

section Shift

/-- On the one-object dg category `SingleObj A`, the twist `f ↦ (-1)^{n |f|} f` of the
morphisms is the twist `DG.Shift.twist A n` of the dg ring `A`. -/
theorem twist_eq_shiftTwist (n : ℤ) {X Y : SingleObj A} (a : X ⟶ Y) :
    (twist n a : A) = Shift.twist A n (a : A) := by
  induction a using DG.induction_on with
  | h_zero => simp
  | h_homogeneous a =>
    rw [twist_of_mem a.2, Shift.twist_of_mem (A := A) a.2]
  | h_add a a' ha ha' => rw [map_add, map_add]; exact congrArg₂ (· + ·) ha ha'

/-- Evaluation at the unique object commutes with the shifts (the identity on elements). -/
def toDGModuleCatShiftIso (n : ℤ) (M : CatModule.{w} (SingleObj A)) :
    (toDGModuleCat A).obj (shift n M) ≅
      (shiftFunctor (DGModuleCat.{w} A) n).obj ((toDGModuleCat A).obj M) :=
  DGModuleEquiv.toDGModuleCatIso (M := (toDGModuleCat A).obj (shift n M))
    (N := DG.Shift n (toDGModuleCatObj M))
    { toFun := fun m => m
      invFun := fun m => m
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun a m => by
        change shift.mk (M := M) (X := SingleObj.star A) n
            (twist n (show SingleObj.star A ⟶ SingleObj.star A from a) •
              shift.unmk (M := M) (X := SingleObj.star A) n m) =
          Shift.mk (M := M.obj (SingleObj.star A)) n
            (M.act (X := SingleObj.star A) (Y := SingleObj.star A) (Shift.twist A n a)
              (Shift.unmk n m))
        rw [← twist_eq_shiftTwist]
        rfl
      map_mem' := fun hm => hm
      map_d' := fun _ => rfl }

@[simp]
theorem toDGModuleCatShiftIso_hom_apply (n : ℤ) (M : CatModule.{w} (SingleObj A))
    (m : (shift n M).obj (SingleObj.star A)) : (toDGModuleCatShiftIso n M).hom m = m := rfl

/-- Evaluation at the unique object commutes with the shifts. -/
instance toDGModuleCatCommShift : (toDGModuleCat.{w} A).CommShift ℤ where
  iso n := NatIso.ofComponents (fun M => toDGModuleCatShiftIso n M) fun _ => rfl
  zero := by
    ext M : 3
    refine DGModuleCat.hom_ext_apply fun m => ?_
    rw [Functor.CommShift.isoZero_hom_app]
    rfl
  add a b := by
    ext M : 3
    refine DGModuleCat.hom_ext_apply fun m => ?_
    rw [Functor.CommShift.isoAdd_hom_app]
    rfl

end Shift

/-! ### Cones -/

namespace cone

variable {M N : CatModule.{w} (SingleObj A)} (φ : M ⟶ N)

/-- Evaluation at the unique object sends the mapping cone of `φ` to the mapping cone
`DG.Cone` of the associated morphism of dg `A`-modules (the identity on elements). -/
def toDGModuleCatIso :
    (toDGModuleCat A).obj (cone φ) ≅ DGModuleCat.of A (DG.Cone ((toDGModuleCat A).map φ).hom) :=
  DGModuleEquiv.toDGModuleCatIso (M := (toDGModuleCat A).obj (cone φ))
    (N := DG.Cone ((toDGModuleCat A).map φ).hom)
    { toFun := fun p => p
      invFun := fun p => p
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun a p => by
        refine Prod.ext ?_ rfl
        change shift.mk (M := M) (X := SingleObj.star A) 1
            (twist 1 (show SingleObj.star A ⟶ SingleObj.star A from a) •
              shift.unmk (M := M) (X := SingleObj.star A) 1 p.1) =
          Shift.mk (M := M.obj (SingleObj.star A)) 1
            (M.act (X := SingleObj.star A) (Y := SingleObj.star A) (Shift.twist A 1 a)
              (Shift.unmk 1 p.1))
        rw [← twist_eq_shiftTwist]
        rfl
      map_mem' := fun hp => hp
      map_d' := fun _ => rfl }

@[simp]
theorem toDGModuleCatIso_hom_apply (p : (cone φ).obj (SingleObj.star A)) :
    (toDGModuleCatIso φ).hom p = p := rfl

/-- Evaluation at the unique object sends the standard triangle of `φ` to the standard triangle
`DG.Cone.triangle` of the associated morphism of dg `A`-modules. -/
def toDGModuleCatTriangleIso :
    (toDGModuleCat A).mapTriangle.obj (triangle φ) ≅
      DG.Cone.triangle ((toDGModuleCat A).map φ) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (toDGModuleCatIso φ)
    (by rw [Iso.refl_hom, Iso.refl_hom, id_comp, comp_id]; rfl)
    (DGModuleCat.hom_ext_apply fun _ => rfl) (DGModuleCat.hom_ext_apply fun _ => rfl)

end cone

namespace HomotopyCategory

variable (A)

/-- The functor `toDGHomotopyCategory A` commutes with the shifts. -/
noncomputable instance toDGHomotopyCategoryCommShift :
    (toDGHomotopyCategory.{w} A).CommShift ℤ :=
  CategoryTheory.Quotient.liftCommShift (toDGModuleCat.{w} A ⋙ DG.HomotopyCategory.quotient A)
    (homotopic.{w} (SingleObj A)) ℤ _

instance : NatTrans.CommShift (toDGHomotopyCategoryFactors.{w} A).hom ℤ :=
  CategoryTheory.Quotient.liftCommShift_compatibility
    (toDGModuleCat.{w} A ⋙ DG.HomotopyCategory.quotient A) (homotopic.{w} (SingleObj A)) ℤ _

variable {A}

/-- The image of the standard triangle `triangleh φ` under `toDGHomotopyCategory A` is the
standard triangle `DG.Cone.triangleh` of the associated morphism of dg `A`-modules. -/
noncomputable def toDGHomotopyCategoryMapTrianglehIso {M N : CatModule.{w} (SingleObj A)}
    (φ : M ⟶ N) :
    (toDGHomotopyCategory A).mapTriangle.obj (cone.triangleh φ) ≅
      DG.Cone.triangleh ((toDGModuleCat A).map φ) :=
  (Functor.mapTriangleCompIso _ _).symm.app _ ≪≫
    (Functor.mapTriangleIso (toDGHomotopyCategoryFactors A)).app _ ≪≫
    (Functor.mapTriangleCompIso _ _).app _ ≪≫
    (DG.HomotopyCategory.quotient A).mapTriangle.mapIso (cone.toDGModuleCatTriangleIso φ)

variable (A)

/-- The functor `HomotopyCategory (SingleObj A) ⥤ DG.HomotopyCategory A` is triangulated. -/
instance toDGHomotopyCategory_isTriangulated : (toDGHomotopyCategory.{w} A).IsTriangulated where
  map_distinguished := by
    rintro T ⟨M, N, φ, ⟨e⟩⟩
    exact ⟨_, _, _, ⟨(toDGHomotopyCategory A).mapTriangle.mapIso e ≪≫
      toDGHomotopyCategoryMapTrianglehIso φ⟩⟩

instance : (toDGHomotopyCategory.{w} A).Faithful where
  map_injective {X Y} f g h := by
    obtain ⟨M⟩ := X
    obtain ⟨N⟩ := Y
    obtain ⟨f, rfl⟩ := (quotient (SingleObj A)).map_surjective f
    obtain ⟨g, rfl⟩ := (quotient (SingleObj A)).map_surjective g
    rw [toDGHomotopyCategory_map_quotient_map, toDGHomotopyCategory_map_quotient_map,
      DG.HomotopyCategory.quotient_map_eq_iff] at h
    exact (quotient_map_eq_iff f g).mpr (homotopic_iff_toDGModuleCat.mpr h)

instance : (toDGHomotopyCategory.{w} A).Full where
  map_surjective {X Y} f := by
    obtain ⟨M⟩ := X
    obtain ⟨N⟩ := Y
    obtain ⟨f, rfl⟩ := (DG.HomotopyCategory.quotient A).map_surjective f
    exact ⟨(quotient (SingleObj A)).map ((toDGModuleCat A).preimage f), by
      rw [toDGHomotopyCategory_map_quotient_map, Functor.map_preimage]⟩

instance : (toDGHomotopyCategory.{w} A).EssSurj where
  mem_essImage Y := by
    obtain ⟨P⟩ := Y
    exact ⟨(quotient (SingleObj A)).obj ((DGModuleCat.toCatModule A).obj P),
      ⟨(DG.HomotopyCategory.quotient A).mapIso ((singleObjEquivalence.{w} A).counitIso.app P)⟩⟩

instance : (toDGHomotopyCategory.{w} A).IsEquivalence where

/-- The homotopy category of dg modules over the one-object dg category `SingleObj A` is
equivalent to the homotopy category of dg `A`-modules, by an equivalence which commutes with
the shifts and whose functor is triangulated. -/
noncomputable def singleObjEquivalence :
    HomotopyCategory.{w} (SingleObj A) ≌ DG.HomotopyCategory.{w} A :=
  (toDGHomotopyCategory A).asEquivalence

end HomotopyCategory

end CatModule

end DG
