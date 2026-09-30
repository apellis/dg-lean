import DG.Category.Homotopy.Triangulated

/-!
# Restriction along a dg functor on homotopy categories

Let `F : C ⥤ D` be a dg functor between dg categories. Restriction along `F`,
`DG.CatModule.precomp F : CatModule D ⥤ CatModule C` (`(M ∘ F) X = M (F X)`), preserves the
Hom complexes, the shifts and the mapping cones. This file shows:

* `DG.CatModule.Cochain.precomp F z` and `DG.CatModule.DGHomotopy.precomp F h`: cochains and
  homotopies restrict along `F`, compatibly with `δ`;
* `DG.CatModule.precompCommShift F`: restriction along `F` commutes with the shifts (the
  commutation isomorphisms are the identity on elements), using that dg functors commute with
  the twist `f ↦ (-1)^{n |f|} f` (`CategoryTheory.Functor.map_twist`);
* `DG.CatModule.cone.precompIso F φ`: the restriction of the cone of `φ` is the cone of the
  restriction of `φ`, and `DG.CatModule.cone.precompTriangleIso F φ`: the restriction of the
  standard triangle of `φ` is the standard triangle of the restriction of `φ`;
* `DG.CatModule.HomotopyCategory.precomp F : HomotopyCategory D ⥤ HomotopyCategory C`, the
  induced functor on homotopy categories, which commutes with the shifts and is a triangulated
  functor (`DG.CatModule.HomotopyCategory.precomp_isTriangulated`).
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Category Limits Pretriangulated

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DG.DGAddCommGroup (X ⟶ Y)]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [∀ X Y : D, DG.DGAddCommGroup (X ⟶ Y)]
  (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]

/-- A dg functor commutes with the twist `f ↦ (-1)^{n |f|} f` of the morphisms. -/
theorem map_twist (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    F.map (DG.CatModule.twist n f) = DG.CatModule.twist n (F.map f) := by
  induction f using DG.induction_on with
  | h_zero => simp
  | h_homogeneous f =>
    rw [DG.CatModule.twist_of_mem f.2, DG.CatModule.twist_of_mem (F.map_mem_grading f.2),
      Units.smul_def, F.map_zsmul, ← Units.smul_def]
  | h_add f f' hf hf' => simp only [_root_.map_add, Functor.map_add, hf, hf']

end CategoryTheory.Functor

namespace DG

namespace CatModule

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [∀ X Y : D, DGAddCommGroup (X ⟶ Y)]
  (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]

/-! ### Cochains and homotopies -/

section Cochain

variable {M N : CatModule.{w} D}

/-- The restriction of a cochain along a dg functor: the components at the objects `F X`. -/
def Cochain.precomp {n : ℤ} (z : Cochain M N n) :
    Cochain (precompObj F M) (precompObj F N) n where
  app X := z.app (F.obj X)
  map_mem' hx := z.map_mem hx
  map_smul' hf x := z.map_smul (F.map_mem_grading hf) x

@[simp]
theorem Cochain.precomp_app {n : ℤ} (z : Cochain M N n) (X : C)
    (x : (precompObj F M).obj X) : (z.precomp F).app X x = z.app (F.obj X) x := rfl

theorem Cochain.precomp_add {n : ℤ} (z₁ z₂ : Cochain M N n) :
    (z₁ + z₂).precomp F = z₁.precomp F + z₂.precomp F := rfl

theorem Cochain.precomp_ofHom (φ : M ⟶ N) :
    (Cochain.ofHom φ).precomp F = Cochain.ofHom ((CatModule.precomp F).map φ) := rfl

theorem Cochain.precomp_δ {n m : ℤ} (z : Cochain M N n) :
    (δ n m z).precomp F = δ n m (z.precomp F) := by
  by_cases hnm : n + 1 = m
  · ext X x
    rw [Cochain.precomp_app, δ_apply _ _ hnm, δ_apply _ _ hnm]
    rfl
  · rw [δ_shape _ _ hnm, δ_shape _ _ hnm]
    rfl

/-- The restriction of a homotopy along a dg functor. -/
@[simps]
def DGHomotopy.precomp {f g : M ⟶ N} (h : DGHomotopy f g) :
    DGHomotopy ((CatModule.precomp F).map f) ((CatModule.precomp F).map g) where
  hom := h.hom.precomp F
  ofHom_eq := by
    rw [← Cochain.precomp_ofHom, ← Cochain.precomp_ofHom, ← Cochain.precomp_δ, h.ofHom_eq,
      Cochain.precomp_add]

end Cochain

/-! ### The homotopy categories -/

namespace HomotopyCategory

/-- Restriction along a dg functor, on homotopy categories. -/
noncomputable def precomp : HomotopyCategory.{w} D ⥤ HomotopyCategory.{w} C :=
  CategoryTheory.Quotient.lift _ (CatModule.precomp F ⋙ quotient C)
    (fun _ _ _ _ h => eq_of_homotopy _ _ (h.some.precomp F))

/-- Restriction along a dg functor on homotopy categories is induced by restriction on dg
modules. -/
noncomputable def precompFactors :
    quotient.{w} D ⋙ precomp F ≅ CatModule.precomp.{w} F ⋙ quotient C :=
  CategoryTheory.Quotient.lift.isLift _ _ _

@[simp]
theorem precomp_map_quotient_map {M N : CatModule.{w} D} (f : M ⟶ N) :
    (precomp F).map ((quotient D).map f) = (quotient C).map ((CatModule.precomp F).map f) :=
  rfl

instance : (precomp.{w} F).Additive := by
  have := Functor.additive_of_iso (precompFactors F).symm
  exact Functor.additive_of_full_essSurj_comp (quotient D) _

end HomotopyCategory

variable [DGCategory C] [DGCategory D]

/-! ### Shifts -/

section Shift

/-- Restriction along a dg functor commutes with the shifts:
`(M⟦n⟧) ∘ F ≅ (M ∘ F)⟦n⟧`, the identity on elements. -/
def precompShiftIso (n : ℤ) (M : CatModule.{w} D) :
    precompObj F (shift n M) ≅ shift n (precompObj F M) :=
  isoMk (fun _ => AddEquiv.refl _) Iff.rfl (fun _ => rfl) (fun {X Y} f m =>
    congrArg (fun g => shift.mk (M := M) (X := F.obj Y) n
      (g • shift.unmk (M := M) (X := F.obj X) n m)) (F.map_twist n f).symm)

@[simp]
theorem precompShiftIso_hom_app (n : ℤ) (M : CatModule.{w} D) (X : C)
    (m : (precompObj F (shift n M)).obj X) : (precompShiftIso F n M).hom.app X m = m := rfl

@[simp]
theorem precompShiftIso_inv_app (n : ℤ) (M : CatModule.{w} D) (X : C)
    (m : (shift n (precompObj F M)).obj X) : (precompShiftIso F n M).inv.app X m = m := rfl

/-- Restriction along a dg functor commutes with the shifts. -/
instance precompCommShift : (CatModule.precomp.{w} F).CommShift ℤ where
  commShiftIso n := NatIso.ofComponents (fun M => precompShiftIso F n M) fun _ => rfl
  commShiftIso_zero := by
    ext M : 3
    refine hom_ext fun X m => ?_
    rw [Functor.CommShift.isoZero_hom_app]
    rfl
  commShiftIso_add a b := by
    ext M : 3
    refine hom_ext fun X m => ?_
    rw [Functor.CommShift.isoAdd_hom_app]
    rfl

theorem precomp_commShiftIso_hom_app_app (n : ℤ) (M : CatModule.{w} D) (X : C)
    (m : (precompObj F (shift n M)).obj X) :
    (((CatModule.precomp F).commShiftIso n).hom.app M).app X m = m := rfl

end Shift

/-! ### Cones -/

namespace cone

variable {M N : CatModule.{w} D} (φ : M ⟶ N)

/-- The restriction of the cone of `φ` along a dg functor is the cone of the restriction of
`φ`, the identity on elements. -/
def precompIso :
    precompObj F (cone φ) ≅ cone ((CatModule.precomp F).map φ) :=
  isoMk (fun _ => AddEquiv.refl _) Iff.rfl (fun _ => rfl) (fun {X Y} f p =>
    Prod.ext (congrArg (fun g => shift.mk (M := M) (X := F.obj Y) 1
      (g • shift.unmk (M := M) (X := F.obj X) 1 p.1)) (F.map_twist 1 f).symm) rfl)

@[simp]
theorem precompIso_hom_app (X : C) (p : (precompObj F (cone φ)).obj X) :
    (precompIso F φ).hom.app X p = p := rfl

/-- The restriction of the standard triangle of `φ` along a dg functor is the standard triangle
of the restriction of `φ`. -/
def precompTriangleIso :
    (CatModule.precomp F).mapTriangle.obj (triangle φ) ≅
      triangle ((CatModule.precomp F).map φ) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (precompIso F φ)
    (by rw [Iso.refl_hom, Iso.refl_hom, id_comp, comp_id]; rfl)
    (hom_ext fun _ _ => rfl) (hom_ext fun X p => by
      change -(shift.unmk 1 p.1 : M.obj (F.obj X)) = -shift.unmk 1 p.1
      rfl)

end cone

namespace HomotopyCategory

/-- Restriction along a dg functor on homotopy categories commutes with the shifts. -/
noncomputable instance precompCommShift : (precomp.{w} F).CommShift ℤ :=
  CategoryTheory.Quotient.liftCommShift (CatModule.precomp.{w} F ⋙ quotient C) (homotopic.{w} D)
    ℤ _

instance : NatTrans.CommShift (precompFactors.{w} F).hom ℤ :=
  CategoryTheory.Quotient.liftCommShift_compatibility (CatModule.precomp.{w} F ⋙ quotient C)
    (homotopic.{w} D) ℤ _

/-- The image of the standard triangle `triangleh φ` under restriction along `F` is the
standard triangle of the restriction of `φ`. -/
noncomputable def precompMapTrianglehIso {M N : CatModule.{w} D} (φ : M ⟶ N) :
    (precomp F).mapTriangle.obj (cone.triangleh φ) ≅
      cone.triangleh ((CatModule.precomp F).map φ) :=
  (Functor.mapTriangleCompIso _ _).symm.app _ ≪≫
    (Functor.mapTriangleIso (precompFactors F)).app _ ≪≫
    (Functor.mapTriangleCompIso _ _).app _ ≪≫
    (quotient C).mapTriangle.mapIso (cone.precompTriangleIso F φ)

/-- Restriction along a dg functor is a triangulated functor on homotopy categories. -/
instance precomp_isTriangulated : (precomp.{w} F).IsTriangulated where
  map_distinguished := by
    rintro T ⟨M, N, φ, ⟨e⟩⟩
    exact ⟨_, _, _, ⟨(precomp F).mapTriangle.mapIso e ≪≫ precompMapTrianglehIso F φ⟩⟩

end HomotopyCategory

end CatModule

end DG
