import Mathlib.CategoryTheory.Triangulated.Functor
import DG.Category.Homotopy.ConeCochain
import DG.Category.Homotopy.HomotopyShift

/-!
# The pretriangulated structure on the homotopy category of dg modules over a dg category

Let `C` be a dg category. This file shows that the homotopy category
`DG.CatModule.HomotopyCategory C` of dg modules over `C` is pretriangulated. It is a port of
`DG.Homotopy.Pretriangulated` (the case of a dg ring), itself a port of Mathlib's
`Mathlib/Algebra/Homology/HomotopyCategory/Pretriangulated.lean`, with the same definitions and
signs.

## Main definitions and results

* `DG.CatModule.cone.triangle φ`: for `φ : M ⟶ N` in `CatModule C`, the standard triangle
  `M ⟶ N ⟶ cone φ ⟶ M⟦1⟧` with morphisms `φ`, `inr φ` and `-fstHom φ`; its image
  `DG.CatModule.cone.triangleh φ` in the homotopy category.
* `DG.CatModule.cone.rotateHomotopyEquiv f : DGHomotopyEquiv (shift 1 M) (cone (inr f))` and
  `DG.CatModule.cone.rotateTrianglehIso φ : (triangleh φ).rotate ≅ triangleh (inr φ)`.
* `DG.CatModule.cone.shiftIso f n : (cone f)⟦n⟧ ≅ cone (f⟦n⟧')` and the isomorphisms of
  triangles `DG.CatModule.cone.shiftTriangleIso`, `DG.CatModule.cone.shiftTrianglehIso`.
* `DG.CatModule.cone.trianglehMapOfHomotopy`, `DG.CatModule.cone.triangleMap`.
* `DG.CatModule.HomotopyCategory.Pretriangulated.distinguishedTriangles C` and the instance
  `DG.CatModule.HomotopyCategory.pretriangulated`.

## Comparison with the dg-ring version

The names are those of the dg-ring version in the namespace `DG.CatModule`; `DG.Cone.shiftEquiv`
(an isomorphism of dg modules) becomes `DG.CatModule.cone.shiftIso`, an isomorphism in
`CatModule C`. Morphisms compose in diagrammatic order.
-/

open CategoryTheory Category Limits Pretriangulated

universe w v u

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

theorem units_smul_app {M N : CatModule.{w} C} (k : ℤˣ) (φ : M ⟶ N) {X : C} (x : M.obj X) :
    (k • φ).app X x = k • φ.app X x := rfl

/-- The coercion of a multiple of a cocycle by a unit. -/
@[simp]
theorem Cocycle.coe_units_smul {M N : CatModule.{w} C} {n : ℤ} (u : ℤˣ) (z : Cocycle M N n) :
    ((u • z : Cocycle M N n) : Cochain M N n) = u • (z : Cochain M N n) :=
  rfl

variable [DGCategory C]

namespace cone

section Cochains

open Cochain

theorem fstHom_eq_mk_fst {M N : CatModule.{w} C} (f : M ⟶ N) {X : C} (p : (cone f).obj X) :
    (fstHom f).app X p = shift.mk 1 ((fst f).1.app X p) := rfl

/-! ### Rotation -/

section Rotate

variable {M N : CatModule.{w} C} (f : M ⟶ N)

namespace RotateHomotopyEquiv

/-- The morphism `M⟦1⟧ ⟶ cone (inr f)` of Mathlib's `mappingCone.rotateHomotopyEquiv`. -/
def hom : shift 1 M ⟶ cone (inr f) :=
  lift (inr f) (-(Cocycle.ofHom f).leftShift 1 1 (zero_add 1))
    (-(inl f).leftShift 1 0 (neg_add_cancel 1)) (by
      refine Cochain.ext fun X x => ?_
      obtain ⟨x, rfl⟩ := shift.mk_surjective (n := 1) x
      simp [δ_zero_cochain_apply, inl_d_apply, leftShift_apply, DG.Cochain.leftShiftSign])

/-- The morphism `cone (inr f) ⟶ M⟦1⟧` of Mathlib's `mappingCone.rotateHomotopyEquiv`. -/
def inv : cone (inr f) ⟶ shift 1 M :=
  desc (inr f) 0 (-fstHom f) (by
    refine Cochain.ext fun X y => ?_
    simp)

variable {f} {X : C}

theorem hom_apply (x : (shift 1 M).obj X) :
    (hom f).app X x = (inl (inr f)).app X (f.app X (shift.unmk 1 x)) -
      (inr (inr f)).app X ((inl f).app X (shift.unmk 1 x)) := by
  obtain ⟨x, rfl⟩ := shift.mk_surjective (n := 1) x
  simp [hom, lift_apply, leftShift_apply, DG.Cochain.leftShiftSign, sub_eq_add_neg]

@[simp]
theorem fst_hom_apply (x : (shift 1 M).obj X) :
    (fst (inr f)).1.app X ((hom f).app X x) = f.app X (shift.unmk 1 x) := by
  simp [hom_apply]

@[simp]
theorem snd_hom_apply (x : (shift 1 M).obj X) :
    (snd (inr f)).app X ((hom f).app X x) = -(inl f).app X (shift.unmk 1 x) := by
  simp [hom_apply]

theorem inv_apply (p : (cone (inr f)).obj X) :
    (inv f).app X p = -(fstHom f).app X ((snd (inr f)).app X p) := by
  simp [inv, desc_apply]

variable (f)

@[simp]
theorem hom_comp_inv : hom f ≫ inv f = 𝟙 _ := by
  refine hom_ext fun X x => ?_
  obtain ⟨x, rfl⟩ := shift.mk_surjective (n := 1) x
  simp [inv_apply]
  rfl

/-- The homotopy `inv ≫ hom ≃ 𝟙` of Mathlib's `mappingCone.rotateHomotopyEquiv`, given by the
cochain `-inl (inr f) ∘ snd f ∘ snd (inr f)` of degree `-1`. -/
def homotopyInvHomId : DGHomotopy (inv f ≫ hom f) (𝟙 _) :=
  DGHomotopy.mk' (-((inl (inr f)).comp (snd f) (zero_add (-1))).comp (snd (inr f)) (zero_add (-1)))
    (fun p => by
      refine ext_to ?_ ?_
      · simp [inv_apply, d_fst_apply, d_snd_apply, ← fst_apply]
        abel
      · refine ext_to ?_ ?_
        · simp [inv_apply, d_fst_apply, d_snd_apply, ← fst_apply]
        · simp [inv_apply, d_fst_apply, d_snd_apply, ← fst_apply])

/-- Mathlib's `rotateHomotopyEquivComm₂Homotopy`: the homotopy
`(-fstHom f) ≫ hom ≃ inr (inr f)`, given by the cochain `-inl (inr f) ∘ snd f`. -/
def comm₂Homotopy : DGHomotopy ((-fstHom f) ≫ hom f) (inr (inr f)) :=
  DGHomotopy.mk' (-(inl (inr f)).comp (snd f) (zero_add (-1))) (fun p => by
    refine ext_to ?_ ?_
    · simp [d_fst_apply, d_snd_apply, ← fst_apply]
    · refine ext_to ?_ ?_
      · simp [d_fst_apply, d_snd_apply, ← fst_apply]
      · simp [d_fst_apply, d_snd_apply, ← fst_apply])

/-- Mathlib's `rotateHomotopyEquiv_comm₃`. -/
theorem comm₃ : hom f ≫ (-fstHom (inr f)) = -shiftMap 1 f := by
  refine hom_ext fun X x => (shift.unmk 1).injective ?_
  simp [← fst_apply, unmk_shiftMap_app]

end RotateHomotopyEquiv

/-- The homotopy equivalence `M⟦1⟧ ≃ cone (inr f)` (Mathlib's
`mappingCone.rotateHomotopyEquiv`). -/
def rotateHomotopyEquiv : DGHomotopyEquiv (shift 1 M) (cone (inr f)) where
  hom := RotateHomotopyEquiv.hom f
  inv := RotateHomotopyEquiv.inv f
  homotopyHomInvId := DGHomotopy.ofEq (RotateHomotopyEquiv.hom_comp_inv f)
  homotopyInvHomId := RotateHomotopyEquiv.homotopyInvHomId f

end Rotate

/-! ### Shifts of cones -/

section ShiftIso

variable {M N : CatModule.{w} C} (f : M ⟶ N) (n : ℤ)

namespace ShiftIso

/-- The morphism `(cone f)⟦n⟧ ⟶ cone (f⟦n⟧)` of Mathlib's `mappingCone.shiftIso`. -/
def hom : shift n (cone f) ⟶ cone (shiftMap n f) :=
  lift (shiftMap n f) (koszulSign n • (fst f).shift n) ((snd f).shift n) (by
    refine Cochain.ext fun X x => ?_
    obtain ⟨x, rfl⟩ := shift.mk_surjective (n := n) x
    simp [δ_zero_cochain_apply, d_snd_apply, Cocycle.coe_units_smul])

/-- The morphism `cone (f⟦n⟧) ⟶ (cone f)⟦n⟧` of Mathlib's `mappingCone.shiftIso`. -/
def inv : cone (shiftMap n f) ⟶ shift n (cone f) :=
  desc (shiftMap n f) (koszulSign n • (inl f).shift n) (shiftMap n (inr f)) (by
    refine Cochain.ext fun X x => ?_
    obtain ⟨x, rfl⟩ := shift.mk_surjective (n := n) x
    simp [δ_neg_one_apply, inl_d_apply, smul_smul])

variable {f n} {X : C}

@[simp]
theorem fst_hom_apply (x : (shift n (cone f)).obj X) :
    (fst (shiftMap n f)).1.app X ((hom f n).app X x) =
      koszulSign n • shift.mk n ((fst f).1.app X (shift.unmk n x)) := by
  simp [hom, lift_apply]

@[simp]
theorem snd_hom_apply (x : (shift n (cone f)).obj X) :
    (snd (shiftMap n f)).app X ((hom f n).app X x) = shift.mk n ((snd f).app X (shift.unmk n x)) := by
  simp [hom, lift_apply]
  rfl

theorem inv_apply (q : (cone (shiftMap n f)).obj X) :
    (inv f n).app X q =
      koszulSign n • shift.mk n ((inl f).app X (shift.unmk n ((fst (shiftMap n f)).1.app X q))) +
        shift.mk n ((inr f).app X (shift.unmk n ((snd (shiftMap n f)).app X q))) := by
  simp [inv, desc_apply]
  rfl

variable (f n)

@[simp]
theorem hom_comp_inv : hom f n ≫ inv f n = 𝟙 _ := by
  refine hom_ext fun X x => ?_
  obtain ⟨x, rfl⟩ := shift.mk_surjective (n := n) x
  simp [inv_apply, smul_smul]
  rw [← map_add, id_X]

@[simp]
theorem inv_comp_hom : inv f n ≫ hom f n = 𝟙 _ := by
  refine hom_ext fun X q => ext_to ?_ ?_
  · simp [inv_apply, smul_smul]
  · simp [inv_apply, smul_smul]

/-- Mathlib's `shiftTriangleIso`, second square. -/
theorem shift_inr_comp_hom : shiftMap n (inr f) ≫ hom f n = inr (shiftMap n f) := by
  refine hom_ext fun X y => ?_
  obtain ⟨y, rfl⟩ := shift.mk_surjective (n := n) y
  refine ext_to ?_ ?_ <;> simp

/-- Mathlib's `shiftTriangleIso`, third square. -/
theorem comm₃ : shiftMap n (-fstHom f) ≫ (shiftComm (M := M) 1 n).hom =
    koszulSign n • (hom f n ≫ (-fstHom (shiftMap n f))) := by
  refine hom_ext fun X x => ?_
  obtain ⟨x, rfl⟩ := shift.mk_surjective (n := n) x
  simp [smul_smul, units_smul_app, fstHom_eq_mk_fst]

end ShiftIso

/-- The isomorphism `(cone f)⟦n⟧ ≅ cone (f⟦n⟧)` (Mathlib's `mappingCone.shiftIso`). -/
def shiftIso : shift n (cone f) ≅ cone (shiftMap n f) where
  hom := ShiftIso.hom f n
  inv := ShiftIso.inv f n
  hom_inv_id := ShiftIso.hom_comp_inv f n
  inv_hom_id := ShiftIso.inv_comp_hom f n

end ShiftIso

end Cochains

/-! ### The standard triangles -/

open HomotopyCategory

section Triangle

variable {M N : CatModule.{w} C} (φ : M ⟶ N)

/-- The standard triangle `M ⟶ N ⟶ cone φ ⟶ M⟦1⟧` in `CatModule C` attached to a morphism
`φ : M ⟶ N`, with the morphisms `φ`, `inr φ` and `-fstHom φ` (Mathlib's
`CochainComplex.mappingCone.triangle`). -/
@[simps! obj₁ obj₂ obj₃ mor₁ mor₂]
def triangle : Triangle (CatModule.{w} C) :=
  Triangle.mk φ (inr φ) (-fstHom φ)

theorem triangle_mor₃ : (triangle φ).mor₃ = -fstHom φ := rfl

@[reassoc (attr := simp)]
theorem inr_triangleδ : inr φ ≫ (triangle φ).mor₃ = 0 := by
  rw [triangle_mor₃, Preadditive.comp_neg, inr_comp_fstHom, neg_zero]

/-- The standard triangle in the homotopy category attached to a morphism of dg modules
(Mathlib's `CochainComplex.mappingCone.triangleh`). -/
noncomputable abbrev triangleh : Triangle (HomotopyCategory.{w} C) :=
  (quotient C).mapTriangle.obj (triangle φ)

end Triangle

section MapOfHomotopy

variable {M₁ N₁ M₂ N₂ : CatModule.{w} C} {φ₁ : M₁ ⟶ N₁} {φ₂ : M₂ ⟶ N₂}
  {a : M₁ ⟶ M₂} {b : N₁ ⟶ N₂} (H : DGHomotopy (φ₁ ≫ b) (a ≫ φ₂))

@[reassoc]
theorem triangleMapOfHomotopy_comm₃ :
    mapOfHomotopy H ≫ (triangle φ₂).mor₃ = (triangle φ₁).mor₃ ≫ a⟦(1 : ℤ)⟧' := by
  rw [triangle_mor₃, triangle_mor₃, Preadditive.comp_neg, Preadditive.neg_comp,
    mapOfHomotopy_comp_fstHom]
  rfl

/-- The morphism `triangleh φ₁ ⟶ triangleh φ₂` induced by a square commuting up to homotopy
(Mathlib's `trianglehMapOfHomotopy`). -/
@[simps]
noncomputable def trianglehMapOfHomotopy : triangleh φ₁ ⟶ triangleh φ₂ where
  hom₁ := (quotient C).map a
  hom₂ := (quotient C).map b
  hom₃ := (quotient C).map (mapOfHomotopy H)
  comm₁ := by
    dsimp
    simp only [← Functor.map_comp]
    exact eq_of_homotopy _ _ H
  comm₂ := by
    dsimp
    simp only [← Functor.map_comp, inr_comp_mapOfHomotopy]
  comm₃ := by
    dsimp
    rw [← Functor.map_comp_assoc, triangleMapOfHomotopy_comm₃, Functor.map_comp, assoc, assoc]
    simp

end MapOfHomotopy

section Map

variable {M₁ N₁ M₂ N₂ : CatModule.{w} C} (φ₁ : M₁ ⟶ N₁) (φ₂ : M₂ ⟶ N₂)
  (a : M₁ ⟶ M₂) (b : N₁ ⟶ N₂) (comm : φ₁ ≫ b = a ≫ φ₂)

/-- The morphism `triangle φ₁ ⟶ triangle φ₂` induced by a commutative square (Mathlib's
`mappingCone.triangleMap`). -/
@[simps!]
def triangleMap : triangle φ₁ ⟶ triangle φ₂ where
  hom₁ := a
  hom₂ := b
  hom₃ := map a b comm
  comm₁ := comm
  comm₂ := inr_comp_map _ _ comm
  comm₃ := by
    change (-fstHom φ₁) ≫ shiftMap 1 a = map a b comm ≫ (-fstHom φ₂)
    rw [Preadditive.comp_neg, Preadditive.neg_comp, map_comp_fstHom]

end Map

section Rotate

variable {M N : CatModule.{w} C} (φ : M ⟶ N)

@[reassoc (attr := simp)]
theorem rotateHomotopyEquiv_comm₂ :
    (quotient C).map (triangle φ).mor₃ ≫ (quotient C).map (rotateHomotopyEquiv φ).hom =
      (quotient C).map (inr (inr φ)) := by
  rw [← Functor.map_comp]
  exact eq_of_homotopy _ _ (RotateHomotopyEquiv.comm₂Homotopy φ)

@[reassoc (attr := simp)]
theorem rotateHomotopyEquiv_comm₃ :
    (rotateHomotopyEquiv φ).hom ≫ (triangle (inr φ)).mor₃ = -φ⟦(1 : ℤ)⟧' :=
  RotateHomotopyEquiv.comm₃ φ

/-- The isomorphism of triangles `(triangleh φ).rotate ≅ triangleh (inr φ)` (Mathlib's
`mappingCone.rotateTrianglehIso`). -/
noncomputable def rotateTrianglehIso :
    (triangleh φ).rotate ≅ triangleh (inr φ) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (((quotient C).commShiftIso (1 : ℤ)).symm.app M ≪≫
      isoOfHomotopyEquiv (rotateHomotopyEquiv φ))
    (by dsimp; simp) (by dsimp; simp) (by
      dsimp
      rw [CategoryTheory.Functor.map_id, comp_id, assoc, ← Functor.map_comp_assoc,
        rotateHomotopyEquiv_comm₃, Functor.map_neg, Preadditive.neg_comp,
        Functor.commShiftIso_hom_naturality, Preadditive.comp_neg,
        Iso.inv_hom_id_app_assoc])

end Rotate

section Shift

variable {M N : CatModule.{w} C} (φ : M ⟶ N) (n : ℤ)

@[reassoc]
theorem shiftIso_comm₂ :
    (inr φ)⟦n⟧' ≫ (shiftIso φ n).hom = inr (φ⟦n⟧') :=
  ShiftIso.shift_inr_comp_hom φ n

/-- The isomorphism `(triangle φ)⟦n⟧ ≅ triangle (φ⟦n⟧')` (Mathlib's
`mappingCone.shiftTriangleIso`). -/
noncomputable def shiftTriangleIso :
    (Triangle.shiftFunctor _ n).obj (triangle φ) ≅ triangle (φ⟦n⟧') := by
  refine Triangle.isoMk _ _ (Iso.refl _) (n.negOnePow • Iso.refl _) (shiftIso φ n) ?_ ?_ ?_
  · dsimp
    simp only [Linear.comp_units_smul, comp_id, id_comp, smul_smul, Int.units_mul_self, one_smul]
  · dsimp
    rw [Linear.units_smul_comp, Linear.units_smul_comp, id_comp, shiftIso_comm₂]
  · dsimp
    rw [CategoryTheory.Functor.map_id]
    erw [comp_id]
    rw [shiftFunctorComm_hom_app_eq]
    refine (congrArg (n.negOnePow • ·) (ShiftIso.comm₃ φ n)).trans ?_
    rw [smul_smul, Int.units_mul_self, one_smul]
    rfl

/-- The isomorphism `(triangleh φ)⟦n⟧ ≅ triangleh (φ⟦n⟧')` (Mathlib's
`mappingCone.shiftTrianglehIso`). -/
noncomputable def shiftTrianglehIso :
    (Triangle.shiftFunctor _ n).obj (triangleh φ) ≅ triangleh (φ⟦n⟧') :=
  ((quotient C).mapTriangle.commShiftIso n).symm.app _ ≪≫
    (quotient C).mapTriangle.mapIso (shiftTriangleIso φ n)

end Shift

end cone

/-! ### The pretriangulated structure -/

namespace HomotopyCategory

open cone

variable (C)

namespace Pretriangulated

/-- A triangle in the homotopy category is distinguished if it is isomorphic to the standard
triangle `triangleh φ` of a morphism `φ` of dg modules (Mathlib's
`HomotopyCategory.Pretriangulated.distinguishedTriangles`). -/
def distinguishedTriangles : Set (Triangle (HomotopyCategory.{w} C)) :=
  fun T => ∃ (M N : CatModule.{w} C) (φ : M ⟶ N), Nonempty (T ≅ triangleh φ)

variable {C}

theorem isomorphic_distinguished (T₁ : Triangle (HomotopyCategory.{w} C))
    (hT₁ : T₁ ∈ distinguishedTriangles C) (T₂ : Triangle (HomotopyCategory.{w} C))
    (e : T₂ ≅ T₁) : T₂ ∈ distinguishedTriangles C := by
  obtain ⟨M, N, φ, ⟨e'⟩⟩ := hT₁
  exact ⟨M, N, φ, ⟨e ≪≫ e'⟩⟩

theorem contractible_distinguished (X : HomotopyCategory.{w} C) :
    Pretriangulated.contractibleTriangle X ∈ distinguishedTriangles C := by
  obtain ⟨X⟩ := X
  refine ⟨_, _, 𝟙 X, ⟨?_⟩⟩
  have h := (isZero_quotient_obj_iff (cone (𝟙 X))).2 (cone.isContractible_id X)
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) h.isoZero.symm
    (by simp) (h.eq_of_tgt _ _) (by dsimp; ext)

theorem distinguished_cocone_triangle {X Y : HomotopyCategory.{w} C} (f : X ⟶ Y) :
    ∃ (Z : HomotopyCategory.{w} C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distinguishedTriangles C := by
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  obtain ⟨f, rfl⟩ := (quotient C).map_surjective f
  exact ⟨_, _, _, ⟨_, _, f, ⟨Iso.refl _⟩⟩⟩

theorem rotate_distinguished_triangle' (T : Triangle (HomotopyCategory.{w} C))
    (hT : T ∈ distinguishedTriangles C) : T.rotate ∈ distinguishedTriangles C := by
  obtain ⟨M, N, φ, ⟨e⟩⟩ := hT
  exact ⟨_, _, _, ⟨(rotate _).mapIso e ≪≫ rotateTrianglehIso φ⟩⟩

theorem shift_distinguished_triangle (T : Triangle (HomotopyCategory.{w} C))
    (hT : T ∈ distinguishedTriangles C) (n : ℤ) :
    (Triangle.shiftFunctor _ n).obj T ∈ distinguishedTriangles C := by
  obtain ⟨M, N, φ, ⟨e⟩⟩ := hT
  exact ⟨_, _, _, ⟨Functor.mapIso _ e ≪≫ shiftTrianglehIso φ n⟩⟩

theorem invRotate_distinguished_triangle' (T : Triangle (HomotopyCategory.{w} C))
    (hT : T ∈ distinguishedTriangles C) : T.invRotate ∈ distinguishedTriangles C :=
  isomorphic_distinguished _
    (shift_distinguished_triangle _ (rotate_distinguished_triangle' _
      (rotate_distinguished_triangle' _ hT)) _) _
    ((invRotateIsoRotateRotateShiftFunctorNegOne _).app T)

theorem rotate_distinguished_triangle (T : Triangle (HomotopyCategory.{w} C)) :
    T ∈ distinguishedTriangles C ↔ T.rotate ∈ distinguishedTriangles C := by
  constructor
  · exact rotate_distinguished_triangle' T
  · intro hT
    exact isomorphic_distinguished _ (invRotate_distinguished_triangle' T.rotate hT) _
      ((triangleRotation _).unitIso.app T)

theorem complete_distinguished_triangle_morphism
    (T₁ T₂ : Triangle (HomotopyCategory.{w} C))
    (hT₁ : T₁ ∈ distinguishedTriangles C) (hT₂ : T₂ ∈ distinguishedTriangles C)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (fac : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ (c : T₁.obj₃ ⟶ T₂.obj₃), T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
      T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨K₁, L₁, φ₁, ⟨e₁⟩⟩ := hT₁
  obtain ⟨K₂, L₂, φ₂, ⟨e₂⟩⟩ := hT₂
  obtain ⟨a', ha'⟩ : ∃ (a' : (quotient C).obj K₁ ⟶ (quotient C).obj K₂),
    a' = e₁.inv.hom₁ ≫ a ≫ e₂.hom.hom₁ := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ (b' : (quotient C).obj L₁ ⟶ (quotient C).obj L₂),
    b' = e₁.inv.hom₂ ≫ b ≫ e₂.hom.hom₂ := ⟨_, rfl⟩
  obtain ⟨a'', rfl⟩ := (quotient C).map_surjective a'
  obtain ⟨b'', rfl⟩ := (quotient C).map_surjective b'
  have H : DGHomotopy (φ₁ ≫ b'') (a'' ≫ φ₂) := homotopyOfEq _ _ (by
    have comm₁₁ := e₁.inv.comm₁
    have comm₁₂ := e₂.hom.comm₁
    dsimp at comm₁₁ comm₁₂
    simp only [Functor.map_comp, ha', hb', reassoc_of% comm₁₁,
      reassoc_of% fac, comm₁₂, assoc])
  let γ := e₁.hom ≫ trianglehMapOfHomotopy H ≫ e₂.inv
  have comm₂ := γ.comm₂
  have comm₃ := γ.comm₃
  dsimp [γ] at comm₂ comm₃
  simp only [ha', hb'] at comm₂ comm₃
  refine ⟨γ.hom₃, ?_, ?_⟩
  · simpa [γ] using comm₂
  · simpa [γ] using comm₃

end Pretriangulated

/-- The homotopy category of dg modules over a dg category is pretriangulated. -/
noncomputable instance pretriangulated : Pretriangulated (HomotopyCategory.{w} C) where
  distinguishedTriangles := Pretriangulated.distinguishedTriangles C
  isomorphic_distinguished := Pretriangulated.isomorphic_distinguished
  contractible_distinguished := Pretriangulated.contractible_distinguished
  distinguished_cocone_triangle := Pretriangulated.distinguished_cocone_triangle
  rotate_distinguished_triangle := Pretriangulated.rotate_distinguished_triangle
  complete_distinguished_triangle_morphism :=
    Pretriangulated.complete_distinguished_triangle_morphism

variable {C}

theorem triangleh_distinguished {M N : CatModule.{w} C} (φ : M ⟶ N) :
    triangleh φ ∈ distTriang (HomotopyCategory.{w} C) :=
  ⟨_, _, φ, ⟨Iso.refl _⟩⟩

end HomotopyCategory

end CatModule

end DG
