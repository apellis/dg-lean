import Mathlib.CategoryTheory.Triangulated.Functor
import DG.Homotopy.ConeCochain
import DG.Homotopy.Shift

/-!
# The pretriangulated structure on the homotopy category of dg modules

Let `A` be a dg ring. This file shows that the homotopy category `DG.HomotopyCategory A` of dg
`A`-modules is pretriangulated. It is a port of Mathlib's
`Mathlib/Algebra/Homology/HomotopyCategory/Pretriangulated.lean` (which follows Verdier's thesis
with the sign conventions of the introduction of B. Conrad, *Grothendieck duality and base
change*), with the same definitions and signs.

## Main definitions and results

* `DG.Cone.triangle φ`: for `φ : M ⟶ N` in `DGModuleCat A`, the standard triangle
  `M ⟶ N ⟶ Cone φ ⟶ M⟦1⟧` with morphisms `φ`, `inr φ` and `-fstHom φ`; its image
  `DG.Cone.triangleh φ` in the homotopy category.
* `DG.Cone.rotateHomotopyEquiv f : DGHomotopyEquiv A (Shift 1 M) (Cone (inr f))` and the
  isomorphism of triangles `DG.Cone.rotateTrianglehIso φ : (triangleh φ).rotate ≅
  triangleh (inr φ)`.
* `DG.Cone.shiftEquiv f n : Shift n (Cone f) ≃ᵈᵍ[A] Cone (f.shift n)` and the isomorphisms of
  triangles `DG.Cone.shiftTriangleIso` and `DG.Cone.shiftTrianglehIso`.
* `DG.Cone.trianglehMapOfHomotopy`: the morphism of standard triangles induced by a square
  commuting up to homotopy; `DG.Cone.triangleMap`, for a commutative square.
* `DG.HomotopyCategory.Pretriangulated.distinguishedTriangles A`: the triangles isomorphic to
  some `triangleh φ`; the instance `Pretriangulated (DG.HomotopyCategory A)`.

## Comparison with Mathlib

The names are Mathlib's (`CochainComplex.mappingCone.*` becomes `DG.Cone.*` and
`HomotopyCategory.Pretriangulated.*` becomes `DG.HomotopyCategory.Pretriangulated.*`), except:
Mathlib's `rotateHomotopyEquivComm₂Homotopy` is `DG.Cone.RotateHomotopyEquiv.comm₂Homotopy`;
Mathlib's `mappingCone.shiftIso` is `DG.Cone.shiftEquiv` on dg modules and `DG.Cone.shiftIso`
in `DGModuleCat A`; Mathlib's `mappingCone_triangleh_distinguished` is
`DG.HomotopyCategory.triangleh_distinguished`.

Composition of dg module maps is written `g.comp f` for Mathlib's `f ≫ g`, and composition of
cochains `z₂.comp z₁` for Mathlib's `z₁.comp z₂`. The identities between morphisms of dg
modules are proved on elements, which is possible since cochains are functions here.
-/

open CategoryTheory Category Limits Pretriangulated

universe v u

namespace DG

namespace DGModuleCat

variable {A : Type u} [Ring A] [DGAddCommGroup A]

theorem units_smul_apply {M N : DGModuleCat.{v} A} (k : ℤˣ) (f : M ⟶ N) (x : M) :
    (k • f) x = k • f x := rfl

theorem hom_units_smul {M N : DGModuleCat.{v} A} (k : ℤˣ) (f : M ⟶ N) :
    (k • f).hom = k • f.hom := rfl

end DGModuleCat

theorem DGModuleHom.units_smul_apply {A M N : Type*} [Ring A] [DGAddCommGroup A]
    [AddCommGroup M] [DGAddCommGroup M] [Module A M]
    [AddCommGroup N] [DGAddCommGroup N] [Module A N] (u : ℤˣ) (f : M →ᵈᵍ[A] N) (x : M) :
    (u • f) x = u • f x := rfl

/-- The coercion of a multiple of a cocycle by a unit. -/
@[simp]
theorem Cocycle.coe_units_smul {A M N : Type*} [Ring A] [DGAddCommGroup A]
    [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
    [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N] {n : ℤ} (u : ℤˣ)
    (z : Cocycle A M N n) :
    ((u • z : Cocycle A M N n) : Cochain A M N n) = u • (z : Cochain A M N n) :=
  rfl

namespace Cone

section Cochains

open Cochain Shift

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]

theorem fstHom_eq_mk_fst {M N : Type*}
    [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
    [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]
    (f : M →ᵈᵍ[A] N) (p : Cone f) : fstHom f p = Shift.mk 1 ((fst f).1 p) := rfl

/-! ### Rotation -/

section Rotate

variable {M N : Type*}
  [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]
  (f : M →ᵈᵍ[A] N)

namespace RotateHomotopyEquiv

/-- The morphism `M⟦1⟧ → Cone (inr f)` of Mathlib's `mappingCone.rotateHomotopyEquiv`. -/
def hom : Shift 1 M →ᵈᵍ[A] Cone (inr f) :=
  lift (inr f) (-(Cocycle.ofHom f).leftShift 1 1 (zero_add 1))
    (-(inl f).leftShift 1 0 (neg_add_cancel 1)) (by
      refine Cochain.ext fun x => ?_
      obtain ⟨x, rfl⟩ := Shift.mk_surjective (n := 1) x
      simp [δ_zero_cochain_apply, inl_d_apply, leftShift_apply, leftShiftSign])

/-- The morphism `Cone (inr f) → M⟦1⟧` of Mathlib's `mappingCone.rotateHomotopyEquiv`. -/
def inv : Cone (inr f) →ᵈᵍ[A] Shift 1 M :=
  desc (inr f) 0 (-fstHom f) (by
    refine Cochain.ext fun y => ?_
    simp)

variable {f}

theorem hom_apply (x : Shift 1 M) :
    hom f x = inl (inr f) (f (unmk 1 x)) - inr (inr f) (inl f (unmk 1 x)) := by
  obtain ⟨x, rfl⟩ := Shift.mk_surjective (n := 1) x
  simp [hom, lift_apply, leftShift_apply, leftShiftSign, sub_eq_add_neg]

@[simp]
theorem fst_hom_apply (x : Shift 1 M) : (fst (inr f)).1 (hom f x) = f (unmk 1 x) := by
  simp [hom_apply]

@[simp]
theorem snd_hom_apply (x : Shift 1 M) : snd (inr f) (hom f x) = -inl f (unmk 1 x) := by
  simp [hom_apply]

theorem inv_apply (p : Cone (inr f)) : inv f p = -fstHom f (snd (inr f) p) := by
  simp [inv, desc_apply]

variable (f)

@[simp]
theorem inv_comp_hom : (inv f).comp (hom f) = DGModuleHom.id := by
  refine DGModuleHom.ext fun x => ?_
  obtain ⟨x, rfl⟩ := Shift.mk_surjective (n := 1) x
  simp [inv_apply]
  rfl

/-- The homotopy `hom ∘ inv ≃ id` of Mathlib's `mappingCone.rotateHomotopyEquiv`, given by the
cochain `-inl (inr f) ∘ snd f ∘ snd (inr f)` of degree `-1`. -/
def homotopyInvHomId : DGHomotopy ((hom f).comp (inv f)) DGModuleHom.id :=
  DGHomotopy.mk' (-((inl (inr f)).comp (snd f) (zero_add (-1))).comp (snd (inr f)) (zero_add (-1)))
    (fun p => by
      refine ext_to ?_ ?_
      · simp [inv_apply, d_fst_apply, d_snd_apply, ← fst_apply]
        abel
      · refine ext_to ?_ ?_
        · simp [inv_apply, d_fst_apply, d_snd_apply, ← fst_apply]
        · simp [inv_apply, d_fst_apply, d_snd_apply, ← fst_apply])

/-- Mathlib's `rotateHomotopyEquivComm₂Homotopy`: the homotopy
`hom ∘ (-fstHom f) ≃ inr (inr f)`, given by the cochain `-inl (inr f) ∘ snd f`. -/
def comm₂Homotopy : DGHomotopy ((hom f).comp (-fstHom f)) (inr (inr f)) :=
  DGHomotopy.mk' (-(inl (inr f)).comp (snd f) (zero_add (-1))) (fun p => by
    refine ext_to ?_ ?_
    · simp [d_fst_apply, d_snd_apply, ← fst_apply]
    · refine ext_to ?_ ?_
      · simp [d_fst_apply, d_snd_apply, ← fst_apply]
      · simp [d_fst_apply, d_snd_apply, ← fst_apply])

/-- Mathlib's `rotateHomotopyEquiv_comm₃`. -/
theorem comm₃ : (-fstHom (inr f)).comp (hom f) = -f.shift 1 := by
  refine DGModuleHom.ext fun x => (unmk 1).injective ?_
  simp [← fst_apply, DGModuleHom.unmk_shift_apply]

end RotateHomotopyEquiv

/-- The homotopy equivalence `M⟦1⟧ ≃ Cone (inr f)` (Mathlib's
`mappingCone.rotateHomotopyEquiv`). -/
def rotateHomotopyEquiv : DGHomotopyEquiv A (Shift 1 M) (Cone (inr f)) where
  hom := RotateHomotopyEquiv.hom f
  inv := RotateHomotopyEquiv.inv f
  homotopyHomInvId := DGHomotopy.ofEq (RotateHomotopyEquiv.inv_comp_hom f)
  homotopyInvHomId := RotateHomotopyEquiv.homotopyInvHomId f

end Rotate

/-! ### Shifts of cones -/

section ShiftIso

variable {M N : Type*}
  [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]
  (f : M →ᵈᵍ[A] N) (n : ℤ)

namespace ShiftIso

/-- The morphism `(Cone f)⟦n⟧ → Cone (f⟦n⟧)` of Mathlib's `mappingCone.shiftIso`. -/
def hom : Shift n (Cone f) →ᵈᵍ[A] Cone (f.shift n) :=
  lift (f.shift n) (koszulSign n • (fst f).shift n) ((snd f).shift n) (by
    refine Cochain.ext fun x => ?_
    obtain ⟨x, rfl⟩ := Shift.mk_surjective (n := n) x
    simp [δ_zero_cochain_apply, d_snd_apply, Cocycle.coe_units_smul])

/-- The morphism `Cone (f⟦n⟧) → (Cone f)⟦n⟧` of Mathlib's `mappingCone.shiftIso`. -/
def inv : Cone (f.shift n) →ᵈᵍ[A] Shift n (Cone f) :=
  desc (f.shift n) (koszulSign n • (inl f).shift n) ((inr f).shift n) (by
    refine Cochain.ext fun x => ?_
    obtain ⟨x, rfl⟩ := Shift.mk_surjective (n := n) x
    simp [δ_neg_one_apply, inl_d_apply, smul_smul])

variable {f n}

@[simp]
theorem fst_hom_apply (x : Shift n (Cone f)) :
    (fst (f.shift n)).1 (hom f n x) = koszulSign n • Shift.mk n ((fst f).1 (unmk n x)) := by
  simp [hom, lift_apply]

@[simp]
theorem snd_hom_apply (x : Shift n (Cone f)) :
    snd (f.shift n) (hom f n x) = Shift.mk n (snd f (unmk n x)) := by
  simp [hom, lift_apply]
  rfl

theorem inv_apply (q : Cone (f.shift n)) :
    inv f n q = koszulSign n • Shift.mk n (inl f (unmk n ((fst (f.shift n)).1 q))) +
      Shift.mk n (inr f (unmk n (snd (f.shift n) q))) := by
  simp [inv, desc_apply]
  rfl

variable (f n)

@[simp]
theorem inv_comp_hom : (inv f n).comp (hom f n) = DGModuleHom.id := by
  refine DGModuleHom.ext fun x => ?_
  obtain ⟨x, rfl⟩ := Shift.mk_surjective (n := n) x
  simp [inv_apply, smul_smul]
  rw [← mk_add, id_X]

@[simp]
theorem hom_comp_inv : (hom f n).comp (inv f n) = DGModuleHom.id := by
  refine DGModuleHom.ext fun q => ext_to ?_ ?_
  · simp [inv_apply, smul_smul]
  · simp [inv_apply, smul_smul]

/-- Mathlib's `shiftTriangleIso`, second square. -/
theorem hom_comp_shift_inr : (hom f n).comp ((inr f).shift n) = inr (f.shift n) := by
  refine DGModuleHom.ext fun y => ?_
  obtain ⟨y, rfl⟩ := Shift.mk_surjective (n := n) y
  refine ext_to ?_ ?_ <;> simp

/-- Mathlib's `shiftTriangleIso`, third square. -/
theorem comm₃ : (Shift.shiftComm 1 n).toDGModuleHom.comp ((-fstHom f).shift n) =
    koszulSign n • (-fstHom (f.shift n)).comp (hom f n) := by
  refine DGModuleHom.ext fun x => ?_
  obtain ⟨x, rfl⟩ := Shift.mk_surjective (n := n) x
  simp [smul_smul, DGModuleHom.units_smul_apply, fstHom_eq_mk_fst]

end ShiftIso

/-- The isomorphism `(Cone f)⟦n⟧ ≃ Cone (f⟦n⟧)` (Mathlib's `mappingCone.shiftIso`). -/
def shiftEquiv : Shift n (Cone f) ≃ᵈᵍ[A] Cone (f.shift n) where
  toFun := ShiftIso.hom f n
  invFun := ShiftIso.inv f n
  left_inv x := congrArg (fun φ => φ x) (ShiftIso.inv_comp_hom f n)
  right_inv q := congrArg (fun φ => φ q) (ShiftIso.hom_comp_inv f n)
  map_add' := map_add _
  map_smul' := map_smul _
  map_mem' := (ShiftIso.hom f n).map_mem
  map_d' := (ShiftIso.hom f n).map_d

end ShiftIso

end Cochains

/-! ### The standard triangles -/

open DGModuleCat HomotopyCategory

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]

section Triangle

variable {M N : DGModuleCat.{v} A} (φ : M ⟶ N)

/-- The standard triangle `M ⟶ N ⟶ Cone φ ⟶ M⟦1⟧` in `DGModuleCat A` attached to a morphism
`φ : M ⟶ N`, with the morphisms `φ`, `inr φ` and `-fstHom φ` (Mathlib's
`CochainComplex.mappingCone.triangle`). -/
@[simps! obj₁ obj₂ obj₃ mor₁ mor₂]
def triangle : Triangle (DGModuleCat.{v} A) :=
  Triangle.mk φ (ofHom (inr φ.hom)) (ofHom (-fstHom φ.hom))

@[simp]
theorem triangle_mor₃_hom : (triangle φ).mor₃.hom = -fstHom φ.hom := rfl

@[reassoc (attr := simp)]
theorem inr_triangleδ : ofHom (inr φ.hom) ≫ (triangle φ).mor₃ = 0 :=
  hom_ext_apply fun y => by simp [DGModuleCat.comp_apply]

/-- The standard triangle in the homotopy category attached to a morphism of dg modules
(Mathlib's `CochainComplex.mappingCone.triangleh`). -/
noncomputable abbrev triangleh : Triangle (HomotopyCategory.{v} A) :=
  (quotient A).mapTriangle.obj (triangle φ)

end Triangle

section MapOfHomotopy

variable {M₁ N₁ M₂ N₂ : DGModuleCat.{v} A} {φ₁ : M₁ ⟶ N₁} {φ₂ : M₂ ⟶ N₂}
  {a : M₁ ⟶ M₂} {b : N₁ ⟶ N₂} (H : DGHomotopy (φ₁ ≫ b).hom (a ≫ φ₂).hom)

@[reassoc]
theorem triangleMapOfHomotopy_comm₂ :
    ofHom (inr φ₁.hom) ≫ ofHom (mapOfHomotopy H) = b ≫ ofHom (inr φ₂.hom) :=
  hom_ext (mapOfHomotopy_comp_inr H)

@[reassoc]
theorem triangleMapOfHomotopy_comm₃ :
    ofHom (mapOfHomotopy H) ≫ (triangle φ₂).mor₃ = (triangle φ₁).mor₃ ≫ a⟦(1 : ℤ)⟧' :=
  hom_ext_apply fun p => by
    have h := congrArg (fun g => g p) (fstHom_comp_mapOfHomotopy H)
    simp only [DGModuleHom.comp_apply] at h
    simp [DGModuleCat.comp_apply]
    exact h

/-- The morphism `triangleh φ₁ ⟶ triangleh φ₂` induced by a square commuting up to homotopy
(Mathlib's `trianglehMapOfHomotopy`). -/
@[simps]
noncomputable def trianglehMapOfHomotopy : triangleh φ₁ ⟶ triangleh φ₂ where
  hom₁ := (quotient A).map a
  hom₂ := (quotient A).map b
  hom₃ := (quotient A).map (ofHom (mapOfHomotopy H))
  comm₁ := by
    dsimp
    simp only [← Functor.map_comp]
    exact eq_of_homotopy _ _ H
  comm₂ := by
    dsimp
    simp only [← Functor.map_comp, triangleMapOfHomotopy_comm₂]
  comm₃ := by
    dsimp
    rw [← Functor.map_comp_assoc, triangleMapOfHomotopy_comm₃, Functor.map_comp, assoc, assoc]
    simp

end MapOfHomotopy

section Map

variable {M₁ N₁ M₂ N₂ : DGModuleCat.{v} A} (φ₁ : M₁ ⟶ N₁) (φ₂ : M₂ ⟶ N₂)
  (a : M₁ ⟶ M₂) (b : N₁ ⟶ N₂) (comm : φ₁ ≫ b = a ≫ φ₂)

/-- The morphism `triangle φ₁ ⟶ triangle φ₂` induced by a commutative square (Mathlib's
`mappingCone.triangleMap`). -/
@[simps!]
def triangleMap : triangle φ₁ ⟶ triangle φ₂ where
  hom₁ := a
  hom₂ := b
  hom₃ := ofHom (map a.hom b.hom (congrArg Hom.hom comm))
  comm₁ := comm
  comm₂ := hom_ext (map_comp_inr _ _ (congrArg Hom.hom comm))
  comm₃ := hom_ext_apply fun p => by
    simp [DGModuleCat.comp_apply]

end Map

section Rotate

variable {M N : DGModuleCat.{v} A} (φ : M ⟶ N)

@[reassoc (attr := simp)]
theorem rotateHomotopyEquiv_comm₂ :
    (quotient A).map (triangle φ).mor₃ ≫
      (quotient A).map (ofHom (rotateHomotopyEquiv φ.hom).hom) =
      (quotient A).map (ofHom (inr (inr φ.hom))) := by
  rw [← Functor.map_comp]
  exact eq_of_homotopy _ _ (RotateHomotopyEquiv.comm₂Homotopy φ.hom)

@[reassoc (attr := simp)]
theorem rotateHomotopyEquiv_comm₃ :
    ofHom (rotateHomotopyEquiv φ.hom).hom ≫ (triangle (ofHom (inr φ.hom))).mor₃ =
      -φ⟦(1 : ℤ)⟧' :=
  hom_ext (RotateHomotopyEquiv.comm₃ φ.hom)

/-- The isomorphism of triangles `(triangleh φ).rotate ≅ triangleh (inr φ)` (Mathlib's
`mappingCone.rotateTrianglehIso`). -/
noncomputable def rotateTrianglehIso :
    (triangleh φ).rotate ≅ triangleh (ofHom (inr φ.hom)) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (((quotient A).commShiftIso (1 : ℤ)).symm.app M ≪≫
      isoOfHomotopyEquiv (rotateHomotopyEquiv φ.hom))
    (by dsimp; simp) (by dsimp; simp) (by
      dsimp
      rw [CategoryTheory.Functor.map_id, comp_id, assoc, ← Functor.map_comp_assoc,
        rotateHomotopyEquiv_comm₃, Functor.map_neg, Preadditive.neg_comp,
        Functor.commShiftIso_hom_naturality, Preadditive.comp_neg,
        Iso.inv_hom_id_app_assoc])

end Rotate

section Shift

variable {M N : DGModuleCat.{v} A} (φ : M ⟶ N) (n : ℤ)

/-- The isomorphism `(Cone φ)⟦n⟧ ≅ Cone (φ⟦n⟧')` (Mathlib's `mappingCone.shiftIso`). -/
def shiftIso : (of A (Cone φ.hom))⟦n⟧ ≅ of A (Cone (φ⟦n⟧').hom) :=
  (shiftEquiv φ.hom n).toDGModuleCatIso

theorem shiftIso_hom_apply (x : Shift n (Cone φ.hom)) :
    (shiftIso φ n).hom x = ShiftIso.hom φ.hom n x := rfl

@[reassoc]
theorem shiftIso_comm₂ :
    (DGModuleCat.ofHom (inr φ.hom))⟦n⟧' ≫ (shiftIso φ n).hom =
      DGModuleCat.ofHom (inr (φ⟦n⟧').hom) :=
  hom_ext (ShiftIso.hom_comp_shift_inr φ.hom n)

theorem shiftIso_comm₃ :
    (triangle φ).mor₃⟦n⟧' ≫ (shiftFunctorComm (DGModuleCat.{v} A) 1 n).hom.app M =
      n.negOnePow • ((shiftIso φ n).hom ≫ (triangle (φ⟦n⟧')).mor₃) := by
  rw [shiftFunctorComm_hom_app_eq]
  exact hom_ext (ShiftIso.comm₃ φ.hom n)

/-- The isomorphism `(triangle φ)⟦n⟧ ≅ triangle (φ⟦n⟧')` (Mathlib's
`mappingCone.shiftTriangleIso`). -/
noncomputable def shiftTriangleIso :
    (Triangle.shiftFunctor _ n).obj (triangle φ) ≅ triangle (φ⟦n⟧') := by
  refine Triangle.isoMk _ _ (Iso.refl _) (n.negOnePow • Iso.refl _) (shiftIso φ n) ?_ ?_ ?_
  · dsimp
    simp only [Linear.comp_units_smul, comp_id, id_comp, smul_smul, Int.units_mul_self, one_smul]
  · dsimp
    rw [Linear.units_smul_comp, Linear.units_smul_comp, id_comp, shiftIso_comm₂]
    rfl
  · dsimp
    rw [CategoryTheory.Functor.map_id]
    erw [comp_id]
    rw [shiftIso_comm₃, smul_smul, Int.units_mul_self, one_smul]

/-- The isomorphism `(triangleh φ)⟦n⟧ ≅ triangleh (φ⟦n⟧')` (Mathlib's
`mappingCone.shiftTrianglehIso`). -/
noncomputable def shiftTrianglehIso :
    (Triangle.shiftFunctor _ n).obj (triangleh φ) ≅ triangleh (φ⟦n⟧') :=
  ((quotient A).mapTriangle.commShiftIso n).symm.app _ ≪≫
    (quotient A).mapTriangle.mapIso (shiftTriangleIso φ n)

end Shift

end Cone

/-! ### The pretriangulated structure -/

namespace HomotopyCategory

open Cone

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

namespace Pretriangulated

/-- A triangle in the homotopy category is distinguished if it is isomorphic to the standard
triangle `triangleh φ` of a morphism `φ` of dg modules (Mathlib's
`HomotopyCategory.Pretriangulated.distinguishedTriangles`). -/
def distinguishedTriangles : Set (Triangle (HomotopyCategory.{v} A)) :=
  fun T => ∃ (M N : DGModuleCat.{v} A) (φ : M ⟶ N), Nonempty (T ≅ triangleh φ)

variable {A}

theorem isomorphic_distinguished (T₁ : Triangle (HomotopyCategory.{v} A))
    (hT₁ : T₁ ∈ distinguishedTriangles A) (T₂ : Triangle (HomotopyCategory.{v} A))
    (e : T₂ ≅ T₁) : T₂ ∈ distinguishedTriangles A := by
  obtain ⟨M, N, φ, ⟨e'⟩⟩ := hT₁
  exact ⟨M, N, φ, ⟨e ≪≫ e'⟩⟩

theorem contractible_distinguished (X : HomotopyCategory.{v} A) :
    Pretriangulated.contractibleTriangle X ∈ distinguishedTriangles A := by
  obtain ⟨X⟩ := X
  refine ⟨_, _, 𝟙 X, ⟨?_⟩⟩
  have h := (isZero_quotient_obj_iff (DGModuleCat.of A (Cone (𝟙 X : X ⟶ X).hom))).2
    (Cone.isContractible_id X)
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) h.isoZero.symm
    (by simp) (h.eq_of_tgt _ _) (by dsimp; ext)

theorem distinguished_cocone_triangle {X Y : HomotopyCategory.{v} A} (f : X ⟶ Y) :
    ∃ (Z : HomotopyCategory.{v} A) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distinguishedTriangles A := by
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  obtain ⟨f, rfl⟩ := (quotient A).map_surjective f
  exact ⟨_, _, _, ⟨_, _, f, ⟨Iso.refl _⟩⟩⟩

theorem rotate_distinguished_triangle' (T : Triangle (HomotopyCategory.{v} A))
    (hT : T ∈ distinguishedTriangles A) : T.rotate ∈ distinguishedTriangles A := by
  obtain ⟨M, N, φ, ⟨e⟩⟩ := hT
  exact ⟨_, _, _, ⟨(rotate _).mapIso e ≪≫ rotateTrianglehIso φ⟩⟩

theorem shift_distinguished_triangle (T : Triangle (HomotopyCategory.{v} A))
    (hT : T ∈ distinguishedTriangles A) (n : ℤ) :
    (Triangle.shiftFunctor _ n).obj T ∈ distinguishedTriangles A := by
  obtain ⟨M, N, φ, ⟨e⟩⟩ := hT
  exact ⟨_, _, _, ⟨Functor.mapIso _ e ≪≫ shiftTrianglehIso φ n⟩⟩

theorem invRotate_distinguished_triangle' (T : Triangle (HomotopyCategory.{v} A))
    (hT : T ∈ distinguishedTriangles A) : T.invRotate ∈ distinguishedTriangles A :=
  isomorphic_distinguished _
    (shift_distinguished_triangle _ (rotate_distinguished_triangle' _
      (rotate_distinguished_triangle' _ hT)) _) _
    ((invRotateIsoRotateRotateShiftFunctorNegOne _).app T)

theorem rotate_distinguished_triangle (T : Triangle (HomotopyCategory.{v} A)) :
    T ∈ distinguishedTriangles A ↔ T.rotate ∈ distinguishedTriangles A := by
  constructor
  · exact rotate_distinguished_triangle' T
  · intro hT
    exact isomorphic_distinguished _ (invRotate_distinguished_triangle' T.rotate hT) _
      ((triangleRotation _).unitIso.app T)

theorem complete_distinguished_triangle_morphism
    (T₁ T₂ : Triangle (HomotopyCategory.{v} A))
    (hT₁ : T₁ ∈ distinguishedTriangles A) (hT₂ : T₂ ∈ distinguishedTriangles A)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (fac : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ (c : T₁.obj₃ ⟶ T₂.obj₃), T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
      T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨K₁, L₁, φ₁, ⟨e₁⟩⟩ := hT₁
  obtain ⟨K₂, L₂, φ₂, ⟨e₂⟩⟩ := hT₂
  obtain ⟨a', ha'⟩ : ∃ (a' : (quotient A).obj K₁ ⟶ (quotient A).obj K₂),
    a' = e₁.inv.hom₁ ≫ a ≫ e₂.hom.hom₁ := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ (b' : (quotient A).obj L₁ ⟶ (quotient A).obj L₂),
    b' = e₁.inv.hom₂ ≫ b ≫ e₂.hom.hom₂ := ⟨_, rfl⟩
  obtain ⟨a'', rfl⟩ := (quotient A).map_surjective a'
  obtain ⟨b'', rfl⟩ := (quotient A).map_surjective b'
  have H : DGHomotopy (φ₁ ≫ b'').hom (a'' ≫ φ₂).hom := homotopyOfEq _ _ (by
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

/-- The homotopy category of dg modules is pretriangulated. -/
noncomputable instance pretriangulated : Pretriangulated (HomotopyCategory.{v} A) where
  distinguishedTriangles := Pretriangulated.distinguishedTriangles A
  isomorphic_distinguished := Pretriangulated.isomorphic_distinguished
  contractible_distinguished := Pretriangulated.contractible_distinguished
  distinguished_cocone_triangle := Pretriangulated.distinguished_cocone_triangle
  rotate_distinguished_triangle := Pretriangulated.rotate_distinguished_triangle
  complete_distinguished_triangle_morphism :=
    Pretriangulated.complete_distinguished_triangle_morphism

variable {A}

theorem triangleh_distinguished {M N : DGModuleCat.{v} A} (φ : M ⟶ N) :
    triangleh φ ∈ distTriang (HomotopyCategory.{v} A) :=
  ⟨_, _, φ, ⟨Iso.refl _⟩⟩

end HomotopyCategory

end DG
