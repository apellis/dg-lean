import DG.Category.Homotopy.ConeCochain

/-!
# The mapping cone of a composition of morphisms of dg modules over a dg category

Let `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` be morphisms of dg modules over a dg category. This file is
a port of `DG.Homotopy.ConeComp` (the case of a dg ring; the cochain-level part of Mathlib's
`Mathlib/Algebra/Homology/HomotopyCategory/Triangulated.lean`), the input of the octahedron
axiom:

* the morphisms `DG.CatModule.cone.compMor₁ f g : cone f ⟶ cone (f ≫ g)`,
  `DG.CatModule.cone.compMor₂ f g : cone (f ≫ g) ⟶ cone g` and
  `DG.CatModule.cone.compMor₃ f g : cone g ⟶ (cone f)⟦1⟧` of Mathlib's
  `mappingConeCompTriangle`;
* the homotopy equivalence `DG.CatModule.cone.mappingConeCompHomotopyEquiv f g` between
  `cone g` and the cone of `compMor₁ f g`, with its compatibilities
  `mappingConeCompHomotopyEquiv_comm₁` and `mappingConeCompHomotopyEquiv_comm₂`.

All definitions and signs are those of Mathlib.
-/

open CategoryTheory

universe w v u

namespace DG

namespace CatModule

namespace cone

open Cochain

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] {X₁ X₂ X₃ : CatModule.{w} C} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)

/-- The first morphism `cone f ⟶ cone (f ≫ g)` of Mathlib's `mappingConeCompTriangle`. -/
def compMor₁ : cone f ⟶ cone (f ≫ g) :=
  map (𝟙 X₁) g (Category.id_comp _).symm

/-- The second morphism `cone (f ≫ g) ⟶ cone g` of Mathlib's `mappingConeCompTriangle`. -/
def compMor₂ : cone (f ≫ g) ⟶ cone g :=
  map f (𝟙 X₃) (Category.comp_id _)

/-- The third morphism `cone g ⟶ (cone f)⟦1⟧` of Mathlib's `mappingConeCompTriangle`: the
third morphism `-fstHom g` of the standard triangle of `g`, followed by `(inr f)⟦1⟧`. -/
def compMor₃ : cone g ⟶ shift 1 (cone f) :=
  (-fstHom g) ≫ shiftMap 1 (inr f)

variable {f g} {X : C}

@[simp]
theorem compMor₁_fst_apply (p : (cone f).obj X) :
    (fst (f ≫ g)).1.app X ((compMor₁ f g).app X p) = (fst f).1.app X p :=
  rfl

@[simp]
theorem compMor₁_snd_apply (p : (cone f).obj X) :
    (snd (f ≫ g)).app X ((compMor₁ f g).app X p) = g.app X ((snd f).app X p) := rfl

@[simp]
theorem compMor₂_fst_apply (p : (cone (f ≫ g)).obj X) :
    (fst g).1.app X ((compMor₂ f g).app X p) = f.app X ((fst (f ≫ g)).1.app X p) := rfl

@[simp]
theorem compMor₂_snd_apply (p : (cone (f ≫ g)).obj X) :
    (snd g).app X ((compMor₂ f g).app X p) = (snd (f ≫ g)).app X p :=
  rfl

variable (f g)

namespace MappingConeCompHomotopyEquiv

/-- The morphism `cone g ⟶ cone (compMor₁ f g)` of Mathlib's
`MappingConeCompHomotopyEquiv.hom`; it is a homotopy equivalence
(`DG.CatModule.cone.mappingConeCompHomotopyEquiv`). -/
def hom : cone g ⟶ cone (compMor₁ f g) :=
  lift _ (descCocycle g (ofHom (inr f)) 0 (zero_add 1) (by simp))
    (descCochain _ 0 (ofHom (inr (f ≫ g))) (neg_add_cancel 1)) (by
      refine Cochain.ext fun X p => ext_to ?_ ?_
      · simp [descCochain_apply, d_snd_apply]
      · simp [descCochain_apply, d_snd_apply])

/-- The morphism `cone (compMor₁ f g) ⟶ cone g` of Mathlib's
`MappingConeCompHomotopyEquiv.inv`. -/
def inv : cone (compMor₁ f g) ⟶ cone g :=
  desc _ ((inl g).comp (snd f) (zero_add (-1)))
    (desc _ ((inl g).comp (ofHom f) (zero_add (-1))) (inr g) (by
      rw [δ_ofHom_comp, δ_inl]; rfl)) (by
      refine Cochain.ext fun X p => ext_to ?_ ?_
      · simp [desc_apply, descCochain_apply, δ_neg_one_apply, inl_d_apply, d_snd_apply]
      · simp [desc_apply, descCochain_apply, δ_neg_one_apply, inl_d_apply, d_snd_apply])

@[simp]
theorem hom_comp_inv : hom f g ≫ inv f g = 𝟙 _ := by
  refine hom_ext fun X p => ext_to ?_ ?_
  · simp [hom, inv, lift_apply, desc_apply, descCochain_apply]
  · simp [hom, inv, lift_apply, desc_apply, descCochain_apply]

/-- The homotopy `inv ≫ hom ≃ 𝟙` of Mathlib's
`MappingConeCompHomotopyEquiv.homotopyInvHomId`, given by the cochain
`-inl ∘ inl ∘ fst ∘ snd` of degree `-1`. -/
def homotopyInvHomId : DGHomotopy (inv f g ≫ hom f g) (𝟙 _) :=
  DGHomotopy.mk' (-(((inl (compMor₁ f g)).comp (inl f) (show -1 + -1 = -2 by norm_num)).comp
    (fst (f ≫ g)).1 (show 1 + -2 = -1 by norm_num)).comp (snd (compMor₁ f g)) (zero_add (-1)))
    (fun p => by
      refine ext_to ?_ ?_
      · refine ext_to ?_ ?_
        · simp [hom, inv, lift_apply, desc_apply, descCochain_apply, d_fst_apply, d_snd_apply]
        · simp [hom, inv, lift_apply, desc_apply, descCochain_apply, d_fst_apply, d_snd_apply]
          abel
      · refine ext_to ?_ ?_
        · simp [hom, inv, lift_apply, desc_apply, descCochain_apply, d_fst_apply, d_snd_apply]
        · simp [hom, inv, lift_apply, desc_apply, descCochain_apply, d_fst_apply, d_snd_apply])

end MappingConeCompHomotopyEquiv

/-- The homotopy equivalence between `cone g` and the cone of
`compMor₁ f g : cone f ⟶ cone (f ≫ g)` (Mathlib's `mappingConeCompHomotopyEquiv`). -/
def mappingConeCompHomotopyEquiv : DGHomotopyEquiv (cone g) (cone (compMor₁ f g)) where
  hom := MappingConeCompHomotopyEquiv.hom f g
  inv := MappingConeCompHomotopyEquiv.inv f g
  homotopyHomInvId := DGHomotopy.ofEq (MappingConeCompHomotopyEquiv.hom_comp_inv f g)
  homotopyInvHomId := MappingConeCompHomotopyEquiv.homotopyInvHomId f g

@[simp]
theorem mappingConeCompHomotopyEquiv_hom_comp_inv :
    (mappingConeCompHomotopyEquiv f g).hom ≫ (mappingConeCompHomotopyEquiv f g).inv = 𝟙 _ :=
  MappingConeCompHomotopyEquiv.hom_comp_inv f g

/-- Mathlib's `mappingConeCompHomotopyEquiv_comm₁`. -/
theorem mappingConeCompHomotopyEquiv_comm₁ :
    inr (compMor₁ f g) ≫ (mappingConeCompHomotopyEquiv f g).inv = compMor₂ f g := by
  refine hom_ext fun X p => ext_to ?_ ?_
  · simp [mappingConeCompHomotopyEquiv, MappingConeCompHomotopyEquiv.inv, compMor₂, desc_apply]
  · simp [mappingConeCompHomotopyEquiv, MappingConeCompHomotopyEquiv.inv, compMor₂, desc_apply]

/-- Mathlib's `mappingConeCompHomotopyEquiv_comm₂`. -/
theorem mappingConeCompHomotopyEquiv_comm₂ :
    (mappingConeCompHomotopyEquiv f g).hom ≫ (-fstHom (compMor₁ f g)) = compMor₃ f g := by
  refine hom_ext fun X p => (shift.unmk 1).injective ?_
  simp only [compMor₃, comp_app, neg_app, map_neg, unmk_shiftMap_app, ← fst_apply]
  simp [mappingConeCompHomotopyEquiv, MappingConeCompHomotopyEquiv.hom, lift_apply,
    descCochain_apply]

end cone

end CatModule

end DG
