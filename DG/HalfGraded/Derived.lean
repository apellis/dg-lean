import DG.HalfGraded.Parity
import DG.Bigraded.Derived
import DG.Category.Derived.KProjective
import DG.Category.Derived.Compact

/-!
# The derived category of half-graded dg modules

Let `H` be a half-graded dg ring with parameter `k` and `C_H = DG.WeightCategory H.Regraded`.
The homotopy category `H(C_H)` and the derived category `D(C_H)` of dg modules over `C_H` are
the homotopy and derived categories of half-graded dg modules; they are triangulated with the
translation `⟦1⟧` (tier 3 and 4 for dg categories). By `DG.HalfGraded.Parity`, on half-graded
modules `⟦1⟧ = Π ∘ ⟨k⟩` is the parity shift combined with the internal shift `⟨k⟩`, with the sign
conventions of the shift of `docs/CONVENTIONS.md`.

## Main definitions and results

* `DG.HalfGradedDGRing.isKProjective_internalShift`,
  `DG.HalfGradedDGRing.isKProjective_parityShift`:
  internal and parity shifts preserve K-projective modules.
* `DG.HalfGradedDGRing.parityShiftD H`: the parity shift `Π = ⟨-k⟩ ⋙ ⟦1⟧` on `D(C_H)`, induced by
  the parity shift of dg modules (`DG.HalfGradedDGRing.QCompParityShiftDIso`), an involution
  (`DG.HalfGradedDGRing.parityShiftDIso : Π ⋙ Π ≅ 𝟭`).
* `DG.HalfGradedDGRing.shiftOneIso : ⟦1⟧ ≅ ⟨k⟩ ⋙ Π`: the translation of `D(C_H)` is the parity
  shift combined with the internal shift `⟨k⟩`; `DG.HalfGradedDGRing.internalShiftOddIso :
  ⟨k⟩ ≅ ⟦1⟧ ⋙ Π`: the internal shift `⟨k⟩` is isomorphic to the translation up to an odd natural
  isomorphism, and for `k = 2`,
  `DG.HalfGradedDGRing.internalShiftOneOneOddIso : ⟨1⟩ ⋙ ⟨1⟩ ≅ ⟦1⟧ ⋙ Π`.
* Odd morphisms in `D(C_H)` (item (b) on derived categories): for a K-projective `P`,
  `DG.HalfGradedDGRing.oddDerivedEquiv`: odd closed maps `P → N` up to homotopy are the morphisms
  `P → Π N` of `D(C_H)`.
* `DG.HalfGradedDGRing.OddIso X Y`: `X` and `Y` are *oddly isomorphic* in `D(C_H)`: there are odd
  closed maps between their K-projective representatives (`DG.CatModule.DerivedCategory.kProjRep`)
  whose two composites are homotopic to the identities. `DG.HalfGradedDGRing.oddIso_iff`:
  `OddIso X Y ↔ Nonempty (X ≅ Π Y)`, and `DG.HalfGradedDGRing.oddIso_iff'`:
  `OddIso X Y ↔ Nonempty (Π X ≅ Y)`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Category Limits

universe w' w u

noncomputable section

namespace DG

namespace HalfGradedDGRing

variable {A : Type u} [Ring A] {k : ℤ} (H : HalfGradedDGRing A k)

open CatModule WeightCategory

/-! ### K-projective modules -/

section KProjective

/-- The dg functors `k ↦ k + s` and `k ↦ k - s` of `C_H` compose to the identity, by
`1 ∈ A⟨0⟩`. -/
def shiftFunctorCompIso (s t : ℤ) (h : s + t = 0) :
    WeightCategory.shiftFunctor H.Regraded s ⋙ WeightCategory.shiftFunctor H.Regraded t ≅
      𝟭 _ :=
  NatIso.ofComponents (fun _ => isoOfEq (by simp [add_assoc, h]))
    (fun f => Subtype.ext (by simp))

/-- Restriction along `k ↦ k + s` followed by restriction along `k ↦ k - s` is isomorphic to the
identity, by the action of `1 ∈ A⟨0⟩`. -/
def internalShiftCompIso (s : ℤ) :
    internalShiftFunctor.{w} H s ⋙ internalShiftFunctor H (-s) ≅ 𝟭 _ :=
  (precompCompIso _ _).symm ≪≫
    precompNatIso (shiftFunctorCompIso H (-s) s (neg_add_cancel s))
      (fun _ => mem_grading_zero_of_val_eq_one _ rfl) (fun _ => d_eq_zero_of_val_eq_one _ rfl)
      (fun _ => mem_grading_zero_of_val_eq_one _ rfl) (fun _ => d_eq_zero_of_val_eq_one _ rfl) ≪≫
    precompIdIso _

/-- Restriction along `k ↦ k - s` followed by restriction along `k ↦ k + s` is isomorphic to the
identity, by the action of `1 ∈ A⟨0⟩`. -/
def internalShiftCompIso' (s : ℤ) :
    internalShiftFunctor.{w} H (-s) ⋙ internalShiftFunctor H s ≅ 𝟭 _ :=
  (precompCompIso _ _).symm ≪≫
    precompNatIso (shiftFunctorCompIso H s (-s) (add_neg_cancel s))
      (fun _ => mem_grading_zero_of_val_eq_one _ rfl) (fun _ => d_eq_zero_of_val_eq_one _ rfl)
      (fun _ => mem_grading_zero_of_val_eq_one _ rfl) (fun _ => d_eq_zero_of_val_eq_one _ rfl) ≪≫
    precompIdIso _

variable {H}

/-- The internal shift of a K-projective module is K-projective. -/
theorem isKProjective_internalShift {P : CatModule.{w} (WeightCategory H.Regraded)}
    (hP : CatModule.IsKProjective P) (s : ℤ) :
    CatModule.IsKProjective ((internalShiftFunctor H s).obj P) := by
  intro N hN f
  let e' := (internalShiftCompIso H s).app P
  have hN' : CatModule.IsAcyclic ((internalShiftFunctor H (-s)).obj N) := hN.precomp _
  have h₁ : CatModule.Homotopic (e'.inv ≫ (internalShiftFunctor H (-s)).map f) 0 := hP _ hN' _
  have h₂ : CatModule.Homotopic ((internalShiftFunctor H (-s)).map f) 0 := by
    have := h₁.comp_left e'.hom
    rwa [Iso.hom_inv_id_assoc, comp_zero] at this
  have h₃ : CatModule.Homotopic
      ((internalShiftFunctor H s).map ((internalShiftFunctor H (-s)).map f)) 0 :=
    ⟨(h₂.some.precomp _).trans (CatModule.DGHomotopy.ofEq (Functor.map_zero _ _ _))⟩
  have h₄ := (h₃.comp_left ((internalShiftCompIso' H s).inv.app _)).comp_right
    ((internalShiftCompIso' H s).hom.app N)
  have hnat := (internalShiftCompIso' H s).hom.naturality f
  simp only [Functor.comp_map, Functor.id_map] at hnat
  rwa [comp_zero, zero_comp, assoc, hnat, Iso.inv_hom_id_app_assoc] at h₄

/-- The parity shift of a K-projective module is K-projective. -/
theorem isKProjective_parityShift {P : CatModule.{w} (WeightCategory H.Regraded)}
    (hP : CatModule.IsKProjective P) : CatModule.IsKProjective ((parityShift H).obj P) :=
  (isKProjective_internalShift hP (-k)).shift 1

end KProjective

/-! ### The parity shift on the derived category -/

section Derived

variable [CatModule.HasDerivedCategory.{w', w} (WeightCategory H.Regraded)]

/-- The parity shift `Π = ⟨-k⟩ ⋙ ⟦1⟧` on the derived category `D(C_H)` of half-graded dg
modules. -/
def parityShiftD : CatModule.DerivedCategory.{w', w} (WeightCategory H.Regraded) ⥤
    CatModule.DerivedCategory.{w', w} (WeightCategory H.Regraded) :=
  CatModule.DerivedCategory.internalShift H.Regraded (-k) ⋙ shiftFunctor _ (1 : ℤ)

/-- The parity shift on `D(C_H)` is induced by the parity shift of dg modules. -/
def QCompParityShiftDIso :
    CatModule.DerivedCategory.Q ⋙ parityShiftD.{w'} H ≅
      parityShift H ⋙ CatModule.DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (CatModule.DerivedCategory.QCompInternalShiftIso H.Regraded (-k)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (CatModule.DerivedCategory.Q.commShiftIso (1 : ℤ)).symm ≪≫
    (Functor.associator _ _ _).symm

/-- The parity shift on `D(C_H)` is an involution, `Π ⋙ Π ≅ 𝟭`, induced by the isomorphism
`Π Π M ≅ M`, `m ↦ u⁻¹ • m`, of dg modules. -/
def parityShiftDIso : parityShiftD.{w'} H ⋙ parityShiftD H ≅ 𝟭 _ :=
  (Localization.whiskeringLeftFunctor' CatModule.DerivedCategory.Q
    (CatModule.quasiIso (WeightCategory H.Regraded)) _).preimageIso
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (QCompParityShiftDIso H) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (QCompParityShiftDIso H) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (parityShiftIso H) _ ≪≫
      Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm)

/-- The translation of `D(C_H)` is the parity shift combined with the internal shift `⟨k⟩`:
`⟦1⟧ ≅ ⟨k⟩ ⋙ Π`. -/
def shiftOneIso : shiftFunctor (CatModule.DerivedCategory.{w', w} (WeightCategory H.Regraded))
    (1 : ℤ) ≅ CatModule.DerivedCategory.internalShift H.Regraded k ⋙ parityShiftD H :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight ((CatModule.DerivedCategory.internalShiftZeroIso H.Regraded).symm ≪≫
      (CatModule.DerivedCategory.internalShiftAction H.Regraded).isoOfEq (add_neg_cancel k).symm ≪≫
      CatModule.DerivedCategory.internalShiftAddIso H.Regraded k (-k)) _ ≪≫
    Functor.associator _ _ _

/-- The internal shift `⟨k⟩` is isomorphic to the translation `⟦1⟧` up to an odd natural
isomorphism: `⟨k⟩ ≅ ⟦1⟧ ⋙ Π` (an odd morphism `X → Y` being a morphism `X → Π Y`). -/
def internalShiftOddIso : CatModule.DerivedCategory.internalShift.{w', w} H.Regraded k ≅
    shiftFunctor _ (1 : ℤ) ⋙ parityShiftD H :=
  ((Functor.isoWhiskerRight (shiftOneIso H) _) ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (parityShiftDIso H) ≪≫ Functor.rightUnitor _).symm

/-- For `k = 2`, `⟨1⟩ ⋙ ⟨1⟩` is isomorphic to the translation `⟦1⟧` up to an odd natural
isomorphism: `⟨1⟩ ⋙ ⟨1⟩ ≅ ⟦1⟧ ⋙ Π`. -/
def internalShiftOneOneOddIso (hk : k = 2) :
    CatModule.DerivedCategory.internalShift.{w', w} H.Regraded 1 ⋙
        CatModule.DerivedCategory.internalShift H.Regraded 1 ≅
      shiftFunctor _ (1 : ℤ) ⋙ parityShiftD H :=
  (CatModule.DerivedCategory.internalShiftAddIso H.Regraded 1 1).symm ≪≫
    (CatModule.DerivedCategory.internalShiftAction H.Regraded).isoOfEq (by rw [hk]; rfl) ≪≫
    internalShiftOddIso H

variable {H}

/-- Odd closed maps out of a K-projective module up to homotopy are the morphisms `P → Π N` of
the derived category. -/
def oddDerivedEquiv {P : CatModule.{w} (WeightCategory H.Regraded)}
    (hP : CatModule.IsKProjective P) (N : CatModule.{w} (WeightCategory H.Regraded)) :
    (OddCocycle H P N ⧸ CatModule.Cocycle.coboundaries P ((internalShiftFunctor H (-k)).obj N) 1)
      ≃+ (CatModule.DerivedCategory.Q.obj P ⟶
        (parityShiftD.{w'} H).obj (CatModule.DerivedCategory.Q.obj N)) :=
  (oddHomotopyEquiv H P N).trans
    ((AddEquiv.ofBijective (CatModule.DerivedCategory.Qh.mapAddHom
      (X := (CatModule.HomotopyCategory.quotient _).obj P)
      (Y := (CatModule.HomotopyCategory.quotient _).obj ((parityShift H).obj N)))
      (CatModule.DerivedCategory.Qh_map_bijective_of_isKProjective hP _)).trans
    { toFun := fun f => f ≫ ((QCompParityShiftDIso H).app N).inv
      invFun := fun f => f ≫ ((QCompParityShiftDIso H).app N).hom
      left_inv := fun f => by
        simp only [assoc]
        exact (congrArg (f ≫ ·) (Iso.inv_hom_id _)).trans (Category.comp_id f)
      right_inv := fun f => by
        simp only [assoc]
        exact (congrArg (f ≫ ·) (Iso.hom_inv_id _)).trans (Category.comp_id f)
      map_add' := fun f g => Preadditive.add_comp _ _ _ _ _ _ })

end Derived

/-! ### Odd isomorphisms in the derived category -/

section OddIso

variable [CatModule.HasDerivedCategory.{w', max u w} (WeightCategory H.Regraded)]

open CatModule.DerivedCategory

variable {H}

/-- Two objects `X`, `Y` of `D(C_H)` are *oddly isomorphic* if there are odd closed maps
`z : P_X → P_Y` and `z' : P_Y → P_X` between their K-projective representatives
(`DG.CatModule.DerivedCategory.kProjRep`) whose composites `z' ∘ z` and `z ∘ z'` (even closed
maps, `DG.HalfGradedDGRing.oddComp`) are homotopic to the identities. -/
def OddIso (X Y : CatModule.DerivedCategory.{w', max u w} (WeightCategory H.Regraded)) : Prop :=
  ∃ (z : OddCocycle H (kProjRep X) (kProjRep Y)) (z' : OddCocycle H (kProjRep Y) (kProjRep X)),
    CatModule.Homotopic (oddComp z z') (𝟙 _) ∧ CatModule.Homotopic (oddComp z' z) (𝟙 _)

theorem homotopic_iff_Q_map_eq {M N : CatModule.{max u w} (WeightCategory H.Regraded)}
    (hM : CatModule.IsKProjective M) (f g : M ⟶ N) :
    CatModule.Homotopic f g ↔ (Q.map f : Q.obj M ⟶ Q.obj N) = Q.map g := by
  rw [CatModule.Homotopic.iff_sub, ← Q_map_eq_zero_iff hM, Functor.map_sub, sub_eq_zero]

/-- Odd isomorphisms are the isomorphisms `X ≅ Π Y` of `D(C_H)`. -/
theorem oddIso_iff (X Y : CatModule.DerivedCategory.{w', max u w} (WeightCategory H.Regraded)) :
    OddIso X Y ↔ Nonempty (X ≅ (parityShiftD H).obj Y) := by
  have hX := isKProjective_kProjRep X
  have hY := isKProjective_kProjRep Y
  have hY' := isKProjective_parityShift hY
  constructor
  · rintro ⟨z, z', h₁, h₂⟩
    let f := oddEquiv H _ _ z
    let g := oddEquiv' H _ _ z'
    have hfg : CatModule.Homotopic (f ≫ g) (𝟙 _) := by rwa [← oddComp_eq']
    have hgf : CatModule.Homotopic (g ≫ f) (𝟙 _) := by
      have : g ≫ f = (parityShift H).map (oddComp z' z) := by
        show oddEquiv' H _ _ z' ≫ oddEquiv H _ _ z = _
        rw [oddComp_eq', Functor.map_comp, oddEquiv'_apply z', oddEquiv_eq_parityShiftHomEquiv z,
          parityShiftHomEquiv_apply, assoc, Iso.hom_inv_id_assoc]
      rw [this, ← CategoryTheory.Functor.map_id]
      exact homotopic_parityShift_map h₂
    have e : Q.obj (kProjRep X) ≅ Q.obj ((parityShift H).obj (kProjRep Y)) :=
      { hom := Q.map f
        inv := Q.map g
        hom_inv_id := by
          rw [← Q.map_comp, ← Q.map_id]
          exact (homotopic_iff_Q_map_eq hX _ _).mp hfg
        inv_hom_id := by
          rw [← Q.map_comp, ← Q.map_id]
          exact (homotopic_iff_Q_map_eq hY' _ _).mp hgf }
    exact ⟨kProjRepIso X ≪≫ e ≪≫ ((QCompParityShiftDIso H).app _).symm ≪≫
      (parityShiftD H).mapIso (kProjRepIso Y).symm⟩
  · rintro ⟨e⟩
    let e₁ : Q.obj (kProjRep X) ≅ Q.obj ((parityShift H).obj (kProjRep Y)) :=
      (kProjRepIso X).symm ≪≫ e ≪≫ (parityShiftD H).mapIso (kProjRepIso Y) ≪≫
        (QCompParityShiftDIso H).app _
    obtain ⟨f, hf⟩ := exists_Q_map_eq hX e₁.hom
    obtain ⟨g, hg⟩ := exists_Q_map_eq hY' e₁.inv
    have hfg : CatModule.Homotopic (f ≫ g) (𝟙 _) := by
      rw [homotopic_iff_Q_map_eq hX, Q.map_comp, hf, hg, e₁.hom_inv_id, Q.map_id]
    have hgf : CatModule.Homotopic (g ≫ f) (𝟙 _) := by
      rw [homotopic_iff_Q_map_eq hY', Q.map_comp, hf, hg, e₁.inv_hom_id, Q.map_id]
    refine ⟨(oddEquiv H _ _).symm f, (oddEquiv' H _ _).symm g, ?_, ?_⟩
    · rw [oddComp_eq', AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
      exact hfg
    · rw [oddComp_eq', oddEquiv_eq_parityShiftHomEquiv, AddEquiv.apply_symm_apply,
        oddEquiv'_apply, AddEquiv.apply_symm_apply, parityShiftHomEquiv_apply, assoc,
        ← assoc ((parityShift H).map g), ← Functor.map_comp]
      have := ((homotopic_parityShift_map (H := H) hgf).comp_right
        (parityShiftIsoObj H _).hom).comp_left
        (parityShiftIsoObj H (kProjRep Y)).inv
      rwa [CategoryTheory.Functor.map_id, id_comp, Iso.inv_hom_id] at this

/-- Odd isomorphisms are the isomorphisms `Π X ≅ Y` of `D(C_H)`. -/
theorem oddIso_iff' (X Y : CatModule.DerivedCategory.{w', max u w} (WeightCategory H.Regraded)) :
    OddIso X Y ↔ Nonempty ((parityShiftD H).obj X ≅ Y) := by
  rw [oddIso_iff]
  constructor
  · rintro ⟨e⟩
    exact ⟨(parityShiftD H).mapIso e ≪≫ (parityShiftDIso H).app Y⟩
  · rintro ⟨e⟩
    exact ⟨((parityShiftDIso H).app X).symm ≪≫ (parityShiftD H).mapIso e⟩

/-- Every object is oddly isomorphic to its parity shift. -/
theorem oddIso_parityShift
    (X : CatModule.DerivedCategory.{w', max u w} (WeightCategory H.Regraded)) :
    OddIso X ((parityShiftD H).obj X) :=
  (oddIso_iff' X _).mpr ⟨Iso.refl _⟩

end OddIso

end HalfGradedDGRing

end DG

end
