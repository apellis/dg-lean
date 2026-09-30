import DG.Category.Derived.KProjective
import DG.Category.Derived.Restriction
import DG.Category.Homotopy.Path
import DG.Category.Tensor.Induction

/-!
# Derived induction along a dg functor

Let `F : C ⥤ D` be a dg functor between dg categories. Induction `F_! = D(F -, -) ⊗_C -` is left
adjoint to restriction `F^*` on dg modules (`DG.CatModule.inductionAdjunction`). This file shows
that the adjunction descends to homotopy categories on K-projective modules, that `F_!`
preserves K-projective modules, and constructs the left derived functor `LF_! : D(C) ⥤ D(D)`,
left adjoint to restriction `D(D) ⥤ D(C)`: on a K-projective `P` it is `Q (F_! P)`
[Keller, *Deriving DG categories*, §6.1].

The arguments only use that the right adjoint is a restriction functor: a morphism `g` out of
`L M` is null-homotopic iff its adjoint `M ⟶ F^* N` is
(`DG.CatModule.homotopic_zero_iff_homEquiv`), since null-homotopic morphisms are those which
factor through the path object (`DG.CatModule.homotopic_zero_iff_exists_lift`), and the path
object commutes with restriction.

## Main definitions and results

* `DG.CatModule.homotopic_iff_homEquiv`: for an adjunction `L ⊣ F^*`, `g ≃ g'` iff their
  adjoints are homotopic; `DG.CatModule.homotopic_map_of_homotopic`: `L` preserves homotopies;
  `DG.CatModule.IsKProjective.of_adjunction`: `L` preserves K-projective modules.
* `DG.CatModule.DerivedCategory.induction F : D(C) ⥤ D(D)` and
  `DG.CatModule.DerivedCategory.inductionAdjunction F : induction F ⊣ restrict F`.
* `DG.CatModule.DerivedCategory.inductionObjIso`: `Q (F_! P) ≅ LF_! (Q P)` for K-projective `P`.

## Universes

Induction takes `CatModule.{max u₁ v₂ w} C` to `CatModule.{max u₁ v₂ w} D`, and resolutions exist
in `CatModule.{max u₁ v₁ w} C`; the derived functor is constructed for dg modules in
`CatModule.{max u₁ v₁ v₂ w}`, i.e. with `induction.{max v₁ w}` and
`DerivedCategory.{_, max u₁ v₁ v₂ w}`. For small dg categories `C` and `D` in the same universe
`v` with modules in `Type v`, all these universes are `v`.
-/

open CategoryTheory

universe w₁ w₂ w v₁ v₂ u₁ u₂

set_option backward.isDefEq.respectTransparency false

namespace DG

namespace CatModule

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] [DGCategory D] (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]

/-! ### Adjunctions with a restriction functor as right adjoint -/

section Adjunction

variable {F} {L : CatModule.{w} C ⥤ CatModule.{w} D} (adj : L ⊣ precomp F)

omit [DGCategory C] [DGCategory D] in
theorem Homotopic.precomp {M N : CatModule.{w} D} {f g : M ⟶ N} (h : Homotopic f g) :
    Homotopic ((CatModule.precomp F).map f) ((CatModule.precomp F).map g) :=
  ⟨h.some.precomp F⟩

include adj in
/-- A morphism `g : L M ⟶ N` is null-homotopic iff its adjoint `M ⟶ F^* N` is. -/
theorem homotopic_zero_iff_homEquiv {M : CatModule.{w} C} {N : CatModule.{w} D}
    (g : L.obj M ⟶ N) : Homotopic g 0 ↔ Homotopic (adj.homEquiv M N g) 0 := by
  constructor
  · intro hg
    rw [adj.homEquiv_unit]
    refine (Homotopic.comp_left (hg.precomp (F := F)) _).trans (Homotopic.of_eq ?_)
    rw [Functor.map_zero, Limits.comp_zero]
  · intro h
    obtain ⟨H, hH⟩ := (homotopic_zero_iff_exists_lift _).mp h
    rw [homotopic_zero_iff_exists_lift]
    refine ⟨(adj.homEquiv M (pathObj N)).symm (H ≫ (pathObj.precompIso F N).hom), ?_⟩
    apply (adj.homEquiv M N).injective
    rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply, Category.assoc,
      pathObj.precompIso_hom_π, hH]

include adj in
/-- Two morphisms `L M ⟶ N` are homotopic iff their adjoints are. -/
theorem homotopic_iff_homEquiv {M : CatModule.{w} C} {N : CatModule.{w} D}
    (g g' : L.obj M ⟶ N) :
    Homotopic g g' ↔ Homotopic (adj.homEquiv M N g) (adj.homEquiv M N g') := by
  have e : adj.homEquiv M N (g - g') = adj.homEquiv M N g - adj.homEquiv M N g' := by
    simp only [adj.homEquiv_unit, Functor.map_sub, Preadditive.comp_sub]
  rw [Homotopic.iff_sub, homotopic_zero_iff_homEquiv adj, e, ← Homotopic.iff_sub]

include adj in
/-- The left adjoint of a restriction functor preserves homotopies. -/
theorem homotopic_map_of_homotopic {M M' : CatModule.{w} C} {f f' : M ⟶ M'}
    (h : Homotopic f f') : Homotopic (L.map f) (L.map f') := by
  rw [homotopic_iff_homEquiv adj, adj.homEquiv_unit, adj.homEquiv_unit, ← Functor.comp_map,
    ← Functor.comp_map, ← adj.unit.naturality, ← adj.unit.naturality]
  exact h.comp_right _

include adj in
/-- The left adjoint of a restriction functor preserves K-projective modules. -/
theorem IsKProjective.of_adjunction {P : CatModule.{w} C} (hP : IsKProjective P) :
    IsKProjective (L.obj P) := fun _ hN g =>
  (homotopic_zero_iff_homEquiv adj g).mpr (hP _ (hN.precomp F) _)

end Adjunction

/-! ### The derived functor -/

namespace DerivedCategory

variable [HasDerivedCategory.{w₁, max u₁ v₁ v₂ w} C]
  [HasDerivedCategory.{w₂, max u₁ v₁ v₂ w} D]

/-- The universal arrow `Q P ⟶ F^* Q (F_! P)` given by the unit of the adjunction
`F_! ⊣ F^*`. -/
noncomputable def unitMap (P : CatModule.{max u₁ v₁ v₂ w} C) :
    Q.obj P ⟶ (restrict F).obj (Q.obj ((CatModule.induction.{max v₁ w} F).obj P)) :=
  Q.map ((CatModule.inductionAdjunction.{max v₁ w} F).unit.app P) ≫
    (QCompRestrictIso F).inv.app _

theorem unitMap_comp_restrict_map (P : CatModule.{max u₁ v₁ v₂ w} C)
    {N : CatModule.{max u₁ v₁ v₂ w} D} (g : (CatModule.induction.{max v₁ w} F).obj P ⟶ N) :
    unitMap F P ≫ (restrict F).map (Q.map g) =
      Q.map ((CatModule.inductionAdjunction.{max v₁ w} F).homEquiv P N g) ≫
        (QCompRestrictIso F).inv.app N := by
  rw [unitMap, Category.assoc, ← Functor.comp_map, ← (QCompRestrictIso F).inv.naturality,
    Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rfl

/-- For a K-projective `P`, the arrow `unitMap F P` is universal: every morphism
`Q P ⟶ F^* Y` factors uniquely through it. -/
theorem bijective_unitMap_comp (P : CatModule.{max u₁ v₁ v₂ w} C) (hP : IsKProjective P)
    (Y : DerivedCategory.{w₂, max u₁ v₁ v₂ w} D) :
    Function.Bijective fun g : Q.obj ((CatModule.induction.{max v₁ w} F).obj P) ⟶ Y =>
      unitMap F P ≫ (restrict F).map g := by
  have hLP : IsKProjective ((CatModule.induction.{max v₁ w} F).obj P) :=
    hP.of_adjunction (CatModule.inductionAdjunction.{max v₁ w} F)
  -- reduce to `Y = Q N`
  obtain ⟨Z, ⟨e⟩⟩ :=
    (Localization.essSurj (Qh (C := D)) (HomotopyCategory.quasiIso D)).mem_essImage Y
  obtain ⟨N, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
  have key : Function.Bijective
      fun g : Q.obj ((CatModule.induction.{max v₁ w} F).obj P) ⟶ Q.obj N =>
        unitMap F P ≫ (restrict F).map g := by
    have hQ := fun {M : CatModule.{max u₁ v₁ v₂ w} C} (hM : IsKProjective M)
        (M' : CatModule.{max u₁ v₁ v₂ w} C) =>
      ((Qh_map_bijective_of_isKProjective hM ((HomotopyCategory.quotient C).obj M')))
    have hQD := (Qh_map_bijective_of_isKProjective hLP ((HomotopyCategory.quotient D).obj N))
    constructor
    · intro a b hab
      obtain ⟨a', rfl⟩ := hQD.2 a
      obtain ⟨a, rfl⟩ := (HomotopyCategory.quotient D).map_surjective a'
      obtain ⟨b', rfl⟩ := hQD.2 b
      obtain ⟨b, rfl⟩ := (HomotopyCategory.quotient D).map_surjective b'
      change unitMap F P ≫ (restrict F).map (Q.map a) =
        unitMap F P ≫ (restrict F).map (Q.map b) at hab
      rw [unitMap_comp_restrict_map, unitMap_comp_restrict_map, cancel_mono] at hab
      have h := (hQ hP _).1 hab
      rw [HomotopyCategory.quotient_map_eq_iff,
        ← homotopic_iff_homEquiv (CatModule.inductionAdjunction.{max v₁ w} F),
        ← HomotopyCategory.quotient_map_eq_iff] at h
      change Qh.map _ = Qh.map _
      rw [h]
    · intro c
      obtain ⟨k', hk'⟩ := (hQ hP ((precomp F).obj N)).2 (c ≫ (QCompRestrictIso F).hom.app N)
      obtain ⟨k, rfl⟩ := (HomotopyCategory.quotient C).map_surjective k'
      refine ⟨Q.map (((CatModule.inductionAdjunction.{max v₁ w} F).homEquiv P N).symm k), ?_⟩
      beta_reduce
      rw [unitMap_comp_restrict_map, Equiv.apply_symm_apply]
      change Qh.map ((HomotopyCategory.quotient C).map k) ≫ _ = c
      rw [hk', Category.assoc, Iso.hom_inv_id_app]
      exact Category.comp_id c
  -- transport along `e : Qh (quotient N) ≅ Y`
  have h1 : (fun g : Q.obj ((CatModule.induction.{max v₁ w} F).obj P) ⟶ Y =>
        unitMap F P ≫ (restrict F).map g) =
      (fun c => c ≫ (restrict F).map e.hom) ∘
        (fun g : Q.obj ((CatModule.induction.{max v₁ w} F).obj P) ⟶ Q.obj N =>
          unitMap F P ≫ (restrict F).map g) ∘ (fun g => g ≫ e.inv) := by
    ext g
    simp only [Function.comp_apply, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      Category.comp_id]
  rw [h1]
  refine Function.Bijective.comp ?_ (key.comp ?_)
  · refine Function.bijective_iff_has_inverse.mpr
      ⟨fun c => c ≫ (restrict F).map e.inv, fun c => ?_, fun c => ?_⟩ <;>
    simp [← Functor.map_comp]
  · exact Function.bijective_iff_has_inverse.mpr
      ⟨fun c => c ≫ e.hom, fun c => by simp, fun c => by simp⟩

/-- The bijection `(Q (F_! P_X) ⟶ Y) ≃ (X ⟶ F^* Y)` defining derived induction, where `P_X` is
the chosen K-projective representative `kProjRep X` of `X`. -/
noncomputable def inductionHomEquiv (X : DerivedCategory.{w₁, max u₁ v₁ v₂ w} C)
    (Y : DerivedCategory.{w₂, max u₁ v₁ v₂ w} D) :
    (Q.obj ((CatModule.induction.{max v₁ w} F).obj (kProjRep.{w₁, max v₂ w, v₁, u₁} X)) ⟶ Y) ≃
      (X ⟶ (restrict F).obj Y) :=
  (Equiv.ofBijective _
    (bijective_unitMap_comp F _ (isKProjective_kProjRep.{w₁, max v₂ w, v₁, u₁} X) Y)).trans
    ((Iso.homCongr (kProjRepIso.{w₁, max v₂ w, v₁, u₁} X) (Iso.refl _)).symm)

theorem inductionHomEquiv_apply (X : DerivedCategory.{w₁, max u₁ v₁ v₂ w} C)
    (Y : DerivedCategory.{w₂, max u₁ v₁ v₂ w} D)
    (g : Q.obj ((CatModule.induction.{max v₁ w} F).obj (kProjRep.{w₁, max v₂ w, v₁, u₁} X)) ⟶ Y) :
    inductionHomEquiv F X Y g = (kProjRepIso.{w₁, max v₂ w, v₁, u₁} X).hom ≫
      unitMap F (kProjRep.{w₁, max v₂ w, v₁, u₁} X) ≫ (restrict F).map g := by
  simp only [inductionHomEquiv, Equiv.trans_apply, Iso.homCongr_symm, Iso.homCongr_apply,
    Equiv.ofBijective_apply, Iso.symm_inv, Iso.refl_symm, Iso.refl_hom, Category.comp_id]

/-- Derived induction `LF_! : D(C) ⥤ D(D)` along a dg functor `F : C ⥤ D`, left adjoint to
restriction (`DG.CatModule.DerivedCategory.inductionAdjunction`). On an object represented by a
K-projective dg module `P` it is `Q (F_! P)` (`DG.CatModule.DerivedCategory.inductionObjIso`). -/
noncomputable def induction :
    DerivedCategory.{w₁, max u₁ v₁ v₂ w} C ⥤ DerivedCategory.{w₂, max u₁ v₁ v₂ w} D :=
  Adjunction.leftAdjointOfEquiv (G := restrict F) (inductionHomEquiv F) fun X Y Y' g h => by
    rw [inductionHomEquiv_apply, inductionHomEquiv_apply, Functor.map_comp]
    simp only [Category.assoc]

/-- Derived induction is left adjoint to restriction. -/
noncomputable def inductionAdjunction : induction F ⊣ restrict F :=
  Adjunction.adjunctionOfEquivLeft _ _

/-- The bijection `(Q (F_! P) ⟶ Y) ≃ (Q P ⟶ F^* Y)` given by the universal arrow `unitMap F P`,
for a K-projective `P`. -/
noncomputable def unitMapEquiv {P : CatModule.{max u₁ v₁ v₂ w} C} (hP : IsKProjective P)
    (Y : DerivedCategory.{w₂, max u₁ v₁ v₂ w} D) :
    (Q.obj ((CatModule.induction.{max v₁ w} F).obj P) ⟶ Y) ≃
      ((Q.obj P : DerivedCategory.{w₁, max u₁ v₁ v₂ w} C) ⟶ (restrict F).obj Y) :=
  Equiv.ofBijective _ (bijective_unitMap_comp F P hP Y)

/-- Derived induction of a K-projective module is computed by induction:
`LF_! (Q P) ≅ Q (F_! P)`. -/
noncomputable def inductionObjIso {P : CatModule.{max u₁ v₁ v₂ w} C} (hP : IsKProjective P) :
    Q.obj ((CatModule.induction.{max v₁ w} F).obj P) ≅
      (induction.{w₁, w₂} F).obj (Q.obj P : DerivedCategory.{w₁, max u₁ v₁ v₂ w} C) :=
  Coyoneda.ext _ _
    (fun f => ((inductionAdjunction F).homEquiv _ _).symm (unitMapEquiv F hP _ f))
    (fun f => (unitMapEquiv F hP _).symm ((inductionAdjunction F).homEquiv _ _ f))
    (fun f => by rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply])
    (fun f => by rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]) (fun f g => by
      have hn : ∀ x,
          unitMapEquiv F hP _ (x ≫ g) = unitMapEquiv F hP _ x ≫ (restrict F).map g :=
        fun x => by
          change unitMap F P ≫ (restrict F).map (x ≫ g) =
            (unitMap F P ≫ (restrict F).map x) ≫ (restrict F).map g
          rw [Functor.map_comp, Category.assoc]
      rw [Equiv.symm_apply_eq, Adjunction.homEquiv_naturality_right, hn, Equiv.apply_symm_apply])

end DerivedCategory

end CatModule

end DG
