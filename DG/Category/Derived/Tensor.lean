import DG.Category.Derived.KProjective
import DG.Category.Derived.Coproducts
import DG.Category.Homotopy.HomBimoduleTriangulated
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# The derived tensor product and the derived Hom functor of a dg bimodule

Let `C` and `D` be dg categories and `B` a dg `(D, C)`-bimodule (`DG.CatBimodule D C`). Tensoring
with `B` is left adjoint to the Hom functor on dg modules,
`B ⊗_C - ⊣ HOM_D(B, -)` (`DG.CatBimodule.tensorHomAdjunction`). This file derives this adjunction
[Keller, *Deriving DG categories*, §6.1], [Bernstein–Lunts, 10.12.2]:

* `DG.CatModule.homotopic_iff_homEquiv_of_pathObj`: for an adjunction `L ⊣ G` between dg modules
  whose right adjoint preserves homotopies and admits a morphism
  `pathObj (G N) ⟶ G (pathObj N)` over the projections, two morphisms `L M ⟶ N` are homotopic iff
  their adjoints are; hence `L` preserves homotopies, and it preserves K-projective modules if
  `G` preserves acyclic modules. This applies to the tensor–Hom adjunction
  (`DG.CatBimodule.homotopic_iff_tensorHomEquiv`, `DG.CatBimodule.homotopic_tensorMap`).
* If every left dg module `B(-, Y)` over `D` is K-projective (`hB`), then `HOM_D(B, -)` preserves
  acyclic modules and quasi-isomorphisms (`DG.CatBimodule.isQuasiIso_homMap`), so it induces
  the derived Hom functor `DG.CatModule.DerivedCategory.rhom B hB : D(D) ⥤ D(C)`, a triangulated
  functor; and `B ⊗_C -` preserves K-projective modules
  (`DG.CatBimodule.isKProjective_tensorObj`).
* `DG.CatModule.DerivedCategory.derivedTensor B hB : D(C) ⥤ D(D)`, the left derived functor
  `B ⊗^L_C -`, constructed from the universal arrows `Q P ⟶ RHOM(B, Q (B ⊗_C P))` at
  K-projective representatives `P`, with the derived tensor–Hom adjunction
  `DG.CatModule.DerivedCategory.derivedTensorAdjunction B hB : B ⊗^L_C - ⊣ RHOM_D(B, -)`.
  It commutes with the shifts, is triangulated and preserves coproducts, and
  `Q (B ⊗_C P) ≅ (B ⊗^L_C -) (Q P)` for K-projective `P`
  (`DG.CatModule.DerivedCategory.derivedTensorObjIso`).

## The hypothesis on `B`

`RHOM_D(B, -)` is computed by `HOM_D(B, -)` only when `B` is K-projective as a left module over
`D` in each variable, i.e. `B(-, Y)` is K-projective for every `Y ∈ C`: then `HOM_D(B(-, Y), N)`
is acyclic for acyclic `N` (`DG.CatModule.isKProjective_iff_isAcyclic_hom`), and conversely this
property of `HOM_D(B, -)` forces `B(-, Y)` to be K-projective. This holds for the bimodule
`D(F -, -)` of a dg functor (whose `B(-, Y) = D(F Y, -)` is representable), giving derived
induction (`DG/Category/Derived/TensorInduction.lean`), and for a dg ring `A` as an
`(A, B)`-bimodule along a morphism of dg rings `B → A`. For a general bimodule, one first
replaces `B` by such a bimodule resolution, which is not constructed in the library.

## Universes

The tensor–Hom adjunction is stated for bimodules and modules with values in
`Type (max u₁ u₂ w)`, and K-projective resolutions over `C` exist in `Type (max u₁ v₁ w)`; the
derived functors are constructed for bimodules and modules with values in
`Type (max u₁ u₂ v₁ w)`.
-/

open CategoryTheory Limits

universe w₁ w₂ w₃ w₄ w v₁ v₂ u₁ u₂

set_option backward.isDefEq.respectTransparency false

namespace DG

namespace CatModule

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] [DGCategory D]

/-! ### Adjunctions whose right adjoint is compatible with the path object -/

section Adjunction

variable {L : CatModule.{w} C ⥤ CatModule.{w} D} {G : CatModule.{w} D ⥤ CatModule.{w} C}
  [G.Additive] (adj : L ⊣ G)
  (hG : ∀ {N N' : CatModule.{w} D} {f g : N ⟶ N'}, Homotopic f g → Homotopic (G.map f) (G.map g))
  (θ : ∀ N : CatModule.{w} D, pathObj (G.obj N) ⟶ G.obj (pathObj N))
  (hθ : ∀ N : CatModule.{w} D, θ N ≫ G.map (pathObj.π N) = pathObj.π (G.obj N))

include adj hG θ hθ in
/-- For an adjunction `L ⊣ G` whose right adjoint preserves homotopies and is compatible with the
path object (`θ`), a morphism `g : L M ⟶ N` is null-homotopic iff its adjoint is. -/
theorem homotopic_zero_iff_homEquiv_of_pathObj {M : CatModule.{w} C} {N : CatModule.{w} D}
    (g : L.obj M ⟶ N) : Homotopic g 0 ↔ Homotopic (adj.homEquiv M N g) 0 := by
  constructor
  · intro hg
    rw [adj.homEquiv_unit]
    refine (Homotopic.comp_left (hG hg) _).trans (Homotopic.of_eq ?_)
    rw [Functor.map_zero, Limits.comp_zero]
  · intro h
    obtain ⟨H, hH⟩ := (homotopic_zero_iff_exists_lift _).mp h
    rw [homotopic_zero_iff_exists_lift]
    refine ⟨(adj.homEquiv M (pathObj N)).symm (H ≫ θ N), ?_⟩
    apply (adj.homEquiv M N).injective
    rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply, Category.assoc, hθ, hH]

include adj hG θ hθ in
/-- For an adjunction `L ⊣ G` as in `homotopic_zero_iff_homEquiv_of_pathObj`, two morphisms
`L M ⟶ N` are homotopic iff their adjoints are. -/
theorem homotopic_iff_homEquiv_of_pathObj {M : CatModule.{w} C} {N : CatModule.{w} D}
    (g g' : L.obj M ⟶ N) :
    Homotopic g g' ↔ Homotopic (adj.homEquiv M N g) (adj.homEquiv M N g') := by
  have e : adj.homEquiv M N (g - g') = adj.homEquiv M N g - adj.homEquiv M N g' := by
    simp only [adj.homEquiv_unit, Functor.map_sub, Preadditive.comp_sub]
  rw [Homotopic.iff_sub, homotopic_zero_iff_homEquiv_of_pathObj adj hG θ hθ, e,
    ← Homotopic.iff_sub]

include adj hG θ hθ in
/-- The left adjoint `L` of an adjunction as in `homotopic_zero_iff_homEquiv_of_pathObj`
preserves homotopies. -/
theorem homotopic_map_of_pathObj {M M' : CatModule.{w} C} {f f' : M ⟶ M'}
    (h : Homotopic f f') : Homotopic (L.map f) (L.map f') := by
  rw [homotopic_iff_homEquiv_of_pathObj adj hG θ hθ, adj.homEquiv_unit, adj.homEquiv_unit,
    ← Functor.comp_map, ← Functor.comp_map, ← adj.unit.naturality, ← adj.unit.naturality]
  exact h.comp_right _

include adj hG θ hθ in
/-- The left adjoint `L` of an adjunction as in `homotopic_zero_iff_homEquiv_of_pathObj`
preserves K-projective modules if `G` preserves acyclic modules. -/
theorem IsKProjective.of_adjunction_of_pathObj
    (hGa : ∀ N : CatModule.{w} D, IsAcyclic N → IsAcyclic (G.obj N))
    {P : CatModule.{w} C} (hP : IsKProjective P) : IsKProjective (L.obj P) := fun N hN g =>
  (homotopic_zero_iff_homEquiv_of_pathObj adj hG θ hθ g).mpr (hP _ (hGa N hN) _)

end Adjunction

omit [DGCategory C] [DGCategory D] in
/-- A dg module isomorphic to an acyclic one is acyclic. -/
theorem IsAcyclic.of_iso {M N : CatModule.{w} D} (e : M ≅ N) (h : IsAcyclic N) :
    IsAcyclic M := fun X =>
  (h X).of_dgAddEquiv (DGAddEquiv.ofAddMonoidHom (e.hom.app X) (e.inv.app X)
    (fun m => by rw [← comp_app, e.hom_inv_id, id_app])
    (fun n => by rw [← comp_app, e.inv_hom_id, id_app])
    (fun hm => e.hom.map_mem hm) (fun m => e.hom.map_d m))

end CatModule

namespace CatBimodule

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] [DGCategory D]

open CatModule

/-! ### The tensor–Hom adjunction up to homotopy -/

section Homotopy

variable (B : CatBimodule.{max u₁ u₂ w} D C)

/-- Two morphisms `B ⊗_C M ⟶ N` are homotopic iff the corresponding morphisms
`M ⟶ HOM_D(B, N)` are. -/
theorem homotopic_iff_tensorHomEquiv {M : CatModule.{max u₁ u₂ w} C}
    {N : CatModule.{max u₁ u₂ w} D} (g g' : B.tensorObj M ⟶ N) :
    CatModule.Homotopic g g' ↔ CatModule.Homotopic (B.tensorHomAdjunction.homEquiv M N g)
      (B.tensorHomAdjunction.homEquiv M N g') :=
  homotopic_iff_homEquiv_of_pathObj B.tensorHomAdjunction (fun h => h.homMap B)
    B.homPathMap B.homPathMap_π g g'

/-- Tensoring with a dg bimodule preserves homotopies. -/
theorem homotopic_tensorMap {M M' : CatModule.{max u₁ u₂ w} C} {f f' : M ⟶ M'}
    (h : CatModule.Homotopic f f') : CatModule.Homotopic (B.tensorMap f) (B.tensorMap f') :=
  homotopic_map_of_pathObj B.tensorHomAdjunction (fun h => h.homMap B) B.homPathMap
    B.homPathMap_π h

end Homotopy

/-! ### Bimodules which are K-projective over `D` -/

section KProjective

variable (B : CatBimodule.{w} D C) (hB : ∀ Y : C, CatModule.IsKProjective (B.left Y))
include hB

/-- If every `B(-, Y)` is K-projective, `HOM_D(B, -)` preserves acyclic modules. -/
theorem isAcyclic_homObj {N : CatModule.{w} D} (hN : CatModule.IsAcyclic N) :
    CatModule.IsAcyclic (B.homObj N) :=
  fun Y => (hB Y).isAcyclic_hom hN

/-- If every `B(-, Y)` is K-projective, `HOM_D(B, -)` preserves quasi-isomorphisms: it sends the
acyclic cone of a quasi-isomorphism to the cone of its image (`DG.CatBimodule.homConeIso`). -/
theorem isQuasiIso_homMap {M N : CatModule.{w} D} {φ : M ⟶ N} (hφ : CatModule.IsQuasiIso φ) :
    CatModule.IsQuasiIso (B.homMap φ) := by
  rw [isQuasiIso_iff_isAcyclic_cone] at hφ ⊢
  exact CatModule.IsAcyclic.of_iso (B.homConeIso φ).symm (B.isAcyclic_homObj hB hφ)

end KProjective

theorem isKProjective_tensorObj (B : CatBimodule.{max u₁ u₂ w} D C)
    (hB : ∀ Y : C, CatModule.IsKProjective (B.left Y)) {P : CatModule.{max u₁ u₂ w} C}
    (hP : CatModule.IsKProjective P) : CatModule.IsKProjective (B.tensorObj P) :=
  CatModule.IsKProjective.of_adjunction_of_pathObj B.tensorHomAdjunction (fun h => h.homMap B)
    B.homPathMap B.homPathMap_π (fun _ hN => B.isAcyclic_homObj hB hN) hP

end CatBimodule

namespace CatModule

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] [DGCategory D]

namespace HomotopyCategory

variable (B : CatBimodule.{w} D C) (hB : ∀ Y : C, IsKProjective (B.left Y))
include hB

/-- If every `B(-, Y)` is K-projective, the Hom functor on homotopy categories preserves
quasi-isomorphisms. -/
theorem homFunctor_map_mem_quasiIso {M N : HomotopyCategory.{w} D} {f : M ⟶ N}
    (hf : quasiIso D f) : quasiIso C ((homFunctor B).map f) := by
  obtain ⟨M, rfl⟩ := quotient_obj_surjective M
  obtain ⟨N, rfl⟩ := quotient_obj_surjective N
  obtain ⟨f, rfl⟩ := (quotient _).map_surjective f
  rw [quotient_map_mem_quasiIso_iff] at hf
  rw [homFunctor_map_quotient_map, quotient_map_mem_quasiIso_iff]
  exact B.isQuasiIso_homMap hB hf

end HomotopyCategory

namespace DerivedCategory

section RHom

variable (B : CatBimodule.{w} D C) (hB : ∀ Y : C, IsKProjective (B.left Y))
  [HasDerivedCategory.{w₁, max u₂ w} C] [HasDerivedCategory.{w₂, w} D]

/-- The derived Hom functor `RHOM_D(B, -) : D(D) ⥤ D(C)` of a dg `(D, C)`-bimodule `B` all of
whose modules `B(-, Y)` are K-projective: the functor induced by `HOM_D(B, -)`. -/
noncomputable def rhom : DerivedCategory.{w₂, w} D ⥤ DerivedCategory.{w₁, max u₂ w} C :=
  Localization.lift (HomotopyCategory.homFunctor B ⋙ Qh)
    (fun _ _ _ hf => Localization.inverts Qh (HomotopyCategory.quasiIso C) _
      (HomotopyCategory.homFunctor_map_mem_quasiIso B hB hf))
    Qh

noncomputable instance rhomLifting :
    Localization.Lifting Qh (HomotopyCategory.quasiIso D)
      (HomotopyCategory.homFunctor B ⋙ Qh) (rhom B hB) :=
  inferInstanceAs (Localization.Lifting _ _ _ (Localization.lift _ _ Qh))

/-- The derived Hom functor is induced by the Hom functor on homotopy categories. -/
noncomputable def QhCompRhomIso : Qh ⋙ rhom B hB ≅ HomotopyCategory.homFunctor B ⋙ Qh :=
  Localization.Lifting.iso Qh (HomotopyCategory.quasiIso D) _ _

/-- The derived Hom functor is induced by the Hom functor on dg modules. -/
noncomputable def QCompRhomIso : Q ⋙ rhom B hB ≅ B.homFunctor ⋙ Q :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (QhCompRhomIso B hB) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (HomotopyCategory.homFunctorFactors B) _ ≪≫
    Functor.associator _ _ _

/-- The derived Hom functor commutes with the shifts. -/
noncomputable instance rhom_commShift : (rhom B hB).CommShift ℤ :=
  Functor.commShiftOfLocalization Qh (HomotopyCategory.quasiIso D) ℤ
    (HomotopyCategory.homFunctor B ⋙ Qh) (rhom B hB)

instance : NatTrans.CommShift (QhCompRhomIso B hB).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization _ _ _ _ _

/-- The derived Hom functor is a triangulated functor. -/
instance rhom_isTriangulated : (rhom B hB).IsTriangulated :=
  Functor.isTriangulated_of_precomp_iso (QhCompRhomIso B hB)

end RHom

/-! ### The derived tensor product -/

section Tensor

variable (B : CatBimodule.{max u₁ u₂ v₁ w} D C) (hB : ∀ Y : C, IsKProjective (B.left Y))
  [HasDerivedCategory.{w₁, max u₁ u₂ v₁ w} C] [HasDerivedCategory.{w₂, max u₁ u₂ v₁ w} D]

/-- The tensor–Hom adjunction for `B`, with the universe levels of this section. -/
private noncomputable abbrev adjB :
    (B.tensorFunctor : CatModule.{max u₁ u₂ v₁ w} C ⥤ CatModule.{max u₁ u₂ v₁ w} D) ⊣
      B.homFunctor :=
  CatBimodule.tensorHomAdjunction.{max v₁ w} B

/-- The universal arrow `Q P ⟶ RHOM_D(B, Q (B ⊗_C P))` given by the unit of the tensor–Hom
adjunction. -/
noncomputable def tensorUnitMap (P : CatModule.{max u₁ u₂ v₁ w} C) :
    Q.obj P ⟶ (rhom B hB).obj (Q.obj (B.tensorObj P)) :=
  Q.map ((adjB B).unit.app P) ≫ (QCompRhomIso B hB).inv.app _

theorem tensorUnitMap_comp_rhom_map (P : CatModule.{max u₁ u₂ v₁ w} C)
    {N : CatModule.{max u₁ u₂ v₁ w} D} (g : B.tensorObj P ⟶ N) :
    tensorUnitMap B hB P ≫ (rhom B hB).map (Q.map g) =
      Q.map ((adjB B).homEquiv P N g) ≫ (QCompRhomIso B hB).inv.app N := by
  rw [tensorUnitMap, Category.assoc, ← Functor.comp_map, ← (QCompRhomIso B hB).inv.naturality,
    Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rfl

/-- For a K-projective `P`, the arrow `tensorUnitMap B hB P` is universal: every morphism
`Q P ⟶ RHOM_D(B, Y)` factors uniquely through it. -/
theorem bijective_tensorUnitMap_comp (P : CatModule.{max u₁ u₂ v₁ w} C) (hP : IsKProjective P)
    (Y : DerivedCategory.{w₂, max u₁ u₂ v₁ w} D) :
    Function.Bijective fun g : Q.obj (B.tensorObj P) ⟶ Y =>
      tensorUnitMap B hB P ≫ (rhom B hB).map g := by
  have hLP : IsKProjective (B.tensorObj P) := CatBimodule.isKProjective_tensorObj.{max v₁ w} B hB hP
  -- reduce to `Y = Q N`
  obtain ⟨Z, ⟨e⟩⟩ :=
    (Localization.essSurj (Qh (C := D)) (HomotopyCategory.quasiIso D)).mem_essImage Y
  obtain ⟨N, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
  have key : Function.Bijective fun g : Q.obj (B.tensorObj P) ⟶ Q.obj N =>
      tensorUnitMap B hB P ≫ (rhom B hB).map g := by
    have hQ := fun {M : CatModule.{max u₁ u₂ v₁ w} C} (hM : IsKProjective M)
        (M' : CatModule.{max u₁ u₂ v₁ w} C) =>
      Qh_map_bijective_of_isKProjective hM ((HomotopyCategory.quotient C).obj M')
    have hQD := Qh_map_bijective_of_isKProjective hLP ((HomotopyCategory.quotient D).obj N)
    constructor
    · intro a b hab
      obtain ⟨a', rfl⟩ := hQD.2 a
      obtain ⟨a, rfl⟩ := (HomotopyCategory.quotient D).map_surjective a'
      obtain ⟨b', rfl⟩ := hQD.2 b
      obtain ⟨b, rfl⟩ := (HomotopyCategory.quotient D).map_surjective b'
      change tensorUnitMap B hB P ≫ (rhom B hB).map (Q.map a) =
        tensorUnitMap B hB P ≫ (rhom B hB).map (Q.map b) at hab
      rw [tensorUnitMap_comp_rhom_map, tensorUnitMap_comp_rhom_map, cancel_mono] at hab
      have h := (hQ hP _).1 hab
      rw [HomotopyCategory.quotient_map_eq_iff,
        ← CatBimodule.homotopic_iff_tensorHomEquiv.{max v₁ w} B,
        ← HomotopyCategory.quotient_map_eq_iff] at h
      change Qh.map _ = Qh.map _
      rw [h]
    · intro c
      obtain ⟨k', hk'⟩ := (hQ hP (B.homObj N)).2 (c ≫ (QCompRhomIso B hB).hom.app N)
      obtain ⟨k, rfl⟩ := (HomotopyCategory.quotient C).map_surjective k'
      refine ⟨Q.map (((adjB B).homEquiv P N).symm k), ?_⟩
      beta_reduce
      rw [tensorUnitMap_comp_rhom_map]
      rw [Equiv.apply_symm_apply]
      change Qh.map ((HomotopyCategory.quotient C).map k) ≫ _ = c
      rw [hk', Category.assoc, Iso.hom_inv_id_app]
      exact Category.comp_id c
  -- transport along `e : Qh (quotient N) ≅ Y`
  have h1 : (fun g : Q.obj (B.tensorObj P) ⟶ Y => tensorUnitMap B hB P ≫ (rhom B hB).map g) =
      (fun c => c ≫ (rhom B hB).map e.hom) ∘
        (fun g : Q.obj (B.tensorObj P) ⟶ Q.obj N => tensorUnitMap B hB P ≫ (rhom B hB).map g) ∘
          (fun g => g ≫ e.inv) := by
    ext g
    simp only [Function.comp_apply, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      Category.comp_id]
  rw [h1]
  refine Function.Bijective.comp ?_ (key.comp ?_)
  · refine Function.bijective_iff_has_inverse.mpr
      ⟨fun c => c ≫ (rhom B hB).map e.inv, fun c => ?_, fun c => ?_⟩ <;>
    simp [← Functor.map_comp]
  · exact Function.bijective_iff_has_inverse.mpr
      ⟨fun c => c ≫ e.hom, fun c => by simp, fun c => by simp⟩

/-- The bijection `(Q (B ⊗_C P_X) ⟶ Y) ≃ (X ⟶ RHOM_D(B, Y))` defining the derived tensor
product, where `P_X` is the chosen K-projective representative `kProjRep X` of `X`. -/
noncomputable def derivedTensorHomEquiv (X : DerivedCategory.{w₁, max u₁ u₂ v₁ w} C)
    (Y : DerivedCategory.{w₂, max u₁ u₂ v₁ w} D) :
    (Q.obj (B.tensorObj (kProjRep.{w₁, max u₂ w, v₁, u₁} X)) ⟶ Y) ≃ (X ⟶ (rhom B hB).obj Y) :=
  (Equiv.ofBijective _
    (bijective_tensorUnitMap_comp B hB _ (isKProjective_kProjRep.{w₁, max u₂ w, v₁, u₁} X) Y)).trans
    ((Iso.homCongr (kProjRepIso.{w₁, max u₂ w, v₁, u₁} X) (Iso.refl _)).symm)

theorem derivedTensorHomEquiv_apply (X : DerivedCategory.{w₁, max u₁ u₂ v₁ w} C)
    (Y : DerivedCategory.{w₂, max u₁ u₂ v₁ w} D)
    (g : Q.obj (B.tensorObj (kProjRep.{w₁, max u₂ w, v₁, u₁} X)) ⟶ Y) :
    derivedTensorHomEquiv B hB X Y g = (kProjRepIso.{w₁, max u₂ w, v₁, u₁} X).hom ≫
      tensorUnitMap B hB (kProjRep.{w₁, max u₂ w, v₁, u₁} X) ≫ (rhom B hB).map g := by
  simp only [derivedTensorHomEquiv, Equiv.trans_apply, Iso.homCongr_symm, Iso.homCongr_apply,
    Equiv.ofBijective_apply, Iso.symm_inv, Iso.refl_symm, Iso.refl_hom, Category.comp_id]

/-- The derived tensor product `B ⊗^L_C - : D(C) ⥤ D(D)` of a dg `(D, C)`-bimodule `B` all of
whose modules `B(-, Y)` are K-projective, left adjoint to `RHOM_D(B, -)`
(`DG.CatModule.DerivedCategory.derivedTensorAdjunction`). On an object represented by a
K-projective dg module `P` it is `Q (B ⊗_C P)`
(`DG.CatModule.DerivedCategory.derivedTensorObjIso`). -/
noncomputable def derivedTensor :
    DerivedCategory.{w₁, max u₁ u₂ v₁ w} C ⥤ DerivedCategory.{w₂, max u₁ u₂ v₁ w} D :=
  Adjunction.leftAdjointOfEquiv (G := rhom B hB) (derivedTensorHomEquiv B hB)
    fun X Y Y' g h => by
      rw [derivedTensorHomEquiv_apply, derivedTensorHomEquiv_apply, Functor.map_comp]
      simp only [Category.assoc]

/-- **The derived tensor–Hom adjunction** `B ⊗^L_C - ⊣ RHOM_D(B, -)`. -/
noncomputable def derivedTensorAdjunction : derivedTensor B hB ⊣ rhom B hB :=
  Adjunction.adjunctionOfEquivLeft _ _

/-- The derived tensor product commutes with the shifts: the structure induced by the adjunction
with `RHOM_D(B, -)` (Mathlib's `Adjunction.leftAdjointCommShift`). -/
noncomputable instance derivedTensor_commShift : (derivedTensor.{w₁, w₂} B hB).CommShift ℤ :=
  (derivedTensorAdjunction B hB).leftAdjointCommShift ℤ

instance derivedTensorAdjunction_commShift :
    (derivedTensorAdjunction.{w₁, w₂} B hB).CommShift ℤ :=
  (derivedTensorAdjunction B hB).commShift_of_rightAdjoint ℤ

/-- The derived tensor product is a triangulated functor, as the left adjoint of the
triangulated functor `RHOM_D(B, -)`. -/
instance derivedTensor_isTriangulated : (derivedTensor.{w₁, w₂} B hB).IsTriangulated :=
  (derivedTensorAdjunction B hB).isTriangulated_leftAdjoint

/-- The derived tensor product preserves all colimits, in particular coproducts, as a left
adjoint. -/
instance derivedTensor_preservesColimitsOfSize :
    PreservesColimitsOfSize.{w₃, w₄} (derivedTensor.{w₁, w₂} B hB) :=
  (derivedTensorAdjunction B hB).leftAdjoint_preservesColimits

/-- The bijection `(Q (B ⊗_C P) ⟶ Y) ≃ (Q P ⟶ RHOM_D(B, Y))` given by the universal arrow
`tensorUnitMap B hB P`, for a K-projective `P`. -/
noncomputable def tensorUnitMapEquiv {P : CatModule.{max u₁ u₂ v₁ w} C} (hP : IsKProjective P)
    (Y : DerivedCategory.{w₂, max u₁ u₂ v₁ w} D) :
    (Q.obj (B.tensorObj P) ⟶ Y) ≃
      ((Q.obj P : DerivedCategory.{w₁, max u₁ u₂ v₁ w} C) ⟶ (rhom B hB).obj Y) :=
  Equiv.ofBijective _ (bijective_tensorUnitMap_comp B hB P hP Y)

section ObjIso

variable {P : CatModule.{max u₁ u₂ v₁ w} C} (hP : IsKProjective P)

/-- The morphism `Q (B ⊗_C P) ⟶ (B ⊗^L_C -) (Q P)` corresponding to the unit at `Q P`. -/
noncomputable def derivedTensorObjIsoHom :
    Q.obj (B.tensorObj P) ⟶
      (derivedTensor.{w₁, w₂} B hB).obj (Q.obj P : DerivedCategory.{w₁, max u₁ u₂ v₁ w} C) :=
  (tensorUnitMapEquiv B hB hP _).symm ((derivedTensorAdjunction B hB).unit.app _)

variable (P) in
/-- The morphism `(B ⊗^L_C -) (Q P) ⟶ Q (B ⊗_C P)` adjoint to `tensorUnitMap B hB P`. -/
noncomputable def derivedTensorObjIsoInv :
    (derivedTensor.{w₁, w₂} B hB).obj (Q.obj P : DerivedCategory.{w₁, max u₁ u₂ v₁ w} C) ⟶
      Q.obj (B.tensorObj P) :=
  ((derivedTensorAdjunction B hB).homEquiv _ _).symm (tensorUnitMap B hB P)

theorem tensorUnitMap_comp_derivedTensorObjIsoHom :
    tensorUnitMap B hB P ≫ (rhom B hB).map (derivedTensorObjIsoHom B hB hP) =
      (derivedTensorAdjunction B hB).unit.app
        (Q.obj P : DerivedCategory.{w₁, max u₁ u₂ v₁ w} C) :=
  (tensorUnitMapEquiv B hB hP _).apply_symm_apply _

omit hP in
theorem unit_comp_derivedTensorObjIsoInv :
    (derivedTensorAdjunction B hB).unit.app
        (Q.obj P : DerivedCategory.{w₁, max u₁ u₂ v₁ w} C) ≫
      (rhom B hB).map (derivedTensorObjIsoInv B hB P) = tensorUnitMap B hB P := by
  have h := ((derivedTensorAdjunction B hB).homEquiv _ _).apply_symm_apply (tensorUnitMap B hB P)
  rwa [Adjunction.homEquiv_unit] at h

/-- The derived tensor product of a K-projective module is computed by the tensor product:
`Q (B ⊗_C P) ≅ (B ⊗^L_C -) (Q P)`, compatibly with the units
(`tensorUnitMap_comp_derivedTensorObjIsoHom`). -/
noncomputable def derivedTensorObjIso :
    Q.obj (B.tensorObj P) ≅
      (derivedTensor.{w₁, w₂} B hB).obj (Q.obj P : DerivedCategory.{w₁, max u₁ u₂ v₁ w} C) where
  hom := derivedTensorObjIsoHom B hB hP
  inv := derivedTensorObjIsoInv B hB P
  hom_inv_id := by
    apply (tensorUnitMapEquiv B hB hP _).injective
    change tensorUnitMap B hB P ≫ (rhom B hB).map (_ ≫ _) =
      tensorUnitMap B hB P ≫ (rhom B hB).map (𝟙 _)
    rw [Functor.map_comp, ← Category.assoc, tensorUnitMap_comp_derivedTensorObjIsoHom,
      unit_comp_derivedTensorObjIsoInv, CategoryTheory.Functor.map_id, Category.comp_id]
  inv_hom_id := by
    apply ((derivedTensorAdjunction B hB).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
      unit_comp_derivedTensorObjIsoInv, tensorUnitMap_comp_derivedTensorObjIsoHom,
      CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm

@[simp]
theorem derivedTensorObjIso_hom :
    (derivedTensorObjIso B hB hP).hom = derivedTensorObjIsoHom B hB hP := rfl

end ObjIso

end Tensor

end DerivedCategory

end CatModule

end DG
