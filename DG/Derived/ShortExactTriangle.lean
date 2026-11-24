/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DG.Derived.Basic
import DG.Homotopy.Abelian
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact

/-!
# Distinguished triangles from short exact sequences of dg modules

The projection from the cone of the first map to the quotient is a quasi-isomorphism
because its underlying cochain map is Mathlib's short exact sequence cone comparison.
This supplies the source triangle used in Webster, [arXiv:1309.3796v2](https://arxiv.org/abs/1309.3796v2),
Lemma 6.8, proof of (6.21).
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DG.DerivedCategory

universe w v u

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]

open DGModuleCat in
private noncomputable def shortExactConeDesc (S : ShortComplex (DGModuleCat.{v} A)) :
    of A (Cone S.f.hom) ⟶ S.X₃ :=
  ofHom (Cone.desc S.f.hom 0 S.g.hom (by
    rw [δ_zero]
    have h : S.g.hom.comp S.f.hom = 0 := congrArg Hom.hom S.zero
    rw [h]
    rfl))

set_option backward.isDefEq.respectTransparency false in
open DGModuleCat in
private theorem isQuasiIso_shortExactConeDesc (S : ShortComplex (DGModuleCat.{v} A)) (hS : S.ShortExact) :
    (shortExactConeDesc S).hom.IsQuasiIso := by
  let F := DGModuleCat.forget ℤ A
  let desc := shortExactConeDesc S
  let e := Cone.forgetIso ℤ S.f
  let S' := S.map F
  have h : e.inv ≫ F.map desc = CochainComplex.mappingCone.descShortComplex S' := by
    apply HomologicalComplex.Hom.ext
    funext n
    refine CochainComplex.mappingCone.ext_from S'.f (n + 1) n rfl ?_ ?_
    · dsimp only [e]
      dsimp only [S', ShortComplex.map_f, F]
      rw [HomologicalComplex.comp_f, ← Category.assoc,
        Cone.inl_v_forgetIso_inv_f ℤ S.f]
      refine Eq.trans ?_ (CochainComplex.mappingCone.inl_v_descShortComplex_f S' (n + 1) n (by omega)).symm
      exact ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (by
        change (shortExactConeDesc S).hom (Cone.inl S.f.hom x.1) = 0
        simp [shortExactConeDesc, Cone.desc_apply]))
    · dsimp only [e]
      dsimp only [S', ShortComplex.map_f, F]
      rw [HomologicalComplex.comp_f, ← Category.assoc,
        Cone.inr_f_forgetIso_inv_f ℤ S.f]
      refine Eq.trans ?_ (CochainComplex.mappingCone.inr_f_descShortComplex_f S' n).symm
      exact ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (by
        change (shortExactConeDesc S).hom (Cone.inr S.f.hom x.1) = S.g.hom x.1
        simp [shortExactConeDesc, Cone.desc_apply]))
  have : QuasiIso (CochainComplex.mappingCone.descShortComplex S') :=
    CochainComplex.mappingCone.quasiIso_descShortComplex (DGModuleCat.shortExact_map_forget ℤ hS)
  apply (DG.HomotopyCategory.forget_map_quotient_map_mem_quasiIso_iff ℤ desc).mp
  rw [DG.HomotopyCategory.forget_map_quotient_map,
    _root_.HomotopyCategory.quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff]
  have eq : F.map desc = e.hom ≫ CochainComplex.mappingCone.descShortComplex S' := by
    rw [← h, Iso.hom_inv_id_assoc]
  rw [eq]
  infer_instance

variable [HasDerivedCategory.{w, v} A]

/-- The image of a short exact sequence of dg modules extends to a distinguished triangle. -/
theorem exists_distinguished_of_shortExact (S : ShortComplex (DGModuleCat.{v} A))
    (hS : S.ShortExact) :
    ∃ δ : Q.obj S.X₃ ⟶ (Q.obj S.X₁)⟦(1 : ℤ)⟧,
      Triangle.mk (Q.map S.f) (Q.map S.g) δ ∈ distTriang (DerivedCategory A) := by
  let desc := shortExactConeDesc S
  have : IsIso (Q.map desc) := (isIso_Q_map_iff desc).mpr (isQuasiIso_shortExactConeDesc S hS)
  let T := Q.mapTriangle.obj (Cone.triangle S.f)
  have hT : T ∈ distTriang (DerivedCategory A) :=
    (mem_distTriang_iff _).mpr ⟨_, _, _, ⟨Iso.refl _⟩⟩
  refine ⟨inv (Q.map desc) ≫ T.mor₃, isomorphic_distinguished T hT _ ?_⟩
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (asIso (Q.map desc)).symm
    (by simp [T]) ?_ (by
      dsimp
      erw [CategoryTheory.Functor.map_id]
      exact Category.comp_id _)
  dsimp [T]
  rw [Category.id_comp, IsIso.comp_inv_eq, ← Functor.map_comp]
  congr 1
  apply DGModuleCat.hom_ext
  symm
  dsimp [desc, shortExactConeDesc]
  apply Cone.inr_desc

end DG.DerivedCategory
