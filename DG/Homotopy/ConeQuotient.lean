import DG.Homotopy.ConeCochain
import DG.Homotopy.KProjective
import DG.Module.SubQuotient

/-!
# Quotients by dg submodules and mapping cones

Let `S` be a dg submodule of a dg module `M` over a dg ring `A`. The short exact sequence
`0 → S → M → M ⧸ S → 0` need not split as a sequence of graded `A`-modules, but the quotient is
still quasi-isomorphic to the mapping cone of the inclusion:

* `DG.DGSubmodule.coneToQuotient S : Cone S.subtype →ᵈᵍ[A] M ⧸ S`, `(x, y) ↦ [y]`, is a
  quasi-isomorphism (`DG.DGSubmodule.isQuasiIso_coneToQuotient`);
* if `S` is acyclic, the quotient map `M → M ⧸ S` is a quasi-isomorphism
  (`DG.DGSubmodule.isQuasiIso_mkQ_of_isAcyclic`).

Both are proved by a diagram chase on homogeneous cocycles. The first identifies the triangle
`S → M → Cone → S⟦1⟧` of the derived category with a triangle `S → M → M ⧸ S → S⟦1⟧` up to
isomorphism of the third objects (see `DG/Derived/TStructure.lean`).
-/

namespace DG

open Cochain

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  {M : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  (S : DGSubmodule A M)

omit [DGRing A] in
theorem DGSubmodule.δ_zero_eq_ofHom_mkQ_comp_subtype :
    δ (-1) 0 (0 : Cochain A S (M ⧸ S.toSubmodule) (-1)) = ofHom (S.mkQ.comp S.subtype) :=
  Cochain.ext fun x => by
    rw [δ_neg_one_apply, Cochain.zero_apply, Cochain.zero_apply, d_zero, add_zero,
      ofHom_apply, DGModuleHom.comp_apply, DGSubmodule.subtype_apply, eq_comm,
      DGSubmodule.mkQ_eq_zero_iff]
    exact x.2

/-- The comparison map `Cone (S → M) → M ⧸ S`, `(x, y) ↦ [y]`. -/
noncomputable def DGSubmodule.coneToQuotient : Cone S.subtype →ᵈᵍ[A] M ⧸ S.toSubmodule :=
  Cone.desc S.subtype 0 S.mkQ S.δ_zero_eq_ofHom_mkQ_comp_subtype

theorem DGSubmodule.coneToQuotient_apply (p : Cone S.subtype) :
    S.coneToQuotient p = S.mkQ (Cone.snd S.subtype p) := by
  rw [coneToQuotient, Cone.desc_apply, Cochain.zero_apply, zero_add]

@[simp]
theorem DGSubmodule.coneToQuotient_comp_inr : S.coneToQuotient.comp (Cone.inr S.subtype) = S.mkQ :=
  Cone.inr_desc _ _ _ _

omit [DGRing A] [DGModule A M] in
/-- A homogeneous element of `M ⧸ S` has a homogeneous preimage of the same degree. -/
theorem DGSubmodule.exists_mem_grading_mk {n : ℤ} {y : M ⧸ S.toSubmodule}
    (hy : y ∈ DGAddCommGroup.grading n) :
    ∃ x ∈ DGAddCommGroup.grading (M := M) n, S.mkQ x = y :=
  (DGSubmodule.mem_grading_quotient_iff S).mp hy

/-- The comparison map from the cone of the inclusion of a dg submodule to the quotient is a
quasi-isomorphism. -/
theorem DGSubmodule.isQuasiIso_coneToQuotient : S.coneToQuotient.IsQuasiIso := fun k => by
  constructor
  · rw [cohomology.map_injective_iff]
    intro p hp hdp hpb
    obtain ⟨w', hw', hw'p⟩ := mem_coboundaries.mp hpb
    obtain ⟨w, hw, hww⟩ := S.exists_mem_grading_mk hw'
    subst hww
    set x := (Cone.fst S.subtype).1 p
    set y := Cone.snd S.subtype p
    have hx : x ∈ DGAddCommGroup.grading (k + 1) := (Cone.fst S.subtype).1.map_mem hp
    have hy : y ∈ DGAddCommGroup.grading k := by simpa using (Cone.snd S.subtype).map_mem hp
    have hdx : (x : M) + DGAddCommGroup.d y = 0 := by
      have := congrArg (Cone.snd S.subtype) hdp
      rwa [Cone.d_snd_apply, map_zero] at this
    rw [coneToQuotient_apply, ← DGModuleHom.map_d, eq_comm, ← sub_eq_zero, ← map_sub,
      DGSubmodule.mkQ_eq_zero_iff] at hw'p
    set s : S := ⟨y - DGAddCommGroup.d w, hw'p⟩
    have hs : s ∈ DGAddCommGroup.grading k :=
      (DGSubmodule.mem_grading S).mpr (sub_mem hy (by simpa using DG.d_mem hw))
    refine mem_coboundaries.mpr ⟨Cone.inl S.subtype s + Cone.inr S.subtype w,
      add_mem (by rw [sub_eq_add_neg]; exact (Cone.inl S.subtype).map_mem hs)
        ((Cone.inr S.subtype).map_mem hw), ?_⟩
    rw [d_add, Cone.inl_d_apply, Cone.inr_d_apply, ← Cone.id_X p]
    have hds : DGAddCommGroup.d s = -x := Subtype.ext (by
      rw [DGSubmodule.coe_d, show ((-x : S) : M) = -(x : M) from rfl, eq_neg_iff_add_eq_zero,
        add_comm,
        show (s : M) = y - DGAddCommGroup.d w from rfl, d_sub, DG.d_d, sub_zero]
      exact hdx)
    rw [hds, map_neg, sub_neg_eq_add, add_comm (Cone.inr _ _), add_assoc, ← map_add,
      DGSubmodule.subtype_apply]
    congr 2
    change y - DGAddCommGroup.d w + DGAddCommGroup.d w = y
    rw [sub_add_cancel]
  · rw [cohomology.map_surjective_iff]
    intro yq hyq hdyq
    obtain ⟨y, hy, hyy⟩ := S.exists_mem_grading_mk hyq
    subst hyy
    rw [← DGModuleHom.map_d, DGSubmodule.mkQ_eq_zero_iff] at hdyq
    set x : S := ⟨-DGAddCommGroup.d y, neg_mem hdyq⟩
    have hx : x ∈ DGAddCommGroup.grading (k + 1) :=
      (DGSubmodule.mem_grading S).mpr (neg_mem (DG.d_mem hy))
    refine ⟨Cone.inl S.subtype x + Cone.inr S.subtype y,
      add_mem (by simpa using (Cone.inl S.subtype).map_mem hx) ((Cone.inr S.subtype).map_mem hy),
      ?_, ?_⟩
    · have hdx : DGAddCommGroup.d x = 0 := Subtype.ext (by
        rw [DGSubmodule.coe_d]
        change DGAddCommGroup.d (-DGAddCommGroup.d y) = 0
        rw [d_neg, DG.d_d, neg_zero])
      rw [d_add, Cone.inl_d_apply, Cone.inr_d_apply, hdx, map_zero, sub_zero, ← map_add,
        DGSubmodule.subtype_apply]
      change Cone.inr S.subtype (-DGAddCommGroup.d y + DGAddCommGroup.d y) = 0
      rw [neg_add_cancel, map_zero]
    · rw [coneToQuotient_apply, map_add, Cone.inl_snd_apply, Cone.inr_snd_apply, zero_add,
        sub_self]
      exact zero_mem _

omit [DGRing A] [DGModule A M] in
/-- If a dg submodule `S` is acyclic, the quotient map `M → M ⧸ S` is a quasi-isomorphism. -/
theorem DGSubmodule.isQuasiIso_mkQ_of_isAcyclic (hS : IsAcyclic S) : S.mkQ.IsQuasiIso := fun k => by
  constructor
  · rw [cohomology.map_injective_iff]
    intro z hz hdz hzb
    obtain ⟨w', hw', hw'z⟩ := mem_coboundaries.mp hzb
    obtain ⟨w, hw, hww⟩ := S.exists_mem_grading_mk hw'
    subst hww
    rw [← DGModuleHom.map_d, eq_comm, ← sub_eq_zero, ← map_sub, DGSubmodule.mkQ_eq_zero_iff] at hw'z
    obtain ⟨t, ht, hdt⟩ := isAcyclic_iff.mp hS k ⟨z - DGAddCommGroup.d w, hw'z⟩
      ((DGSubmodule.mem_grading S).mpr (sub_mem hz (by simpa using DG.d_mem hw)))
      (Subtype.ext (by
        rw [DGSubmodule.coe_d]
        change DGAddCommGroup.d (z - DGAddCommGroup.d w) = 0
        rw [d_sub, DG.d_d, hdz, sub_zero]))
    refine mem_coboundaries.mpr ⟨w + t, add_mem hw ((DGSubmodule.mem_grading S).mp ht), ?_⟩
    have := congrArg Subtype.val hdt
    rw [DGSubmodule.coe_d] at this
    rw [d_add, this]
    change DGAddCommGroup.d w + (z - DGAddCommGroup.d w) = z
    abel
  · rw [cohomology.map_surjective_iff]
    intro yq hyq hdyq
    obtain ⟨y, hy, hyy⟩ := S.exists_mem_grading_mk hyq
    subst hyy
    rw [← DGModuleHom.map_d, DGSubmodule.mkQ_eq_zero_iff] at hdyq
    obtain ⟨t, ht, hdt⟩ := isAcyclic_iff.mp hS (k + 1) ⟨DGAddCommGroup.d y, hdyq⟩
      ((DGSubmodule.mem_grading S).mpr (DG.d_mem hy))
      (Subtype.ext (by rw [DGSubmodule.coe_d]; exact DG.d_d y))
    rw [add_sub_cancel_right] at ht
    have ht' : (t : M) ∈ S := t.2
    refine ⟨y - t, sub_mem hy ((DGSubmodule.mem_grading S).mp ht), ?_, ?_⟩
    · have := congrArg Subtype.val hdt
      rw [DGSubmodule.coe_d] at this
      rw [d_sub, this]
      exact sub_self _
    · rw [map_sub, sub_sub_cancel_left, (DGSubmodule.mkQ_eq_zero_iff S).mpr ht', neg_zero]
      exact zero_mem _

end DG
