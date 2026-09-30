import DG.K0.Triangulated

/-!
# Grothendieck groups with identified objects

Let `C` be a pretriangulated category and `r` a relation on its objects. The group
`DG.K0Rel C r` is the free abelian group on the objects of `C` modulo the triangle relations
`[Y] = [X] + [Z]` of `K₀(C)` (`DG.K0`) and the additional relations `[X] = [Y]` whenever `r X Y`.
It is used for the super Grothendieck group of half-graded dg modules, where `r` is "isomorphic
by an even or an odd isomorphism" (`DG.HalfGradedDGRing.SuperK0`).

## Main results

* `DG.K0Rel.mk`, `DG.K0Rel.mk_obj₂`, `DG.K0Rel.mk_eq_of_rel`, `DG.K0Rel.lift`,
  `DG.K0Rel.addMonoidHom_ext`.
* `DG.K0Rel.equivQuotient`: if every relation `r X Y` comes from an isomorphism `X ≅ Y` or an
  isomorphism `P X ≅ Y` for an object map `P : C → C`, and `r X (P X)` for all `X`, then
  `K0Rel C r ≃+ K₀(C) ⧸ ⟨[P X] - [X]⟩`, `[X] ↦ [X]`.
-/

namespace DG

open CategoryTheory Category Limits Pretriangulated

universe v u

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (r : C → C → Prop)

namespace K0Rel

/-- The relations: the triangle relations of `K₀(C)` together with `of X - of Y` for `r X Y`. -/
def relations : AddSubgroup (FreeAbelianGroup C) :=
  K0.relations C ⊔
    AddSubgroup.closure {x | ∃ X Y, r X Y ∧ x = FreeAbelianGroup.of X - FreeAbelianGroup.of Y}

end K0Rel

/-- The Grothendieck group of `C` with the additional identifications `[X] = [Y]` for `r X Y`:
the free abelian group on the objects of `C` modulo `[T.obj₂] = [T.obj₁] + [T.obj₃]` for the
distinguished triangles `T` and `[X] = [Y]` for `r X Y`. -/
def K0Rel : Type u := FreeAbelianGroup C ⧸ K0Rel.relations C r

namespace K0Rel

instance : AddCommGroup (K0Rel C r) := QuotientAddGroup.Quotient.addCommGroup _

/-- The quotient map from the free abelian group. -/
def mkHom : FreeAbelianGroup C →+ K0Rel C r := QuotientAddGroup.mk' _

variable {C r}

/-- The class of an object. -/
def mk (X : C) : K0Rel C r := mkHom C r (FreeAbelianGroup.of X)

theorem mkHom_surjective : Function.Surjective (mkHom C r) := QuotientAddGroup.mk'_surjective _

theorem mk_obj₂ (T : Triangle C) (hT : T ∈ distTriang C) :
    (mk T.obj₂ : K0Rel C r) = mk T.obj₁ + mk T.obj₃ := by
  have h := (QuotientAddGroup.eq_zero_iff _).2
    ((le_sup_left : K0.relations C ≤ relations C r) (K0.relation_mem T hT))
  change mkHom C r _ = 0 at h
  rwa [map_sub, map_sub, sub_sub, sub_eq_zero] at h

theorem mk_eq_of_rel {X Y : C} (h : r X Y) : (mk X : K0Rel C r) = mk Y := by
  have h := (QuotientAddGroup.eq_zero_iff _).2
    ((le_sup_right : _ ≤ relations C r) (AddSubgroup.subset_closure
      (k := {x | ∃ X Y, r X Y ∧ x = FreeAbelianGroup.of X - FreeAbelianGroup.of Y})
      ⟨X, Y, h, rfl⟩))
  change mkHom C r _ = 0 at h
  rwa [map_sub, sub_eq_zero] at h

set_option backward.isDefEq.respectTransparency false in
/-- Two homomorphisms out of `K0Rel C r` which agree on the classes of objects are equal. -/
@[ext]
theorem addMonoidHom_ext {G : Type*} [AddCommGroup G] ⦃f g : K0Rel C r →+ G⦄
    (h : ∀ X : C, f (mk X) = g (mk X)) : f = g := by
  apply QuotientAddGroup.addMonoidHom_ext
  exact FreeAbelianGroup.lift_ext _ _ h

set_option backward.isDefEq.respectTransparency false in
/-- The universal property of `K0Rel C r`. -/
def lift {G : Type*} [AddCommGroup G] (f : C → G)
    (hf : ∀ T ∈ distTriang C, f T.obj₂ = f T.obj₁ + f T.obj₃) (hr : ∀ X Y, r X Y → f X = f Y) :
    K0Rel C r →+ G :=
  QuotientAddGroup.lift _ (FreeAbelianGroup.lift f) (by
    refine sup_le ((AddSubgroup.closure_le _).2 ?_) ((AddSubgroup.closure_le _).2 ?_)
    · rintro x ⟨T, hT, rfl⟩
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, FreeAbelianGroup.lift_apply_of]
      rw [hf T hT]
      abel
    · rintro x ⟨X, Y, h, rfl⟩
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, FreeAbelianGroup.lift_apply_of]
      rw [hr X Y h, sub_self])

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem lift_mk {G : Type*} [AddCommGroup G] (f : C → G) (hf) (hr) (X : C) :
    lift (r := r) f hf hr (mk X) = f X :=
  (QuotientAddGroup.lift_mk' _ _ (FreeAbelianGroup.of X)).trans
    (FreeAbelianGroup.lift_apply_of f X)

/-! ### Comparison with `K₀(C)` -/

section Comparison

variable (P : C → C) (hr : ∀ X Y, r X Y → Nonempty (X ≅ Y) ∨ Nonempty (P X ≅ Y))
  (hP : ∀ X, r X (P X))

theorem of_sub_of_mem_relations_of_iso {X Y : C} (e : X ≅ Y) :
    FreeAbelianGroup.of X - FreeAbelianGroup.of Y ∈ K0.relations C := by
  have h := K0.mk_eq_of_iso e
  rw [← sub_eq_zero, ← K0.mkHom_of, ← K0.mkHom_of, ← map_sub] at h
  exact (QuotientAddGroup.eq_zero_iff _).mp h

include hr hP in
theorem relations_eq : relations C r = K0.relations C ⊔
    AddSubgroup.closure {x | ∃ X, x = FreeAbelianGroup.of (P X) - FreeAbelianGroup.of X} := by
  apply le_antisymm
  · refine sup_le le_sup_left ((AddSubgroup.closure_le _).2 ?_)
    rintro x ⟨X, Y, h, rfl⟩
    rcases hr X Y h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact AddSubgroup.mem_sup_left (of_sub_of_mem_relations_of_iso e)
    · rw [show FreeAbelianGroup.of X - FreeAbelianGroup.of Y =
          -(FreeAbelianGroup.of (P X) - FreeAbelianGroup.of X) +
            (FreeAbelianGroup.of (P X) - FreeAbelianGroup.of Y) by abel]
      exact add_mem (neg_mem (AddSubgroup.mem_sup_right (AddSubgroup.subset_closure ⟨X, rfl⟩)))
        (AddSubgroup.mem_sup_left (of_sub_of_mem_relations_of_iso e))
  · refine sup_le le_sup_left ((AddSubgroup.closure_le _).2 ?_)
    rintro x ⟨X, rfl⟩
    rw [← neg_sub]
    exact neg_mem (AddSubgroup.mem_sup_right (AddSubgroup.subset_closure ⟨X, P X, hP X, rfl⟩))

/-- The subgroup of `K₀(C)` generated by the differences `[P X] - [X]`. -/
def parityRelations : AddSubgroup (K0 C) :=
  AddSubgroup.closure {x | ∃ X, x = K0.mk (P X) - K0.mk X}

set_option backward.isDefEq.respectTransparency false in
include hr hP in
/-- If the relation `r` is "isomorphic, or isomorphic after applying `P`", then `K0Rel C r` is
the quotient of `K₀(C)` by the classes `[P X] - [X]`. -/
def equivQuotient : K0Rel C r ≃+ K0 C ⧸ parityRelations P :=
  (QuotientAddGroup.quotientAddEquivOfEq (relations_eq P hr hP)).trans
    ((QuotientAddGroup.quotientQuotientEquivQuotient (K0.relations C)
      (K0.relations C ⊔ AddSubgroup.closure
        {x | ∃ X, x = FreeAbelianGroup.of (P X) - FreeAbelianGroup.of X}) le_sup_left).symm.trans
      (QuotientAddGroup.quotientAddEquivOfEq (by
        rw [AddSubgroup.map_sup, parityRelations, AddMonoidHom.map_closure]
        have h0 : (K0.relations C).map (QuotientAddGroup.mk' (K0.relations C)) = ⊥ := by
          rw [AddSubgroup.map_eq_bot_iff, QuotientAddGroup.ker_mk']
        rw [h0, bot_sup_eq]
        congr 1
        ext x
        simp only [Set.mem_image, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨y, ⟨X, rfl⟩, rfl⟩
          exact ⟨X, by rw [map_sub]; rfl⟩
        · rintro ⟨X, rfl⟩
          exact ⟨_, ⟨X, rfl⟩, by rw [map_sub]; rfl⟩)))

theorem equivQuotient_mk (X : C) :
    equivQuotient P hr hP (mk X) = QuotientAddGroup.mk (K0.mk X) :=
  rfl

end Comparison

end K0Rel

end DG
