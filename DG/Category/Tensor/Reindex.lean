import DG.Category.DoubleOpposite
import DG.Category.Derived.RestrictionIso
import DG.Category.Tensor.ShiftedCorner

/-!
# Reindexing dg coends in degree zero

A fully faithful dg functor which is bijective on objects preserves the
coend under restriction. The inverse on pure tensors uses the unique
original object. Consequently restriction preserves acyclicity of the
coend with a fixed module whenever the original module has that property.
-/


namespace DG
open CategoryTheory DGOpposite

universe u v u' v'
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]
  [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] [DGCategory D]
  (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]
  (hC : ∀ {X Y : C} (f : X ⟶ Y), f ∈ grading (0 : ℤ))

/-- A dg functor between degree-zero dg categories induces the functor on dg opposites. -/
def degreeZeroOppositeFunctor : DGOpposite C ⥤ DGOpposite D where
  obj X := op (F.obj X.unop)
  map f := homOp (F.map (homUnop f))
  map_id X := congrArg homOp (F.map_id X.unop)
  map_comp {X Y Z} f g := by
    apply (show Function.Injective (homUnop (X := op (F.obj X.unop)) (Y := op (F.obj Z.unop))) from
      fun _ _ h => congrArg homOp h)
    have hf : f ∈ grading (0 : ℤ) := hC (homUnop f)
    have hg : g ∈ grading (0 : ℤ) := hC (homUnop g)
    have hf' : homOp (F.map (homUnop f)) ∈ grading (0 : ℤ) :=
      F.map_mem_grading (hC (homUnop f))
    have hg' : homOp (F.map (homUnop g)) ∈ grading (0 : ℤ) :=
      F.map_mem_grading (hC (homUnop g))
    change F.map (homUnop (f ≫ g)) =
      homUnop (homOp (F.map (homUnop f)) ≫ homOp (F.map (homUnop g)))
    rw [homUnop_comp_of_mem hf hg, homUnop_comp_of_mem hf' hg', zero_mul,
      koszulSign_zero, one_smul, one_smul, F.map_comp]
    rfl

instance : (degreeZeroOppositeFunctor F hC).Additive where
  map_add := by intros; exact congrArg homOp F.map_add

instance : (degreeZeroOppositeFunctor F hC).IsDGFunctor where
  map_mem' hf := F.map_mem_grading hf
  map_d' f := congrArg homOp (F.map_d (homUnop f))

end DG


noncomputable section

namespace DG

open CategoryTheory

private theorem eq_zero_of_two_grades {M : Type*} [AddCommGroup M] [DGAddCommGroup M]
    {i j : ℤ} {x : M} (hi : x ∈ grading i) (hj : x ∈ grading j) (h : i ≠ j) : x = 0 := by
  have hzero := DirectSum.decompose_of_mem_ne (grading (M := M)) hj h.symm
  rw [DirectSum.decompose_of_mem_same _ hi] at hzero
  exact hzero

universe u v u' v'
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]
  [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] [DGCategory D]

omit [DGCategory C] in
/-- The differentials on the hom groups of a degree-zero dg category vanish. -/
theorem d_eq_zero_of_category_degreeZero
    (hC : ∀ {X Y : C} (f : X ⟶ Y), f ∈ grading (0 : ℤ)) {X Y : C} (f : X ⟶ Y) :
    d f = 0 :=
  eq_zero_of_two_grades (hC (d f)) (by simpa using d_mem (hC f)) (by decide : (0 : ℤ) ≠ 1)

omit [DGCategory C] [DGCategory D] in
/-- An additive functor between degree-zero dg categories is a dg functor. -/
theorem isDGFunctor_of_degreeZero (F : C ⥤ D) [F.Additive]
    (hC : ∀ {X Y : C} (f : X ⟶ Y), f ∈ grading (0 : ℤ))
    (hD : ∀ {X Y : D} (f : X ⟶ Y), f ∈ grading (0 : ℤ)) :
    F.IsDGFunctor := by
  refine ⟨?_, ?_⟩
  · intro X Y n f hf
    by_cases hn : n = 0
    · subst n
      exact hD (F.map f)
    · rw [eq_zero_of_two_grades hf (hC f) hn, F.map_zero]
      exact zero_mem _
  · intro X Y f
    rw [d_eq_zero_of_category_degreeZero hC, d_eq_zero_of_category_degreeZero hD, F.map_zero]

end DG


noncomputable section

namespace DG.CatTensorProduct

open CategoryTheory DGOpposite
open scoped CatModule

universe w u v u' v'
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]
  [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] [DGCategory D]
  (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]
  (hC : ∀ {X Y : C} (f : X ⟶ Y), f ∈ grading (0 : ℤ))
  (N : CatModule.{w} (DGOpposite D)) (M : CatModule.{w} D)

local notation "P" => CatModule.precompObj (degreeZeroOppositeFunctor F hC) N
local notation "Q" => CatModule.precompObj F M

private def reindexFamily (X : C) : (P).obj (op X) →+ (Q).obj X →+ CatTensorProduct N M :=
  tmulAddHom N M (F.obj X)

private theorem reindexFamily_balanced :
    Balanced (reindexFamily F hC N M) := by
  intro X Y f n m
  have hf : F.map f ∈ grading (0 : ℤ) := F.map_mem_grading (hC f)
  rw [CatModule.ract_eq_op_smul_of_degree_zero P (hC f)]
  let n' : N.obj (op (F.obj Y)) := n
  let m' : M.obj (F.obj X) := m
  change tmul (N := N) (M := M) (F.obj X) (N.act (homOp (F.map f)) n') m' =
    tmul (N := N) (M := M) (F.obj Y) n' (M.act (F.map f) m')
  have he : N.ract (F.map f) n' = N.act (homOp (F.map f)) n' :=
    CatModule.ract_eq_op_smul_of_degree_zero N hf n'
  exact (congrArg (fun z => tmul (N := N) (M := M) (F.obj X) z m') he.symm).trans
    (ract_tmul (F.map f) n' m')

/-- The map on coends induced by restriction along a degree-zero dg functor. -/
def reindexHom : CatTensorProduct P Q →+ CatTensorProduct N M :=
  lift _ (reindexFamily_balanced F hC N M)

@[simp]
theorem reindexHom_tmul (X : C) (n : (P).obj (op X)) (m : (Q).obj X) :
    reindexHom F hC N M (tmul X n m) = tmul (F.obj X) n m :=
  lift_tmul _ (reindexFamily_balanced F hC N M) X n m

variable (hF : Function.Bijective F.obj) (hfull : F.FullyFaithful)

private abbrev inverseObj (Y : D) : C := Function.surjInv hF.2 Y

omit [Preadditive C] [Preadditive D] [(X Y : C) → DGAddCommGroup (X ⟶ Y)] [DGCategory C]
  [(X Y : D) → DGAddCommGroup (X ⟶ Y)] [DGCategory D] [F.Additive] [F.IsDGFunctor] in
private theorem obj_inverseObj (Y : D) : F.obj (inverseObj F hF Y) = Y :=
  Function.rightInverse_surjInv hF.2 Y

private def invFamily (Y : D) : N.obj (op Y) →+ M.obj Y →+ CatTensorProduct P Q :=
  obj_inverseObj F hF Y ▸ tmulAddHom P Q (inverseObj F hF Y)

private theorem invFamily_onImage (X : C) :
    invFamily F hC N M hF (F.obj X) = tmulAddHom P Q X := by
  have aux (Y : C) (h : Y = X) (e : F.obj Y = F.obj X) :
      (e ▸ tmulAddHom P Q Y : N.obj (op (F.obj X)) →+ M.obj (F.obj X) →+
        CatTensorProduct P Q) = tmulAddHom P Q X := by
    subst Y
    rfl
  exact aux (inverseObj F hF (F.obj X)) (hF.1 (obj_inverseObj F hF (F.obj X)))
    (obj_inverseObj F hF (F.obj X))

include hfull in
private theorem invFamily_balanced : Balanced (invFamily F hC N M hF) := by
  intro X Y f n m
  obtain ⟨X', rfl⟩ := hF.2 X
  obtain ⟨Y', rfl⟩ := hF.2 Y
  obtain ⟨f', rfl⟩ := hfull.map_surjective f
  rw [invFamily_onImage, invFamily_onImage]
  have hf : F.map f' ∈ grading (0 : ℤ) := F.map_mem_grading (hC f')
  rw [CatModule.ract_eq_op_smul_of_degree_zero N hf]
  let n' : (P).obj (op Y') := n
  let m' : (Q).obj X' := m
  change tmul (N := P) (M := Q) X' ((P).act (homOp f') n') m' =
    tmul (N := P) (M := Q) Y' n' ((Q).act f' m')
  have he : (P).ract f' n' = (P).act (homOp f') n' :=
    CatModule.ract_eq_op_smul_of_degree_zero P (hC f') n'
  exact (congrArg (fun z => tmul (N := P) (M := Q) X' z m') he.symm).trans
    (ract_tmul f' n' m')

private def reindexInvHom : CatTensorProduct N M →+ CatTensorProduct P Q :=
  lift _ (invFamily_balanced F hC N M hF hfull)

private theorem reindexInvHom_tmul (X : C) (n : (P).obj (op X)) (m : (Q).obj X) :
    reindexInvHom F hC N M hF hfull (tmul (F.obj X) n m) = tmul X n m := by
  let n' : N.obj (op (F.obj X)) := n
  let m' : M.obj (F.obj X) := m
  change reindexInvHom F hC N M hF hfull (tmul (F.obj X) n' m') = _
  exact (lift_tmul _ (invFamily_balanced F hC N M hF hfull) (F.obj X) n' m').trans
    (congrArg (fun t => t n' m') (invFamily_onImage F hC N M hF X))

/-- Restricting along a fully faithful dg functor that is bijective on objects
does not change the dg coend. -/
def reindexDGEquiv : DGAddEquiv (CatTensorProduct P Q) (CatTensorProduct N M) :=
  by
    let f := reindexHom F hC N M
    let g := reindexInvHom F hC N M hF hfull
    have hl : g.comp f = AddMonoidHom.id _ := by
      apply addHom_ext
      intro X n m
      change g (f (tmul X n m)) = _
      rw [reindexHom_tmul F hC N M, reindexInvHom_tmul F hC N M hF hfull]
      rfl
    have hr : f.comp g = AddMonoidHom.id _ := by
      apply addHom_ext
      intro Y n m
      obtain ⟨X, rfl⟩ := hF.2 Y
      change f (g (tmul (F.obj X) n m)) = _
      exact (congrArg f (reindexInvHom_tmul F hC N M hF hfull X n m)).trans
        (reindexHom_tmul F hC N M X n m)
    exact DGAddEquiv.ofAddMonoidHom f g (DFunLike.congr_fun hl) (DFunLike.congr_fun hr)
      (fun hx => lift_mem (reindexFamily F hC N M) (reindexFamily_balanced F hC N M)
        (fun X a b n m hn hm => by
          let n' : N.obj (op (F.obj X)) := n
          let m' : M.obj (F.obj X) := m
          change tmul (N := N) (M := M) (F.obj X) n' m' ∈ grading (a+b)
          exact tmul_mem_grading (N := N) (M := M) (X := F.obj X) hn hm) hx)
      (lift_d (reindexFamily F hC N M) (reindexFamily_balanced F hC N M)
        (fun X _ _ hn m => d_tmul_of_mem (F.obj X) hn m))

end DG.CatTensorProduct


noncomputable section

namespace DG.CatTensorProduct

open CategoryTheory DGOpposite

universe w u v u' v'
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]
  [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] [DGCategory D]
  (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]
  (hC : ∀ {X Y : C} (f : X ⟶ Y), f ∈ grading (0 : ℤ))
  (hD : ∀ {X Y : D} (f : X ⟶ Y), f ∈ grading (0 : ℤ))
  (hF : Function.Bijective F.obj) (hfull : F.FullyFaithful)

private def oppositeFullyFaithful : (degreeZeroOppositeFunctor F hC).FullyFaithful where
  preimage f := homOp (hfull.preimage (homUnop f))
  map_preimage f := congrArg homOp (hfull.map_preimage (homUnop f))
  preimage_map f := congrArg homOp (hfull.preimage_map (homUnop f))

include hF in
private theorem oppositeObj_surjective :
    Function.Surjective (degreeZeroOppositeFunctor F hC).obj := by
  intro Y
  obtain ⟨X, hX⟩ := hF.2 Y.unop
  exact ⟨op X, congrArg op hX⟩

include hC hD hF hfull in
/-- Restriction across a bijective fully faithful weight reindexing preserves
the acyclicity-preserving property of a fixed coend argument. -/
theorem isAcyclic_precomp_of_coend
    (M : CatModule.{w} D)
    (h : ∀ P : CatModule.{w} (DGOpposite D), CatModule.IsAcyclic P →
      DG.IsAcyclic (CatTensorProduct P M))
    (P : CatModule.{w} (DGOpposite C)) (hP : CatModule.IsAcyclic P) :
    DG.IsAcyclic (CatTensorProduct P (CatModule.precompObj F M)) := by
  let O := degreeZeroOppositeFunctor F hC
  let H := oppositeFullyFaithful F hC hfull
  let _ : O.IsEquivalence :=
    ⟨H.faithful, H.full, ⟨fun X => by
      obtain ⟨Y, hYX⟩ := oppositeObj_surjective F hC hF X
      exact ⟨Y, ⟨eqToIso hYX⟩⟩⟩⟩
  let E := O.asEquivalence
  let G := E.inverse
  let _ : E.functor.Additive := inferInstanceAs O.Additive
  let _ : G.Additive := E.inverse_additive
  have hC' {X Y : DGOpposite C} (f : X ⟶ Y) : f ∈ grading (0 : ℤ) := hC (homUnop f)
  have hD' {X Y : DGOpposite D} (f : X ⟶ Y) : f ∈ grading (0 : ℤ) := hD (homUnop f)
  let _ : G.IsDGFunctor := isDGFunctor_of_degreeZero G hD' hC'
  let P' := CatModule.precompObj G P
  have hP' : CatModule.IsAcyclic P' := fun X => hP (G.obj X)
  let u : O ⋙ G ≅ 𝟭 (DGOpposite C) := E.unitIso.symm
  let e : CatModule.precompObj O P' ≅ P :=
    (CatModule.precompCompIso O G).symm.app P ≪≫
      (CatModule.precompNatIso u (fun X => hC' (u.hom.app X))
        (fun X => d_eq_zero_of_category_degreeZero hC' (u.hom.app X))
        (fun X => hC' (u.inv.app X))
        (fun X => d_eq_zero_of_category_degreeZero hC' (u.inv.app X))).app P ≪≫
      (CatModule.precompIdIso (DGOpposite C)).app P
  exact acyclic_of_DGAddEquiv (congr e.symm (Iso.refl _))
    (acyclic_of_DGAddEquiv (reindexDGEquiv F hC P' M hF hfull) (h P' hP'))

end DG.CatTensorProduct
