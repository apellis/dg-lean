import DG.Category.Tensor.Shift
import DG.Category.Resolution.KProjective
import DG.Category.Derived.QuasiIso
import DG.Homotopy.Comparison

/-!
# Coends of mapping cones in the right module

For degree-zero morphism categories, the graded cone splitting induces
the additive splitting of the coend. Its first summand is identified by
the coend shift, and the cone differential agrees under this identification.
-/

noncomputable section

namespace DG.CatTensorProduct

open CategoryTheory DGOpposite
open scoped CatModule DG.DegreeZero

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]
  {L N : CatModule.{w} (DGOpposite C)} (M : CatModule.{w} C)
  (h₀ : ∀ {X Y : C} (f : X ⟶ Y), f ∈ grading (0 : ℤ))

include h₀ in
private theorem balanced_left_cochain (r : CatModule.Cochain L N 0) :
    Balanced fun X => (tmulAddHom N M X).comp (r.app (op X)) := by
  intro X Y f n m
  have hf : f ∈ grading (0 : ℤ) := h₀ f
  have hf' : homOp f ∈ grading (0 : ℤ) := hf
  change tmul X (r.app (op X) (n <• f)) m = tmul Y (r.app (op Y) n) (f • m)
  rw [CatModule.ract_eq_op_smul_of_degree_zero L hf, r.map_smul hf', zero_mul,
    koszulSign_zero, one_smul, ← CatModule.ract_eq_op_smul_of_degree_zero N hf, ract_tmul]

/-- A degree-zero cochain in the right module induces an additive map on the coend. -/
def mapLeftCochain (r : CatModule.Cochain L N 0) : CatTensorProduct L M →+ CatTensorProduct N M :=
  lift _ (balanced_left_cochain M h₀ r)

include h₀ in
@[simp]
theorem mapLeftCochain_tmul (r : CatModule.Cochain L N 0) (X : C)
    (l : L.obj (op X)) (m : M.obj X) :
    mapLeftCochain M h₀ r (tmul X l m) = tmul X (r.app (op X) l) m :=
  lift_tmul _ (balanced_left_cochain M h₀ r) X l m

variable (f : L ⟶ N)

private abbrev fstCochain := CatModule.Cochain.ofHom (CatModule.cone.fstHom f)
private abbrev split (f : L ⟶ N) := CatModule.cone.gradedSplitting f

private def coneSplitHom : CatTensorProduct (CatModule.cone f) M →+
    CatTensorProduct (CatModule.shift 1 L) M × CatTensorProduct N M :=
  (mapLeftCochain M h₀ (fstCochain f)).prod (mapLeftCochain M h₀ (split f).r)

private def coneJoinHom :
    CatTensorProduct (CatModule.shift 1 L) M × CatTensorProduct N M →+
      CatTensorProduct (CatModule.cone f) M :=
  (mapLeftCochain M h₀ (split f).s).coprod
    (mapLeftCochain M h₀ (CatModule.Cochain.ofHom (CatModule.cone.inr f)))

private theorem coneSplitHom_tmul (X : C) (p : (CatModule.cone f).obj (op X)) (m : M.obj X) :
    coneSplitHom M h₀ f (tmul X p m) =
      (tmul X ((fstCochain f).app (op X) p) m, tmul X ((split f).r.app (op X) p) m) :=
  Prod.ext (mapLeftCochain_tmul M h₀ _ X p m) (mapLeftCochain_tmul M h₀ _ X p m)

private theorem coneJoinHom_split :
    (coneJoinHom M h₀ f).comp (coneSplitHom M h₀ f) = AddMonoidHom.id _ := by
  apply addHom_ext
  intro X p m
  rw [AddMonoidHom.comp_apply, coneSplitHom_tmul]
  change mapLeftCochain M h₀ (split f).s (tmul X ((fstCochain f).app (op X) p) m) +
    mapLeftCochain M h₀ (CatModule.Cochain.ofHom (CatModule.cone.inr f))
      (tmul X ((split f).r.app (op X) p) m) = tmul X p m
  rw [mapLeftCochain_tmul, mapLeftCochain_tmul, ← add_tmul]
  exact congrArg (fun z => tmul X z m) (by
    rw [add_comm]
    exact (split f).i_r_add_s_p p)


private theorem coneSplitHom_join (z : CatTensorProduct (CatModule.shift 1 L) M × CatTensorProduct N M) :
    coneSplitHom M h₀ f (coneJoinHom M h₀ f z) = z := by
  let P := coneSplitHom M h₀ f
  let l := mapLeftCochain M h₀ (split f).s
  let r := mapLeftCochain M h₀ (CatModule.Cochain.ofHom (CatModule.cone.inr f))
  have hl : P.comp l = AddMonoidHom.inl _ _ := by
    apply addHom_ext
    intro X x m
    change P (l (tmul X x m)) = (tmul X x m, 0)
    rw [show l (tmul X x m) = tmul X ((split f).s.app (op X) x) m from
      mapLeftCochain_tmul M h₀ _ X x m]
    change coneSplitHom M h₀ f _ = _
    rw [coneSplitHom_tmul]
    change (tmul X x m, tmul X (0 : N.obj (op X)) m) = _
    rw [zero_tmul]
  have hr : P.comp r = AddMonoidHom.inr _ _ := by
    apply addHom_ext
    intro X x m
    change P (r (tmul X x m)) = (0, tmul X x m)
    rw [show r (tmul X x m) = tmul X ((CatModule.cone.inr f).app (op X) x) m from
      mapLeftCochain_tmul M h₀ _ X x m]
    change coneSplitHom M h₀ f _ = _
    rw [coneSplitHom_tmul]
    change (tmul X (0 : (CatModule.shift 1 L).obj (op X)) m, tmul X x m) = _
    rw [zero_tmul]
  change P (l z.1 + r z.2) = z
  rw [map_add, show P (l z.1) = (z.1, 0) from DFunLike.congr_fun hl z.1,
    show P (r z.2) = (0, z.2) from DFunLike.congr_fun hr z.2]
  exact Prod.ext (add_zero _) (zero_add _)

private def coneSplitAddEquiv :
    CatTensorProduct (CatModule.cone f) M ≃+
      CatTensorProduct (CatModule.shift 1 L) M × CatTensorProduct N M where
  toFun := coneSplitHom M h₀ f
  invFun := coneJoinHom M h₀ f
  left_inv x := DFunLike.congr_fun (coneJoinHom_split M h₀ f) x
  right_inv := coneSplitHom_join M h₀ f
  map_add' := map_add _

/-- The morphism of integer DG modules induced on the coend. -/
def mapLeftInt : CatTensorProduct L M →ᵈᵍ[ℤ] CatTensorProduct N M where
  toLinearMap := (map f (𝟙 M)).toIntLinearMap
  map_mem' := map_mem f (𝟙 M)
  map_d' := map_d f (𝟙 M)

private def coneLeftAddEquiv :
    CatTensorProduct (CatModule.cone f) M ≃+ DG.Cone (mapLeftInt M f) :=
  (coneSplitAddEquiv M h₀ f).trans
    ((shiftLeftDGEquiv L M 1 h₀).toAddEquiv.prodCongr (AddEquiv.refl _))

private theorem coneLeftAddEquiv_tmul (X : C) (p : (CatModule.cone f).obj (op X)) (m : M.obj X) :
    coneLeftAddEquiv M h₀ f (tmul X p m) =
      (Shift.mk 1 (tmul X (CatModule.shift.unmk 1 p.1) m), tmul X p.2 m) := by
  change (AddEquiv.prodCongr _ _) (coneSplitHom M h₀ f (tmul X p m)) = _
  rw [coneSplitHom_tmul]
  exact Prod.ext (shiftLeftDGEquiv_tmul L M 1 h₀ X p.1 m) rfl


private theorem coneLeftAddEquiv_mem {j : ℤ}
    {z : CatTensorProduct (CatModule.cone f) M} (hz : z ∈ grading j) :
    coneLeftAddEquiv M h₀ f z ∈ grading j := by
  refine induction_on_mem_grading (P := fun y => coneLeftAddEquiv M h₀ f y ∈ grading j)
    (by rw [map_zero]; exact zero_mem _) ?_ ?_ ?_ hz
  · intro X a b p m hp hm hab
    have hparts := (CatModule.cone.mem_grading_iff (f := f)).mp hp
    rw [← hab, coneLeftAddEquiv_tmul]
    change Shift.mk 1 (tmul X (CatModule.shift.unmk 1 p.1) m) ∈ grading (a+b) ∧
      tmul X p.2 m ∈ grading (a+b)
    have hp₁ : p.1 ∈ grading a := hparts.1
    have hp₂ : p.2 ∈ grading a := hparts.2
    have h₁ := (shiftLeftDGEquiv L M 1 h₀).map_mem (tmul_mem_grading hp₁ hm)
    rw [shiftLeftDGEquiv_tmul L M 1 h₀ X p.1 m] at h₁
    exact ⟨h₁, tmul_mem_grading hp₂ hm⟩
  · intro x y hx hy
    rw [map_add]
    exact add_mem hx hy
  · intro x hx
    rw [map_neg]
    exact neg_mem hx

private theorem coneLeftAddEquiv_d (z : CatTensorProduct (CatModule.cone f) M) :
    coneLeftAddEquiv M h₀ f (d z) = d (coneLeftAddEquiv M h₀ f z) := by
  induction z using induction_on with
  | zero => simp
  | add x y hx hy => rw [d_add, map_add, hx, hy, map_add, d_add]
  | tmul X p m =>
    induction p using DG.induction_on with
    | h_zero => simp
    | h_add p q hp hq => rw [add_tmul, d_add, map_add, hp, hq, map_add, d_add]
    | @h_homogeneous a p =>
      have hp := p.property
      let E := coneLeftAddEquiv M h₀ f
      have hs : E (koszulSign a • tmul X p.val (d m)) = koszulSign a • E (tmul X p.val (d m)) :=
        map_units_zsmul E.toAddMonoidHom _ _
      rw [d_tmul_of_mem X hp, map_add, hs,
        coneLeftAddEquiv_tmul, coneLeftAddEquiv_tmul, coneLeftAddEquiv_tmul]
      have hparts := (CatModule.cone.mem_grading_iff (f := f)).mp hp
      have hp₁ : p.val.1 ∈ grading a := hparts.1
      have hp₂ : p.val.2 ∈ grading a := hparts.2
      apply Prod.ext
      · change Shift.mk 1 (tmul X (CatModule.shift.unmk 1 (d p.val.1)) m) +
          koszulSign a • Shift.mk 1 (tmul X (CatModule.shift.unmk 1 p.val.1) (d m)) =
          d (Shift.mk 1 (tmul X (CatModule.shift.unmk 1 p.val.1) m))
        let e := shiftLeftDGEquiv L M 1 h₀
        have h := e.map_d (tmul X p.val.1 m)
        have hs' : e (koszulSign a • tmul X p.val.1 (d m)) = koszulSign a • e (tmul X p.val.1 (d m)) :=
          map_units_zsmul e.toAddEquiv.toAddMonoidHom _ _
        rw [d_tmul_of_mem X hp₁, map_add, hs'] at h
        simpa only [e, shiftLeftDGEquiv_tmul] using h
      · change tmul X (f.app (op X) (CatModule.shift.unmk 1 p.val.1) + d p.val.2) m +
          koszulSign a • tmul X p.val.2 (d m) =
          map f (𝟙 M) (tmul X (CatModule.shift.unmk 1 p.val.1) m) + d (tmul X p.val.2 m)
        rw [map_tmul, CatModule.id_app, d_tmul_of_mem X hp₂, add_tmul, add_assoc]

/-- The coend in its right-module argument carries the mapping cone to the
mapping cone of the induced morphism. -/
def coneLeftDGEquiv : DGAddEquiv (CatTensorProduct (CatModule.cone f) M) (DG.Cone (mapLeftInt M f)) where
  toAddEquiv := coneLeftAddEquiv M h₀ f
  map_mem' := coneLeftAddEquiv_mem M h₀ f
  map_d' := coneLeftAddEquiv_d M h₀ f

end DG.CatTensorProduct
