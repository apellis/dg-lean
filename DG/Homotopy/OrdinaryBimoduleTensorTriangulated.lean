import DG.Module.TensorProductOverProd
import DG.Homotopy.BimoduleTensor
import DG.Homotopy.Comparison
import DG.Homotopy.ConeCochain

/-!
# Ordinary bimodule tensor preserves standard triangles

For rings concentrated in degree zero and a dg bimodule concentrated in degree zero,
balanced tensor commutes with cochain shifts and mapping cones. The functor induced
on homotopy categories is triangulated.

This supplies the exact functor used in Webster,
[arXiv:1309.3796v2](https://arxiv.org/abs/1309.3796v2), Definition 6.6 and Lemma 6.8,
proof of (6.21).
-/

open CategoryTheory
open scoped DG.DegreeZero

noncomputable section

namespace DG

open TensorProductOver

universe u

variable {B : Type u} [Ring B] {M N : Type u} [AddCommGroup M] [DGAddCommGroup M] [Module Bᵐᵒᵖ M]
  [AddCommGroup N] [DGAddCommGroup N] [Module B N] [DGModule B N]

omit [DGAddCommGroup M] [DGAddCommGroup N] [DGModule B N] in
private theorem shift_unmk_smul_degreeZero (j : ℤ) (b : B) (x : Shift j N) :
    Shift.unmk j (b • x) = b • Shift.unmk j x := by
  rw [Shift.unmk_smul (i := 0) (DegreeZero.mem_grading_iff.mpr (Or.inl rfl))]
  rw [mul_zero, koszulSign_zero, one_smul]

/-- The additive map comparing degree-zero bimodule tensor with a cochain shift. -/
def tensorShiftTo (j : ℤ) :
    TensorProductOver B M (Shift j N) →+
      Shift j (TensorProductOver B M N) :=
  let f := ((TensorProductOver.tmulAddHom B M N).compr₂ (Shift.mk j).toAddMonoidHom).compl₂
    (Shift.unmk j).toAddMonoidHom
  lift f fun b m x => by
    change Shift.mk j (tmul B (MulOpposite.op b • m) (Shift.unmk j x)) =
      Shift.mk j (tmul B m (Shift.unmk j (b • x)))
    rw [shift_unmk_smul_degreeZero, op_smul_tmul]

omit [DGAddCommGroup M] [DGAddCommGroup N] [DGModule B N] in
@[simp]
theorem tensorShiftTo_tmul (j : ℤ) (m : M) (x : Shift j N) :
    tensorShiftTo j (tmul B m x) = Shift.mk j (tmul B m (Shift.unmk j x)) := rfl

private def tensorShiftFrom (j : ℤ) :
    Shift j (TensorProductOver B M N) →+
      TensorProductOver B M (Shift j N) :=
  let f := (TensorProductOver.tmulAddHom B M (Shift j N)).compl₂ (Shift.mk j).toAddMonoidHom
  (lift f (fun b m x => by
    change tmul B (MulOpposite.op b • m) (Shift.mk j x) = tmul B m (Shift.mk j (b • x))
    rw [op_smul_tmul]
    congr 1
    apply (Shift.unmk j).injective
    rw [shift_unmk_smul_degreeZero, Shift.unmk_mk, Shift.unmk_mk])).comp (Shift.unmk j).toAddMonoidHom

/-- Tensoring with an ordinary bimodule commutes with shifts on underlying additive groups. -/
def tensorShiftAddEquiv (j : ℤ) :
    TensorProductOver B M (Shift j N) ≃+
      Shift j (TensorProductOver B M N) := by
  refine { tensorShiftTo j with
    invFun := tensorShiftFrom j
    left_inv := ?_
    right_inv := ?_ }
  · intro x
    change tensorShiftFrom j (tensorShiftTo j x) = x
    have h : (tensorShiftFrom j).comp (tensorShiftTo j) =
        AddMonoidHom.id (TensorProductOver B M (Shift j N)) := by
      apply addHom_ext
      intro m x
      rfl
    exact DFunLike.congr_fun h x
  · have h : ((tensorShiftTo (B := B) (M := M) (N := N) j).comp (tensorShiftFrom j)).comp
          (Shift.mk j).toAddMonoidHom = (Shift.mk j).toAddMonoidHom := by
      apply addHom_ext
      intro m x
      rfl
    intro y
    obtain ⟨x, rfl⟩ := (Shift.mk j).surjective y
    change tensorShiftTo j (tensorShiftFrom j (Shift.mk j x)) = Shift.mk j x
    exact DFunLike.congr_fun h x

variable {A : Type u} [Ring A] [Module A M] [DGBimodule A B M]
  [Fact (∀ m : M, m ∈ grading 0)]

private theorem mem_concentrated (m : M) : m ∈ grading 0 :=
  (Fact.out : ∀ m : M, m ∈ grading 0) m

private theorem d_eq_zero_of_concentrated (m : M) : d m = 0 := by
  have h₀ : d m ∈ grading 0 := mem_concentrated (d m)
  have h₁ : d m ∈ grading (1 : ℤ) := d_mem (mem_concentrated m : m ∈ grading 0)
  have h := DirectSum.decompose_of_mem_ne (grading (M := M)) h₁ (by decide : (1 : ℤ) ≠ 0)
  rw [DirectSum.decompose_of_mem_same _ h₀]
    at h
  exact h

/-- The shift comparison for balanced tensor with a degree-zero bimodule. -/
def tensorShiftEquiv (j : ℤ) :
    TensorProductOver B M (Shift j N) ≃ᵈᵍ[A]
      Shift j (TensorProductOver B M N) where
  __ := tensorShiftAddEquiv j
  map_smul' a y := by
    change tensorShiftTo j (a • y) = a • tensorShiftTo j y
    induction y using TensorProductOver.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul m x =>
      apply (Shift.unmk j).injective
      rw [TensorProductOver.smul_tmul, tensorShiftTo_tmul, tensorShiftTo_tmul,
        shift_unmk_smul_degreeZero, Shift.unmk_mk, Shift.unmk_mk, TensorProductOver.smul_tmul]
  map_mem' := by
    intro k y hy
    change tensorShiftTo j y ∈ grading k
    refine lift_mem _ ?_ ?_ hy
    · intro b m x
      change Shift.mk j (tmul B (MulOpposite.op b • m) (Shift.unmk j x)) =
        Shift.mk j (tmul B m (Shift.unmk j (b • x)))
      rw [shift_unmk_smul_degreeZero, op_smul_tmul]
    intro i l m x hm hx
    change Shift.mk j (tmul B m (Shift.unmk j x)) ∈ grading (i + l)
    rw [Shift.mem_grading_iff, add_assoc]
    exact TensorProductOver.tmul_mem_grading hm (Shift.unmk_mem_grading hx)
  map_d' y := by
    change tensorShiftTo j (d y) = d (tensorShiftTo j y)
    refine lift_d _ ?_ ?_ y
    · intro b m x
      change Shift.mk j (tmul B (MulOpposite.op b • m) (Shift.unmk j x)) =
        Shift.mk j (tmul B m (Shift.unmk j (b • x)))
      rw [shift_unmk_smul_degreeZero, op_smul_tmul]
    intro i m hm x
    change d (Shift.mk j (tmul B m (Shift.unmk j x))) =
      Shift.mk j (tmul B (d m) (Shift.unmk j x)) +
        koszulSign i • Shift.mk j (tmul B m (Shift.unmk j (d x)))
    rw [d_eq_zero_of_concentrated m, zero_tmul, Shift.mk_zero, zero_add, Shift.d_mk,
      TensorProductOver.d_tmul_of_mem hm, d_eq_zero_of_concentrated m, zero_tmul, zero_add, Shift.unmk_d,
      tmul_units_smul, Shift.mk_units_smul, Shift.mk_units_smul, smul_comm]
    rw [Shift.mk_units_smul]


variable {N' : Type u} [AddCommGroup N'] [DGAddCommGroup N'] [Module B N'] [DGModule B N']
  (g : N →ᵈᵍ[B] N')

/-- Comparison of the cone carriers under tensoring by an ordinary bimodule. -/
noncomputable def tensorConeAddEquiv :
    TensorProductOver B M (Cone g) ≃+
      Cone (DGModuleHom.lTensor A M g) :=
  prodRightAddEquiv.trans (AddEquiv.prodCongr (tensorShiftAddEquiv 1) (AddEquiv.refl _))

omit [Fact (∀ m : M, m ∈ grading 0)] in
theorem tensorConeAddEquiv_tmul (m : M) (x : Cone g) :
    tensorConeAddEquiv (A := A) g (tmul B m x) =
      ((tensorShiftAddEquiv 1 (tmul B m x.1), tmul B m x.2) :
        Cone (DGModuleHom.lTensor A M g)) := rfl


/-- The balanced tensor with a degree-zero bimodule commutes with mapping cones. -/
noncomputable def tensorConeEquiv :
    TensorProductOver B M (Cone g) ≃ᵈᵍ[A]
      Cone (DGModuleHom.lTensor A M g) where
  __ := tensorConeAddEquiv g
  map_smul' a y := by
    change tensorConeAddEquiv g (a • y) = a • tensorConeAddEquiv g y
    induction y using TensorProductOver.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul m x =>
      rw [TensorProductOver.smul_tmul, tensorConeAddEquiv_tmul, tensorConeAddEquiv_tmul]
      refine Prod.ext ?_ ?_
      · change tensorShiftEquiv (A := A) 1 (tmul B (a • m) x.1) = a • tensorShiftEquiv (A := A) 1 (tmul B m x.1)
        rw [← TensorProductOver.smul_tmul, map_smul]
      · exact (TensorProductOver.smul_tmul a m x.2).symm
  map_mem' {k y} hy := by
    change tensorConeAddEquiv g y ∈ grading k
    obtain ⟨x, hx, rfl⟩ := hy
    have h := DG.map_mem_grading_of_tmul
      ((tensorConeAddEquiv (A := A) g).toAddMonoidHom.comp (TensorProductOver.mk B _ _)) 0
      (fun {i j m p} hm hp => by
        change tensorConeAddEquiv (A := A) g (tmul B m p) ∈ grading (i + j + 0)
        rw [add_zero, tensorConeAddEquiv_tmul]
        refine Cone.mem_grading_iff.mpr ⟨?_, ?_⟩
        · exact (tensorShiftEquiv (A := A) 1).map_mem
            (TensorProductOver.tmul_mem_grading hm (Cone.mem_grading_iff.mp hp).1)
        · exact TensorProductOver.tmul_mem_grading hm (Cone.mem_grading_iff.mp hp).2) hx
    rwa [add_zero] at h
  map_d' y := by
    change tensorConeAddEquiv g (d y) = d (tensorConeAddEquiv g y)
    induction y using TensorProductOver.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul m p =>
      have hm : m ∈ grading 0 := mem_concentrated m
      rw [TensorProductOver.d_tmul_of_mem hm, d_eq_zero_of_concentrated m, zero_tmul,
        koszulSign_zero, one_smul, zero_add, tensorConeAddEquiv_tmul, tensorConeAddEquiv_tmul]
      refine Prod.ext ?_ ?_
      · change tensorShiftEquiv (A := A) 1 (tmul B m (d p.1)) = d (tensorShiftEquiv (A := A) 1 (tmul B m p.1))
        rw [← DGModuleEquiv.map_d, TensorProductOver.d_tmul_of_mem hm, d_eq_zero_of_concentrated m,
          zero_tmul, koszulSign_zero, one_smul, zero_add]
      · change tmul B m (g (Shift.unmk 1 p.1) + d p.2) =
          DGModuleHom.lTensor A M g
            (tmul B m (Shift.unmk 1 p.1)) + d (tmul B m p.2)
        rw [tmul_add, DGModuleHom.lTensor_tmul, TensorProductOver.d_tmul_of_mem hm,
          d_eq_zero_of_concentrated m, zero_tmul, koszulSign_zero, one_smul, zero_add]


open CategoryTheory.Pretriangulated

variable (A B M)

private noncomputable abbrev ordinaryTensorFunctor := DGModuleCat.tensorFunctor A M (B := B)

private noncomputable def tensorShiftIso (n : ℤ) (X : DGModuleCat.{u} B) :
    (shiftFunctor (DGModuleCat.{u} B) n ⋙ ordinaryTensorFunctor B M A).obj X ≅
      (ordinaryTensorFunctor B M A ⋙ shiftFunctor (DGModuleCat.{u} A) n).obj X :=
  DGModuleCat.isoOfDGModuleEquiv
    (M := DGModuleCat.of A (TensorProductOver B M (Shift n X)))
    (N := DGModuleCat.of A (Shift n (TensorProductOver B M X)))
    (tensorShiftEquiv (A := A) n)

set_option backward.isDefEq.respectTransparency false in
noncomputable instance ordinaryTensorFunctor_commShift :
    (ordinaryTensorFunctor B M A).CommShift ℤ where
  commShiftIso n := NatIso.ofComponents (tensorShiftIso B M A n) fun {X Y} h =>
    DGModuleCat.tensor_hom_ext (A := A) (M := M)
      (N := DGModuleCat.of B (Shift n X)) fun _ _ => rfl
  commShiftIso_zero := by
    ext X : 3
    rw [Functor.CommShift.isoZero_hom_app]
    exact DGModuleCat.tensor_hom_ext (A := A) (M := M)
      (N := DGModuleCat.of B (Shift 0 X)) fun _ _ => rfl
  commShiftIso_add a b := by
    ext X : 3
    rw [Functor.CommShift.isoAdd_hom_app]
    exact DGModuleCat.tensor_hom_ext (A := A) (M := M)
      (N := DGModuleCat.of B (Shift (a + b) X)) fun _ _ => rfl

/-- The ordinary bimodule tensor sends the standard cone triangle to the standard cone triangle. -/
noncomputable def tensorMapTriangleIso {X Y : DGModuleCat.{u} B} (f : X ⟶ Y) :
    (ordinaryTensorFunctor B M A).mapTriangle.obj (Cone.triangle f) ≅
      Cone.triangle ((ordinaryTensorFunctor B M A).map f) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (DGModuleCat.isoOfDGModuleEquiv (tensorConeEquiv f.hom))
    (by simp; rfl)
    (by
      apply DGModuleCat.tensor_hom_ext
      intro m y
      refine Prod.ext ?_ rfl
      change Shift.mk 1 (tmul B m (0 : X)) = 0
      rw [tmul_zero, Shift.mk_zero])
    (by
      apply DGModuleCat.tensor_hom_ext
      intro m x
      change Shift.mk 1 (tmul B m (-(Shift.unmk 1 x.1))) =
        -Shift.mk 1 (tmul B m (Shift.unmk 1 x.1))
      rw [tmul_neg, Shift.mk_neg])


private noncomputable abbrev homotopyTensorFunctor :=
  DG.HomotopyCategory.tensorFunctor A M (B := B)

omit [Fact (∀ m : M, m ∈ grading 0)] in
private theorem quotient_tensor_agrees (X Y : DGModuleCat.{u} B) (f g : X ⟶ Y)
    (h : DGModuleCat.homotopic B f g) :
    (ordinaryTensorFunctor B M A ⋙ DG.HomotopyCategory.quotient A).map f =
      (ordinaryTensorFunctor B M A ⋙ DG.HomotopyCategory.quotient A).map g :=
  (DG.HomotopyCategory.quotient_map_eq_iff _ _).mpr
    (DG.HomotopyCategory.tensorFunctor_homotopic A M f g h)

noncomputable instance homotopyTensorFunctor_commShift :
    (homotopyTensorFunctor B M A).CommShift ℤ :=
  CategoryTheory.Quotient.liftCommShift
    (ordinaryTensorFunctor B M A ⋙ DG.HomotopyCategory.quotient A)
    (DGModuleCat.homotopic.{u} B) ℤ (quotient_tensor_agrees B M A)

instance homotopyTensorFunctorQuotientIso_commShift :
    NatTrans.CommShift (DG.HomotopyCategory.tensorFunctorQuotientIso
      A M (B := B)).hom ℤ :=
  CategoryTheory.Quotient.liftCommShift_compatibility
    (ordinaryTensorFunctor B M A ⋙ DG.HomotopyCategory.quotient A)
    (DGModuleCat.homotopic.{u} B) ℤ (quotient_tensor_agrees B M A)

instance homotopyTensorFunctor_isTriangulated :
    (homotopyTensorFunctor B M A).IsTriangulated where
  map_distinguished := by
    rintro T ⟨X, Y, f, ⟨e⟩⟩
    exact ⟨_, _, _, ⟨(homotopyTensorFunctor B M A).mapTriangle.mapIso e ≪≫
      (Functor.mapTriangleCompIso _ _).symm.app _ ≪≫
      (Functor.mapTriangleIso
        (DG.HomotopyCategory.tensorFunctorQuotientIso A M)).app _ ≪≫
      (Functor.mapTriangleCompIso _ _).app _ ≪≫
      (DG.HomotopyCategory.quotient A).mapTriangle.mapIso (tensorMapTriangleIso B M A f)⟩⟩


end DG
