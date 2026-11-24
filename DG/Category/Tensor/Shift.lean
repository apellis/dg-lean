import DG.Category.Tensor.Symmetry
import DG.Category.Homotopy.Shift

/-!
# Shifting the right module of a dg coend

For a dg category concentrated in degree zero, shifting the right module
shifts the coend by the same cohomological degree. The comparison sends
a pure tensor of a shifted element to the shift of the corresponding pure tensor.
-/

noncomputable section

namespace DG.CatTensorProduct

open CategoryTheory DGOpposite
open scoped CatModule

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]
  (N : CatModule.{w} (DGOpposite C)) (M : CatModule.{w} C)
  (j : ℤ) (h₀ : ∀ {X Y : C} (f : X ⟶ Y), f ∈ grading (0 : ℤ))

local notation "U" => fun X : C => CatModule.shift.unmk (M := N) (X := op X) j
local notation "K" => fun X : C => CatModule.shift.mk (M := N) (X := op X) j
local notation "T" => CatTensorProduct N M

include h₀ in
private theorem unmk_ract_shift {X Y : C} (f : X ⟶ Y)
    (x : (CatModule.shift j N).obj (op Y)) :
    U X (x <• f) = U Y x <• f := by
  have hf := h₀ f
  have hf' : homOp f ∈ grading (0 : ℤ) := hf
  have htw : CatModule.twist j (homOp f) = homOp f := by
    rw [CatModule.twist_of_mem hf', mul_zero, koszulSign_zero, one_smul]
  rw [CatModule.ract_eq_op_smul_of_degree_zero (CatModule.shift j N) hf,
    CatModule.shift.unmk_smul_eq, htw, CatModule.ract_eq_op_smul_of_degree_zero N hf]

private def shiftLeftFamily (X : C) :
    (CatModule.shift j N).obj (op X) →+ M.obj X →+
      Shift j (CatTensorProduct N M) :=
  ((tmulAddHom N M X).comp (U X).toAddMonoidHom).compr₂
    (Shift.mk j).toAddMonoidHom

include h₀ in
private theorem shiftLeftFamily_balanced : Balanced (shiftLeftFamily N M j) := by
  intro X Y f x y
  change Shift.mk j (tmul X (U X (x <• f)) y) =
    Shift.mk j (tmul Y (U Y x) (f • y))
  rw [unmk_ract_shift N j h₀, ract_tmul]

/-- Shift in the right-module variable of a coend over a degree-zero dg category. -/
def shiftLeftHom : CatTensorProduct (CatModule.shift j N) M →+
    Shift j (CatTensorProduct N M) :=
  lift (shiftLeftFamily N M j) (shiftLeftFamily_balanced N M j h₀)


include h₀ in
private theorem mk_ract_shift {X Y : C} (f : X ⟶ Y) (x : N.obj (op Y)) :
    K Y x <• f = K X (x <• f) := by
  apply (U X).injective
  rw [unmk_ract_shift N j h₀, CatModule.shift.unmk_mk, CatModule.shift.unmk_mk]

private def unshiftLeftFamily (X : C) :
    N.obj (op X) →+ M.obj X →+ CatTensorProduct (CatModule.shift j N) M :=
  (tmulAddHom (CatModule.shift j N) M X).comp (K X).toAddMonoidHom

include h₀ in
private theorem unshiftLeftFamily_balanced : Balanced (unshiftLeftFamily N M j) := by
  intro X Y f x m
  change tmul X (K X (x <• f)) m =
    tmul Y (K Y x) (f • m)
  rw [← mk_ract_shift N j h₀, ract_tmul]

def shiftLeftInvHom : Shift j (CatTensorProduct N M) →+
    CatTensorProduct (CatModule.shift j N) M :=
  (lift (unshiftLeftFamily N M j) (unshiftLeftFamily_balanced N M j h₀)).comp
    (Shift.unmk j).toAddMonoidHom

include h₀ in
theorem shiftLeftHom_tmul (X : C) (x : (CatModule.shift j N).obj (op X))
    (m : M.obj X) :
    shiftLeftHom N M j h₀ (tmul X x m) = Shift.mk j (tmul X (U X x) m) := by
  exact lift_tmul _ (shiftLeftFamily_balanced N M j h₀) X x m

include h₀ in
theorem shiftLeftInvHom_mk_tmul (X : C) (x : N.obj (op X)) (m : M.obj X) :
    shiftLeftInvHom N M j h₀ (Shift.mk j (tmul X x m)) = tmul X (K X x) m := by
  change lift (unshiftLeftFamily N M j) (unshiftLeftFamily_balanced N M j h₀)
    (Shift.unmk j (Shift.mk j (tmul X x m))) = _
  rw [Shift.unmk_mk]
  exact lift_tmul _ (unshiftLeftFamily_balanced N M j h₀) X x m

include h₀ in
private theorem shiftLeftInvHom_comp :
    (shiftLeftInvHom N M j h₀).comp (shiftLeftHom N M j h₀) = AddMonoidHom.id _ := by
  apply addHom_ext
  intro X x m
  change shiftLeftInvHom N M j h₀ (shiftLeftHom N M j h₀ (tmul X x m)) = tmul X x m
  rw [shiftLeftHom_tmul, shiftLeftInvHom_mk_tmul, CatModule.shift.mk_unmk]

include h₀ in
private theorem shiftLeftHom_inv (x : CatTensorProduct N M) :
    shiftLeftHom N M j h₀ (shiftLeftInvHom N M j h₀ (Shift.mk j x)) = Shift.mk j x := by
  have h : ((shiftLeftHom N M j h₀).comp (shiftLeftInvHom N M j h₀)).comp
      (Shift.mk j).toAddMonoidHom = (Shift.mk j).toAddMonoidHom := by
    apply addHom_ext
    intro X n m
    change shiftLeftHom N M j h₀ (shiftLeftInvHom N M j h₀ (Shift.mk j (tmul X n m))) =
      Shift.mk j (tmul X n m)
    rw [shiftLeftInvHom_mk_tmul, shiftLeftHom_tmul, CatModule.shift.unmk_mk]
  exact DFunLike.congr_fun h x

private theorem shiftLeftFamily_mem (X : C) {a b : ℤ}
    {x : (CatModule.shift j N).obj (op X)} {m : M.obj X}
    (hx : x ∈ grading a) (hm : m ∈ grading b) :
    shiftLeftFamily N M j X x m ∈ grading (a+b) := by
  have hux : U X x ∈ grading (a+j) := CatModule.shift.unmk_mem_grading hx
  have h := Shift.mk_mem_grading (n := j) (tmul_mem_grading hux hm)
  change Shift.mk j (tmul X (U X x) m) ∈ grading (a+b)
  simpa only [show (a+j+b)-j = a+b by omega] using h

private theorem shiftLeftFamily_d (X : C) {a : ℤ}
    {x : (CatModule.shift j N).obj (op X)}
    (hx : x ∈ grading a) (m : M.obj X) :
    d (shiftLeftFamily N M j X x m) =
      shiftLeftFamily N M j X (d x) m + koszulSign a • shiftLeftFamily N M j X x (d m) := by
  have hux : U X x ∈ grading (a+j) := CatModule.shift.unmk_mem_grading hx
  change d (Shift.mk j (tmul X (U X x) m)) =
    Shift.mk j (tmul X (U X (d x)) m) +
      koszulSign a • Shift.mk j (tmul X (U X x) (d m))
  rw [Shift.d_mk, d_tmul_of_mem X hux, CatModule.shift.unmk_d,
    smul_add, units_smul_tmul, smul_smul]
  have hsign : koszulSign j * koszulSign (a+j) = koszulSign a := by
    rw [koszulSign_add, mul_left_comm, Int.units_mul_self, mul_one]
  rw [hsign, map_add]
  congr 1

/-- The coend shift in the first variable, using the existing cohomological shift. -/
def shiftLeftDGEquiv : DGAddEquiv (CatTensorProduct (CatModule.shift j N) M)
    (Shift j (CatTensorProduct N M)) where
  toAddEquiv := {
    toFun := shiftLeftHom N M j h₀
    invFun := shiftLeftInvHom N M j h₀
    left_inv x := DFunLike.congr_fun (shiftLeftInvHom_comp N M j h₀) x
    right_inv x := by simpa only [Shift.mk_unmk] using shiftLeftHom_inv N M j h₀ (Shift.unmk j x)
    map_add' := map_add (shiftLeftHom N M j h₀) }
  map_mem' h := lift_mem (shiftLeftFamily N M j) (shiftLeftFamily_balanced N M j h₀)
    (fun X _ _ _ _ hx hm => shiftLeftFamily_mem N M j X hx hm) h
  map_d' := lift_d (shiftLeftFamily N M j) (shiftLeftFamily_balanced N M j h₀)
    (fun X _ _ hx => shiftLeftFamily_d N M j X hx)

include h₀ in
@[simp]
theorem shiftLeftDGEquiv_tmul (X : C) (x : (CatModule.shift j N).obj (op X))
    (m : M.obj X) :
    shiftLeftDGEquiv N M j h₀ (tmul X x m) = Shift.mk j (tmul X (U X x) m) :=
  shiftLeftHom_tmul N M j h₀ X x m

end DG.CatTensorProduct
