import DG.Category.Tensor.Basic
import DG.Category.Homotopy.Acyclic
import DG.Category.Coproducts

/-!
# Tensor products over dg categories and coproducts

The coend commutes with coproducts in the left-module variable, with its
ordinary differential and grading. Evaluation at a representable and
the tensor of two retracts give basic acyclicity tests for Tor balance.
-/

namespace DG.CatTensorProduct

open CategoryTheory DGOpposite

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]

private theorem isAcyclic_of_addEquiv {P Q : Type*} [AddCommGroup P]
    [DGAddCommGroup P] [AddCommGroup Q] [DGAddCommGroup Q]
    (e : DGAddEquiv P Q) (h : DG.IsAcyclic Q) : DG.IsAcyclic P := by
  refine DG.isAcyclic_iff.mpr fun n x hx hdx => ?_
  obtain ⟨y, hy, hdy⟩ := h.exists_d_eq (e.map_mem hx) (by rw [← e.map_d, hdx, map_zero])
  exact ⟨e.symm y, e.symm.map_mem hy, e.injective (by rw [e.map_d, e.apply_symm_apply, hdy])⟩

/-- A right dg module which is acyclic remains acyclic after tensoring with a
left representable. -/
theorem isAcyclic_rid {N : CatModule.{w} (DGOpposite C)}
    (hN : CatModule.IsAcyclic N) (X : C) :
    DG.IsAcyclic (CatTensorProduct N (CatModule.representable X)) :=
  isAcyclic_of_addEquiv (rid N X) (hN (op X))

/-- A left dg module which is acyclic remains acyclic after tensoring with a
right representable. -/
theorem isAcyclic_lid {M : CatModule.{w} C} (hM : CatModule.IsAcyclic M) (X : C) :
    DG.IsAcyclic (CatTensorProduct (CatModule.representable (op X)) M) :=
  isAcyclic_of_addEquiv (lid M X) (hM X)

/-- Tensoring two retracts gives a retract, so acyclicity descends from the
tensor of the larger pair. -/
theorem isAcyclic_of_tensor_retract
    {N N' : CatModule.{w} (DGOpposite C)} {M M' : CatModule.{w} C}
    (iN : N ⟶ N') (pN : N' ⟶ N) (iM : M ⟶ M') (pM : M' ⟶ M)
    (hN : iN ≫ pN = 𝟙 N) (hM : iM ≫ pM = 𝟙 M)
    (h : DG.IsAcyclic (CatTensorProduct N' M')) : DG.IsAcyclic (CatTensorProduct N M) := by
  refine DG.isAcyclic_iff.mpr fun n x hx hdx => ?_
  have hz : d (map iN iM x) = 0 := by rw [← map_d, hdx, map_zero]
  obtain ⟨y, hy, hdy⟩ := h.exists_d_eq (map_mem iN iM hx) hz
  refine ⟨map pN pM y, map_mem pN pM hy, ?_⟩
  rw [← map_d, hdy, ← map_comp_apply, hN, hM, map_id]
  rfl

end DG.CatTensorProduct

open DirectSum

namespace DG.DirectSum


/-- A cycle in a direct sum of acyclic complexes has a primitive supported
on the finite support of the cycle. -/
theorem isAcyclic_directSum {ι : Type*} [DecidableEq ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, DGAddCommGroup (M i)]
    (hM : ∀ i, DG.IsAcyclic (M i)) : DG.IsAcyclic (⨁ i, M i) := by
  classical
  refine DG.isAcyclic_iff.mpr fun n x hx hdx => ?_
  have hd (i : ι) : DGAddCommGroup.d (x i) = 0 := by
    have hi := congrArg (fun z : (⨁ i, M i) => z i) hdx
    simpa only [coe_d_apply, _root_.DirectSum.zero_apply] using hi
  choose y hy hdy using fun i => (hM i).exists_d_eq ((mem_grading M).mp hx i) (hd i)
  let z : ⨁ i, M i := DFinsupp.mk x.support fun i => y i.val
  refine ⟨z, (mem_grading M).2 ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ x.support
    · rw [show z i = y i from DFinsupp.mk_of_mem hi]
      exact hy i
    · rw [show z i = 0 from DFinsupp.mk_of_notMem hi]
      exact zero_mem _
  · apply DFinsupp.ext
    intro i
    rw [coe_d_apply]
    by_cases hi : i ∈ x.support
    · rw [show z i = y i from DFinsupp.mk_of_mem hi, hdy]
    · rw [show z i = 0 from DFinsupp.mk_of_notMem hi, map_zero,
        DFinsupp.notMem_support_iff.mp hi]

end DG.DirectSum

noncomputable section

open CategoryTheory DirectSum

namespace DG.CatTensorProduct

open DGOpposite CatModule

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]
  {J : Type w} [DecidableEq J] (N : CatModule.{w} (DGOpposite C))
  (F : J → CatModule.{w} C)

local notation "L" => CatModule.directSum F
local notation "T" => fun j => CatTensorProduct N (F j)

private def sumFamily (X : C) :
    N.obj (op X) →+ (L).obj X →+ (⨁ j, T j) where
  toFun n := _root_.DirectSum.map fun j => tmulAddHom N (F j) X n
  map_zero' := by
    apply AddMonoidHom.ext
    intro m
    let m' : ⨁ j, (F j).obj X := m
    change (DirectSum.map fun j => tmulAddHom N (F j) X 0) m' = 0
    apply DFinsupp.ext
    intro j
    simp only [DirectSum.map_apply, DirectSum.zero_apply, tmulAddHom_apply, zero_tmul]
  map_add' n n' := by
    apply AddMonoidHom.ext
    intro m
    let m' : ⨁ j, (F j).obj X := m
    change (DirectSum.map fun j => tmulAddHom N (F j) X (n + n')) m' =
      (DirectSum.map fun j => tmulAddHom N (F j) X n) m' +
      (DirectSum.map fun j => tmulAddHom N (F j) X n') m'
    apply DFinsupp.ext
    intro j
    simp only [DirectSum.map_apply, DirectSum.add_apply, tmulAddHom_apply, add_tmul]

private abbrev sumCoordinate (X : C) (m : (L).obj X) (j : J) :=
  (show ⨁ i, (F i).obj X from m) j

private theorem sumFamily_apply (X : C) (n : N.obj (op X)) (m : (L).obj X) (j : J) :
    sumFamily N F X n m j = tmul X n (sumCoordinate F X m j) := by
  exact DirectSum.map_apply _ _ _

private theorem sumFamily_balanced : Balanced (sumFamily N F) := by
  intro X Y f n m
  apply DFinsupp.ext
  intro j
  rw [sumFamily_apply, sumFamily_apply]
  let m' : ⨁ j, (F j).obj X := m
  change tmul X _ (m' j) = tmul Y n
    (DirectSum.map (fun j => (F j).act f) m' j)
  rw [DirectSum.map_apply]
  exact ract_tmul f n (m' j)

private def sumForward : CatTensorProduct N L →+ (⨁ j, T j) :=
  lift (sumFamily N F) (sumFamily_balanced N F)

private def sumBackward : (⨁ j, T j) →+ CatTensorProduct N L :=
  DirectSum.toAddMonoid fun j => map (𝟙 N) (CatModule.directSumι F j)

private theorem sumForward_tmul_of (X : C) (j : J) (n : N.obj (op X))
    (m : (F j).obj X) :
    sumForward N F (tmul X n (DirectSum.of (fun j => (F j).obj X) j m)) =
      DirectSum.of T j (tmul X n m) := by
  calc
    _ = sumFamily N F X n (DirectSum.of (fun j => (F j).obj X) j m) :=
      lift_tmul _ _ X n _
    _ = _ := DirectSum.map_of _ _ _

private theorem sumBackward_of_tmul (X : C) (j : J) (n : N.obj (op X))
    (m : (F j).obj X) :
    sumBackward N F (DirectSum.of T j (tmul X n m)) =
      tmul X n (DirectSum.of (fun j => (F j).obj X) j m) := by
  simp [sumBackward, CatModule.directSumι_app]

private theorem sumBackward_forward :
    (sumBackward N F).comp (sumForward N F) = AddMonoidHom.id _ := by
  apply addHom_ext
  intro X n m
  have h : (sumBackward N F).comp ((sumForward N F).comp (tmulAddHom N L X n)) =
      tmulAddHom N L X n := by
    apply DirectSum.addHom_ext
    intro j z
    change sumBackward N F (sumForward N F (tmul X n (DirectSum.of _ j z))) = _
    rw [sumForward_tmul_of, sumBackward_of_tmul]
    rfl
  exact DFunLike.congr_fun h m

private theorem sumForward_backward :
    (sumForward N F).comp (sumBackward N F) = AddMonoidHom.id _ := by
  apply DirectSum.addHom_ext
  intro j y
  have h : (sumForward N F).comp ((sumBackward N F).comp (DirectSum.of T j)) =
      DirectSum.of T j := by
    apply addHom_ext
    intro X n m
    change sumForward N F (sumBackward N F (DirectSum.of T j (tmul X n m))) = _
    rw [sumBackward_of_tmul, sumForward_tmul_of]
  exact DFunLike.congr_fun h y

/-- Coends commute with direct sums in their left-module variable. -/
def directSumAddEquiv : CatTensorProduct N L ≃+ (⨁ j, T j) where
  toFun := sumForward N F
  invFun := sumBackward N F
  left_inv x := DFunLike.congr_fun (sumBackward_forward N F) x
  right_inv x := DFunLike.congr_fun (sumForward_backward N F) x
  map_add' := map_add (sumForward N F)

private theorem sumFamily_mem (X : C) {i j : ℤ}
    {n : N.obj (op X)} {m : (L).obj X}
    (hn : n ∈ grading i) (hm : m ∈ grading j) :
    sumFamily N F X n m ∈ grading (i + j) := by
  apply (DG.DirectSum.mem_grading _).2
  intro k
  rw [sumFamily_apply]
  exact tmul_mem_grading hn ((DG.DirectSum.mem_grading _).1 hm k)

private theorem sumFamily_d (X : C) {i : ℤ} {n : N.obj (op X)}
    (hn : n ∈ grading i) (m : (L).obj X) :
    d (sumFamily N F X n m) =
      sumFamily N F X (d n) m + koszulSign i • sumFamily N F X n (d m) := by
  apply DFinsupp.ext
  intro j
  have hd : sumCoordinate F X (d m) j = d (sumCoordinate F X m j) :=
    DG.DirectSum.coe_d_apply (fun j => (F j).obj X) m j
  simp only [DG.DirectSum.coe_d_apply, DirectSum.add_apply, Units.smul_def,
    DirectSum.smul_apply, sumFamily_apply, hd]
  simpa only [Units.smul_def] using d_tmul_of_mem X hn (sumCoordinate F X m j)

/-- Coends commute with direct sums as dg abelian groups. -/
def directSumDGEquiv : DGAddEquiv (CatTensorProduct N L) (⨁ j, T j) where
  toAddEquiv := directSumAddEquiv N F
  map_mem' hm := lift_mem _ _ (fun X _ _ _ _ hn hx => sumFamily_mem N F X hn hx) hm
  map_d' := lift_d _ _ (fun X _ _ hn => sumFamily_d N F X hn)

/-- If all coends with the summands are acyclic, so is the coend with their coproduct. -/
theorem isAcyclic_directSum (hF : ∀ j, DG.IsAcyclic (T j)) :
    DG.IsAcyclic (CatTensorProduct N L) :=
  isAcyclic_of_addEquiv (directSumDGEquiv N F)
    (DG.DirectSum.isAcyclic_directSum _ hF)

end DG.CatTensorProduct
