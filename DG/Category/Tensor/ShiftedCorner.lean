import DG.Category.Tensor.Shift
import DG.Category.Tensor.Coproducts
import DG.Category.Homotopy.Precomp
import DG.Category.Derived.FiniteCell

/-!
# Acyclicity of shifted coends and representable corner coends

The signed transpose transfers the shift comparison to the left module
argument. Co-Yoneda and the representable retract handle corners.
-/

noncomputable section
namespace DG.CatTensorProduct
open CategoryTheory DGOpposite

universe w v u
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]

theorem acyclic_of_DGAddEquiv {P Q : Type*} [AddCommGroup P] [AddCommGroup Q]
    [DGAddCommGroup P] [DGAddCommGroup Q]
    (e : DGAddEquiv P Q) (h : DG.IsAcyclic Q) : DG.IsAcyclic P := by
  refine DG.isAcyclic_iff.mpr fun _ x hx hdx => ?_
  obtain ⟨y, hy, hdy⟩ := h.exists_d_eq (e.map_mem hx) (by rw [← e.map_d, hdx, map_zero])
  exact ⟨e.symm y, e.symm.map_mem hy, e.injective (by rw [e.map_d, e.apply_symm_apply, hdy])⟩

/-- A left shift preserves acyclicity of a coend. -/
theorem isAcyclic_shift_right (N : CatModule.{w} (DGOpposite C)) (M : CatModule.{w} C) (j : ℤ)
    (h₀ : ∀ {X Y : C} (f : X ⟶ Y), f ∈ grading (0 : ℤ))
    (h : DG.IsAcyclic (CatTensorProduct N M)) :
    DG.IsAcyclic (CatTensorProduct N (CatModule.shift j M)) := by
  let e : transposeLeftModule (CatModule.shift j M) ≅ CatModule.shift j (transposeLeftModule M) :=
    CatModule.precompShiftIso (doubleUnopFunctor C) j M
  have h₀' {X Y : DGOpposite C} (f : X ⟶ Y) : f ∈ grading (0 : ℤ) := h₀ (homUnop f)
  have htrans : DG.IsAcyclic (CatTensorProduct (transposeLeftModule M) N) :=
    acyclic_of_DGAddEquiv (transposeDGEquiv N M h₀).symm h
  exact acyclic_of_DGAddEquiv
    ((transposeDGEquiv N (CatModule.shift j M) h₀).trans (congr e (Iso.refl N)))
    (acyclic_of_DGAddEquiv (shiftLeftDGEquiv (transposeLeftModule M) N j h₀') (htrans.shift j))

/-- Acyclic right modules have acyclic coend against a representable corner. -/
theorem isAcyclic_corner {N : CatModule.{v} (DGOpposite C)} (hN : CatModule.IsAcyclic N)
    {X : C} (e : DGCategory.Idempotent X) :
    DG.IsAcyclic (CatTensorProduct N (CatModule.corner e)) := by
  let R : CatModule.{v} C := CatModule.representable X
  let E : CatModule.{v} C := CatModule.corner e
  let r : Retract E R := CatModule.cornerRetract e
  have hr : DG.IsAcyclic (CatTensorProduct N R) := isAcyclic_rid hN X
  have hid : 𝟙 N ≫ 𝟙 N = 𝟙 N := Category.id_comp _
  exact isAcyclic_of_tensor_retract (𝟙 N) (𝟙 N) r.i r.r hid r.retract hr

end DG.CatTensorProduct
